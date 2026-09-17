#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
IMEI-помощник (мобильная версия) — определение модели по TAC и подбор IMEI2.

Однофайловая сборка под Android/iOS (Flet 1.0 + serious_python), по образцу
приложения учёта топлива: то же хранилище (JSON в FLET_APP_STORAGE_DATA),
те же обёртки совместимости для диалогов/меню и та же схема «боковое меню
вместо нижней навигации».

Отличия от десктопной версии (core/ + ui/):
  * SQLite заменён на JSON-файл — на мобильной сборке так надёжнее и не нужен
    отдельный файл БД рядом с приложением;
  * статистика пар считается тем же способом (комбинация TAC2+офсет с
    затуханием веса по возрасту и повышенным весом ручных подтверждений),
    но без sqlite-слоя;
  * интерфейс переделан под узкий экран: карточки в один столбец вместо
    сайдбара и широких таблиц.

Запуск на компьютере:  pip install flet && python imei_app.py
"""

import datetime
import json
import os
import re
import inspect
import shutil
from urllib.parse import quote

import flet as ft
import httpx

# --------------------------------------------------------------------------
# Палитра — та же, что в ui/theme.py десктопной версии, чтобы приложения
# выглядели как одна линейка, а не как два разных продукта.
# --------------------------------------------------------------------------
BG_DARK = "#14101f"
BG_PANEL = "#1c1730"
BG_CARD = "#231d3d"
BORDER_GLASS = "#3a3260"
TEXT_MAIN = "#f2f0fa"
TEXT_MUTED = "#9b93b8"
ACCENT_1 = "#7c5cff"
ACCENT_2 = "#ff5ec4"
ACCENT_3 = "#4fd6ff"
SUCCESS = "#3ddc97"
WARNING = "#ffb84f"
DANGER = "#ff5c7a"

STORE_KEY = "imei_helper_data_v1"


# ==========================================================================
#                        ЧИСТАЯ ЛОГИКА IMEI (без UI)
# ==========================================================================

DIGITS_RE = re.compile(r"\D")
IMEI_RE = re.compile(r"\b\d{15}\b")
TAC_RE = re.compile(r"\b\d{8}\b")


def clean_digits(value):
    return DIGITS_RE.sub("", value or "")


def extract_imeis_and_tacs(text):
    """Вытаскивает из произвольного текста все IMEI (15 цифр) и отдельно TAC
    (8 цифр, которые не являются началом уже найденного IMEI)."""
    imeis = IMEI_RE.findall(text or "")
    all_8 = TAC_RE.findall(text or "")
    tacs = [t for t in all_8 if not any(t == imei[:8] for imei in imeis)]
    return imeis, tacs


def luhn_check_digit(imei14):
    if len(imei14) != 14 or not imei14.isdigit():
        return 0
    checksum = 0
    for i, ch in enumerate(reversed(imei14)):
        d = int(ch)
        if i % 2 == 0:
            d *= 2
            if d > 9:
                d -= 9
        checksum += d
    return (10 - (checksum % 10)) % 10


def luhn_valid(imei):
    if len(imei) != 15 or not imei.isdigit():
        return False
    return luhn_check_digit(imei[:14]) == int(imei[14])


def apply_luhn(imei14):
    return imei14 + str(luhn_check_digit(imei14))


def imeisv_to_imei(imeisv):
    """IMEISV (16 цифр, последние две — версия прошивки) → обычный IMEI."""
    d = clean_digits(imeisv)
    if len(d) != 16:
        return None
    return apply_luhn(d[:14])


def apply_digit_rule(imei1, base_tac, position, delta):
    """Правило вида «разница между каналами в N-й цифре ±D».
    position — 1-индексация по всем 15 цифрам IMEI."""
    if len(imei1) != 15 or len(base_tac) != 8:
        return None
    idx0 = position - 1
    if not (0 <= idx0 < 14):
        return None
    body = list(base_tac + imei1[8:14])
    body[idx0] = str((int(body[idx0]) + delta) % 10)
    return apply_luhn("".join(body))


_RULE_CROSS_TAC_REF = re.compile(r"см\.?\s*(\d{6,})")
_RULE_DIGIT_OFFSET = re.compile(r"(\d{1,2})-[йяе]\s*цифр\w*\s*\(?\+?-(\d+)", re.IGNORECASE)
_RULE_SHARED_IMEI = re.compile(r"один\s*imei|1\s*imei\s*на\s*оба", re.IGNORECASE)
_RULE_LIBRARY = re.compile(r"библиотек", re.IGNORECASE)
_RULE_HYBRID = re.compile(r"гибридн", re.IGNORECASE)


def parse_imei2_rule(text):
    """Разбор поля «доп. информация» из базы моделей в формальное правило.
    Порядок проверок важен: сначала самое конкретное."""
    if not text:
        return None
    if _RULE_SHARED_IMEI.search(text):
        return {"type": "shared_imei"}
    m = _RULE_CROSS_TAC_REF.search(text)
    if m:
        return {"type": "cross_tac_ref", "partner_tac": m.group(1)}
    m = _RULE_DIGIT_OFFSET.search(text)
    if m:
        return {"type": "digit_offset", "position": int(m.group(1)), "delta": int(m.group(2))}
    if _RULE_LIBRARY.search(text):
        return {"type": "library"}
    if _RULE_HYBRID.search(text):
        return {"type": "hybrid"}
    return None


def fmt_count(n):
    """Разряды через неразрывный пробел: 271 480 читается с телефона легче,
    чем 271480."""
    return "{:,}".format(int(n or 0)).replace(",", "\u00a0")


def is_single_sim(dev):
    """True, если по карточке модели это односимочный аппарат без eSIM —
    подбирать IMEI2 тогда бессмысленно, и честнее сказать об этом сразу."""
    if not dev:
        return False
    if str(dev.get("imei_count", "")).strip() == "1":
        return True
    if str(dev.get("sim_type", "")).strip() == "1":
        return True
    return False


# --------------------------------------------------------------------------
# Непроверенное предположение — когда для TAC нет ни правила, ни пары.
#
# Важно: никакой производитель формулу связи IMEI1↔IMEI2 официально не
# публикует. Ни у GSMA, ни в документации Samsung/LG такой зависимости нет —
# проверено поиском. Схемы ниже — это распространённая среди техников
# практика (последовательные серийники одного TAC при производстве,
# наблюдаемый на части Samsung/LG/Motorola/Nokia сдвиг одной цифры), но это
# именно ДОГАДКА, а не факт, и в интерфейсе она обязана показываться
# отдельно от достоверных результатов — с явной пометкой и без процента
# уверенности, который выглядел бы как ложная точность.

def guess_unverified(imei1, brand=""):
    if len(imei1) != 15:
        return None
    bl = (brand or "").lower()
    if "samsung" in bl:
        digits = list(imei1)
        digits[5] = str((int(digits[5]) + 1) % 10)
        return apply_luhn("".join(digits[:14])), \
            "Догадка по практике Samsung: 6-я цифра +1 (не подтверждено производителем)"
    if any(b in bl for b in ("lg", "motorola", "nokia", "lenovo", "asus")):
        digits = list(imei1)
        digits[13] = str((int(digits[13]) + 1) % 10)
        return apply_luhn("".join(digits[:14])), \
            "Догадка по практике LG/Motorola/Nokia: 14-я цифра +1 (не подтверждено)"
    # Общий запасной вариант: серийник в том же TAC +1 — так часто нумеруют
    # партии на производстве, но это тоже не задокументированное правило.
    tac, snr = imei1[:8], int(imei1[8:14])
    cand = apply_luhn(tac + "%06d" % ((snr + 1) % 1000000))
    if cand != imei1:
        return cand, "Догадка: серийный номер +1 в том же TAC (не подтверждено)"
    return None


def guess_imei2(imei1, dev_get, pair_get):
    """Возвращает IMEI2 с явной пометкой достоверности ("reliable"):

      reliable=True  — есть основание: правило из карточки модели (сдвиг
                       цифры / общий IMEI / ссылка на партнёрский TAC) или
                       запись в библиотеке TAC-пар;
      reliable=False — ничего из этого нет, показан лишь наименее плохой
                       вариант из непроверенной практики (guess_unverified),
                       и интерфейс обязан показать его отдельно, не как факт.

    dev_get(tac)  — карточка модели по TAC (правки пользователя, затем
                    вшитая база) или None;
    pair_get(tac) — партнёрский TAC из библиотеки пар или None."""
    imei1 = clean_digits(imei1)
    empty = {"imei2": None, "method": "", "confidence": None, "reliable": False}
    if len(imei1) != 15:
        return empty

    tac1 = imei1[:8]
    dev = dev_get(tac1)
    if not dev:
        return empty

    # Правило хранится в готовом виде (rule_type/rule_param — так его пишет
    # своя база и разбирает вшитая), либо разбирается на лету из «доп.
    # информации», если карточка заведена вручную без этих полей.
    if dev.get("rule_type"):
        rule = {"type": dev["rule_type"]}
        if dev["rule_type"] == "cross_tac_ref":
            rule["partner_tac"] = dev.get("rule_param")
        elif dev["rule_type"] == "digit_offset" and ":" in str(dev.get("rule_param", "")):
            pos_s, delta_s = str(dev["rule_param"]).split(":", 1)
            try:
                rule = {"type": "digit_offset", "position": int(pos_s), "delta": int(delta_s)}
            except ValueError:
                rule = None
    else:
        rule = parse_imei2_rule(dev.get("specs", ""))

    if rule and rule.get("type") == "shared_imei":
        return {"imei2": imei1, "method": "Общий IMEI на оба канала (данные модели)",
                "confidence": 1.0, "reliable": True}

    partner_tac, partner_source = None, ""
    if rule and rule.get("type") == "cross_tac_ref" and rule.get("partner_tac"):
        partner_tac = str(rule["partner_tac"])[:8]
        partner_source = "по данным модели"
    else:
        from_lib = pair_get(tac1)
        if from_lib:
            partner_tac = str(from_lib)[:8]
            partner_source = "по библиотеке TAC-пар"

    if rule and rule.get("type") == "digit_offset" and rule.get("position"):
        base_tac = partner_tac or tac1
        cand = apply_digit_rule(imei1, base_tac, rule["position"], rule["delta"])
        if cand and cand != imei1:
            return {"imei2": cand,
                    "method": "Правило модели: %d-я цифра %+d" % (rule["position"], rule["delta"]),
                    "confidence": 0.95, "reliable": True}

    if partner_tac and partner_tac != tac1:
        cand = apply_luhn(partner_tac + imei1[8:14])
        return {"imei2": cand,
                "method": "TAC второго канала известен (%s), серийник тот же" % partner_source,
                "confidence": 0.7, "reliable": True}

    # Достоверных данных нет — пробуем непроверенную догадку, но честно
    # помечаем её как таковую.
    guess = guess_unverified(imei1, dev.get("brand", ""))
    if guess:
        cand, method = guess
        return {"imei2": cand, "method": method, "confidence": None, "reliable": False}

    return empty


# ==========================================================================
#            ГОТОВАЯ БАЗА TAC, ВШИТАЯ В СБОРКУ (только чтение)
# ==========================================================================
# Большую базу (сотни тысяч TAC) нельзя держать в JSON: разбор такого файла
# при запуске займёт десятки секунд, а словарь в памяти — сотни мегабайт,
# чего на телефоне просто нет. Поэтому файл tac_database.db из настольной
# версии кладётся рядом с main.py в репозитории, попадает в APK как есть и
# читается запросом по одному TAC — память не расходуется вообще.
#
# Схема совпадает с core/repository.py настольной версии, так что файл
# берётся без переделки: таблицы tac_devices и (если есть) tac_pairs_lib.

try:
    import sqlite3
except Exception:          # на всякий случай: сборка без sqlite3
    sqlite3 = None

BUNDLED_DB_NAMES = ("tac_database.db", "tac_base.db", "tacs.db")

DB_EXTRA_COLUMNS = [
    "model", "model_code", "case_type", "chip", "platform", "sim_slots",
    "imei_count", "sim_type", "release_year", "manufacturer", "device_type",
    "network_gen", "form_factor", "compat_class",
    "imei2_rule_type", "imei2_rule_param",
]
DB_DEVICE_COLUMNS_WHITELIST = ["tac", "brand", "specs"] + DB_EXTRA_COLUMNS
DB_PAIRS_COLUMNS_WHITELIST = ["tac", "partner_tac", "form"]


class BundledBase:
    """Справочник моделей, вшитый в приложение. Все методы безопасны:
    если файла нет или он повреждён, база просто считается пустой, и
    приложение продолжает работать на том, что пользователь завёл сам."""

    def __init__(self):
        self.conn = None
        self.path = None
        self.error = None
        self.columns = []
        self.has_pairs = False
        if sqlite3 is None:
            self.error = "в этой сборке нет модуля sqlite3"
            return
        # Где искать файл базы. На Android приложение распаковывается в
        # отдельную папку, и надёжнее всего отталкиваться от каталога самого
        # main.py; но __file__ есть не во всех режимах запуска (например, при
        # компиляции в .pyc или запуске через exec), поэтому проверяем ещё
        # текущий каталог и папку данных приложения.
        search_dirs = []
        try:
            search_dirs.append(os.path.dirname(os.path.abspath(__file__)))
        except NameError:
            pass
        search_dirs.append(os.getcwd())
        app_dir = os.getenv("FLET_APP_STORAGE_DATA")
        if app_dir:
            search_dirs.append(app_dir)

        for directory in search_dirs:
            for name in BUNDLED_DB_NAMES:
                candidate = os.path.join(directory, name)
                if os.path.isfile(candidate):
                    self.path = candidate
                    break
            if self.path:
                break
        if not self.path:
            return
        try:
            # Только чтение: файл внутри установленного приложения менять
            # нельзя, и попытка записи на Android приводит к ошибке.
            try:
                self.conn = sqlite3.connect(
                    "file:%s?mode=ro" % self.path, uri=True, check_same_thread=False)
            except Exception:
                self.conn = sqlite3.connect(self.path, check_same_thread=False)
            self.columns = [r[1] for r in self.conn.execute("PRAGMA table_info(tac_devices)")]
            if not self.columns:
                raise ValueError("в файле нет таблицы tac_devices")
            self.has_pairs = bool(list(self.conn.execute(
                "SELECT name FROM sqlite_master WHERE type='table' AND name='tac_pairs_lib'")))
        except Exception as ex:
            self.conn = None
            self.error = str(ex)

    @property
    def available(self):
        return self.conn is not None

    def get(self, tac):
        if not self.conn or len(tac) != 8:
            return None
        cols = ["brand", "specs"] + [c for c in DB_EXTRA_COLUMNS if c in self.columns]
        cols = [c for c in cols if c in self.columns]
        if not cols:
            return None
        try:
            row = self.conn.execute(
                "SELECT %s FROM tac_devices WHERE tac = ?" % ", ".join(cols), (tac,)
            ).fetchone()
        except Exception:
            return None
        if row is None:
            return None
        rec = {}
        for key, value in zip(cols, row):
            if value not in (None, ""):
                rec[key] = value
        # Настольная версия хранит разобранное правило в отдельных колонках —
        # приводим к тем же именам, что использует подбор здесь.
        if "imei2_rule_type" in rec:
            rec["rule_type"] = rec.pop("imei2_rule_type")
        if "imei2_rule_param" in rec:
            rec["rule_param"] = rec.pop("imei2_rule_param")
        return rec

    def partner_tac(self, tac):
        if not self.conn or not self.has_pairs:
            return None
        try:
            row = self.conn.execute(
                "SELECT partner_tac FROM tac_pairs_lib WHERE tac = ?", (tac,)).fetchone()
        except Exception:
            return None
        return row[0] if row else None

    def search(self, query, limit=60):
        """Поиск по TAC, бренду и модели. Запрос идёт в SQLite с LIMIT, а не
        перебором в Python — иначе на большой базе экран подвисал бы."""
        if not self.conn or not query:
            return []
        like = "%" + query.strip() + "%"
        name_cols = [c for c in ("brand", "model", "model_code") if c in self.columns]
        where = ["tac LIKE ?"] + ["%s LIKE ?" % c for c in name_cols]
        params = [query.strip() + "%"] + [like] * len(name_cols)
        cols = ["tac", "brand"] + (["model"] if "model" in self.columns else []) + \
               (["specs"] if "specs" in self.columns else [])
        try:
            rows = self.conn.execute(
                "SELECT %s FROM tac_devices WHERE %s LIMIT ?"
                % (", ".join(cols), " OR ".join(where)), params + [limit]).fetchall()
        except Exception:
            return []
        out = []
        for row in rows:
            rec = {k: (v if v is not None else "") for k, v in zip(cols, row)}
            out.append((rec.pop("tac"), rec))
        return out

    def count(self):
        if not self.conn:
            return 0
        try:
            return self.conn.execute("SELECT COUNT(*) FROM tac_devices").fetchone()[0]
        except Exception:
            return 0

    def pairs_count(self):
        if not self.conn or not self.has_pairs:
            return 0
        try:
            return self.conn.execute("SELECT COUNT(*) FROM tac_pairs_lib").fetchone()[0]
        except Exception:
            return 0

    def close(self):
        if self.conn:
            try:
                self.conn.close()
            except Exception:
                pass
            self.conn = None


def merge_database_file(new_path, dest_path):
    """Вливает файл new_path в рабочую базу dest_path, не стирая то, что там
    уже было: TAC, которых не было — добавляются; TAC, которые уже были —
    обновляются данными из нового файла (он считается более свежим).
    Если рабочей базы ещё нет — новый файл становится ею целиком, это
    просто копирование, без построчной вставки.

    Список разрешённых колонок (DB_DEVICE_COLUMNS_WHITELIST /
    DB_PAIRS_COLUMNS_WHITELIST) — это подстраховка при формировании SQL:
    имена колонок туда никогда не приходят от пользователя напрямую, но
    так спокойнее.

    Возвращает (added, updated, pairs_added) или бросает исключение с
    понятным текстом, если файл не похож на такую же базу."""
    if sqlite3 is None:
        raise RuntimeError("в этой сборке нет модуля sqlite3")
    if not os.path.isfile(dest_path):
        shutil.copyfile(new_path, dest_path)
        total = sqlite3.connect(new_path).execute("SELECT COUNT(*) FROM tac_devices").fetchone()[0]
        return total, 0, 0

    conn = sqlite3.connect(dest_path)
    try:
        conn.execute("ATTACH DATABASE ? AS newdb", (new_path,))

        dest_cols = [r[1] for r in conn.execute("PRAGMA table_info(tac_devices)")]
        new_cols = [r[1] for r in conn.execute("PRAGMA newdb.table_info(tac_devices)")]
        if "tac" not in new_cols:
            raise ValueError("в выбранном файле нет таблицы tac_devices с колонкой tac")
        common = [c for c in DB_DEVICE_COLUMNS_WHITELIST if c in dest_cols and c in new_cols]
        collist = ", ".join(common)

        before = conn.execute("SELECT COUNT(*) FROM tac_devices").fetchone()[0]
        overlap = conn.execute(
            "SELECT COUNT(*) FROM newdb.tac_devices WHERE tac IN (SELECT tac FROM tac_devices)"
        ).fetchone()[0]
        conn.execute("INSERT OR REPLACE INTO tac_devices (%s) SELECT %s FROM newdb.tac_devices"
                     % (collist, collist))

        pairs_added = 0
        has_pairs_new = bool(list(conn.execute(
            "SELECT name FROM newdb.sqlite_master WHERE type='table' AND name='tac_pairs_lib'")))
        if has_pairs_new:
            has_pairs_dest = bool(list(conn.execute(
                "SELECT name FROM sqlite_master WHERE type='table' AND name='tac_pairs_lib'")))
            if not has_pairs_dest:
                conn.execute("CREATE TABLE tac_pairs_lib "
                            "(tac TEXT PRIMARY KEY, partner_tac TEXT NOT NULL, form TEXT)")
            new_pcols = [r[1] for r in conn.execute("PRAGMA newdb.table_info(tac_pairs_lib)")]
            dest_pcols = [r[1] for r in conn.execute("PRAGMA table_info(tac_pairs_lib)")]
            pcommon = [c for c in DB_PAIRS_COLUMNS_WHITELIST if c in dest_pcols and c in new_pcols]
            if "tac" in pcommon:
                pcollist = ", ".join(pcommon)
                pairs_added = conn.execute("SELECT COUNT(*) FROM newdb.tac_pairs_lib").fetchone()[0]
                conn.execute("INSERT OR REPLACE INTO tac_pairs_lib (%s) SELECT %s FROM newdb.tac_pairs_lib"
                             % (pcollist, pcollist))

        conn.commit()
        after = conn.execute("SELECT COUNT(*) FROM tac_devices").fetchone()[0]
    finally:
        try:
            conn.execute("DETACH DATABASE newdb")
        except Exception:
            pass
        conn.close()

    added = after - before
    updated = overlap
    return added, updated, pairs_added


# ==========================================================================
#                              ХРАНИЛИЩЕ
# ==========================================================================
# Тот же подход, что в приложении учёта топлива: client_storage на мобильной
# сборке доступен не всегда, поэтому пишем обычный JSON в постоянную папку
# приложения FLET_APP_STORAGE_DATA — её Flet гарантирует на всех платформах.

APP_DATA_DIR = os.getenv("FLET_APP_STORAGE_DATA") or "."
DATA_FILE_PATH = os.path.join(APP_DATA_DIR, STORE_KEY + ".json")


def storage_get():
    if not os.path.exists(DATA_FILE_PATH):
        return None
    try:
        with open(DATA_FILE_PATH, "r", encoding="utf-8") as f:
            return f.read()
    except Exception:
        return None


def storage_set(value):
    os.makedirs(APP_DATA_DIR, exist_ok=True)
    with open(DATA_FILE_PATH, "w", encoding="utf-8") as f:
        f.write(value)


DEVICE_FIELDS = [
    ("brand", "Бренд"),
    ("model", "Модель"),
    ("model_code", "Код модели"),
    ("manufacturer", "Производитель"),
    ("device_type", "Тип устройства"),
    ("chip", "Чип"),
    ("platform", "Платформа"),
    ("sim_slots", "Слотов SIM"),
    ("imei_count", "Кол-во IMEI"),
    ("sim_type", "Тип SIM"),
    ("release_year", "Год"),
    ("specs", "Доп. информация"),
]


# ==========================================================================
#                    ФОТО МОДЕЛИ (по запросу, с кэшем)
# ==========================================================================
# Своей базы фотографий нет и не будет: заранее скачивать и хранить снимки
# для сотен тысяч TAC — это и огромный размер APK, и вопрос прав на чужие
# фото производителей. Вместо этого при показе конкретной модели картинка
# по запросу ищется через открытый API Википедии (без ключа, свободные
# лицензии) и один раз кэшируется локально по TAC — повторно эта модель
# сеть уже не дёргает. Если сети нет или карточки не нашлось — просто нет
# фото, само приложение от этого не ломается.

async def lookup_device_image(brand, model):
    query = " ".join(x for x in [(brand or "").strip(), (model or "").strip()] if x)
    if not query:
        return None
    try:
        async with httpx.AsyncClient(timeout=6.0, follow_redirects=True) as client:
            r = await client.get("https://en.wikipedia.org/w/api.php", params={
                "action": "query", "list": "search", "srsearch": query,
                "format": "json", "srlimit": 1,
            })
            hits = r.json().get("query", {}).get("search", [])
            if not hits:
                return None
            title = hits[0]["title"]
            r2 = await client.get(
                "https://en.wikipedia.org/api/rest_v1/page/summary/" + quote(title, safe=""))
            data = r2.json()
            thumb = (data.get("thumbnail") or {}).get("source")
            return thumb or None
    except Exception:
        return None


# ==========================================================================
#                                ПРИЛОЖЕНИЕ
# ==========================================================================

async def main(page: ft.Page):
    page.title = "IMEI-помощник"
    page.theme_mode = ft.ThemeMode.DARK
    page.bgcolor = BG_DARK

    state = {
        "devices": {},     # TAC -> карточка модели
        "tac_pairs": {},   # TAC -> партнёрский TAC (библиотека пар)
        "history": [],
        "tab": 0,
        "last": None,      # результат последней проверки
        "image_cache": {}, # TAC -> URL фото или "" (уже искали — не нашлось)
    }
    base = BundledBase()
    file_picker = ft.FilePicker()
    page.services.append(file_picker)

    async def import_database(e=None):
        """Вливает выбранный .db-файл в базу приложения, не стирая то, что
        там уже было — новые модели добавляются, уже известные обновляются.
        Работает без пересборки APK: скачал файл на телефон любым способом
        (Telegram, Google Диск, кабель) и указал его здесь."""
        nonlocal base
        path = None
        last_err = None
        for name in ("pick_files_async", "pick_files"):
            fn = getattr(file_picker, name, None)
            if fn is None:
                continue
            try:
                result = fn(allow_multiple=False, allowed_extensions=["db", "sqlite", "sqlite3"])
            except TypeError:
                try:
                    result = fn()
                except Exception as ex:
                    last_err = ex
                    continue
            except Exception as ex:
                last_err = ex
                continue
            if inspect.isawaitable(result):
                try:
                    result = await result
                except Exception as ex:
                    last_err = ex
                    continue
            # Результат бывает по-разному оформлен в зависимости от сборки
            # Flet: то список файлов напрямую, то объект с атрибутом .files,
            # то результат нужно брать отдельно из file_picker.result.
            files = None
            if isinstance(result, list):
                files = result
            elif result is not None and getattr(result, "files", None):
                files = result.files
            if not files:
                fallback = getattr(file_picker, "result", None)
                if isinstance(fallback, list):
                    files = fallback
                elif fallback is not None and getattr(fallback, "files", None):
                    files = fallback.files
            picked = files[0] if files else None
            path = getattr(picked, "path", None) if picked is not None else None
            if path:
                break
        if not path:
            if last_err:
                snack("Не удалось открыть выбор файла: " + str(last_err))
            else:
                snack("Файл не выбран")
            return
        try:
            os.makedirs(APP_DATA_DIR, exist_ok=True)
            dest = os.path.join(APP_DATA_DIR, "tac_database.db")
            # Закрываем текущее соединение перед записью в тот же файл —
            # иначе запись может конфликтовать с открытым read-only курсором.
            base.close()
            added, updated, pairs_added = merge_database_file(path, dest)
        except Exception as ex:
            snack("Не удалось объединить базы: " + str(ex))
            base = BundledBase()
            render()
            return
        base = BundledBase()
        if base.available:
            parts = ["новых моделей: %s" % fmt_count(added)]
            if updated:
                parts.append("обновлено: %s" % fmt_count(updated))
            if pairs_added:
                parts.append("TAC-пар: %s" % fmt_count(pairs_added))
            snack("Добавлено — " + ", ".join(parts) + ". Всего в базе: %s"
                  % fmt_count(base.count()))
        else:
            snack("Файл обработан, но база не распознана (%s)"
                  % (base.error or "неизвестная ошибка"))
        render()

    # Поиск модели: сначала то, что пользователь завёл или поправил сам
    # (его правка должна побеждать вшитую базу), затем большая база из сборки.
    def dev_get(tac):
        if not tac or len(tac) != 8:
            return None
        own = state["devices"].get(tac)
        if own:
            return own
        return base.get(tac)

    def pair_get(tac):
        if not tac:
            return None
        return state["tac_pairs"].get(tac) or base.partner_tac(tac)

    def check_guess(imei):
        return guess_imei2(imei, dev_get, pair_get)

    async def save_all():
        storage_set(json.dumps({
            "devices": state["devices"],
            "tac_pairs": state["tac_pairs"],
            "history": state["history"][-500:],
            "image_cache": state["image_cache"],
        }, ensure_ascii=False))

    async def load_all():
        raw = storage_get()
        data = json.loads(raw) if raw else {}
        state["devices"] = data.get("devices", {})
        state["tac_pairs"] = data.get("tac_pairs", {})
        state["history"] = data.get("history", [])
        state["image_cache"] = data.get("image_cache", {})

    async def ensure_device_image(tac, brand, model, force=False):
        """Подгружает фото модели в фоне и один раз перерисовывает экран,
        когда оно готово — сам показ результата это не блокирует."""
        if not tac:
            return
        if not force and tac in state["image_cache"]:
            return
        url = await lookup_device_image(brand, model)
        state["image_cache"][tac] = url or ""
        await save_all()
        last = state.get("last")
        if last:
            relevant_tacs = {last["imei1"][:8]}
            imei2 = (last["guess"] or {}).get("imei2")
            if imei2:
                relevant_tacs.add(imei2[:8])
            if tac in relevant_tacs:
                render()



    # ---------- совместимость оверлеев (как в приложении по топливу) ----------
    # Разные сборки Flet по-разному показывают диалоги, меню и снекбары:
    # где-то show_x(control), где-то show_x(), где-то только page.open().
    # Эти обёртки перебирают варианты, поэтому остальной код от сборки не зависит.

    def _show_overlay(page_prop, method_name, control):
        try:
            setattr(page, page_prop, control)
        except Exception:
            pass
        try:
            control.open = True
        except Exception:
            pass
        fn = getattr(page, method_name, None)
        if fn is not None:
            try:
                fn(control)
                page.update()
                return
            except TypeError:
                try:
                    fn()
                    page.update()
                    return
                except TypeError:
                    pass
        try:
            page.open(control)
            page.update()
            return
        except AttributeError:
            pass
        page.overlay.append(control)
        page.update()

    def _hide_overlay(method_name, control):
        if control is not None:
            try:
                control.open = False
            except Exception:
                pass
        fn = getattr(page, method_name, None)
        if fn is not None:
            try:
                fn()
                page.update()
                return
            except TypeError:
                try:
                    fn(control)
                    page.update()
                    return
                except TypeError:
                    pass
        try:
            page.close(control)
            page.update()
            return
        except AttributeError:
            pass
        page.update()

    def open_dialog(dlg):
        _show_overlay("dialog", "show_dialog", dlg)

    def close_dialog(dlg=None):
        _hide_overlay("pop_dialog", dlg)

    def snack(msg):
        _show_overlay("dialog", "show_dialog", ft.SnackBar(ft.Text(msg)))

    def copy_text(value, msg="Скопировано"):
        try:
            page.set_clipboard(value)
            snack(msg)
        except Exception:
            snack("Не удалось скопировать — выделите текст вручную")

    # ---------- строительные блоки оформления ----------

    def safe_gradient(colors):
        # LinearGradient/Alignment отличаются между сборками Flet — если
        # конструктор не подошёл, карточка просто будет одноцветной.
        try:
            return ft.LinearGradient(begin=ft.Alignment.TOP_LEFT,
                                     end=ft.Alignment.BOTTOM_RIGHT, colors=colors)
        except Exception:
            return None

    def card(content, padding=16, bgcolor=BG_CARD, gradient=None, border_color=BORDER_GLASS):
        kwargs = dict(content=content, padding=padding, border_radius=20,
                      bgcolor=None if gradient else bgcolor)
        if gradient is not None:
            kwargs["gradient"] = gradient
        try:
            kwargs["border"] = ft.Border.all(1, border_color)
        except Exception:
            pass
        try:
            return ft.Container(**kwargs)
        except Exception:
            kwargs.pop("border", None)
            kwargs.pop("gradient", None)
            return ft.Container(**kwargs)

    def muted(text, size=12):
        return ft.Text(text, size=size, color=TEXT_MUTED)

    def title_row(text, icon=None, color=ACCENT_3):
        controls = []
        if icon:
            controls.append(ft.Icon(icon, color=color, size=20))
        controls.append(ft.Text(text, size=16, weight=ft.FontWeight.W_600, color=TEXT_MAIN))
        return ft.Row(controls, spacing=8)

    def stat_chip(label, value, color=ACCENT_3):
        return card(ft.Column([
            muted(label, 11),
            ft.Text(value, size=18, weight=ft.FontWeight.BOLD, color=color),
        ], spacing=2, tight=True), padding=14, bgcolor=BG_PANEL)

    def imei_text(value, size=22, color=TEXT_MAIN):
        # Моноширинный шрифт: цифры IMEI проще сверять с экраном телефона,
        # когда они не «пляшут» по ширине.
        return ft.Text(value, size=size, color=color, weight=ft.FontWeight.W_600,
                       font_family="monospace", selectable=True)

    def field(label, value="", **kw):
        return ft.TextField(
            label=label, value=value, border_radius=14,
            bgcolor=BG_PANEL, border_color=BORDER_GLASS,
            focused_border_color=ACCENT_1, color=TEXT_MAIN,
            label_style=ft.TextStyle(color=TEXT_MUTED) if hasattr(ft, "TextStyle") else None,
            **kw)

    def primary_button(text, icon=None, on_click=None, expand=False):
        label = ft.Row([], spacing=8, alignment=ft.MainAxisAlignment.CENTER)
        if icon:
            label.controls.append(ft.Icon(icon, size=18, color="white"))
        label.controls.append(ft.Text(text, color="white", weight=ft.FontWeight.W_600, size=14))
        g = safe_gradient([ACCENT_1, ACCENT_2])
        kwargs = dict(content=label, padding=ft.Padding.symmetric(horizontal=18, vertical=14),
                      border_radius=16, ink=True, on_click=on_click,
                      alignment=ft.Alignment.CENTER, expand=expand)
        if g is not None:
            kwargs["gradient"] = g
        else:
            kwargs["bgcolor"] = ACCENT_1
        try:
            return ft.Container(**kwargs)
        except Exception:
            return ft.Button(content=text, icon=icon, on_click=on_click)

    def ghost_button(text, icon=None, on_click=None, expand=False, color=ACCENT_3):
        label = ft.Row([], spacing=8, alignment=ft.MainAxisAlignment.CENTER)
        if icon:
            label.controls.append(ft.Icon(icon, size=16, color=color))
        label.controls.append(ft.Text(text, color=color, weight=ft.FontWeight.W_500, size=13))
        kwargs = dict(content=label, padding=ft.Padding.symmetric(horizontal=14, vertical=12),
                      border_radius=14, ink=True, on_click=on_click, bgcolor=BG_PANEL,
                      alignment=ft.Alignment.CENTER, expand=expand)
        try:
            kwargs["border"] = ft.Border.all(1, BORDER_GLASS)
        except Exception:
            pass
        try:
            return ft.Container(**kwargs)
        except Exception:
            return ft.OutlinedButton(text, icon=icon, on_click=on_click)

    def confidence_bar(conf):
        """Полоса уверенности: цвет сразу говорит, можно ли доверять результату
        без ручной проверки."""
        pct = max(0.0, min(1.0, conf or 0.0))
        color = SUCCESS if pct >= 0.8 else (WARNING if pct >= 0.5 else DANGER)
        return ft.Column([
            ft.Row([
                muted("Уверенность", 11),
                ft.Text("%d%%" % round(pct * 100), size=12, color=color,
                        weight=ft.FontWeight.W_600),
            ], alignment=ft.MainAxisAlignment.SPACE_BETWEEN),
            ft.ProgressBar(value=pct, color=color, bgcolor=BG_PANEL,
                           border_radius=4, height=6),
        ], spacing=4, tight=True)

    # ==================================================================
    #                         ВКЛАДКА «ПРОВЕРКА»
    # ==================================================================

    check_input = field("IMEI — 15 цифр (или IMEISV — 16)", keyboard_type=ft.KeyboardType.NUMBER,
                        hint_text="например 356296901234567")

    def do_check(e=None):
        raw = clean_digits(check_input.value or "")
        if len(raw) == 16:
            conv = imeisv_to_imei(raw)
            if conv:
                raw = conv
                snack("IMEISV распознан и переведён в IMEI")
        if len(raw) < 14:
            snack("Нужно минимум 14 цифр")
            return
        if len(raw) == 14:
            raw = apply_luhn(raw)
            snack("Контрольная цифра рассчитана автоматически")
        raw = raw[:15]

        dev = dev_get(raw[:8])
        guess = check_guess(raw)
        state["last"] = {"imei1": raw, "dev": dev, "guess": guess,
                         "single_sim": is_single_sim(dev)}
        state["history"].append({
            "imei1": raw, "imei2": guess.get("imei2") or "",
            "brand": (dev or {}).get("brand", ""),
            "method": guess.get("method", ""),
            "at": datetime.datetime.now().isoformat(timespec="seconds"),
        })
        page.run_task(save_all)
        if dev:
            page.run_task(ensure_device_image, raw[:8], dev.get("brand", ""), dev.get("model", ""))
        render()

    def clear_check(e=None):
        check_input.value = ""
        state["last"] = None
        render()

    def device_card(dev, tac, title="Модель по TAC"):
        if not dev:
            return card(ft.Column([
                title_row(title, ft.Icons.DEVICES_OTHER),
                ft.Row([muted("TAC"), imei_text(tac, 15, TEXT_MUTED)], spacing=8),
                ft.Text("В базе нет такого TAC", color=WARNING, size=13),
                muted("Можно добавить её самому — тогда подбор для этой модели "
                      "будет опираться на правило, а не на перебор."),
                ghost_button("Добавить модель", ft.Icons.ADD,
                             (lambda t: lambda e: open_device_dialog(t))(tac)),
            ], spacing=10, tight=True))

        rows = [ft.Row([title_row(title, ft.Icons.SMARTPHONE), ft.Container(expand=True),
                        ft.IconButton(ft.Icons.EDIT, icon_color=TEXT_MUTED, icon_size=18,
                                      tooltip="Исправить карточку модели",
                                      on_click=(lambda t: lambda e: open_device_dialog(t))(tac))],
                       alignment=ft.MainAxisAlignment.SPACE_BETWEEN)]
        head = " ".join(x for x in [(dev.get("brand") or "").strip(),
                                    (dev.get("model") or "").strip()] if x)

        img_url = state["image_cache"].get(tac)
        if img_url:
            photo = ft.Image(src=img_url, width=56, height=56, fit=ft.ImageFit.COVER,
                             border_radius=12)
        elif tac not in state["image_cache"]:
            photo = ft.Container(width=56, height=56, border_radius=12, bgcolor=BG_PANEL,
                                 alignment=ft.Alignment.CENTER,
                                 content=ft.ProgressRing(width=18, height=18, stroke_width=2,
                                                         color=ACCENT_3))
        else:
            photo = ft.Container(
                width=56, height=56, border_radius=12, bgcolor=BG_PANEL, ink=True,
                alignment=ft.Alignment.CENTER,
                tooltip="Фото не нашлось — нажмите, чтобы поискать ещё раз",
                on_click=(lambda t, b, m: lambda e: (
                    state["image_cache"].pop(t, None),
                    page.run_task(ensure_device_image, t, b, m, True), render()))(
                    tac, dev.get("brand", ""), dev.get("model", "")),
                content=ft.Icon(ft.Icons.ADD_A_PHOTO_OUTLINED, color=TEXT_MUTED, size=18))

        rows.append(ft.Row([
            photo,
            ft.Column([
                ft.Text(head, size=18, weight=ft.FontWeight.BOLD, color=TEXT_MAIN)
                if head else ft.Container(height=0),
                ft.Row([muted("TAC"), imei_text(tac, 14, TEXT_MUTED)], spacing=8),
            ], spacing=4, tight=True, expand=True),
        ], spacing=12, vertical_alignment=ft.CrossAxisAlignment.CENTER))

        details = []
        for key, label in DEVICE_FIELDS:
            if key in ("brand", "model"):
                continue
            val = str(dev.get(key) or "").strip()
            if val:
                details.append(ft.Row([
                    ft.Container(content=muted(label, 11), width=120),
                    ft.Text(val, size=12, color=TEXT_MAIN, expand=True, selectable=True),
                ], spacing=8, vertical_alignment=ft.CrossAxisAlignment.START))
        if details:
            rows.append(ft.Divider(height=12, color=BORDER_GLASS))
            rows.extend(details)
        return card(ft.Column(rows, spacing=8, tight=True))

    def check_view():
        items = [
            card(ft.Column([
                title_row("Проверка IMEI", ft.Icons.SEARCH, ACCENT_2),
                muted("Введите IMEI1 — приложение определит модель по TAC "
                      "и подберёт IMEI2 для второй SIM."),
                check_input,
                ft.Row([
                    primary_button("Определить", ft.Icons.BOLT, do_check, expand=True),
                    ghost_button("Очистить", ft.Icons.CLOSE, clear_check),
                ], spacing=10),
            ], spacing=12, tight=True), gradient=safe_gradient(["#2a2350", "#241c3f"])),
        ]

        last = state["last"]
        if not last:
            items.append(card(ft.Column([
                ft.Icon(ft.Icons.QR_CODE_2, size=40, color=BORDER_GLASS),
                ft.Text("Результат появится здесь", color=TEXT_MUTED, size=13),
                muted("Второй IMEI показывается, только если для модели есть "
                      "достоверные данные — правило или пара TAC."),
            ], spacing=10, tight=True,
               horizontal_alignment=ft.CrossAxisAlignment.CENTER)))
            return ft.ListView(items, expand=True, spacing=14,
                               padding=ft.Padding.all(14))

        imei1, dev, guess = last["imei1"], last["dev"], last["guess"]

        # Корректность контрольной цифры.
        valid = luhn_valid(imei1)
        must_be = luhn_check_digit(imei1[:14])
        items.append(card(ft.Row([
            ft.Icon(ft.Icons.CHECK_CIRCLE if valid else ft.Icons.ERROR,
                    color=SUCCESS if valid else DANGER, size=22),
            ft.Column([
                ft.Text("IMEI1: " + imei1, size=15, color=TEXT_MAIN,
                        font_family="monospace", selectable=True,
                        weight=ft.FontWeight.W_600),
                muted("Контрольная цифра верна" if valid
                      else "Контрольная цифра неверна — должна быть %d" % must_be, 12),
            ], spacing=2, expand=True, tight=True),
            ft.IconButton(ft.Icons.COPY, icon_color=TEXT_MUTED,
                          on_click=lambda e: copy_text(imei1, "IMEI1 скопирован")),
        ], spacing=12, vertical_alignment=ft.CrossAxisAlignment.CENTER),
            bgcolor=BG_PANEL, border_color=SUCCESS if valid else DANGER))

        items.append(device_card(dev, imei1[:8]))

        # IMEI2.
        if last["single_sim"]:
            items.append(card(ft.Column([
                title_row("IMEI2", ft.Icons.SIM_CARD, WARNING),
                ft.Text("У этой модели один IMEI", color=WARNING, size=14,
                        weight=ft.FontWeight.W_600),
                muted("По карточке модели это односимочный аппарат без eSIM — "
                      "второго IMEI у него не существует, подбирать нечего."),
            ], spacing=8, tight=True), border_color=WARNING))
        elif guess.get("imei2") and guess.get("reliable"):
            body = [
                title_row("Второй IMEI", ft.Icons.SIM_CARD, ACCENT_2),
                ft.Row([
                    imei_text(guess["imei2"], 22, ACCENT_3),
                    ft.IconButton(ft.Icons.COPY, icon_color=TEXT_MUTED,
                                  on_click=lambda e: copy_text(guess["imei2"],
                                                               "IMEI2 скопирован")),
                ], alignment=ft.MainAxisAlignment.SPACE_BETWEEN,
                   vertical_alignment=ft.CrossAxisAlignment.CENTER),
                muted(guess.get("method", ""), 12),
            ]
            if guess.get("confidence") is not None:
                body.append(confidence_bar(guess["confidence"]))
            items.append(card(ft.Column(body, spacing=10, tight=True)))

            # Партнёрская модель, если её TAC тоже есть в базе.
            partner_tac = guess["imei2"][:8]
            partner_dev = dev_get(partner_tac)
            if partner_dev and partner_tac != imei1[:8]:
                if partner_tac not in state["image_cache"]:
                    page.run_task(ensure_device_image, partner_tac,
                                 partner_dev.get("brand", ""), partner_dev.get("model", ""))
                items.append(device_card(partner_dev, partner_tac, "Модель второго канала"))
        elif guess.get("imei2"):
            # Непроверенное предположение: другой цвет и пометка в заголовке,
            # без процента уверенности и без пояснений — чтобы не путать
            # с достоверным результатом выше, но и не перегружать текстом.
            items.append(card(ft.Column([
                ft.Row([
                    ft.Icon(ft.Icons.HELP_OUTLINE, color=WARNING, size=18),
                    ft.Text("Предположение, не подтверждено", color=WARNING, size=13,
                            weight=ft.FontWeight.W_600),
                ], spacing=8),
                ft.Row([
                    imei_text(guess["imei2"], 20, TEXT_MAIN),
                    ft.IconButton(ft.Icons.COPY, icon_color=TEXT_MUTED,
                                  on_click=lambda e: copy_text(guess["imei2"],
                                                               "IMEI2 скопирован")),
                ], alignment=ft.MainAxisAlignment.SPACE_BETWEEN,
                   vertical_alignment=ft.CrossAxisAlignment.CENTER),
            ], spacing=8, tight=True), bgcolor=BG_PANEL, border_color=WARNING))
        elif dev:
            items.append(card(ft.Column([
                title_row("Второй IMEI", ft.Icons.SIM_CARD, TEXT_MUTED),
                ft.Text("Нет достоверных данных", color=TEXT_MUTED, size=14,
                        weight=ft.FontWeight.W_600),
                muted("По этой модели в базе нет ни правила расчёта, ни пары "
                      "TAC — гадать не будем. Посмотрите IMEI2 на самом "
                      "аппарате (набрать *#06#) или на коробке."),
            ], spacing=8, tight=True)))

        return ft.ListView(items, expand=True, spacing=14, padding=ft.Padding.all(14))

    # ==================================================================
    #                         ВКЛАДКА «БАЗА TAC»
    # ==================================================================

    def open_device_dialog(tac=None):
        existing = dev_get(tac or "") or {}
        tac_tf = field("TAC — первые 8 цифр IMEI", value=tac or "",
                       keyboard_type=ft.KeyboardType.NUMBER, disabled=bool(tac))
        fields = {}
        controls = [tac_tf]
        for key, label in DEVICE_FIELDS:
            extra = {"multiline": True, "min_lines": 2, "max_lines": 4} if key == "specs" else {}
            tf = field(label, value=str(existing.get(key, "") or ""), **extra)
            fields[key] = tf
            controls.append(tf)
        controls.insert(1, muted("«Доп. информация» разбирается автоматически: фразы вида "
                                 "«разница в 14-й цифре +-1», «2-й канал см. 35629690» или "
                                 "«один IMEI на оба канала» станут точным правилом подбора."))

        async def save(e):
            t = clean_digits(tac_tf.value or "")[:8]
            if len(t) != 8:
                snack("TAC должен быть из 8 цифр")
                return
            rec = {k: (tf.value or "").strip() for k, tf in fields.items()}
            rule = parse_imei2_rule(rec.get("specs", ""))
            if rule:
                rec["rule_type"] = rule["type"]
                if rule["type"] == "cross_tac_ref":
                    rec["rule_param"] = rule["partner_tac"]
                    state["tac_pairs"][t] = str(rule["partner_tac"])[:8]
                elif rule["type"] == "digit_offset":
                    rec["rule_param"] = "%d:%d" % (rule["position"], rule["delta"])
            state["devices"][t] = rec
            await save_all()
            close_dialog(dlg)
            snack("Модель сохранена")
            render()

        async def delete(e):
            state["devices"].pop(tac, None)
            await save_all()
            close_dialog(dlg)
            snack("Модель удалена")
            render()

        actions = [ft.TextButton("Отмена", on_click=lambda e: close_dialog(dlg))]
        if tac:
            actions.append(ft.TextButton("Удалить", on_click=delete))
        actions.append(ft.Button(content="Сохранить", icon=ft.Icons.SAVE, on_click=save))

        dlg = ft.AlertDialog(
            title=ft.Text("Модель по TAC" if tac else "Новая модель"),
            content=ft.Column(controls, spacing=10, scroll=ft.ScrollMode.AUTO,
                              height=440, width=min((page.width or 380) - 32, 440)),
            actions=actions,
        )
        open_dialog(dlg)

    # ==================================================================
    #                        ВКЛАДКА «ИСТОРИЯ»
    # ==================================================================

    def history_view():
        async def clear(e):
            state["history"] = []
            await save_all()
            snack("История очищена")
            render()

        items = [
            card(ft.Column([
                title_row("История проверок", ft.Icons.HISTORY, ACCENT_2),
                muted("Последние проверенные номера — можно вернуться "
                      "к любому и скопировать результат."),
                ft.Row([
                    stat_chip("Записей", str(len(state["history"]))),
                    ghost_button("Очистить", ft.Icons.DELETE_SWEEP, clear, color=DANGER),
                ], spacing=10),
            ], spacing=12, tight=True), gradient=safe_gradient(["#2a2350", "#241c3f"])),
        ]

        if not state["history"]:
            items.append(card(ft.Column([
                ft.Icon(ft.Icons.HISTORY_TOGGLE_OFF, size=40, color=BORDER_GLASS),
                ft.Text("Пока пусто", color=TEXT_MUTED, size=14),
            ], spacing=10, tight=True,
               horizontal_alignment=ft.CrossAxisAlignment.CENTER)))
        else:
            def again(imei):
                def handler(e):
                    check_input.value = imei
                    state["tab"] = 0
                    do_check()
                return handler

            for h in reversed(state["history"][-120:]):
                items.append(card(ft.Row([
                    ft.Column([
                        ft.Text(h.get("imei1", ""), size=13, color=TEXT_MAIN,
                                font_family="monospace", selectable=True),
                        ft.Text(h.get("imei2", "") or "—", size=13, color=ACCENT_3,
                                font_family="monospace", selectable=True),
                        muted(" · ".join(x for x in [h.get("brand", ""),
                                                     (h.get("at") or "").replace("T", " ")[:16]] if x), 10),
                    ], spacing=2, expand=True, tight=True),
                    ft.IconButton(ft.Icons.REFRESH, icon_color=ACCENT_3,
                                  on_click=again(h.get("imei1", ""))),
                ], vertical_alignment=ft.CrossAxisAlignment.CENTER),
                    padding=14, bgcolor=BG_PANEL))

        return ft.ListView(items, expand=True, spacing=12, padding=ft.Padding.all(14))

    # ==================================================================
    #                    НАВИГАЦИЯ И СБОРКА СТРАНИЦЫ
    # ==================================================================
    # Всего два раздела — боковое меню для этого избыточно, переключаемся
    # простым сегментом из двух вкладок прямо под шапкой.

    body = ft.Column(expand=True)
    tabs_row = ft.Row(spacing=8)

    TABS = [
        ("Проверка", ft.Icons.SEARCH, check_view),
        ("История", ft.Icons.HISTORY, history_view),
    ]

    def go(idx):
        def handler(e):
            state["tab"] = idx
            render()
        return handler

    def build_tabs_row():
        chips = []
        for idx, (label, icon, _builder) in enumerate(TABS):
            active = state["tab"] == idx
            chips.append(ft.Container(
                content=ft.Row([
                    ft.Icon(icon, size=16, color="white" if active else TEXT_MUTED),
                    ft.Text(label, size=13, color="white" if active else TEXT_MUTED,
                            weight=ft.FontWeight.W_600 if active else None),
                ], spacing=6, alignment=ft.MainAxisAlignment.CENTER),
                padding=ft.Padding.symmetric(horizontal=16, vertical=10),
                border_radius=12, ink=True, on_click=go(idx), expand=True,
                bgcolor=ACCENT_1 if active else BG_PANEL,
                alignment=ft.Alignment.CENTER,
            ))
        return chips

    def db_status_icon():
        return ft.IconButton(
            ft.Icons.CLOUD_DONE if base.available else ft.Icons.CLOUD_OFF,
            icon_color=SUCCESS if base.available else WARNING,
            tooltip=("База подключена: %s моделей" % fmt_count(base.count()))
                    if base.available else "База не найдена — нажмите, чтобы указать файл",
            on_click=import_database,
        )

    def render():
        body.controls.clear()
        body.controls.append(TABS[state["tab"]][2]())
        tabs_row.controls = build_tabs_row()
        page.appbar.actions = [db_status_icon()]
        page.update()

    page.appbar = ft.AppBar(
        title=ft.Text("IMEI-помощник"),
        bgcolor=BG_PANEL,
        color=TEXT_MAIN,
        actions=[db_status_icon()],
    )
    page.add(
        ft.Container(content=tabs_row, padding=ft.Padding.only(left=14, right=14, top=12)),
        body,
    )

    await load_all()
    render()


ft.run(main)
