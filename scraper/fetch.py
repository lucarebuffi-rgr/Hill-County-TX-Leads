#!/usr/bin/env python3
"""
Hill County TX – Motivated Seller Lead Scraper
Clerk  : hillcountytx-web.tylerhost.net (Tyler Technologies)
CAD    : hillcad.org (shape-files ZIP - we extract Parcels_export.dbf)

Mirrors Kaufman's output schema exactly so the dashboard renders identically.
"""

import asyncio
import csv
import io
import json
import logging
import os
import re
import struct
import traceback
import zipfile
from datetime import datetime, timedelta
from difflib import SequenceMatcher
from pathlib import Path
from typing import Optional

import httpx
from bs4 import BeautifulSoup

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
)
log = logging.getLogger(__name__)

BASE_URL      = "https://hillcountytx-web.tylerhost.net/web/search/DOCSEARCH100427S1"
BASE_HOST     = "https://hillcountytx-web.tylerhost.net"
SEARCH_ID     = "DOCSEARCH100427S1"
CAD_ZIP_URL   = "https://hillcad.org/wp-content/uploads/2026/05/HillCADMapFiles.zip"
CAD_DBF_NAME  = "Parcels_export.dbf"
LOOKBACK_DAYS = int(os.getenv("LOOKBACK_DAYS", "14"))

DOC_TYPES = {
    "LIS PENDENS"            : ("pre_foreclosure", "Lis Pendens",          "LP"),
    "FEDERAL TAX LIEN"       : ("lien",            "Federal Tax Lien",     "FTL"),
    "STATE TAX LIEN"         : ("lien",            "State Tax Lien",       "STL"),
    "ABSTRACT OF JUDGMENT"   : ("judgment",        "Abstract of Judgment", "AJ"),
    "JUDGMENT"               : ("judgment",        "Judgment",             "J"),
    "AFFIDAVIT OF HEIRSHIP"  : ("probate",         "Affidavit of Heirship","AFH"),
    "LIEN"                   : ("lien",            "Lien",                 "L"),
    "CHILD SUPPORT LIEN"     : ("lien",            "Child Support Lien",   "CSL"),
    "MECHANIC LIEN"          : ("lien",            "Mechanic Lien",        "ML"),
    "QUIT CLAIM DEED"        : ("other",           "Quit Claim Deed",      "QCD"),
}

GRANTEE_IS_OWNER = {
    "FEDERAL TAX LIEN", "STATE TAX LIEN",
    "JUDGMENT", "ABSTRACT OF JUDGMENT",
    "LIEN",
    "CHILD SUPPORT LIEN",
    "MECHANIC LIEN",
    "QUIT CLAIM DEED",
}

NAME_SUFFIXES = {"JR", "SR", "II", "III", "IV", "V", "ESQ", "TRUSTEE", "TR",
                 "ETAL", "ET", "AL", "ET AL", "ETUX", "ET UX", "ESTATE",
                 "DECEASED", "DECD"}

ENTITY_FILTERS = (
    "LLC", "INC", "CORP", "LTD", "LP ", "L.P.", "TRUST", "ASSOC", "HOMEOWNERS",
    "STATE OF", "CITY OF", "COUNTY OF", "DISTRICT", "MUNICIPALITY", "DEPT ",
    "ISD", "UTILITY", "AUTHORITY", "COMMISSION", "FEDERAL", "NATIONAL BANK",
    "MORTGAGE", "FINANCIAL", "INVESTMENT", "PROPERTIES", "REALTY", "HOLDINGS",
    "PARTNERS", "SERVICES", "MANAGEMENT", "SOLUTIONS", "ENTERPRISES",
    "N/A", "UNKNOWN", "PUBLIC", "ATTY GEN", "ATTY/GEN", "HILL COUNTY",
    "CITY OF HILLSBORO", "CITY OF WHITNEY", "CITY OF ITASCA",
    "CREDIT UNION", "LENDING", "LOAN SERVICING",
    "ANNUITY", "INSURANCE CO", "PENSION",
    "PNC BANK", "WELLS FARGO", "BANK OF AMERICA", "CHASE BANK",
    "IDAHO HOUSING", "US BANK", "NATIONSTAR", "LAKEVIEW LOAN",
    "UNITED WHOLESALE", "PENNYMAC", "FREEDOM MORTGAGE",
    "CHURCH", "MINISTRY", "FOUNDATION",
)

# Suffixes/prefixes used on clerk records when a party is deceased.
# Stripped from grantor names before matching to CAD (CAD doesn't include these).
DECEASED_TOKENS = re.compile(
    r"\b(DECEASED|DECD|DEC'D|ESTATE\s+OF|EST\s+OF)\b\.?",
    re.IGNORECASE,
)


def strip_deceased(name: str) -> str:
    """Remove deceased markers so 'BARNES NETA BELLE DECEASED' matches 'BARNES NETA B' in CAD."""
    if not name:
        return name
    cleaned = DECEASED_TOKENS.sub("", name).strip()
    cleaned = re.sub(r"\s+", " ", cleaned)
    return cleaned


# ---------------------------------------------------------------------------
# Name handling (mirrors Kaufman's logic)
# ---------------------------------------------------------------------------

def parse_date(raw: str) -> Optional[str]:
    for fmt in ("%m/%d/%Y", "%Y-%m-%d", "%m-%d-%Y", "%Y%m%d",
                "%m/%d/%Y %I:%M %p", "%m/%d/%Y %H:%M:%S"):
        try:
            return datetime.strptime(raw.strip(), fmt).strftime("%Y-%m-%d")
        except ValueError:
            continue
    return None


def strip_suffixes(tokens: list) -> list:
    return [t for t in tokens if t not in NAME_SUFFIXES]


def name_variants(full: str) -> list:
    full = re.sub(r"[^\w\s]", "", full.strip().upper())
    tokens = strip_suffixes(full.split())
    if not tokens:
        return [full]
    variants = set()
    variants.add(" ".join(tokens))
    if len(tokens) < 2:
        return list(variants)
    last  = tokens[0]
    first = tokens[1] if len(tokens) > 1 else ""
    mid   = tokens[2] if len(tokens) > 2 else ""
    variants.add(f"{last} {first} {mid}".strip())
    variants.add(f"{last}, {first} {mid}".strip())
    variants.add(f"{last} {first}")
    variants.add(f"{last}, {first}")
    variants.add(f"{first} {last}")
    if mid:
        variants.add(f"{first} {mid} {last}")
        variants.add(f"{first} {last}")
        if len(mid) == 1:
            variants.add(f"{last} {first}")
    return [v for v in variants if v]


def normalize_for_fuzzy(name: str) -> tuple:
    name = re.sub(r"[^\w\s]", "", name.strip().upper())
    tokens = strip_suffixes(name.split())
    filtered = [t for t in tokens if len(t) > 1]
    if len(filtered) >= 2:
        tokens = filtered
    if not tokens:
        return ("", set())
    return tokens[0], set(tokens[1:])


def is_entity(name: str) -> bool:
    n = name.strip().upper()
    if not n or n in ("N/A", "NA", "UNKNOWN", "PUBLIC", ""):
        return True
    tokens = [t for t in re.sub(r"[^\w\s]", "", n).split() if len(t) > 1]
    if len(tokens) < 2:
        return True
    return any(x in n for x in ENTITY_FILTERS)


# ---------------------------------------------------------------------------
# DBF reader (stdlib only)
# ---------------------------------------------------------------------------

def read_dbf_bytes(data: bytes):
    """
    Yield record dicts from DBF file bytes. dBase III layout, UTF-8 encoded.
    """
    header = data[:32]
    num_records = struct.unpack("<I", header[4:8])[0]
    header_len  = struct.unpack("<H", header[8:10])[0]
    record_len  = struct.unpack("<H", header[10:12])[0]

    fields = []
    pos = 32
    while True:
        descriptor = data[pos:pos+32]
        if descriptor[0:1] == b"\x0D":
            break
        name = descriptor[0:11].rstrip(b"\x00").decode("ascii", errors="replace")
        flen = descriptor[16]
        fields.append((name, flen))
        pos += 32

    pos = header_len
    for _ in range(num_records):
        rec = data[pos:pos+record_len]
        pos += record_len
        if not rec or rec[0:1] == b"\x1A":
            break
        if rec[0:1] == b"\x2A":  # deleted
            continue
        offset = 1
        row = {}
        for (n, l) in fields:
            row[n] = rec[offset:offset+l].decode("utf-8", errors="replace").strip()
            offset += l
        yield row


def parse_imprv(val: str) -> float:
    try:
        return float(val) if val else 0.0
    except ValueError:
        return 0.0


# ---------------------------------------------------------------------------
# Build CAD parcel lookup from the Hill CAD shape-files ZIP
# ---------------------------------------------------------------------------

def build_parcel_lookup() -> dict:
    lookup = {}
    log.info("Downloading Hill CAD data ...")
    try:
        resp = httpx.get(CAD_ZIP_URL, timeout=120, follow_redirects=True,
                         headers={"User-Agent": "Mozilla/5.0"})
        resp.raise_for_status()
        log.info(f"  Downloaded {len(resp.content)/1_048_576:.1f} MB")

        zf = zipfile.ZipFile(io.BytesIO(resp.content))
        candidates = [n for n in zf.namelist() if n.endswith(CAD_DBF_NAME)]
        if not candidates:
            log.error(f"Could not find {CAD_DBF_NAME}. Files: {zf.namelist()[:20]}")
            return lookup
        log.info(f"  Parsing {candidates[0]} ...")
        dbf_bytes = zf.read(candidates[0])

        total = 0
        for row in read_dbf_bytes(dbf_bytes):
            # Filter: must have improvements (a structure on the parcel)
            if parse_imprv(row.get("imprv_val", "0")) <= 0:
                continue

            owner_name = row.get("file_as_na", "").strip().upper()
            # Defensive: strip any 'DECEASED' tokens from CAD too (rare but possible)
            owner_name = strip_deceased(owner_name)
            if not owner_name or is_entity(owner_name):
                continue

            # Build property (situs) address
            situs_num    = row.get("situs_num", "").strip()
            situs_prefix = row.get("situs_stre", "").strip()
            situs_name   = row.get("situs_st_1", "").strip()
            situs_suffix = row.get("situs_st_2", "").strip()
            situs_st     = " ".join(p for p in (situs_num, situs_prefix, situs_name, situs_suffix) if p)
            situs_city   = row.get("situs_city", "").strip()
            situs_zip    = row.get("situs_zip", "").strip()[:5]

            # Build mailing address (most data is in AddressL_1 per the DBF)
            mail_l1 = row.get("AddressLin", "").strip()
            mail_l2 = row.get("AddressL_1", "").strip()
            mail_l3 = row.get("AddressL_2", "").strip()
            mail_addr = ", ".join(l for l in (mail_l1, mail_l2, mail_l3) if l)
            mail_city = row.get("AddressCit", "").strip()
            mail_state = row.get("AddressSta", "").strip() or "TX"
            mail_zip = row.get("AddressZip", "").strip()[:5]

            # Skip if no address at all
            if not situs_st and not mail_addr:
                continue

            parcel = {
                "prop_address": situs_st,
                "prop_city":    situs_city or "Hillsboro",
                "prop_state":   "TX",
                "prop_zip":     situs_zip,
                "mail_address": mail_addr,
                "mail_city":    mail_city,
                "mail_state":   mail_state,
                "mail_zip":     mail_zip,
            }

            # Index every co-owner separately, with surname inheritance for
            # spouse-style entries like 'GERMER KEVIN T & ESTHER Y'.
            parts = [p.strip() for p in re.split(r'\s*&\s*', owner_name) if p.strip()]
            if not parts:
                continue
            primary_surname = parts[0].split()[0] if parts[0].split() else ""
            full_parts = [parts[0]]
            for p in parts[1:]:
                tokens = p.split()
                if primary_surname and primary_surname not in tokens:
                    full_parts.append(f"{primary_surname} {p}")
                else:
                    full_parts.append(p)

            for part in full_parts:
                if part and not is_entity(part):
                    for variant in name_variants(part):
                        lookup[variant] = parcel
            total += 1
            if total % 5000 == 0:
                log.info(f"  Processed {total:,} parcels ...")

        log.info(f"Hill CAD lookup: {len(lookup):,} name variants from {total:,} parcels")
    except Exception:
        log.error(f"CAD lookup error:\n{traceback.format_exc()}")
    return lookup


# ---------------------------------------------------------------------------
# Clerk results parser - same Tyler Tech HTML shape as Kaufman
# ---------------------------------------------------------------------------

def parse_results_html(html: str, doc_type: str, cat: str, cat_label: str,
                       debug: bool = False) -> list:
    records = []
    try:
        soup = BeautifulSoup(html, "html.parser")
        result_list = soup.find("ul", class_="selfServiceSearchResultList")
        if not result_list:
            log.warning(f"  {doc_type}: no selfServiceSearchResultList found")
            return records

        items = result_list.find_all("li", recursive=False)
        log.info(f"  {doc_type}: {len(items)} result li items found")

        seen = set()
        for item in items:
            full_text = item.get_text(" ", strip=True)

            # Walk the labeled columns FIRST to get authoritative values
            # (doc_number, recording date, grantor, grantee, legal).
            instrument = ""
            filed = ""
            grantor = ""
            grantee = ""
            legal   = ""

            columns = item.find_all("div", class_="searchResultFourColumn")
            for col in columns:
                ul = col.find("ul", class_="selfServiceSearchResultColumn")
                if not ul:
                    continue
                lis = ul.find_all("li")
                if not lis:
                    continue
                label = lis[0].get_text(strip=True).lower()
                val = ""
                if len(lis) > 1:
                    b = lis[1].find("b")
                    val = b.get_text(strip=True) if b else lis[1].get_text(strip=True)

                if "grantor" in label:
                    grantor = val
                elif "grantee" in label:
                    grantee = val
                elif "legal" in label:
                    legal = val
                elif ("document" in label and ("number" in label or "#" in label)) \
                     or label.strip() in ("doc #", "doc number", "instrument"):
                    instrument = val
                elif ("recording" in label or "rec date" in label or
                      "filed" in label or "file date" in label or "date" in label):
                    if not filed:
                        filed = val

            # Fallbacks if the labeled columns didn't give us a doc number.
            # Try several common Tyler Tech formats.
            if not instrument:
                for pattern in (r"(\d{4}-\d+)",          # 2026-12345 (Kaufman style)
                                r"\b(\d{8,})\b",          # 00012345 (8+ digit plain)
                                r"\b([A-Z]{1,3}\d{6,})\b"):  # prefix+digits
                    m = re.search(pattern, full_text)
                    if m:
                        instrument = m.group(1)
                        break

            if not filed:
                m2 = re.search(r"(\d{2}/\d{2}/\d{4})", full_text)
                if m2:
                    filed = m2.group(1)

            # Skip records we genuinely can't identify
            if not instrument and not (grantor or grantee):
                continue
            if not instrument:
                # synthesize an ID so dedupe still works
                instrument = f"NOID-{abs(hash(full_text)) % 10**8}"

            if instrument in seen:
                continue
            seen.add(instrument)

            if debug:
                log.info(f"  PARSED: {instrument} | filed={filed} | grantor={grantor} | grantee={grantee}")

            records.append({
                "doc_num"  : instrument,
                "doc_type" : doc_type,
                "cat"      : cat,
                "cat_label": cat_label,
                "filed"    : parse_date(filed) or filed,
                "grantor"  : grantor,
                "grantee"  : grantee,
                "legal"    : legal,
                "amount"   : None,
                "clerk_url": BASE_URL,
                "_demo"    : False,
            })
    except Exception:
        log.error(f"  Parse error:\n{traceback.format_exc()}")
    return records


async def scrape_all(date_from: str, date_to: str) -> list:
    all_records = []

    def fmt_date(d):
        dt = datetime.strptime(d, "%m/%d/%Y")
        return f"{dt.month}/{dt.day}/{dt.year}"

    df = fmt_date(date_from)
    dt = fmt_date(date_to)

    ajax_headers = {
        "X-Requested-With": "XMLHttpRequest",
        "Ajaxrequest":       "true",
        "Accept":            "application/json, text/javascript, */*; q=0.01",
        "Referer":           BASE_URL,
    }

    async with httpx.AsyncClient(
        follow_redirects=True,
        headers={
            "User-Agent": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
                          "AppleWebKit/537.36 (KHTML, like Gecko) "
                          "Chrome/120.0.0.0 Safari/537.36",
            "Referer": BASE_URL,
        },
        timeout=60
    ) as client:
        await client.get(BASE_URL)
        await client.post(
            BASE_HOST + "/web/user/disclaimer",
            data={"disclaimer": "accept", "submit": "Accept"}
        )
        r = await client.get(BASE_URL)
        log.info(f"  Search page loaded: {r.status_code} len={len(r.text)}")
        log.info(f"  Cookies: {list(client.cookies.keys())}")

        for doc_type, (cat, cat_label, holder_input) in DOC_TYPES.items():
            try:
                form_data = {
                    "field_BothNamesID-containsInput":               "Contains Any",
                    "field_BothNamesID":                             "",
                    "field_GrantorID-containsInput":                 "Contains Any",
                    "field_GrantorID":                               "",
                    "field_GranteeID-containsInput":                 "Contains Any",
                    "field_GranteeID":                               "",
                    "field_RecDateID_DOT_StartDate":                 df,
                    "field_RecDateID_DOT_EndDate":                   dt,
                    "field_DocNumID":                                "",
                    "field_BookVolPageID_DOT_Book":                  "",
                    "field_BookVolPageID_DOT_Volume":                "",
                    "field_BookVolPageID_DOT_Page":                  "",
                    "field_selfservice_documentTypes-holderInput":   holder_input,
                    "field_selfservice_documentTypes-holderValue":   doc_type,
                    "field_selfservice_documentTypes-containsInput": "Contains Any",
                    "field_selfservice_documentTypes":               "",
                }

                post_resp = await client.post(
                    BASE_HOST + f"/web/searchPost/{SEARCH_ID}",
                    data=form_data,
                    headers={
                        **ajax_headers,
                        "Content-Type": "application/x-www-form-urlencoded; charset=UTF-8",
                    }
                )
                log.info(f"  {doc_type} POST: {post_resp.status_code}")

                try:
                    post_json   = post_resp.json()
                    total_pages = post_json.get("totalPages", 0)
                    log.info(f"  {doc_type} totalPages={total_pages}")
                except Exception:
                    log.warning(f"  {doc_type} POST not JSON")
                    total_pages = 0

                if total_pages == 0:
                    continue

                for pg in range(1, total_pages + 1):
                    ts = int(datetime.now().timestamp() * 1000)
                    get_resp = await client.get(
                        BASE_HOST + f"/web/searchResults/{SEARCH_ID}",
                        params={"page": str(pg), "_": str(ts)},
                        headers=ajax_headers
                    )
                    log.info(f"  {doc_type} GET p{pg}: {get_resp.status_code} len={len(get_resp.text)}")

                    debug = (doc_type == "LIS PENDENS" and pg == 1)
                    if get_resp.status_code == 200 and len(get_resp.text) > 500:
                        recs = parse_results_html(
                            get_resp.text, doc_type, cat, cat_label, debug=debug
                        )
                        log.info(f"  {doc_type} p{pg}: {len(recs)} records parsed")
                        all_records.extend(recs)

            except Exception as e:
                log.warning(f"  {doc_type} failed: {e}\n{traceback.format_exc()}")

    log.info(f"  Total scraped: {len(all_records)}")
    return all_records


# ---------------------------------------------------------------------------
# Demo data fallback (so dashboard isn't empty before first successful scrape)
# ---------------------------------------------------------------------------

def generate_demo_records(date_from: str, date_to: str) -> list:
    samples = [
        ("LIS PENDENS",            "pre_foreclosure", "Lis Pendens",
         "SMITH ROBERT",    "ROCKET MORTGAGE",   0),
        ("ABSTRACT OF JUDGMENT",   "judgment",        "Abstract of Judgment",
         "JONES MARY B",    "CAPITAL ONE",    87500),
        ("FEDERAL TAX LIEN",       "lien",            "Federal Tax Lien",
         "WILLIAMS DAVID",  "IRS",            45200),
        ("JUDGMENT",               "judgment",        "Judgment",
         "JOHNSON PAT",     "CITIBANK",       18700),
        ("LIEN",                   "lien",            "Lien",
         "BROWN MICHAEL",   "ACME CONTR",     22000),
        ("AFFIDAVIT OF HEIRSHIP",  "probate",         "Affidavit of Heirship",
         "GARCIA CARLOS",   "GARCIA MARIA",       0),
        ("CHILD SUPPORT LIEN",     "lien",            "Child Support Lien",
         "TAYLOR JAMES",    "TX OAG",          7500),
        ("MECHANIC LIEN",          "lien",            "Mechanic Lien",
         "MARTINEZ LUIS",   "ABC ROOFING",    12300),
        ("QUIT CLAIM DEED",        "other",           "Quit Claim Deed",
         "ANDERSON SUSAN",  "ANDERSON ROBERT",    0),
    ]
    base = datetime.strptime(date_from, "%m/%d/%Y")
    recs = []
    for i, (code, cat, cat_label, grantor, grantee, amt) in enumerate(samples):
        filed_dt = base + timedelta(days=i % LOOKBACK_DAYS)
        recs.append({
            "doc_num":   f"2026-DEMO-{i+1:04d}",
            "doc_type":  code,
            "cat":       cat,
            "cat_label": cat_label,
            "filed":     filed_dt.strftime("%Y-%m-%d"),
            "grantor":   grantor,
            "grantee":   grantee,
            "legal":     "DEMO RECORD",
            "amount":    float(amt) if amt else None,
            "clerk_url": BASE_URL,
            "_demo":     True,
        })
    return recs


# ---------------------------------------------------------------------------
# Match clerk records to CAD parcels
# ---------------------------------------------------------------------------

def enrich_with_parcel(records: list, lookup: dict) -> list:
    fuzzy_index = []
    seen = set()
    for variant, parcel in lookup.items():
        last, firsts = normalize_for_fuzzy(variant)
        key = (last, frozenset(firsts))
        if last and key not in seen:
            seen.add(key)
            fuzzy_index.append((last, firsts, parcel))

    matched = 0
    for rec in records:
        dtype  = rec.get("doc_type", "")
        owner_raw = (rec.get("grantee") if dtype in GRANTEE_IS_OWNER
                     else rec.get("grantor") or "").upper().strip()
        # Strip 'DECEASED', 'ESTATE OF', etc. BEFORE entity check so heirship
        # records like 'ESTATE OF JOHN SMITH' aren't filtered out as entities.
        owner = strip_deceased(owner_raw)
        parcel = None
        if is_entity(owner):
            rec.setdefault("prop_address", "")
            rec.setdefault("prop_city",    "")
            rec.setdefault("prop_state",   "TX")
            rec.setdefault("prop_zip",     "")
            rec.setdefault("mail_address", "")
            rec.setdefault("mail_city",    "")
            rec.setdefault("mail_state",   "TX")
            rec.setdefault("mail_zip",     "")
            continue
        for variant in name_variants(owner):
            parcel = lookup.get(variant)
            if parcel:
                break
        if not parcel and owner:
            o_last, o_firsts = normalize_for_fuzzy(owner)
            if o_last and o_firsts:
                for c_last, c_firsts, candidate in fuzzy_index:
                    if c_last != o_last:
                        continue
                    if not c_firsts:
                        continue
                    if o_firsts & c_firsts:
                        parcel = candidate
                        break
                    o_str = " ".join(sorted(o_firsts))
                    c_str = " ".join(sorted(c_firsts))
                    if o_str and c_str and SequenceMatcher(
                            None, o_str, c_str).ratio() >= 0.85:
                        parcel = candidate
                        break
        if parcel:
            rec.update(parcel)
            matched += 1
        else:
            if owner and not is_entity(owner):
                log.info(f"  NO MATCH: {owner}")
            rec.setdefault("prop_address", "")
            rec.setdefault("prop_city",    "")
            rec.setdefault("prop_state",   "TX")
            rec.setdefault("prop_zip",     "")
            rec.setdefault("mail_address", "")
            rec.setdefault("mail_city",    "")
            rec.setdefault("mail_state",   "TX")
            rec.setdefault("mail_zip",     "")
    log.info(f"Parcel enrichment: {matched}/{len(records)} records matched")
    return records


# ---------------------------------------------------------------------------
# Score and flag each record (mirrors Kaufman's logic)
# ---------------------------------------------------------------------------

def score_record(rec: dict) -> tuple:
    score = 30
    flags = []
    dtype  = rec.get("doc_type", "")
    amount = rec.get("amount") or 0
    if dtype == "LIS PENDENS":                              flags.append("Lis pendens")
    if dtype in ("FEDERAL TAX LIEN", "STATE TAX LIEN"):     flags.append("Tax lien")
    if dtype in ("JUDGMENT", "ABSTRACT OF JUDGMENT"):       flags.append("Judgment lien")
    if dtype == "AFFIDAVIT OF HEIRSHIP":                    flags.append("Probate / estate")
    if dtype == "LIEN":                                     flags.append("Lien")
    if dtype == "CHILD SUPPORT LIEN":                       flags.append("Child support lien")
    if dtype == "MECHANIC LIEN":                            flags.append("Mechanic lien")
    if dtype == "QUIT CLAIM DEED":                          flags.append("Quit claim deed")
    try:
        filed = datetime.strptime(rec.get("filed", ""), "%Y-%m-%d")
        if (datetime.today() - filed).days <= 14:
            flags.append("New this week")
    except Exception:
        pass
    has_addr = bool(rec.get("prop_address") or rec.get("mail_address"))
    score += 10 * len(flags)
    if "Lis pendens" in flags:      score += 20
    if "Probate / estate" in flags: score += 10
    if "Tax lien" in flags:         score += 10
    if amount and amount > 100_000: score += 15
    elif amount and amount > 50_000: score += 10
    if "New this week" in flags:    score += 5
    if has_addr:                    score += 5
    return min(score, 100), flags


# ---------------------------------------------------------------------------
# Output assembly
# ---------------------------------------------------------------------------

def build_output(raw_records: list, date_from: str, date_to: str) -> dict:
    seen_docs   = set()
    out_records = []
    for raw in raw_records:
        try:
            doc_num = raw.get("doc_num", "")
            if doc_num and doc_num in seen_docs:
                continue
            if doc_num:
                seen_docs.add(doc_num)
            dtype = raw.get("doc_type", "")
            if dtype in GRANTEE_IS_OWNER:
                owner   = raw.get("grantee", "")
                grantee = raw.get("grantor", "")
            else:
                owner   = raw.get("grantor", "")
                grantee = raw.get("grantee", "")
            # Strip deceased markers so the entity filters below don't drop heirship records
            owner = strip_deceased(owner)
            if not owner:
                owner = f"UNKNOWN ({doc_num})"
            score, flags = score_record({**raw, "owner": owner})
            out_records.append({
                "doc_num":      doc_num,
                "doc_type":     dtype,
                "filed":        raw.get("filed", ""),
                "cat":          raw.get("cat", "other"),
                "cat_label":    raw.get("cat_label", ""),
                "owner":        owner,
                "grantee":      grantee,
                "amount":       raw.get("amount"),
                "legal":        raw.get("legal", ""),
                "prop_address": raw.get("prop_address", ""),
                "prop_city":    raw.get("prop_city", ""),
                "prop_state":   raw.get("prop_state", "TX"),
                "prop_zip":     raw.get("prop_zip", ""),
                "mail_address": raw.get("mail_address", ""),
                "mail_city":    raw.get("mail_city", ""),
                "mail_state":   raw.get("mail_state", "TX"),
                "mail_zip":     raw.get("mail_zip", ""),
                "clerk_url":    raw.get("clerk_url", ""),
                "flags":        flags,
                "score":        score,
                "_demo":        raw.get("_demo", False),
            })
        except Exception:
            log.warning(f"Skipping: {traceback.format_exc()}")
    out_records = [r for r in out_records if not is_entity(r.get("owner", ""))]
    out_records = [r for r in out_records if not any(
        x in (r.get("owner", "")).upper() for x in ENTITY_FILTERS
    )]
    out_records = [r for r in out_records if r.get("prop_address") or r.get("mail_address") or r.get("_demo")]
    out_records.sort(key=lambda r: (-r["score"], r.get("filed", "") or ""))
    with_address = sum(1 for r in out_records if r["prop_address"] or r["mail_address"])
    return {
        "fetched_at":   datetime.utcnow().isoformat() + "Z",
        "source":       "Hill County TX – Tyler Technologies",
        "date_range":   {"from": date_from, "to": date_to},
        "total":        len(out_records),
        "with_address": with_address,
        "records":      out_records,
    }


def save_output(data: dict):
    for path in ["dashboard/records.json", "data/records.json"]:
        p = Path(path)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(data, indent=2))
        log.info(f"Saved {data['total']} records → {path}")


def export_ghl_csv(data: dict):
    fieldnames = [
        "First Name", "Last Name", "Mailing Address", "Mailing City",
        "Mailing State", "Mailing Zip", "Property Address", "Property City",
        "Property State", "Property Zip", "Lead Type", "Document Type",
        "Date Filed", "Document Number", "Amount/Debt Owed", "Seller Score",
        "Motivated Seller Flags", "Source", "Public Records URL",
    ]
    buf = io.StringIO()
    writer = csv.DictWriter(buf, fieldnames=fieldnames)
    writer.writeheader()
    for r in data["records"]:
        parts = (r.get("owner", "")).split()
        writer.writerow({
            "First Name":             parts[0] if parts else "",
            "Last Name":              " ".join(parts[1:]) if len(parts) > 1 else "",
            "Mailing Address":        r.get("mail_address", ""),
            "Mailing City":           r.get("mail_city", ""),
            "Mailing State":          r.get("mail_state", "TX"),
            "Mailing Zip":            r.get("mail_zip", ""),
            "Property Address":       r.get("prop_address", ""),
            "Property City":          r.get("prop_city", ""),
            "Property State":         r.get("prop_state", "TX"),
            "Property Zip":           r.get("prop_zip", ""),
            "Lead Type":              r.get("cat_label", ""),
            "Document Type":          r.get("doc_type", ""),
            "Date Filed":             r.get("filed", ""),
            "Document Number":        r.get("doc_num", ""),
            "Amount/Debt Owed":       str(r.get("amount", "") or ""),
            "Seller Score":           str(r.get("score", "")),
            "Motivated Seller Flags": "|".join(r.get("flags", [])),
            "Source":                 "Hill County TX",
            "Public Records URL":     r.get("clerk_url", ""),
        })
    Path("data/ghl_export.csv").write_text(buf.getvalue())
    log.info("GHL CSV saved")


async def main():
    today     = datetime.today()
    start     = today - timedelta(days=LOOKBACK_DAYS)
    date_from = start.strftime("%m/%d/%Y")
    date_to   = today.strftime("%m/%d/%Y")

    log.info("=== Hill County TX Lead Scraper ===")
    log.info(f"Date range: {date_from} → {date_to}")

    log.info("Building parcel lookup ...")
    parcel_lookup = build_parcel_lookup()
    log.info(f"  {len(parcel_lookup):,} name variants indexed")

    log.info("Scraping clerk records ...")
    raw_records = await scrape_all(date_from, date_to)
    log.info(f"Total raw records: {len(raw_records)}")

    if not raw_records:
        log.warning("No live records – using demo data")
        raw_records = generate_demo_records(date_from, date_to)

    raw_records = enrich_with_parcel(raw_records, parcel_lookup)
    data = build_output(raw_records, date_from, date_to)
    save_output(data)
    export_ghl_csv(data)
    log.info(f"Done. {data['total']} leads | {data['with_address']} with address")


if __name__ == "__main__":
    asyncio.run(main())
