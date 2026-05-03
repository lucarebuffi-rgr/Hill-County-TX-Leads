"""
Hill County, TX motivated seller lead scraper.

Pipeline:
  1. Auth against Tyler Tech clerk site (disclaimer accept -> session cookies).
  2. For each tracked document type, POST a date-range search and GET paginated results.
  3. Parse grantor/grantee names + doc number + filing date + legal description.
  4. Download Hill CAD shape-file ZIP, extract Parcels_export.dbf, build name -> parcel lookup.
  5. Match clerk records to CAD records using fuzzy name variants.
  6. Output dashboard/records.json, data/records.json, data/ghl_export.csv.

Dependencies: httpx, beautifulsoup4 (kept identical to Kaufman so requirements don't drift).
"""
import os
import re
import io
import json
import csv
import struct
import zipfile
import asyncio
from datetime import datetime, timedelta
from collections import defaultdict

import httpx
from bs4 import BeautifulSoup

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

BASE_URL = "https://hillcountytx-web.tylerhost.net/web/search/DOCSEARCH100427S1"
HOST     = "https://hillcountytx-web.tylerhost.net"

LOOKBACK_DAYS = int(os.getenv("LOOKBACK_DAYS", "14"))

# Hill CAD shape files - the only public bulk download Hill CAD offers.
# Parcels_export.dbf inside this ZIP has the full appraisal roll (owner + addresses).
CAD_ZIP_URL  = "https://hillcad.org/wp-content/uploads/2026/05/HillCADMapFiles.zip"
CAD_DBF_NAME = "Parcels_export.dbf"

# Document types to track.
# IMPORTANT: holderInput/holderValue values below are PLACEHOLDERS based on Kaufman's
# pattern. Hill County may use different abbreviations - verify each one by:
#   1. Open https://hillcountytx-web.tylerhost.net/web/search/DOCSEARCH100427S1
#   2. Open DevTools -> Network tab
#   3. Run a search for one document type at a time
#   4. Click the searchPost request -> Payload tab
#   5. Copy the exact holderInput (abbreviation) and holderValue (full name) values
DOC_TYPES = {
    # full name (holderValue)                : (category,           display label,         abbreviation (holderInput))
    "LIS PENDENS"                            : ("pre_foreclosure", "Lis Pendens",          "LP"),
    "FEDERAL TAX LIEN"                       : ("lien",            "Federal Tax Lien",     "FTL"),
    "STATE TAX LIEN"                         : ("lien",            "State Tax Lien",       "STL"),
    "ABSTRACT OF JUDGMENT"                   : ("judgment",        "Abstract of Judgment", "AJ"),
    "JUDGMENT"                               : ("judgment",        "Judgment",             "J"),
    "AFFIDAVIT OF HEIRSHIP"                  : ("probate",         "Affidavit of Heirship","AFH"),
    "LIEN"                                   : ("lien",            "Lien",                 "L"),
    "CHILD SUPPORT LIEN"                     : ("lien",            "Child Support Lien",   "CSL"),
    "MECHANIC LIEN"                          : ("lien",            "Mechanic Lien",        "ML"),
    "QUIT CLAIM DEED"                        : ("other",           "Quit Claim Deed",      "QCD"),
}

# For these doc types, the GRANTEE is the property owner / motivated seller.
# For all others, the GRANTOR is the owner.
GRANTEE_IS_OWNER = {
    "FEDERAL TAX LIEN", "STATE TAX LIEN",
    "JUDGMENT", "ABSTRACT OF JUDGMENT",
    "LIEN",
    "CHILD SUPPORT LIEN",
    "MECHANIC LIEN",
    "QUIT CLAIM DEED",
}

ENTITY_FILTERS = (
    "LLC", "INC", "CORP", "LTD", "LP ", "L.P.", "TRUST", "ASSOC", "HOMEOWNERS",
    "STATE OF", "CITY OF", "COUNTY OF", "DISTRICT", "MUNICIPALITY", "DEPT ",
    "ISD", "UTILITY", "AUTHORITY", "COMMISSION", "FEDERAL", "NATIONAL BANK",
    "MORTGAGE", "FINANCIAL", "INVESTMENT", "PROPERTIES", "REALTY", "HOLDINGS",
    "PARTNERS", "SERVICES", "MANAGEMENT", "SOLUTIONS", "ENTERPRISES",
    "N/A", "UNKNOWN", "PUBLIC", "ATTY GEN", "ATTY/GEN",
    "CREDIT UNION", "LENDING", "LOAN SERVICING",
    "ANNUITY", "INSURANCE CO", "PENSION",
    "PNC BANK", "WELLS FARGO", "BANK OF AMERICA", "CHASE BANK",
    "IDAHO HOUSING", "US BANK", "NATIONSTAR", "LAKEVIEW LOAN",
    "UNITED WHOLESALE", "PENNYMAC", "FREEDOM MORTGAGE",
    "CHURCH", "MINISTRY", "FOUNDATION", "ESTATE OF",
)

LEGAL_SUFFIXES = re.compile(
    r"\s+(ET\s*UX|ET\s*VIR|ET\s*AL|ETAL|ETUX|ETVIR|"
    r"TRUSTEE|TRUSTEES|TR|LIFE\s+ESTATE|LIFE\s+TENANT|"
    r"DECEASED|DECD|DEC'D|"
    r"JR|SR|II|III|IV)\b\.?",
    re.IGNORECASE,
)

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def fmt_date(d: datetime) -> str:
    """M/D/YYYY with no leading zeros - Tyler Tech's required format."""
    return f"{d.month}/{d.day}/{d.year}"


def is_entity(name: str) -> bool:
    upper = name.upper()
    return any(token in upper for token in ENTITY_FILTERS)


def clean_owner(name: str) -> str:
    name = LEGAL_SUFFIXES.sub("", name)
    return re.sub(r"\s+", " ", name).strip()


def name_variants(name: str):
    parts = name.split()
    out = set()
    if len(parts) >= 2:
        out.add(name)
        out.add(f"{parts[1]} {parts[0]}")
        if len(parts) >= 3:
            out.add(f"{parts[0]} {parts[1]}")
            out.add(f"{parts[1]} {parts[-1]} {parts[0]}")
    elif len(parts) == 1:
        out.add(parts[0])
    return out


# ---------------------------------------------------------------------------
# CAD DBF reader (stdlib, no dbfread dependency)
# ---------------------------------------------------------------------------

def read_dbf_bytes(data: bytes):
    """
    Yield record dicts from DBF file bytes. dBase III layout, UTF-8 encoded
    (per Hill CAD's .cpg sidecar).
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


def build_situs(row):
    num    = row.get("situs_num", "").strip()
    prefix = row.get("situs_stre", "").strip()
    name   = row.get("situs_st_1", "").strip()
    suffix = row.get("situs_st_2", "").strip()
    city   = row.get("situs_city", "").strip()
    state  = row.get("situs_stat", "").strip()
    zipcd  = row.get("situs_zip", "").strip()
    street = " ".join(p for p in (num, prefix, name, suffix) if p)
    if not street and not city:
        return None
    return {"street": street, "city": city, "state": state, "zip": zipcd}


def build_mailing(row):
    line1 = row.get("AddressLin", "").strip()
    line2 = row.get("AddressL_1", "").strip()
    line3 = row.get("AddressL_2", "").strip()
    city  = row.get("AddressCit", "").strip()
    state = row.get("AddressSta", "").strip()
    zipcd = row.get("AddressZip", "").strip()
    street = ", ".join(l for l in (line1, line2, line3) if l)
    if not street and not city:
        return None
    return {"street": street, "city": city, "state": state, "zip": zipcd}


async def download_cad_lookup(client: httpx.AsyncClient) -> dict:
    """
    Download HillCADMapFiles.zip, extract Parcels_export.dbf, return name -> parcel lookup.
    Filters to imprv_val > 0 (parcels with structures) and skips entity owners.
    """
    print(f"Downloading CAD shape files from {CAD_ZIP_URL}...")
    resp = await client.get(CAD_ZIP_URL, timeout=120.0)
    resp.raise_for_status()
    print(f"  downloaded {len(resp.content):,} bytes")

    with zipfile.ZipFile(io.BytesIO(resp.content)) as zf:
        # File may be at root or inside HillCADMapFiles/ folder depending on year
        candidates = [n for n in zf.namelist() if n.endswith(CAD_DBF_NAME)]
        if not candidates:
            raise RuntimeError(f"{CAD_DBF_NAME} not found in CAD zip. Contents: {zf.namelist()[:20]}")
        dbf_bytes = zf.read(candidates[0])
        print(f"  extracted {candidates[0]} ({len(dbf_bytes):,} bytes)")

    lookup = {}
    stats = defaultdict(int)
    for row in read_dbf_bytes(dbf_bytes):
        stats["total"] += 1
        if parse_imprv(row.get("imprv_val", "0")) <= 0:
            stats["no_improvements"] += 1
            continue
        owner_raw = row.get("file_as_na", "").strip()
        if not owner_raw:
            continue
        if is_entity(owner_raw):
            stats["entity"] += 1
            continue

        situs = build_situs(row)
        mailing = build_mailing(row)
        if not mailing and not situs:
            stats["no_address"] += 1
            continue

        parcel = {
            "prop_id": row.get("PROP_ID", "").strip(),
            "owner_name": owner_raw,
            "property_address": situs,
            "mailing_address": mailing,
            "market_value": row.get("market", "").strip(),
            "legal_desc": row.get("legal_desc", "").strip(),
        }

        cleaned = clean_owner(owner_raw)
        co_owners = [c.strip() for c in re.split(r"\s*&\s*", cleaned) if c.strip()]
        if not co_owners:
            continue

        # Inherit primary's surname for first-name-only co-owners ('& MARTHA' -> 'MARSHALL MARTHA')
        primary_surname = co_owners[0].split()[0]
        full_co_owners = [co_owners[0]]
        for co in co_owners[1:]:
            tokens = co.split()
            if primary_surname in tokens:
                full_co_owners.append(co)
            else:
                full_co_owners.append(f"{primary_surname} {co}")

        for co in full_co_owners:
            for variant in name_variants(co):
                lookup[variant.upper()] = parcel
        stats["kept"] += 1

    print(f"  CAD stats: {dict(stats)}")
    print(f"  indexed {len(lookup):,} name variants across {stats['kept']:,} parcels")
    return lookup


# ---------------------------------------------------------------------------
# Tyler Tech clerk scraper
# ---------------------------------------------------------------------------

async def init_session(client: httpx.AsyncClient) -> None:
    """Disclaimer-accept flow that establishes JSESSIONID + disclaimerAccepted cookies."""
    await client.get(BASE_URL, timeout=30.0)
    await client.get(f"{HOST}/web/user/disclaimer", timeout=30.0)
    await client.post(
        f"{HOST}/web/user/disclaimer",
        data={"disclaimer": "accept", "submit": "Accept"},
        timeout=30.0,
    )
    # Critical: must re-load search page after accepting to initialize search session
    await client.get(BASE_URL, timeout=30.0)


def build_search_form(start: datetime, end: datetime, doc_type_full: str, doc_type_abbr: str) -> dict:
    return {
        "field_BothNamesID-containsInput": "Contains Any",
        "field_BothNamesID": "",
        "field_GrantorID-containsInput": "Contains Any",
        "field_GrantorID": "",
        "field_GranteeID-containsInput": "Contains Any",
        "field_GranteeID": "",
        "field_RecDateID_DOT_StartDate": fmt_date(start),
        "field_RecDateID_DOT_EndDate": fmt_date(end),
        "field_DocNumID": "",
        "field_BookVolPageID_DOT_Book": "",
        "field_BookVolPageID_DOT_Volume": "",
        "field_BookVolPageID_DOT_Page": "",
        "field_selfservice_documentTypes-holderInput": doc_type_abbr,
        "field_selfservice_documentTypes-holderValue": doc_type_full,
        "field_selfservice_documentTypes-containsInput": "Contains Any",
        "field_selfservice_documentTypes": "",
    }


async def search_doc_type(client: httpx.AsyncClient, doc_type_full: str, doc_type_abbr: str,
                          start: datetime, end: datetime) -> list:
    """Run one date-range search for one document type and return parsed records."""
    headers = {
        "X-Requested-With": "XMLHttpRequest",
        "Ajaxrequest": "true",
        "Accept": "application/json, text/javascript, */*; q=0.01",
        "Referer": BASE_URL,
        "Content-Type": "application/x-www-form-urlencoded; charset=UTF-8",
    }
    form = build_search_form(start, end, doc_type_full, doc_type_abbr)

    try:
        resp = await client.post(
            f"{HOST}/web/searchPost/DOCSEARCH100427S1",
            data=form,
            headers=headers,
            timeout=60.0,
        )
        resp.raise_for_status()
        meta = resp.json()
    except Exception as e:
        print(f"  searchPost failed for {doc_type_full}: {e}")
        return []

    total_pages = meta.get("totalPages", 0)
    if not total_pages:
        return []

    print(f"  {doc_type_full}: {total_pages} pages")
    records = []
    for page in range(1, total_pages + 1):
        ts = int(datetime.now().timestamp() * 1000)
        try:
            resp = await client.get(
                f"{HOST}/web/searchResults/DOCSEARCH100427S1",
                params={"page": page, "_": ts},
                headers={
                    "X-Requested-With": "XMLHttpRequest",
                    "Ajaxrequest": "true",
                    "Accept": "application/json, text/javascript, */*; q=0.01",
                    "Referer": BASE_URL,
                },
                timeout=60.0,
            )
            resp.raise_for_status()
            page_records = parse_results_html(resp.text, doc_type_full)
            records.extend(page_records)
        except Exception as e:
            print(f"    page {page} failed: {e}")
        await asyncio.sleep(0.5)
    return records


def parse_results_html(html: str, doc_type_full: str) -> list:
    """Parse Tyler Tech result cards into structured records."""
    soup = BeautifulSoup(html, "html.parser")
    out = []
    for li in soup.select("ul.selfServiceSearchResultList li.ss-search-row"):
        record = {
            "doc_type": doc_type_full,
            "grantors": [],
            "grantees": [],
            "doc_number": "",
            "filing_date": "",
            "legal_desc": "",
        }
        for col in li.select("div.searchResultFourColumn"):
            lis = col.select("ul.selfServiceSearchResultColumn li")
            if len(lis) < 2:
                continue
            label = lis[0].get_text(" ", strip=True).lower()
            value_el = lis[1].find("b") or lis[1]
            value = value_el.get_text(" ", strip=True)

            if "grantor" in label:
                record["grantors"].append(value)
            elif "grantee" in label:
                record["grantees"].append(value)
            elif "legal" in label:
                record["legal_desc"] = value
            elif "document" in label and "number" in label:
                record["doc_number"] = value
            elif "filing" in label or "rec" in label:
                record["filing_date"] = value
        if record["grantors"] or record["grantees"]:
            out.append(record)
    return out


# ---------------------------------------------------------------------------
# Match clerk records to CAD lookup
# ---------------------------------------------------------------------------

def match_to_cad(clerk_records: list, cad_lookup: dict) -> list:
    """Attach CAD parcel info to each clerk record. Drop records with no address match."""
    enriched = []
    seen_doc_numbers = set()  # dedupe by doc number across runs

    for rec in clerk_records:
        if rec["doc_number"] and rec["doc_number"] in seen_doc_numbers:
            continue
        seen_doc_numbers.add(rec["doc_number"])

        # Determine which side is the owner based on doc type
        owners = rec["grantees"] if rec["doc_type"] in GRANTEE_IS_OWNER else rec["grantors"]
        if not owners:
            continue

        # Try every owner name, every variant - pick first hit
        matched = None
        matched_name = None
        for owner in owners:
            if is_entity(owner):
                continue
            cleaned = clean_owner(owner)
            for variant in name_variants(cleaned):
                hit = cad_lookup.get(variant.upper())
                if hit:
                    matched = hit
                    matched_name = owner
                    break
            if matched:
                break

        if not matched:
            continue  # no CAD address = drop, matching Kaufman's behavior

        category, label, _ = DOC_TYPES.get(rec["doc_type"], ("other", rec["doc_type"], ""))
        enriched.append({
            "doc_number": rec["doc_number"],
            "filing_date": rec["filing_date"],
            "doc_type": rec["doc_type"],
            "doc_label": label,
            "category": category,
            "owner_name": matched_name,
            "all_grantors": rec["grantors"],
            "all_grantees": rec["grantees"],
            "property_address": matched["property_address"],
            "mailing_address": matched["mailing_address"],
            "market_value": matched["market_value"],
            "prop_id": matched["prop_id"],
            "legal_desc_clerk": rec["legal_desc"],
            "legal_desc_cad": matched["legal_desc"],
        })

    return enriched


# ---------------------------------------------------------------------------
# Output writers
# ---------------------------------------------------------------------------

def fmt_addr(addr):
    if not addr:
        return ""
    parts = [addr.get("street", ""), addr.get("city", ""), addr.get("state", ""), addr.get("zip", "")]
    return ", ".join(p for p in parts if p)


def write_outputs(records: list) -> None:
    payload = {
        "generated_at": datetime.utcnow().isoformat() + "Z",
        "lookback_days": LOOKBACK_DAYS,
        "county": "Hill",
        "state": "TX",
        "count": len(records),
        "records": records,
    }
    for path in ("dashboard/records.json", "data/records.json"):
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8") as f:
            json.dump(payload, f, indent=2, ensure_ascii=False)
    print(f"Wrote {len(records)} records to dashboard/records.json and data/records.json")

    # GHL CSV export - one row per record, mailing address preferred for direct mail
    csv_path = "data/ghl_export.csv"
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow([
            "First Name", "Last Name", "Full Name",
            "Property Address", "Property City", "Property State", "Property Zip",
            "Mailing Address", "Mailing City", "Mailing State", "Mailing Zip",
            "Lead Source", "Doc Type", "Filing Date", "Doc Number", "Market Value",
        ])
        for r in records:
            owner = r.get("owner_name", "")
            tokens = owner.split()
            # CAD format is LAST FIRST [MIDDLE] - but clerk records vary, so just split.
            first = tokens[1] if len(tokens) >= 2 else ""
            last  = tokens[0] if tokens else ""

            prop = r.get("property_address") or {}
            mail = r.get("mailing_address") or {}

            w.writerow([
                first, last, owner,
                prop.get("street", ""), prop.get("city", ""), prop.get("state", ""), prop.get("zip", ""),
                mail.get("street", ""), mail.get("city", ""), mail.get("state", ""), mail.get("zip", ""),
                f"Hill County {r.get('doc_label', '')}",
                r.get("doc_type", ""),
                r.get("filing_date", ""),
                r.get("doc_number", ""),
                r.get("market_value", ""),
            ])
    print(f"Wrote GHL CSV to {csv_path}")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

async def main():
    end = datetime.now()
    start = end - timedelta(days=LOOKBACK_DAYS)
    print(f"Hill County, TX scraper")
    print(f"Date range: {fmt_date(start)} to {fmt_date(end)} ({LOOKBACK_DAYS} days)")

    async with httpx.AsyncClient(follow_redirects=True) as client:
        # CAD download in parallel with clerk auth - CAD takes a while.
        cad_task = asyncio.create_task(download_cad_lookup(client))

        await init_session(client)
        print("Session initialized")

        # Run document type searches sequentially (Tyler Tech can be picky about parallelism).
        all_clerk_records = []
        for doc_type_full, (_, _, abbr) in DOC_TYPES.items():
            recs = await search_doc_type(client, doc_type_full, abbr, start, end)
            all_clerk_records.extend(recs)
        print(f"Total clerk records: {len(all_clerk_records)}")

        cad_lookup = await cad_task
        enriched = match_to_cad(all_clerk_records, cad_lookup)
        print(f"Matched to CAD with addresses: {len(enriched)}")

    write_outputs(enriched)


if __name__ == "__main__":
    asyncio.run(main())
