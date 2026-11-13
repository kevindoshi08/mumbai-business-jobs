#!/usr/bin/env python3
"""Mumbai and remote job board for business roles.

Finds HR, administration, executive assistant, operations, management, and
sales and marketing openings in the Mumbai region, plus remote roles open to
people in India. It reads public job-search feeds and official employer job
boards, keeps a small JSON history, and builds a static dashboard.

It never applies to jobs, contacts anyone, or scrapes LinkedIn or Naukri.
"""
from __future__ import annotations

import argparse
import concurrent.futures as cf
import datetime as dt
import email.utils
import hashlib
import html
import json
import os
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from pathlib import Path
from typing import Any, Callable

ROOT = Path(__file__).resolve().parent
CONFIG_PATH = ROOT / "config.json"
STATE_PATH = ROOT / "data" / "jobs.json"
TEMPLATE_PATH = ROOT / "dashboard.html"
SITE_DIR = ROOT / "site"
IST = dt.timezone(dt.timedelta(hours=5, minutes=30), "IST")
USER_AGENT = "Mozilla/5.0 (compatible; mumbai-business-jobs/1.0; +https://github.com/kevindoshi08/mumbai-business-jobs)"
RETRY_CODES = {408, 425, 429, 500, 502, 503, 504}

# ---------------------------------------------------------------------------
# Matching rules
# ---------------------------------------------------------------------------

FAMILY_PATTERNS: list[tuple[str, str]] = [
    ("ea", r"executive assistant|personal assistant|virtual assistant|executive secretary|secretary to|"
           r"\bsecretary\b|assistant to (?:the )?(?:ceo|cfo|coo|md|founders?|chairman|chairperson|directors?|president|"
           r"managing director|partners?|leadership|cxos?)|\b(?:ea|pa) to\b|\bea\s*/\s*pa\b|\bpa\s*/\s*ea\b|executive support"),
    ("hr", r"\bhr\b|\bh\.r\.?|human resources?|\bpeople\b|talent acquisition|\bta (?:executive|specialist|partner|associate|coordinator)|"
           r"recruit(?:er|ers|ment|ing)|hiring (?:coordinator|associate|specialist|executive)|sourcer|\bpayroll\b|"
           r"employee (?:engagement|relations|experience|lifecycle)|learning (?:and|&) development|\bl\s?&\s?d\b|\bhrbp\b|"
           r"compensation (?:and|&) benefits|\bc\s?&\s?b\b|talent (?:management|partner|coordinator|specialist|associate)|"
           r"campus (?:hiring|recruit)|onboarding coordinator"),
    ("admin", r"\badmin\b|administration|administrative|administrator|office (?:manager|administrator|coordinator|executive|"
              r"assistant|admin|operations|management)|front (?:office|desk)|receptionist|\breception\b|"
              r"facilit(?:y|ies) (?:executive|coordinator|associate|officer|manager|admin|management|services)|"
              r"soft services|back office|\bmis (?:executive|coordinator|associate)|documentation (?:executive|officer|"
              r"specialist|coordinator)|document controller|travel (?:desk|coordinator|executive|admin)|"
              r"workplace (?:coordinator|experience|services|operations|admin)"),
    ("sales", r"\bsales\b|selling|business development|biz ?dev|\bbd[ea]\b|\bbdm\b|\bbd (?:executive|associate|manager|"
              r"specialist|representative)|inside sales|tele-?sales|account (?:executive|manager|management|coordinator|"
              r"associate|specialist)|key accounts?|relationship (?:manager|executive|officer|associate|specialist)|"
              r"client (?:servicing|services? (?:executive|associate|manager)|relationship|partner|acquisition|success)|"
              r"customer success|partnerships?|alliances?|channel (?:sales|partner|manager|development)|distributor|"
              r"territory|area sales|trade marketing|go[- ]to[- ]market|lead generation|marketing|marketer|\bbrand\b|"
              r"social media|content (?:marketing|strategist|executive|manager|associate)|\bseo\b|\bsem\b|"
              r"growth (?:associate|executive|manager|marketing|marketer)|\bcrm (?:executive|marketing|associate|specialist|"
              r"manager)|e-?mail marketing|community (?:manager|associate|executive)|\bcommunications?\b|public relations|"
              r"\bpr\b|events? (?:executive|coordinator|manager|associate|specialist)|influencer|media (?:planner|planning|"
              r"buying|buyer|executive)|advertising|ad sales|merchandis(?:ing|er)|franchise|business associate|"
              r"demand generation|market research"),
    ("ops", r"\boperations?\b|\bops\b|process (?:associate|executive|specialist|analyst)|supply chain|logistics|procurement|"
            r"\bpurchase\b|purchasing|\bbuyer\b|sourcing (?:executive|associate|specialist|manager)|vendor (?:management|"
            r"manager|coordinator|executive|relations|onboarding)|inventory|dispatch|fulfil?lment (?:executive|associate|"
            r"coordinator|specialist)|order (?:management|processing)|coordinator|co-ordinator|trade (?:services|support|"
            r"lifecycle|settlements?)|fund servic(?:es|ing)|settlements?|reconciliation|payments? (?:lifecycle|operations|"
            r"specialist|processing)|client onboarding|middle office|transaction (?:services|processing|management)|"
            r"service delivery|planning (?:executive|coordinator|associate)|demand planner|category (?:executive|associate|"
            r"specialist|manager)|catalog(?:ue)? (?:executive|associate|specialist)|business support|"
            r"customer experience (?:associate|executive|specialist)|process excellence"),
    ("management", r"management trainee|graduate trainee|\bmt\b|business analyst|strategy|strategic initiatives|"
                   r"founder'?s office|office of the (?:ceo|founder)|chief of staff|program(?:me)? (?:associate|coordinator|"
                   r"executive|manager|management)|project (?:associate|coordinator|executive|manager|management|lead)|"
                   r"\bpmo\b|assistant manager|deputy manager|associate manager|team (?:lead|leader)|business manager|"
                   r"branch manager|store manager|cluster manager|area manager|cent(?:re|er) manager|management associate|"
                   r"rotational|\bmanagement\b"),
]
FAMILY_RES = [(fid, re.compile(pattern, re.I)) for fid, pattern in FAMILY_PATTERNS]

EXCLUDE_RE = re.compile(
    r"\b(engineer(?:ing)?|developer|software|programmer|data scien\w*|data engineer|machine learning|\bml\b|"
    r"architect|devops|\bsre\b|tester|testing|cyber|security (?:analyst|engineer|architect|operations)|"
    r"it (?:support|executive|engineer|admin|manager|helpdesk|infrastructure)|helpdesk|help desk|technical|technician|"
    r"scientist|(?<!market )research(?:er)?|clinical|medical (?:advisor|affairs|lead|writer|science|manager)|physician|doctor|nurse|"
    r"pharmacist|pharmacovigilance|regulatory|quality assurance|quality control|\bqc\b|\bqa\b|laborator\w*|chemist|"
    r"accountant|accounting|accounts (?:payable|receivable|executive|assistant|manager|officer)|account (?:payable|receivable)|"
    r"\baudit\w*|\btax\w*|treasury|"
    r"^finance\b|finance (?:executive|associate|analyst|manager|officer|specialist|controller|operations|business partner)|"
    r"financial (?:analyst|controller|planning|reporting|accountant)|fp&a|controller|"
    r"credit (?:analyst|risk|manager|officer|underwriter|operations|review)|underwrit\w*|actuar\w*|\blegal\b|lawyer|counsel|advocate|"
    r"paralegal|company secretary|compliance|\brisk\b|fraud|sanction\w*|\baml\b|\bkyc\b|collections?|recover(?:y|ies)|"
    r"designer|graphic|\bui\b|\bux\b|video|animator|photographer|copywriter|\bwriter\b|\beditor\b|journalist|"
    r"teacher|tutor|faculty|professor|lecturer|trainer|\bcoach\b|chef|\bcook\b|steward|housekeeping|driver|"
    r"delivery (?:executive|associate|partner|boy|agent)|\brider\b|picker|packer|loader|warehouse associate|"
    r"security guard|\bguard\b|electrician|plumber|mechanic|welder|fitter|machine operator|\behs\b|\bhse\b|safety|"
    r"data entry|tele-?caller|calling executive|\bbpo\b|voice process|"
    r"customer (?:support|care|service)|call cent(?:er|re)|retail associate|store associate|cashier|beauty advisor|"
    r"beautician|fashion consultant|pre-?sales|solutions? (?:engineer|architect|consultant|specialist)|implementation|"
    r"functional consultant|(?:sap|oracle|workday|salesforce|servicenow|dynamics) (?:consultant|developer|admin\w*)|"
    r"product (?:manager|owner|designer|analyst|lead)|data analyst|analytics|business intelligence|\bbi\b|statistic\w*|"
    r"\bquant\w*|equity research|investment bank\w*|portfolio|\btrader\b|\btrading\b|valuation|"
    r"(?:system|systems|database|network|salesforce|servicenow|workday|sap|crm|platform|cloud|linux|windows|server|"
    r"application|identity|lms|ats|hris|talent system) admin\w*|content moderator|annotat\w*|ai trainer|"
    r"language (?:specialist|expert)|translator|interpreter|transcription)\b",
    re.I,
)
# Roles outside the target functions that slip through the family patterns above.
EXCLUDE_EXTRA_RE = re.compile(
    r"\b(commission|independent (?:sales )?(?:agent|contractor|consultant|rep\w*)|expert|data cent(?:er|re)|"
    r"operations tech|mep|electrical|mechanical|civil|hvac|structural|construction|fit[- ]?out|uat|investment|"
    r"liquidity|multi-asset|fixed income|equit(?:y|ies)|derivatives|fund accounting|nav|private (?:markets|financing|credit)|"
    r"embedded|cmc|care coordinator|patient|clinic\w*|nursing)\b",
    re.I,
)
RECRUITING_TECH_RE = re.compile(
    r"\b(?:tech(?:nical|nology)?|engineering|software|it|product|data|gtm|non[- ]tech)\s+(?:recruit\w*|sourc\w*|hiring|"
    r"talent acquisition)\b|\b(?:recruit\w*|sourc\w*|hiring|talent acquisition)\s*[-–,:(/]*\s*(?:for\s+)?"
    r"(?:tech(?:nical|nology)?|engineering|software|it|product|data)\b",
    re.I,
)
EXCLUDE_TYPE_RE = re.compile(r"\b(intern|interns|internship|apprentice\w*|summer (?:analyst|associate)|volunteer|unpaid|freelanc\w*)\b", re.I)
SENIOR_REJECT_RE = re.compile(
    r"\b(director|vice[- ]president|\bvp\b|\bavp\b|\bsvp\b|\bevp\b|head|\bhod\b|chief(?! of staff)|\bceo\b|\bcfo\b|\bcoo\b|"
    r"\bcmo\b|\bcto\b|\bchro\b|general manager|\bgm\b|principal|president|executive director|managing director|"
    r"\bdgm\b|\bagm\b|\bsgm\b|"
    r"managing consultant|engagement manager|country manager|national (?:\w+ )?manager|zonal (?:\w+ )?manager|"
    r"regional (?:\w+ )?manager|cluster head|group (?:\w+ )?manager|senior lead|enterprise account|strategic account|"
    r"named account|global account|(?:senior|sr\.?)\s+(?:[\w&/-]+\s+){0,2}manager|level\s*[5-9])\b",
    re.I,
)
TO_EXECUTIVE_RE = re.compile(
    r"\b(?:to|for|of|in|supporting)\s+(?:the\s+)?(?:ceo|cfo|coo|cmo|cto|md|founders?|chairman|chairperson|president|"
    r"managing director|vice president|vp|director|directors|head|leadership|senior management|cxos?|partners?)\b.*",
    re.I,
)
STRETCH_RE = re.compile(
    r"\b(manager|lead|leader|supervisor|senior (?:specialist|consultant|analyst)|sr\.? (?:specialist|consultant|analyst)|"
    r"hrbp|business partner|chief of staff|founder'?s office|consultant)\b",
    re.I,
)
FIT_LEVEL_RE = re.compile(r"\bassistant manager\b", re.I)

MUMBAI_RE = re.compile(
    r"\b(mumbai|bombay|navi mumbai|thane|bhiwandi|panvel|kalyan|dombivli|vasai|virar|mira road|bhayandar|powai|"
    r"andheri|bandra|bkc|lower parel|worli|goregaon|malad|kandivali|borivali|dahisar|vikhroli|ghatkopar|kurla|chembur|"
    r"dadar|prabhadevi|mahalaxmi|nariman point|santacruz|vile parle|jogeshwari|marol|saki ?naka|mulund|bhandup|vashi|"
    r"airoli|belapur|kharghar|ghansoli|turbhe|rabale|sanpada|nerul|seawoods|byculla|wadala|matunga|kalina|mahape)\b",
    re.I,
)
OTHER_CITY_RE = re.compile(
    r"\b(bengaluru|bangalore|hyderabad|pune|gurgaon|gurugram|noida|delhi|new delhi|chennai|kolkata|ahmedabad|jaipur|"
    r"kochi|cochin|indore|chandigarh|lucknow|surat|nagpur|aurangabad|nashik|vadodara|coimbatore|bhubaneswar|"
    r"visakhapatnam|patna|guwahati|goa|mysore|mysuru|trivandrum|thiruvananthapuram|raipur|bhopal|ranchi|kanpur|"
    r"agra|varanasi|meerut|moradabad|bareilly|aligarh|ghaziabad|faridabad|ludhiana|amritsar|jalandhar|dehradun|"
    r"jodhpur|udaipur|kota|ajmer|gwalior|jabalpur|rajkot|jamnagar|bhavnagar|hubli|belgaum|belagavi|mangalore|"
    r"mangaluru|madurai|trichy|tiruchirappalli|salem|vijayawada|guntur|warangal|cuttack|siliguri|durgapur|asansol|"
    r"jamshedpur|dhanbad|prayagraj|allahabad|gorakhpur|kolhapur|solapur|sangli|satara|ahmednagar|jalgaon|amravati|"
    r"akola|nanded|latur|hisar|rohtak|panipat|karnal|sonipat|bhiwadi|hosur|tirupati|nellore|puducherry|pondicherry|"
    r"srinagar|jammu|shimla|haridwar|rishikesh|greater noida)\b",
    re.I,
)
INDIA_RE = re.compile(r"\b(india|indian|in\b(?=\s*[-,;)]|$)|maharashtra|ist|indian standard time)\b", re.I)
REMOTE_RE = re.compile(r"\b(remote|work from home|wfh|work from anywhere|distributed|telecommute|virtual)\b", re.I)
GLOBAL_RE = re.compile(
    r"\b(anywhere|worldwide|world wide|global|international|all countries|apac|asia[- ]pacific|\basia\b|south asia|"
    r"emerging markets|utc\s*\+\s*5(?::30|\.5)?|gmt\s*\+\s*5(?::30|\.5)?)\b",
    re.I,
)
# Remote roles count only when they explicitly accept people in India or Asia-Pacific.
ASIA_RE = re.compile(
    r"\b(apac|asia[- ]pacific|asia|south asia|utc\s*\+\s*5(?::30|\.5)?|gmt\s*\+\s*5(?::30|\.5)?)\b",
    re.I,
)
FOREIGN_TITLE_RE = re.compile(
    r"\b(us|usa|u\.s\.|united states|north america|americas|canada|uk|united kingdom|europe|emea|latam|latin america|"
    r"australia|anz|new zealand|midwest|northeast|southeast|southwest|west coast|east coast|federal|est|pst|cst|mst|"
    r"germany|france|spain|dach|nordics|benelux|japan|singapore|philippines|mexico|brazil|dubai|uae|saudi|ksa|gcc)\b",
    re.I,
)
EMOJI_RE = re.compile("[\U0001F000-\U0001FAFF\u2600-\u27BF\uFE0F\u200D]+")
RESTRICT_RE = re.compile(
    r"\b(us only|usa only|u\.s\. only|united states only|must (?:be|reside|live) in the (?:us|u\.s\.|united states)|"
    r"authorized to work in the (?:us|u\.s\.|united states)|us citizens?|north america only|canada only|europe only|"
    r"eu only|uk only|latam only|(?:must|only|able to hire|hire candidates)[^.]{0,60}(?:reside|live|located|based) in "
    r"(?!india\b)[a-z]+)\b",
    re.I,
)
YEARS_RE = re.compile(
    r"(?<![\d.$€£₹])(\d{1,2})\s*(?:\+|plus)?\s*(?:(?:-|–|—|to)\s*(\d{1,2})\s*\+?)?\s*(?:years?|yrs?)(?-i:(?![a-z]))"
    r"(?P<after>[^.\n;]{0,90})",
    re.I,
)

# ---------------------------------------------------------------------------
# Small helpers
# ---------------------------------------------------------------------------


def utc_now() -> dt.datetime:
    return dt.datetime.now(dt.timezone.utc).replace(microsecond=0)


def now_iso() -> str:
    return utc_now().isoformat()


def strip_html(value: Any) -> str:
    if value is None:
        return ""
    text = str(value)
    text = re.sub(r"<\s*br\s*/?>|</p>|</div>|</li>|</h\d>", "\n", text, flags=re.I)
    text = re.sub(r"<[^>]+>", " ", text)
    text = html.unescape(text)
    text = re.sub(r"[ \t\r\f\v]+", " ", text)
    return re.sub(r"\n\s*\n+", "\n", text).strip()


def clean(value: Any, limit: int = 200) -> str:
    text = EMOJI_RE.sub("", strip_html(value))
    text = re.sub(r"\(do not use\)", "", text, flags=re.I)
    text = re.sub(r"\s+", " ", text).strip(" -|")
    return text if len(text) <= limit else text[: limit - 1].rstrip() + "…"


def norm(value: str | None) -> str:
    value = (value or "").lower()
    value = re.sub(r"\b(pvt|private|ltd|limited|inc|llc|llp|corp|corporation|india|technologies|technology)\b", "", value)
    return re.sub(r"[^a-z0-9]+", "", value)


def parse_date(value: Any) -> str:
    if value in (None, "", 0):
        return ""
    try:
        if isinstance(value, (int, float)) or (isinstance(value, str) and value.strip().isdigit()):
            number = float(value)
            if number > 10_000_000_000:
                number /= 1000
            return dt.datetime.fromtimestamp(number, dt.timezone.utc).replace(microsecond=0).isoformat()
        text = str(value).strip()
        if re.match(r"\d{4}-\d{2}-\d{2}", text):
            parsed = dt.datetime.fromisoformat(text.replace("Z", "+00:00"))
            if parsed.tzinfo is None:
                parsed = parsed.replace(tzinfo=dt.timezone.utc)
            return parsed.astimezone(dt.timezone.utc).replace(microsecond=0).isoformat()
        for fmt in ("%B %d, %Y", "%b %d, %Y", "%d %B %Y", "%d %b %Y"):
            try:
                return dt.datetime.strptime(text, fmt).replace(tzinfo=dt.timezone.utc).isoformat()
            except ValueError:
                pass
        parsed = email.utils.parsedate_to_datetime(text)
        if parsed.tzinfo is None:
            parsed = parsed.replace(tzinfo=dt.timezone.utc)
        return parsed.astimezone(dt.timezone.utc).replace(microsecond=0).isoformat()
    except Exception:
        lower = str(value).lower()
        if "today" in lower or "just" in lower or "hour" in lower:
            return now_iso()
        if "yesterday" in lower:
            return (utc_now() - dt.timedelta(days=1)).isoformat()
        match = re.search(r"(\d+)\+?\s+days?\s+ago", lower)
        if match:
            return (utc_now() - dt.timedelta(days=int(match.group(1)))).isoformat()
        match = re.search(r"(\d+)\+?\s+(weeks?|months?)\s+ago", lower)
        if match:
            days = int(match.group(1)) * (7 if match.group(2).startswith("week") else 30)
            return (utc_now() - dt.timedelta(days=days)).isoformat()
        return ""


def age_days(iso: str) -> float | None:
    if not iso:
        return None
    try:
        return (utc_now() - dt.datetime.fromisoformat(iso)).total_seconds() / 86400
    except Exception:
        return None


def required_years(text: str | None) -> int | None:
    """Return the minimum years of experience a posting clearly asks for."""
    text = text or ""
    best = None
    for match in YEARS_RE.finditer(text):
        minimum = int(match.group(1))
        before = text[max(0, match.start() - 70):match.start()].lower()
        after = match.group("after").lower()
        context = f"{before} {after}"
        token = match.group(0).split("y")[0].lower()
        if not 0 <= minimum <= 20:
            continue
        if not re.search(r"experience|experienced|\bexp\b|industry|professional|background|track record|work(?:ing)?|"
                         r"in (?:sales|hr|human|admin|operations|marketing|recruit)|role|similar|relevant",
                         after[:70] + " " + before[-30:]):
            continue
        if re.search(r"\b(company|founded|history|old|age|ago|warranty|retention|in business|since|anniversary|vesting|"
                     r"tenure|contract|duration|period|commitment|leases?)\b", context):
            continue
        if re.search(r"\b(our|founder|founders|leaders?|team has|has been|have been|we have|who has|alumni|clients?)\b", before[-60:]):
            continue
        strong = (
            re.search(r"\+|plus|-|–|—|\bto\b", token)
            or re.search(r"(at least|minimum(?: of)?|min\.?|more than|over|require[sd]?|must have|you have|you bring|need|"
                         r"experience\s*:?|exp\s*:?|having|with)\s*$", before)
            or re.search(r"(^|\n|[-•*:])\s*$", before)
        )
        if not strong:
            continue
        nearby = text[max(0, match.start() - 90):min(len(text), match.end() + 90)].lower()
        if re.search(r"\d{1,2}\s*\+?\s*(?:years?|yrs?)[^.\n;]{0,70}\bor\b[^.\n;]{0,50}\d{1,2}\s*\+?\s*(?:years?|yrs?)", nearby):
            continue
        clause = re.split(r"[,(]", after, maxsplit=1)[0]
        if re.search(r"(last|past|next|within|every|over the)\s*$", before) or re.search(
            r"\b(preferred|nice to have|bonus|ideally|advantage)\b", before[-40:] + " " + clause
        ):
            continue
        best = minimum if best is None else max(best, minimum)
    return best


def valid_url(url: str) -> bool:
    return bool(re.match(r"^https?://[^\s\"'<>]+$", url or ""))


# ---------------------------------------------------------------------------
# HTTP
# ---------------------------------------------------------------------------


def fetch(url: str, *, data: bytes | None = None, method: str | None = None, timeout: int = 30,
          accept: str = "application/json", headers: dict[str, str] | None = None) -> bytes:
    hdrs = {"User-Agent": USER_AGENT, "Accept": accept, "Accept-Language": "en-IN,en;q=0.9"}
    hdrs.update(headers or {})
    last: Exception | None = None
    for attempt in range(3):
        req = urllib.request.Request(url, data=data, headers=hdrs, method=method)
        try:
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                return resp.read()
        except urllib.error.HTTPError as exc:
            if exc.code not in RETRY_CODES or attempt == 2:
                raise
            last = exc
        except (urllib.error.URLError, TimeoutError, ConnectionError) as exc:
            if attempt == 2:
                raise
            last = exc
        time.sleep(2 * (attempt + 1))
    raise last or RuntimeError("request failed")


def get_json(url: str, **kwargs: Any) -> Any:
    return json.loads(fetch(url, **kwargs).decode("utf-8", "replace"))


def post_json(url: str, payload: Any, **kwargs: Any) -> Any:
    body = json.dumps(payload).encode()
    return get_json(url, data=body, method="POST", headers={"Content-Type": "application/json"}, **kwargs)


def get_text(url: str, **kwargs: Any) -> str:
    accept = "application/rss+xml, application/xml, text/xml, text/html;q=0.8, */*;q=0.5"
    return fetch(url, accept=accept, **kwargs).decode("utf-8", "replace")


# ---------------------------------------------------------------------------
# Sources
# ---------------------------------------------------------------------------


def posting(source_id: str, via: str, company: Any, title: Any, location: Any, url: Any, posted: Any = "",
            description: Any = "", *, remote: bool = False, remote_india: bool = False, ext_id: Any = "",
            detail: dict[str, str] | None = None) -> dict[str, Any]:
    url = str(url or "").strip()
    ident = str(ext_id or url)
    return {
        "key": hashlib.sha1(f"{source_id}|{ident}".encode()).hexdigest()[:16],
        "source_id": source_id,
        "via": via,
        "company": clean(company, 120) or "Company not listed",
        "title": clean(title, 180),
        "location": clean(location, 260),
        "url": url,
        "posted_at": parse_date(posted),
        "description": strip_html(description)[:9000],
        "remote": remote,
        "remote_india": remote_india,
        "detail": detail,
    }


def src_workable(cfg: dict[str, Any]) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    seen: set[str] = set()
    plan = [("Mumbai", cfg.get("mumbai_queries", []), False), ("India", cfg.get("remote_queries", []), True)]
    for location, queries, remote_only in plan:
        for query in queries:
            token = ""
            for _ in range(int(cfg.get("pages", 2))):
                params = {"query": query, "location": location}
                if token:
                    params["pageToken"] = token
                data = get_json("https://jobs.workable.com/api/v1/jobs?" + urllib.parse.urlencode(params))
                for x in data.get("jobs", []):
                    workplace = (x.get("workplace") or "").lower()
                    if x.get("id") in seen or (remote_only and workplace != "remote"):
                        continue
                    seen.add(x.get("id"))
                    loc = "; ".join(x.get("locations") or [])
                    if workplace in {"remote", "hybrid"}:
                        loc = f"{loc} ({workplace})"
                    desc = "\n".join([x.get("description") or "", x.get("requirementsSection") or ""])
                    india = "india" in loc.lower()
                    out.append(posting("workable", "Workable", (x.get("company") or {}).get("title"), x.get("title"), loc,
                                       x.get("url"), x.get("created"), desc, remote=workplace == "remote",
                                       remote_india=workplace == "remote" and india, ext_id=x.get("id")))
                token = data.get("nextPageToken") or ""
                time.sleep(0.4)
                if not token:
                    break
    return out


def src_amazon(_: dict[str, Any]) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    offset = 0
    while offset < 800:
        params = [("normalized_country_code[]", "IND"), ("normalized_city_name[]", "Mumbai"), ("result_limit", "100"),
                  ("offset", str(offset)), ("sort", "recent")]
        data = get_json("https://www.amazon.jobs/en/search.json?" + urllib.parse.urlencode(params))
        jobs = data.get("jobs") or []
        for x in jobs:
            if x.get("is_intern"):
                continue
            desc = "\n".join([x.get("description") or "", x.get("basic_qualifications") or "",
                              x.get("preferred_qualifications") or ""])
            loc = x.get("normalized_location") or x.get("location") or x.get("city") or ""
            out.append(posting("amazon", "Amazon Jobs", x.get("company_name") or "Amazon", x.get("title"), loc,
                               "https://www.amazon.jobs" + (x.get("job_path") or ""), x.get("posted_date"), desc,
                               ext_id=x.get("id_icims") or x.get("id")))
        offset += 100
        if not jobs or offset >= int(data.get("hits") or 0):
            break
    return out


def src_oracle(board: dict[str, Any]) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    host, site = board["host"], board["site"]
    offset = 0
    while offset < int(board.get("max", 300)):
        finder = (f"findReqs;siteNumber={site},limit=25,offset={offset},locationId={board['location_id']},"
                  "sortBy=POSTING_DATES_DESC")
        url = (f"https://{host}/hcmRestApi/resources/latest/recruitingCEJobRequisitions?onlyData=true"
               f"&expand=requisitionList.secondaryLocations&finder={urllib.parse.quote(finder, safe='=,;')}")
        data = get_json(url)
        item = (data.get("items") or [{}])[0]
        reqs = item.get("requisitionList") or []
        for x in reqs:
            locs = [x.get("PrimaryLocation") or ""]
            locs += [s.get("Name") or s.get("LocationName") or "" for s in x.get("secondaryLocations") or []]
            loc = "; ".join(dict.fromkeys(filter(None, locs)))
            if not MUMBAI_RE.search(loc):
                loc = f"{loc}; {board.get('location_label', 'Mumbai')}".strip("; ")
            desc = "\n".join([x.get("ShortDescriptionStr") or "", x.get("ExternalQualificationsStr") or "",
                              x.get("ExternalResponsibilitiesStr") or ""])
            out.append(posting(f"oracle:{board['name']}", "Company site", board["name"], x.get("Title"), loc,
                               f"https://{host}/hcmUI/CandidateExperience/en/sites/{site}/job/{x.get('Id')}",
                               x.get("PostedDate"), desc, ext_id=x.get("Id")))
        offset += 25
        if len(reqs) < 25:
            break
    return out


def src_workday(board: dict[str, Any]) -> list[dict[str, Any]]:
    host, tenant, site = board["host"], board["tenant"], board["site"]
    base = f"https://{host}/wday/cxs/{tenant}/{site}/jobs"
    out: list[dict[str, Any]] = []
    offset, total = 0, None
    while True:
        data = post_json(base, {"appliedFacets": {}, "limit": 20, "offset": offset, "searchText": board.get("search", "Mumbai")})
        if total is None:
            total = int(data.get("total") or 0)
        page = data.get("jobPostings") or []
        for x in page:
            path = x.get("externalPath") or ""
            loc = x.get("locationsText") or ""
            match = re.match(r"/job/([^/]+)/", path)
            if match:
                loc = f"{loc}; {match.group(1).replace('-', ' ')}"
            out.append(posting(f"workday:{board['name']}", "Company site", board["name"], x.get("title"), loc,
                               f"https://{host}/en-US/{site}{path}", x.get("postedOn"), ext_id=path,
                               detail={"kind": "workday", "url": f"https://{host}/wday/cxs/{tenant}/{site}{path}"}))
        offset += 20
        if not page or offset >= min(total or 0, int(board.get("max", 400))):
            break
    return out


def src_greenhouse(board: dict[str, Any]) -> list[dict[str, Any]]:
    slug = urllib.parse.quote(board["slug"])
    data = get_json(f"https://boards-api.greenhouse.io/v1/boards/{slug}/jobs")
    return [
        posting(f"greenhouse:{board['name']}", "Company site", board["name"], x.get("title"),
                (x.get("location") or {}).get("name", ""), x.get("absolute_url"),
                x.get("first_published") or x.get("updated_at"), ext_id=x.get("id"),
                detail={"kind": "greenhouse", "url": f"https://boards-api.greenhouse.io/v1/boards/{slug}/jobs/{x.get('id')}"})
        for x in data.get("jobs", [])
    ]


def src_lever(board: dict[str, Any]) -> list[dict[str, Any]]:
    data = get_json(f"https://api.lever.co/v0/postings/{urllib.parse.quote(board['slug'])}?mode=json", timeout=40)
    out = []
    for x in data:
        cats = x.get("categories") or {}
        locs = cats.get("allLocations") or [cats.get("location", "")]
        loc = "; ".join(filter(None, locs))
        workplace = (x.get("workplaceType") or "").lower()
        if workplace:
            loc = f"{loc} ({workplace})"
        lists = "\n".join(f"{i.get('text', '')}\n{strip_html(i.get('content', ''))}" for i in x.get("lists") or [])
        desc = "\n".join([x.get("descriptionPlain") or "", lists, x.get("additionalPlain") or ""])
        out.append(posting(f"lever:{board['name']}", "Company site", board["name"], x.get("text"), loc, x.get("hostedUrl"),
                           x.get("createdAt"), desc, remote=workplace == "remote", ext_id=x.get("id")))
    return out


def src_ashby(board: dict[str, Any]) -> list[dict[str, Any]]:
    data = get_json(f"https://api.ashbyhq.com/posting-api/job-board/{urllib.parse.quote(board['slug'])}", timeout=40)
    out = []
    for x in data.get("jobs", []):
        if x.get("isListed") is False:
            continue
        locs = [x.get("location", "")] + [y.get("location", "") for y in x.get("secondaryLocations") or []]
        loc = "; ".join(dict.fromkeys(filter(None, locs)))
        if x.get("isRemote"):
            loc += " (remote)"
        out.append(posting(f"ashby:{board['name']}", "Company site", board["name"], x.get("title"), loc, x.get("jobUrl"),
                           x.get("publishedAt"), x.get("descriptionPlain", ""), remote=bool(x.get("isRemote")),
                           ext_id=x.get("id")))
    return out


def src_smartrecruiters(board: dict[str, Any]) -> list[dict[str, Any]]:
    slug = urllib.parse.quote(board["slug"])
    content: list[dict[str, Any]] = []
    for offset in range(0, 1000, 100):
        data = get_json(f"https://api.smartrecruiters.com/v1/companies/{slug}/postings?limit=100&offset={offset}&country=in")
        page = data.get("content", [])
        content.extend(page)
        if len(page) < 100:
            break
    out = []
    for x in content:
        loc_data = x.get("location") or {}
        loc = loc_data.get("fullLocation") or ", ".join(filter(None, [loc_data.get("city"), loc_data.get("region"), loc_data.get("country")]))
        if loc_data.get("remote"):
            loc += " (remote)"
        out.append(posting(f"smartrecruiters:{board['name']}", "Company site", board["name"], x.get("name"), loc,
                           f"https://jobs.smartrecruiters.com/{board['slug']}/{x.get('id')}", x.get("releasedDate"),
                           remote=bool(loc_data.get("remote")), ext_id=x.get("id"),
                           detail={"kind": "smartrecruiters", "url": f"https://api.smartrecruiters.com/v1/companies/{slug}/postings/{x.get('id')}"}))
    return out


def src_himalayas(cfg: dict[str, Any]) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    seen: set[str] = set()
    for query in cfg.get("queries", []):
        for page in range(1, int(cfg.get("pages", 2)) + 1):
            params = {"q": query, "country": "India", "page": page}
            data = get_json("https://himalayas.app/jobs/api/search?" + urllib.parse.urlencode(params), timeout=40)
            jobs = data.get("jobs") or []
            for x in jobs:
                guid = x.get("guid") or x.get("applicationLink")
                if guid in seen:
                    continue
                seen.add(guid)
                restrictions = x.get("locationRestrictions") or []
                if restrictions and not any("india" in str(r).lower() for r in restrictions):
                    continue
                loc = "Remote: " + (", ".join(restrictions[:6]) + ("…" if len(restrictions) > 6 else "") if restrictions else "worldwide")
                desc = "\n".join([x.get("excerpt") or "", x.get("description") or ""])
                out.append(posting("himalayas", "Himalayas", x.get("companyName"), x.get("title"), loc,
                                   x.get("applicationLink") or guid, x.get("pubDate"), desc, remote=True,
                                   remote_india=bool(restrictions), ext_id=guid))
            time.sleep(0.4)
            if len(jobs) < 20:
                break
    return out


def remote_place_ok(location: str) -> bool:
    return bool(INDIA_RE.search(location) or ASIA_RE.search(location))


def src_remotive(cfg: dict[str, Any]) -> list[dict[str, Any]]:
    # Remotive asks for at most a few requests a day, so fetch the whole public feed once.
    data = get_json("https://remotive.com/api/remote-jobs?limit=1000", timeout=40)
    out = []
    for x in data.get("jobs", []):
        loc = x.get("candidate_required_location") or "Remote"
        out.append(posting("remotive", "Remotive", x.get("company_name"), x.get("title"), f"Remote: {loc}", x.get("url"),
                           x.get("publication_date"), x.get("description"), remote=True,
                           remote_india=remote_place_ok(loc), ext_id=x.get("id")))
    return out


def src_jobicy(cfg: dict[str, Any]) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for geo in cfg.get("geos", ["apac", "anywhere"]):
        data = get_json(f"https://jobicy.com/api/v2/remote-jobs?count=100&geo={urllib.parse.quote(geo)}", timeout=40)
        for x in data.get("jobs", []):
            loc = x.get("jobGeo") or geo
            desc = "\n".join([x.get("jobExcerpt") or "", x.get("jobDescription") or "", x.get("jobLevel") or ""])
            out.append(posting("jobicy", "Jobicy", x.get("companyName"), x.get("jobTitle"), f"Remote: {loc}", x.get("url"),
                               x.get("pubDate"), desc, remote=True, remote_india=remote_place_ok(loc), ext_id=x.get("id")))
    return out


def src_workingnomads(_: dict[str, Any]) -> list[dict[str, Any]]:
    data = get_json("https://www.workingnomads.com/api/exposed_jobs/", timeout=40)
    out = []
    for x in data:
        loc = x.get("location") or "Remote"
        out.append(posting("workingnomads", "Working Nomads", x.get("company_name"), x.get("title"), f"Remote: {loc}",
                           x.get("url"), x.get("pub_date"), x.get("description"), remote=True,
                           remote_india=remote_place_ok(loc), ext_id=x.get("url")))
    return out


def src_weworkremotely(cfg: dict[str, Any]) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for feed in cfg.get("feeds", []):
        root = ET.fromstring(get_text(feed))
        for item in root.findall(".//item"):
            raw_title = item.findtext("title") or ""
            company, title = raw_title.split(":", 1) if ":" in raw_title else ("", raw_title)
            region = item.findtext("region") or ""
            desc = strip_html(item.findtext("description") or "")
            if not region:
                match = re.search(r"(?:^|\n)\s*(?:Region|Candidate Location)\s*:\s*([^\n]{2,80})", desc, re.I)
                region = match.group(1).strip() if match else ""
            loc = f"Remote: {region or 'region not stated'}"
            out.append(posting("weworkremotely", "We Work Remotely", company, title, loc, item.findtext("link"),
                               item.findtext("pubDate"), desc, remote=True, remote_india=remote_place_ok(region),
                               ext_id=item.findtext("guid") or item.findtext("link")))
    return out


BOARD_FETCHERS: dict[str, Callable[[dict[str, Any]], list[dict[str, Any]]]] = {
    "greenhouse": src_greenhouse,
    "lever": src_lever,
    "ashby": src_ashby,
    "smartrecruiters": src_smartrecruiters,
}


def fetch_detail(job: dict[str, Any]) -> dict[str, Any]:
    kind, url = job["detail"]["kind"], job["detail"]["url"]
    data = get_json(url, timeout=30)
    location, description = job["location"], ""
    if kind == "workday":
        info = data.get("jobPostingInfo") or {}
        description = strip_html(info.get("jobDescription") or "")
        locs = [info.get("location")] + list(info.get("additionalLocations") or [])
        if any(locs):
            location = "; ".join(dict.fromkeys(filter(None, locs)))
        if info.get("remoteType"):
            location += f" ({info['remoteType']})"
    elif kind == "greenhouse":
        description = strip_html(html.unescape(data.get("content") or ""))
        offices = [o.get("name") or o.get("location") or "" for o in data.get("offices") or []]
        location = "; ".join(dict.fromkeys(filter(None, [(data.get("location") or {}).get("name", "")] + offices))) or location
    elif kind == "smartrecruiters":
        sections = ((data.get("jobAd") or {}).get("sections") or {}).values()
        description = strip_html("\n".join(s.get("text", "") for s in sections if isinstance(s, dict)))
        loc_data = data.get("location") or {}
        location = loc_data.get("fullLocation") or location
    return {"location": clean(location, 260), "years": required_years(description), "checked": now_iso()}


# ---------------------------------------------------------------------------
# Classification
# ---------------------------------------------------------------------------


def classify_title(title: str) -> tuple[str, str] | None:
    """Return (family, level) for a target role, or None when it should be skipped."""
    if not title or EXCLUDE_TYPE_RE.search(title):
        return None
    screened = RECRUITING_TECH_RE.sub(" recruiter ", title)
    if EXCLUDE_RE.search(screened) or EXCLUDE_EXTRA_RE.search(screened):
        return None
    family = next((fid for fid, pattern in FAMILY_RES if pattern.search(title)), None)
    if not family:
        return None
    level_text = TO_EXECUTIVE_RE.sub("", title)
    if SENIOR_REJECT_RE.search(level_text):
        return None
    if FIT_LEVEL_RE.search(level_text):
        return family, "fit"
    return family, "stretch" if STRETCH_RE.search(level_text) else "fit"


def classify_places(job: dict[str, Any]) -> list[str]:
    loc, title = job["location"], job["title"]
    places: list[str] = []
    in_mumbai = bool(MUMBAI_RE.search(loc))
    title_city = OTHER_CITY_RE.search(title)
    if in_mumbai and title_city and not MUMBAI_RE.search(title):
        in_mumbai = False
    if in_mumbai:
        places.append("mumbai")
    remote = job.get("remote") or bool(REMOTE_RE.search(loc)) or bool(re.search(r"\bremote\b", title, re.I))
    if not remote:
        return places
    if in_mumbai:
        places.append("remote")
        return places
    company_site = job["source_id"].split(":")[0] in {"workday", "oracle", "greenhouse", "lever", "ashby", "smartrecruiters"}
    if company_site and (job["source_id"].startswith(("workday:", "oracle:")) or OTHER_CITY_RE.search(f"{loc} {title}")):
        # Employer boards often mark field roles in other cities as remote; those are not work-from-home roles.
        return places
    if OTHER_CITY_RE.search(title) and not REMOTE_RE.search(title):
        # A city in the title of a "remote" listing usually means a field role based there.
        return places
    if FOREIGN_TITLE_RE.search(title) and not re.search(r"\bindia\b", title, re.I):
        return places
    if RESTRICT_RE.search(job.get("description") or ""):
        return places
    if job.get("remote_india") or INDIA_RE.search(loc) or ASIA_RE.search(loc):
        places.append("remote")
    return places


# ---------------------------------------------------------------------------
# Runner
# ---------------------------------------------------------------------------


class Tracker:
    def __init__(self, config: dict[str, Any], verbose: bool = False):
        self.config = config
        self.verbose = verbose
        self.filters = config.get("filters", {})
        self.health: dict[str, dict[str, Any]] = {}
        self.state = load_state()

    def log(self, message: str) -> None:
        if self.verbose:
            print(message, file=sys.stderr, flush=True)

    def tasks(self) -> list[tuple[str, str, Callable[[dict[str, Any]], list[dict[str, Any]]], dict[str, Any]]]:
        cfg = self.config
        sources = cfg.get("sources", {})
        simple = {
            "workable": ("Workable", src_workable),
            "amazon": ("Amazon Jobs", src_amazon),
            "himalayas": ("Himalayas", src_himalayas),
            "remotive": ("Remotive", src_remotive),
            "jobicy": ("Jobicy", src_jobicy),
            "workingnomads": ("Working Nomads", src_workingnomads),
            "weworkremotely": ("We Work Remotely", src_weworkremotely),
        }
        tasks = []
        for sid, (label, fn) in simple.items():
            settings = sources.get(sid, {})
            if settings.get("enabled", True):
                tasks.append((sid, label, fn, settings))
        for board in cfg.get("oracle", []):
            tasks.append((f"oracle:{board['name']}", board["name"], src_oracle, board))
        for board in cfg.get("workday", []):
            tasks.append((f"workday:{board['name']}", board["name"], src_workday, board))
        for board in cfg.get("boards", []):
            fn = BOARD_FETCHERS[board["provider"]]
            tasks.append((f"{board['provider']}:{board['name']}", board["name"], fn, board))
        return tasks

    def collect(self, only: set[str] | None) -> list[dict[str, Any]]:
        jobs: list[dict[str, Any]] = []

        def run(task: tuple[str, str, Callable[[dict[str, Any]], list[dict[str, Any]]], dict[str, Any]]) -> list[dict[str, Any]]:
            sid, label, fn, settings = task
            start = time.time()
            try:
                found = fn(settings)
                self.health[sid] = {"label": label, "ok": True, "count": len(found), "seconds": round(time.time() - start, 1)}
                self.log(f"ok    {sid}: {len(found)} postings in {time.time() - start:.1f}s")
                return found
            except Exception as exc:  # One broken source should not stop the rest.
                message = f"{type(exc).__name__}: {clean(str(exc), 160)}"
                self.health[sid] = {"label": label, "ok": False, "count": 0, "error": message}
                self.log(f"ERROR {sid}: {message}")
                return []

        tasks = [t for t in self.tasks() if not only or t[0].split(":")[0] in only or t[0] in only]
        with cf.ThreadPoolExecutor(max_workers=10) as pool:
            for found in pool.map(run, tasks):
                jobs.extend(found)
        return jobs

    def screen(self, raw: list[dict[str, Any]]) -> list[dict[str, Any]]:
        details_cache: dict[str, Any] = self.state.setdefault("details", {})
        candidates = []
        for job in raw:
            if not valid_url(job["url"]):
                continue
            result = classify_title(job["title"])
            if not result:
                continue
            job["family"], job["level"] = result
            candidates.append(job)

        # Fetch full postings only for title matches whose location could be relevant.
        maybe_place = re.compile(f"{MUMBAI_RE.pattern}|{REMOTE_RE.pattern}|\\b\\d+ locations\\b|\\bindia\\b", re.I)
        pending = []
        for job in candidates:
            if not job.get("detail"):
                continue
            cached = details_cache.get(job["key"])
            if cached:
                job["location"] = cached.get("location") or job["location"]
                job["years"] = cached.get("years")
                job["detail_done"] = True
                cached["seen"] = now_iso()
            elif maybe_place.search(job["location"]):
                pending.append(job)
        limit = int(self.filters.get("detail_fetch_limit", 450))
        fetched = failed = 0
        with cf.ThreadPoolExecutor(max_workers=8) as pool:
            futures = {pool.submit(fetch_detail, job): job for job in pending[:limit]}
            for future in cf.as_completed(futures):
                job = futures[future]
                try:
                    info = future.result()
                    info["seen"] = now_iso()
                    details_cache[job["key"]] = info
                    job["location"] = info["location"] or job["location"]
                    job["years"] = info["years"]
                    job["detail_done"] = True
                    fetched += 1
                except Exception:
                    failed += 1
        self.log(f"details: fetched {fetched}, failed {failed}, skipped {max(0, len(pending) - limit)}")

        max_years = int(self.filters.get("max_years_required", 5))
        max_age = float(self.filters.get("max_age_days", 60))
        accepted = []
        for job in candidates:
            places = classify_places(job)
            if not places:
                continue
            years = job.get("years") if job.get("detail_done") else required_years(job["description"])
            if years is not None and years > max_years:
                continue
            age = age_days(job["posted_at"])
            if age is not None and age > max_age:
                continue
            job["places"] = places
            job["years"] = years
            accepted.append(job)
        return dedupe(accepted)

    def merge(self, jobs: list[dict[str, Any]]) -> dict[str, Any]:
        state = self.state
        stored: dict[str, Any] = state.setdefault("jobs", {})
        now = now_iso()
        baseline = not state.get("runs")
        seen_keys = set()
        for job in jobs:
            prev = stored.get(job["key"], {})
            seen_keys.add(job["key"])
            stored[job["key"]] = {
                "key": job["key"],
                "title": job["title"],
                "company": job["company"],
                "family": job["family"],
                "level": job["level"],
                "places": job["places"],
                "location": clean(job["location"], 160),
                "url": job["url"],
                "via": job["via"],
                "source_id": job["source_id"],
                "posted_at": job["posted_at"] or prev.get("posted_at", ""),
                "years": job.get("years"),
                "first_seen": prev.get("first_seen", now),
                "baseline": prev.get("baseline", baseline),
                "last_seen": now,
                "active": True,
            }
        failed_sources = {sid for sid, h in self.health.items() if not h.get("ok")}
        forget_after = float(self.filters.get("forget_after_days", 45))
        for key in list(stored):
            rec = stored[key]
            if key in seen_keys:
                continue
            last = age_days(rec.get("last_seen", "")) or 0
            # Keep roles from a source that failed this run, but only briefly.
            rec["active"] = rec.get("source_id") in failed_sources and last <= 3 and rec.get("active", False)
            if last > forget_after:
                del stored[key]
        details = state.setdefault("details", {})
        for key in list(details):
            if (age_days(details[key].get("seen", "")) or 0) > forget_after:
                del details[key]
        active = [r for r in stored.values() if r.get("active")]
        run = {
            "at": now,
            "active": len(active),
            "new": sum(1 for r in active if r["first_seen"] == now and not r["baseline"]),
            "sources_ok": sum(1 for h in self.health.values() if h.get("ok")),
            "sources_failed": sorted(failed_sources),
        }
        state["runs"] = (state.get("runs") or [])[-59:] + [run]
        state["health"] = self.health
        state["updated_at"] = now
        return run


def dedupe(jobs: list[dict[str, Any]]) -> list[dict[str, Any]]:
    best: dict[tuple[str, str, tuple[str, ...]], dict[str, Any]] = {}
    for job in jobs:
        group = (norm(job["company"]), norm(job["title"]), tuple(job["places"]))
        current = best.get(group)
        if current is None or (job["posted_at"] or "") > (current["posted_at"] or ""):
            best[group] = job
    return list(best.values())


def load_state() -> dict[str, Any]:
    if STATE_PATH.exists():
        return json.loads(STATE_PATH.read_text())
    return {"jobs": {}, "details": {}, "runs": []}


def save_state(state: dict[str, Any]) -> None:
    STATE_PATH.parent.mkdir(parents=True, exist_ok=True)
    tmp = STATE_PATH.with_suffix(".tmp")
    tmp.write_text(json.dumps(state, indent=1, ensure_ascii=False, sort_keys=True) + "\n")
    os.replace(tmp, STATE_PATH)


# ---------------------------------------------------------------------------
# Dashboard
# ---------------------------------------------------------------------------


def search_links(config: dict[str, Any]) -> list[dict[str, Any]]:
    out = []
    for item in config.get("search_links", []):
        links = []
        for term in item["terms"]:
            q = urllib.parse.quote(term)
            slug = re.sub(r"[^a-z0-9]+", "-", term.lower()).strip("-")
            links.append({
                "term": term,
                "linkedin": f"https://www.linkedin.com/jobs/search/?keywords={q}&location=Mumbai%2C%20Maharashtra%2C%20India&f_TPR=r604800",
                "linkedin_remote": f"https://www.linkedin.com/jobs/search/?keywords={q}&location=India&f_WT=2&f_TPR=r604800",
                "naukri": f"https://www.naukri.com/{slug}-jobs-in-mumbai",
                "indeed": f"https://in.indeed.com/jobs?q={urllib.parse.quote_plus(term)}&l=Mumbai%2C+Maharashtra&fromage=7",
            })
        out.append({"family": item["family"], "links": links})
    return out


def source_summary(health: dict[str, Any]) -> list[dict[str, Any]]:
    groups: dict[str, dict[str, Any]] = {}
    names = {
        "workable": "Workable", "amazon": "Amazon Jobs", "himalayas": "Himalayas", "remotive": "Remotive",
        "jobicy": "Jobicy", "workingnomads": "Working Nomads", "weworkremotely": "We Work Remotely",
    }
    for sid, h in health.items():
        kind = sid.split(":")[0]
        name = names.get(kind, "Company career sites")
        g = groups.setdefault(name, {"name": name, "checked": 0, "failed": [], "postings": 0})
        g["checked"] += 1
        g["postings"] += int(h.get("count") or 0)
        if not h.get("ok"):
            g["failed"].append(h.get("label") or sid)
    order = list(names.values()) + ["Company career sites"]
    return sorted(groups.values(), key=lambda g: order.index(g["name"]) if g["name"] in order else 99)


def build_site(config: dict[str, Any], state: dict[str, Any]) -> Path:
    jobs = [r for r in state.get("jobs", {}).values() if r.get("active")]
    jobs.sort(key=lambda r: (r.get("posted_at") or r.get("first_seen") or ""), reverse=True)
    public_jobs = [
        {k: r.get(k) for k in ("key", "title", "company", "family", "level", "places", "location", "url", "via",
                                "posted_at", "years", "first_seen", "baseline")}
        for r in jobs
    ]
    health = state.get("health", {})
    company_sites = sum(1 for sid in health if ":" in sid)
    payload = {
        "title": config.get("title", "Mumbai & remote business jobs"),
        "updated_at": state.get("updated_at") or now_iso(),
        "schedule": config.get("schedule_label", ""),
        "new_days": int(config.get("filters", {}).get("new_days", 3)),
        "families": config.get("families", []),
        "jobs": public_jobs,
        "sources": source_summary(health),
        "company_sites": company_sites,
        "search_links": search_links(config),
    }
    data = json.dumps(payload, ensure_ascii=False, separators=(",", ":")).replace("</", "<\\/")
    template = TEMPLATE_PATH.read_text()
    page = template.replace("__TITLE__", html.escape(payload["title"])).replace("__DATA__", data)
    SITE_DIR.mkdir(parents=True, exist_ok=True)
    (SITE_DIR / "index.html").write_text(page)
    (SITE_DIR / "jobs.json").write_text(json.dumps(payload, ensure_ascii=False, indent=1) + "\n")
    (SITE_DIR / ".nojekyll").write_text("")
    return SITE_DIR / "index.html"


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def load_config() -> dict[str, Any]:
    return json.loads(CONFIG_PATH.read_text())


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    run_p = sub.add_parser("run", help="collect jobs, update history, and rebuild the dashboard")
    run_p.add_argument("--only", help="comma-separated source ids for testing, such as workable,workday")
    run_p.add_argument("--no-save", action="store_true", help="do not write data/jobs.json")
    run_p.add_argument("--raw-out", help="development: also save fetched postings to this file")
    run_p.add_argument("--raw-in", help="development: reuse postings saved with --raw-out instead of fetching")
    run_p.add_argument("-v", "--verbose", action="store_true")
    sub.add_parser("build", help="rebuild the dashboard from data/jobs.json")
    args = parser.parse_args()
    config = load_config()
    if args.command == "build":
        print(build_site(config, load_state()))
        return 0
    tracker = Tracker(config, verbose=args.verbose)
    only = {s.strip() for s in args.only.split(",")} if args.only else None
    if args.raw_in:
        saved = json.loads(Path(args.raw_in).read_text())
        raw, tracker.health = saved["postings"], saved["health"]
    else:
        raw = tracker.collect(only)
    if args.raw_out:
        Path(args.raw_out).write_text(json.dumps({"postings": raw, "health": tracker.health}))
    jobs = tracker.screen(raw)
    run = tracker.merge(jobs)
    if not args.no_save:
        save_state(tracker.state)
    path = build_site(config, tracker.state)
    failed = run["sources_failed"]
    print(f"{run['active']} open roles ({run['new']} new) from {len(raw)} postings; "
          f"{run['sources_ok']} sources ok, {len(failed)} failed{': ' + ', '.join(failed) if failed else ''}. "
          f"Dashboard: {path}")
    # Fail the scheduled run only when almost everything broke, so one flaky board does not block publishing.
    return 1 if run["sources_ok"] == 0 else 0


if __name__ == "__main__":
    sys.exit(main())
