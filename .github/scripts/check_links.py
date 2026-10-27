#!/usr/bin/env python3
"""Check every link and image on a GitHub Pages site and raise one issue per dead URL.

Works in any repository that publishes a GitHub Pages site. The site folder is
detected automatically: docs/ when it holds the site (index page or _config.yml),
otherwise the repository root. Set SITE_ROOT (relative to the repo) to override.

What is checked
    Markdown and HTML source files in the site folder (Jekyll build output,
    dependency folders and .github are ignored): Markdown links and images,
    HTML href/src attributes. Liquid templates ({{ }} / {% %}) are skipped.

    Site-relative paths ("/assets/x.png") are checked against files in the site
    folder. External URLs are requested over the network.

What counts as dead
    Only definite failures: a missing local file, HTTP 404 or 410, or a host
    that does not resolve. Responses that are often temporary or bot-related
    (403, 429, 5xx, timeouts) are shown in the run summary as warnings but
    never become issues, so a busy server cannot flood the tracker.

Issues (one per link, never duplicated)
    Each dead URL gets one issue labelled "dead-link". The URL is stored in a
    hidden marker in the issue body, which is how duplicates are avoided:
      - an open issue already exists for the URL  -> left alone
      - a closed issue exists for the URL         -> reopened with a comment
      - no issue exists                           -> a new issue is opened
    Open issues whose URL now works, or is no longer used anywhere, are closed
    with a comment.

Usage
    python .github/scripts/check_links.py              # check and update issues
    python .github/scripts/check_links.py --dry-run    # check only, print results
    python .github/scripts/check_links.py --local-only --dry-run

Environment
    GITHUB_TOKEN and GITHUB_REPOSITORY (owner/repo) are needed unless --dry-run.
    GITHUB_STEP_SUMMARY, when set, receives a Markdown summary of the run.
    MAX_RUNTIME_MINUTES (default 40) stops checking after that long; unchecked
    URLs are left alone, and the starting point rotates daily so every URL is
    reached eventually.
"""

import argparse
import concurrent.futures
import datetime
import html
import json
import os
import re
import socket
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LABEL = "dead-link"
MARKER = "<!-- dead-link-url: {} -->"
MARKER_RE = re.compile(r"<!-- dead-link-url: (.+?) -->")
USER_AGENT = "pages-link-checker/1.0 (+https://github.com/" + os.environ.get("GITHUB_REPOSITORY", "dfbr") + ")"
TIMEOUT = 25
HOST_DELAY = 1.0          # seconds between requests to the same host
MAX_NEW_ISSUES = 25       # per run, so a mass outage cannot open hundreds of issues
MAX_FILE_BYTES = 2_000_000
SOURCE_SUFFIXES = {".md", ".markdown", ".html", ".htm"}
SKIP_DIRS = {".git", ".github", "node_modules", "vendor", "_site", ".jekyll-cache",
             ".sass-cache", "bundle", ".bundle", "venv", ".venv", "__pycache__"}
GENERATED_SUFFIXES = {".xml", ".atom", ".rss", ".json"}  # feeds/sitemaps built by Jekyll plugins

# Search and map query links always answer 200 whether or not the thing searched
# for exists, so checking them proves nothing. Extra regexes (one per line, "#"
# for comments) can go in .github/link-check-ignore.txt.
DEFAULT_IGNORE = [
    r"^https?://maps\.google\.[a-z.]+/",
    r"^https?://(www\.)?google\.[a-z.]+/(maps|search)",
    r"^https?://(www\.)?duckduckgo\.com/\?",
    r"^https?://(www\.)?bing\.com/(search|maps)",
    r"^https?://(localhost|127\.0\.0\.1)([:/]|$)",
]


def load_ignore() -> list:
    patterns = list(DEFAULT_IGNORE)
    extra = ROOT / ".github" / "link-check-ignore.txt"
    if extra.is_file():
        for line in extra.read_text(encoding="utf-8", errors="replace").splitlines():
            line = line.strip()
            if line and not line.startswith("#"):
                patterns.append(line)
    return [re.compile(p) for p in patterns]


IGNORE = load_ignore()

# A Markdown URL may itself contain balanced brackets, e.g. "File_(1879).jpg".
MD_URL = r"<?((?:[^()\s<>]|\([^()\s]*\))+)>?"
MD_IMAGE = re.compile(r"!\[[^\]]*\]\(\s*" + MD_URL + r"(?:\s+\"[^\"]*\")?\s*\)")
MD_LINK = re.compile(r"(?<!!)\[[^\]]*\]\(\s*" + MD_URL + r"(?:\s+\"[^\"]*\")?\s*\)")
HTML_SRC = re.compile(r"""<(?:img|source|script)\b[^>]*?\bsrc\s*=\s*["']([^"']+)["']""", re.I)
HTML_HREF = re.compile(r"""<(?:a|link)\b[^>]*?\bhref\s*=\s*["']([^"']+)["']""", re.I)


# --------------------------------------------------------------------------- site detection

def find_site_root() -> Path:
    override = os.environ.get("SITE_ROOT")
    if override:
        return (ROOT / override).resolve()
    docs = ROOT / "docs"
    if docs.is_dir() and any((docs / n).exists() for n in
                             ("_config.yml", "index.html", "index.md", "CNAME")):
        return docs
    return ROOT


SITE = find_site_root()


def read_baseurl() -> str:
    cfg = SITE / "_config.yml"
    if cfg.is_file():
        m = re.search(r"^baseurl:\s*[\"']?([^\"'#\s]*)", cfg.read_text(encoding="utf-8", errors="replace"), re.M)
        if m:
            return m.group(1).rstrip("/")
    return ""


BASEURL = read_baseurl()


# --------------------------------------------------------------------------- collection

def strip_code(text: str) -> str:
    text = re.sub(r"```.*?```", "", text, flags=re.S)
    return re.sub(r"`[^`\n]*`", "", text)


def source_files():
    for dirpath, dirnames, filenames in os.walk(SITE):
        dirnames[:] = sorted(d for d in dirnames if d not in SKIP_DIRS)
        for name in sorted(filenames):
            path = Path(dirpath) / name
            if path.suffix.lower() in SOURCE_SUFFIXES and path.stat().st_size <= MAX_FILE_BYTES:
                yield path


def collect() -> dict:
    """Return {url: {"kind": "image"|"link", "files": set()}}."""
    found = defaultdict(lambda: {"kind": "link", "files": set()})
    for path in source_files():
        raw = path.read_text(encoding="utf-8", errors="replace")
        rel = str(path.relative_to(ROOT))
        body = strip_code(raw) if path.suffix.lower() in (".md", ".markdown") else raw

        def add(url: str, kind: str) -> None:
            url = html.unescape(url.strip())
            if not url or "{{" in url or "{%" in url:
                return  # Liquid templates are resolved at build time
            if url.startswith(("#", "mailto:", "tel:", "javascript:", "data:", "sms:")):
                return
            if url.startswith("//"):
                url = "https:" + url
            if any(p.search(url) for p in IGNORE):
                return
            entry = found[url]
            if kind == "image":
                entry["kind"] = "image"
            entry["files"].add(rel)

        for regex, kind in ((MD_IMAGE, "image"), (HTML_SRC, "image"), (MD_LINK, "link"), (HTML_HREF, "link")):
            for m in regex.finditer(body):
                add(m.group(1), kind)
    return found


# --------------------------------------------------------------------------- checking

def check_local(url: str) -> tuple:
    path = urllib.parse.unquote(urllib.parse.urlsplit(url).path)
    if BASEURL and (path == BASEURL or path.startswith(BASEURL + "/")):
        path = path[len(BASEURL):] or "/"
    target = SITE / path.lstrip("/")
    if target.is_file():
        return "ok", "file exists"
    if target.is_dir() and any((target / n).is_file() for n in ("index.html", "index.md", "index.markdown")):
        return "ok", "directory index exists"
    suffix = Path(path).suffix.lower()
    if not suffix or suffix in GENERATED_SUFFIXES or suffix in SOURCE_SUFFIXES:
        # Page permalinks and plugin-built feeds have no matching source file.
        return "skip", "generated page"
    return "dead", f"file not found in {SITE.relative_to(ROOT) if SITE != ROOT else 'repository root'}"


_last_request = {}


def fetch(url: str, method: str) -> int:
    host = urllib.parse.urlsplit(url).netloc
    wait = HOST_DELAY - (time.monotonic() - _last_request.get(host, 0))
    if wait > 0:
        time.sleep(wait)
    _last_request[host] = time.monotonic()
    request = urllib.request.Request(url, method=method, headers={
        "User-Agent": USER_AGENT,
        "Accept": "*/*",
    })
    try:
        with urllib.request.urlopen(request, timeout=TIMEOUT) as response:
            if method == "GET":
                response.read(1024)
            return response.status
    except urllib.error.HTTPError as err:
        return err.code


def check_external(url: str) -> tuple:
    host = urllib.parse.urlsplit(url).hostname or ""
    try:
        socket.getaddrinfo(host, 443)
    except (socket.gaierror, UnicodeError):
        return "dead", f"host {host} does not resolve"

    last = "no response"
    for attempt in range(3):
        try:
            status = fetch(url, "HEAD")
            if status in (403, 405, 400, 501) or status >= 500:
                status = fetch(url, "GET")  # many servers mishandle HEAD
            if status < 400:
                return "ok", f"HTTP {status}"
            if status in (404, 410):
                return "dead", f"HTTP {status}"
            last = f"HTTP {status}"
            if status != 429 and status < 500:
                return "warn", last
        except (urllib.error.URLError, TimeoutError, ConnectionError, OSError, ValueError) as err:
            last = f"{type(err).__name__}: {getattr(err, 'reason', err)}"
        time.sleep(5 * (attempt + 1))
    return "warn", last


def check(urls: dict, local_only: bool, deadline: float) -> dict:
    results = {}
    by_host = defaultdict(list)

    # Rotate the starting point daily so a truncated run still covers everything over time.
    ordered = sorted(urls)
    if ordered:
        offset = (datetime.date.today().toordinal() * 97) % len(ordered)
        ordered = ordered[offset:] + ordered[:offset]

    for url in ordered:
        scheme = urllib.parse.urlsplit(url).scheme
        if scheme in ("http", "https"):
            if local_only:
                results[url] = ("skip", "external not checked")
            else:
                by_host[urllib.parse.urlsplit(url).netloc].append(url)
        elif url.startswith("/"):
            results[url] = check_local(url)
        else:
            results[url] = ("skip", "relative or unsupported URL")

    def run_host(host_urls):
        out = {}
        for u in host_urls:
            if time.monotonic() > deadline:
                out[u] = ("skip", "not checked (time limit reached)")
                continue
            out[u] = check_external(u)
        return out

    if by_host:
        with concurrent.futures.ThreadPoolExecutor(max_workers=16) as pool:
            for out in pool.map(run_host, by_host.values()):
                results.update(out)
    return results


# --------------------------------------------------------------------------- GitHub issues

class GitHub:
    def __init__(self, token: str, repo: str):
        self.token, self.repo = token, repo

    def call(self, method: str, path: str, data=None):
        url = path if path.startswith("https://") else f"https://api.github.com/repos/{self.repo}{path}"
        body = json.dumps(data).encode() if data is not None else None
        request = urllib.request.Request(url, data=body, method=method, headers={
            "Authorization": f"Bearer {self.token}",
            "Accept": "application/vnd.github+json",
            "X-GitHub-Api-Version": "2022-11-28",
            "User-Agent": USER_AGENT,
        })
        with urllib.request.urlopen(request, timeout=30) as response:
            text = response.read().decode()
            link = response.headers.get("Link", "")
        return (json.loads(text) if text else None), link

    def ensure_label(self) -> None:
        try:
            self.call("GET", f"/labels/{LABEL}")
        except urllib.error.HTTPError as err:
            if err.code != 404:
                raise
            self.call("POST", "/labels", {
                "name": LABEL, "color": "d73a4a",
                "description": "A link or image on the site no longer works",
            })

    def labelled_issues(self) -> list:
        issues, url = [], f"/issues?labels={LABEL}&state=all&per_page=100"
        while url:
            page, link = self.call("GET", url)
            issues += [i for i in page if "pull_request" not in i]
            nxt = re.search(r'<([^>]+)>;\s*rel="next"', link)
            url = nxt.group(1) if nxt else None
        return issues


def issue_body(url: str, info: dict, reason: str) -> str:
    noun = "image" if info["kind"] == "image" else "link"
    files = sorted(info["files"])
    listed = "\n".join(f"- `{f}`" for f in files[:20])
    if len(files) > 20:
        listed += f"\n- ...and {len(files) - 20} more files"
    return (
        f"The daily link check found a dead {noun}.\n\n"
        f"**URL:** {url}\n\n**Problem:** {reason}\n\n**Used in:**\n{listed}\n\n"
        f"Please check it and fix or replace the {noun} in the files above. This issue closes "
        f"itself once the {noun} works again or is no longer used.\n\n{MARKER.format(url)}"
    )


def update_issues(gh: GitHub, urls: dict, results: dict, today: str) -> list:
    log = []
    gh.ensure_label()
    by_url = {}
    for issue in gh.labelled_issues():
        m = MARKER_RE.search(issue.get("body") or "")
        if m:
            # Prefer the open issue if there are several for one URL.
            current = by_url.get(m.group(1))
            if current is None or (issue["state"] == "open" and current["state"] != "open"):
                by_url[m.group(1)] = issue

    created = 0
    for url, (status, reason) in results.items():
        if status != "dead":
            continue
        issue = by_url.get(url)
        if issue and issue["state"] == "open":
            log.append(f"already open: #{issue['number']} {url}")
        elif issue:
            gh.call("PATCH", f"/issues/{issue['number']}", {"state": "open"})
            gh.call("POST", f"/issues/{issue['number']}/comments",
                    {"body": f"Still dead on {today} ({reason}). Reopening."})
            log.append(f"reopened: #{issue['number']} {url}")
        elif created < MAX_NEW_ISSUES:
            noun = "image" if urls[url]["kind"] == "image" else "link"
            short = url if len(url) <= 90 else url[:87] + "..."
            new, _ = gh.call("POST", "/issues", {
                "title": f"Dead {noun}: {short}",
                "body": issue_body(url, urls[url], reason),
                "labels": [LABEL],
            })
            by_url[url] = new  # guards against a second issue for the same URL within this run
            created += 1
            log.append(f"opened: #{new['number']} {url}")
        else:
            log.append(f"not opened (limit of {MAX_NEW_ISSUES} new issues per run reached): {url}")

    for url, issue in by_url.items():
        if issue["state"] != "open":
            continue
        if url not in urls:
            note = f"No longer used anywhere on the site as of {today}. Closing."
        elif results.get(url, ("", ""))[0] == "ok":
            note = f"Working again on {today} ({results[url][1]}). Closing."
        else:
            continue  # still dead, warned, skipped or not checked: leave open
        gh.call("POST", f"/issues/{issue['number']}/comments", {"body": note})
        gh.call("PATCH", f"/issues/{issue['number']}", {"state": "closed", "state_reason": "completed"})
        log.append(f"closed: #{issue['number']} {url}")
    return log


# --------------------------------------------------------------------------- main

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--dry-run", action="store_true", help="Check only; do not touch issues")
    parser.add_argument("--local-only", action="store_true", help="Skip external URLs")
    args = parser.parse_args()

    minutes = float(os.environ.get("MAX_RUNTIME_MINUTES", "40"))
    deadline = time.monotonic() + minutes * 60

    print(f"Site folder: {SITE.relative_to(ROOT) if SITE != ROOT else '.'}  baseurl: '{BASEURL}'")
    urls = collect()
    results = check(urls, args.local_only, deadline)
    counts = defaultdict(int)
    for status, _ in results.values():
        counts[status] += 1
    print(f"Checked {len(results)} URLs: " + ", ".join(f"{k} {v}" for k, v in sorted(counts.items())))
    for url, (status, reason) in results.items():
        if status in ("dead", "warn"):
            print(f"  {status.upper():4} {reason:30} {url}")

    log = []
    if not args.dry_run:
        token, repo = os.environ.get("GITHUB_TOKEN"), os.environ.get("GITHUB_REPOSITORY")
        if not token or not repo:
            print("GITHUB_TOKEN and GITHUB_REPOSITORY are required unless --dry-run", file=sys.stderr)
            return 2
        log = update_issues(GitHub(token, repo), urls, results, time.strftime("%Y-%m-%d"))
        for line in log:
            print(line)

    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a", encoding="utf-8") as out:
            out.write(f"## Link check\n\nChecked {len(results)} URLs: "
                      + ", ".join(f"**{k}** {v}" for k, v in sorted(counts.items())) + "\n\n")
            rows = [(s, r, u) for u, (s, r) in results.items() if s in ("dead", "warn")]
            if rows:
                out.write("| Status | Detail | URL |\n|---|---|---|\n")
                out.writelines(f"| {s} | {r} | {u} |\n" for s, r, u in rows)
            if log:
                out.write("\n### Issues\n\n" + "".join(f"- {line}\n" for line in log))
    return 0


if __name__ == "__main__":
    sys.exit(main())
