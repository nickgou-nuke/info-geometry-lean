#!/usr/bin/env python3
from __future__ import annotations

import argparse
import re
from pathlib import Path
from urllib.parse import urlparse
from urllib.request import urlopen

ARXIV_ID_RE = re.compile(r"(?:arxiv\.org/(?:abs|pdf|html)/|^)([a-z\-]+/\d{7}|\d{4}\.\d{4,5})(?:v\d+)?", re.IGNORECASE)
TITLE_RE = re.compile(r"<title>(.*?)</title>", re.IGNORECASE | re.DOTALL)
TAG_RE = re.compile(r"<[^>]+>")
WS_RE = re.compile(r"\s+")


def extract_arxiv_id(raw: str) -> str | None:
    raw = raw.strip()
    match = ARXIV_ID_RE.search(raw)
    if match:
        return match.group(1)
    return None


def fetch_text(url: str) -> str:
    with urlopen(url, timeout=30) as response:
        data = response.read()
    return data.decode("utf-8", errors="replace")


def html_to_text(html: str) -> str:
    html = re.sub(r"<script.*?</script>", " ", html, flags=re.IGNORECASE | re.DOTALL)
    html = re.sub(r"<style.*?</style>", " ", html, flags=re.IGNORECASE | re.DOTALL)
    title_match = TITLE_RE.search(html)
    title = WS_RE.sub(" ", TAG_RE.sub(" ", title_match.group(1))).strip() if title_match else "arXiv paper"
    html = re.sub(r"</(p|div|section|article|li|tr|h1|h2|h3|h4|h5|h6|blockquote)>", "\n\n", html, flags=re.IGNORECASE)
    html = re.sub(r"<(br|hr)\s*/?>", "\n", html, flags=re.IGNORECASE)
    body = TAG_RE.sub(" ", html)
    body = body.replace("&nbsp;", " ").replace("&amp;", "&")
    body = re.sub(r"\n[ \t]+", "\n", body)
    body = re.sub(r"[ \t]+\n", "\n", body)
    body = re.sub(r"\n{3,}", "\n\n", body)
    body = re.sub(r"[ \t]{2,}", " ", body)
    return f"# {title}\n\n{body.strip()}\n"


def download_arxiv_entry(arxiv_id: str, out_dir: Path) -> Path:
    out_dir.mkdir(parents=True, exist_ok=True)
    url = f"https://arxiv.org/html/{arxiv_id}"
    try:
        payload = fetch_text(url)
        text = html_to_text(payload)
        suffix = "html"
    except Exception:
        url = f"https://arxiv.org/abs/{arxiv_id}"
        payload = fetch_text(url)
        text = html_to_text(payload)
        suffix = "abs"
    path = out_dir / f"{arxiv_id.replace('/', '_')}.{suffix}.md"
    path.write_text(text, encoding="utf-8")
    return path


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description="Download a small arXiv corpus into markdown-like cache files for Alexandria ingestion")
    ap.add_argument("--id", action="append", default=[], help="arXiv id or URL, repeatable")
    ap.add_argument("--ids-file", help="text file with one arXiv id or URL per line")
    ap.add_argument("--output-dir", required=True)
    return ap.parse_args()


def main() -> int:
    args = parse_args()
    raw_items = list(args.id)
    if args.ids_file:
        raw_items.extend(Path(args.ids_file).read_text(encoding="utf-8").splitlines())

    ids: list[str] = []
    seen: set[str] = set()
    for raw in raw_items:
        raw = raw.strip()
        if not raw:
            continue
        arxiv_id = extract_arxiv_id(raw)
        if not arxiv_id or arxiv_id in seen:
            continue
        seen.add(arxiv_id)
        ids.append(arxiv_id)

    out_dir = Path(args.output_dir)
    manifest_lines: list[str] = []
    for arxiv_id in ids:
        path = download_arxiv_entry(arxiv_id, out_dir)
        manifest_lines.append(f"{arxiv_id}\t{path.name}")
        print(f"fetched {arxiv_id} -> {path}")

    (out_dir / "MANIFEST.tsv").write_text("\n".join(manifest_lines) + ("\n" if manifest_lines else ""), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
