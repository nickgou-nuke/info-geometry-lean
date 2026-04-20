#!/usr/bin/env python3
from __future__ import annotations

import argparse
import gzip
import io
import re
import tarfile
from pathlib import Path
from urllib.request import urlopen

ARXIV_ID_RE = re.compile(r"(?:arxiv\.org/(?:abs|pdf|html|e-print)/|^)([a-z\-]+/\d{7}|\d{4}\.\d{4,5})(?:v\d+)?", re.IGNORECASE)
TITLE_RE = re.compile(r"<title>(.*?)</title>", re.IGNORECASE | re.DOTALL)
TAG_RE = re.compile(r"<[^>]+>")
WS_RE = re.compile(r"\s+")
TEX_SECTION_RE = re.compile(r"\\(section|subsection|subsubsection|chapter)\*?\{([^}]*)\}")
TEX_COMMAND_RE = re.compile(r"\\[A-Za-z@]+(?:\[[^\]]*\])?(?:\{[^{}]*\})?")
TEX_COMMENT_RE = re.compile(r"(?m)^\s*%.*$")


def extract_arxiv_id(raw: str) -> str | None:
    raw = raw.strip()
    match = ARXIV_ID_RE.search(raw)
    if match:
        return match.group(1)
    return None


def fetch_bytes(url: str) -> bytes:
    with urlopen(url, timeout=40) as response:
        return response.read()


def fetch_text(url: str) -> str:
    return fetch_bytes(url).decode("utf-8", errors="replace")


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


def tex_to_text(tex: str, *, title: str) -> str:
    tex = TEX_COMMENT_RE.sub("", tex)
    tex = tex.replace("\r\n", "\n")
    tex = tex.replace("\\[", "\n$$\n").replace("\\]", "\n$$\n")
    tex = tex.replace("\\(", "$ ").replace("\\)", " $")

    def section_repl(match: re.Match[str]) -> str:
        level = match.group(1)
        header = match.group(2).strip()
        prefix = {
            "chapter": "#",
            "section": "##",
            "subsection": "###",
            "subsubsection": "####",
        }.get(level, "##")
        return f"\n\n{prefix} {header}\n\n"

    tex = TEX_SECTION_RE.sub(section_repl, tex)
    tex = re.sub(r"\\begin\{abstract\}", "\n\n## Abstract\n\n", tex)
    tex = re.sub(r"\\end\{abstract\}", "\n\n", tex)
    tex = re.sub(r"\\begin\{(theorem|lemma|proposition|corollary|definition|remark|proof)\}", lambda m: f"\n\n## {m.group(1).title()}\n\n", tex)
    tex = re.sub(r"\\end\{(theorem|lemma|proposition|corollary|definition|remark|proof)\}", "\n\n", tex)
    tex = TEX_COMMAND_RE.sub(" ", tex)
    tex = re.sub(r"\$\$?", " $ ", tex)
    tex = re.sub(r"\{|", " ", tex)
    tex = re.sub(r"\}", " ", tex)
    tex = re.sub(r"[ \t]+", " ", tex)
    tex = re.sub(r"\n{3,}", "\n\n", tex)
    return f"# {title}\n\n{tex.strip()}\n"


def try_extract_tex(source_bytes: bytes) -> tuple[str | None, str | None]:
    candidates: list[tuple[str, str]] = []
    try:
        with tarfile.open(fileobj=io.BytesIO(source_bytes), mode="r:*") as tar:
            for member in tar.getmembers():
                if not member.isfile() or not member.name.endswith(".tex"):
                    continue
                handle = tar.extractfile(member)
                if not handle:
                    continue
                text = handle.read().decode("utf-8", errors="replace")
                candidates.append((member.name, text))
    except tarfile.ReadError:
        try:
            text = gzip.decompress(source_bytes).decode("utf-8", errors="replace")
            return "main.tex", text
        except Exception:
            try:
                text = source_bytes.decode("utf-8", errors="replace")
                if "\\begin{document}" in text or "\\section{" in text:
                    return "main.tex", text
            except Exception:
                return None, None
            return None, None

    if not candidates:
        return None, None
    best_name, best_text = max(candidates, key=lambda item: ("\\begin{document}" in item[1], len(item[1])))
    return best_name, best_text


def download_arxiv_entry(arxiv_id: str, out_dir: Path, *, prefer_source: bool = True) -> tuple[Path, str]:
    out_dir.mkdir(parents=True, exist_ok=True)
    safe_id = arxiv_id.replace('/', '_')

    if prefer_source:
        try:
            source_bytes = fetch_bytes(f"https://arxiv.org/e-print/{arxiv_id}")
            tex_name, tex_payload = try_extract_tex(source_bytes)
            if tex_payload:
                title = tex_name or f"arXiv {arxiv_id}"
                text = tex_to_text(tex_payload, title=title)
                path = out_dir / f"{safe_id}.tex.md"
                path.write_text(text, encoding="utf-8")
                (out_dir / f"{safe_id}.source.tar").write_bytes(source_bytes)
                return path, "tex"
        except Exception:
            pass

    url = f"https://arxiv.org/html/{arxiv_id}"
    try:
        payload = fetch_text(url)
        text = html_to_text(payload)
        path = out_dir / f"{safe_id}.html.md"
        path.write_text(text, encoding="utf-8")
        return path, "html"
    except Exception:
        url = f"https://arxiv.org/abs/{arxiv_id}"
        payload = fetch_text(url)
        text = html_to_text(payload)
        path = out_dir / f"{safe_id}.abs.md"
        path.write_text(text, encoding="utf-8")
        return path, "abs"


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description="Download a small arXiv corpus into source-aware markdown cache files for Alexandria ingestion")
    ap.add_argument("--id", action="append", default=[], help="arXiv id or URL, repeatable")
    ap.add_argument("--ids-file", help="text file with one arXiv id or URL per line")
    ap.add_argument("--output-dir", required=True)
    ap.add_argument("--no-source", action="store_true", help="disable source/LaTeX preference")
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
        path, mode = download_arxiv_entry(arxiv_id, out_dir, prefer_source=not args.no_source)
        manifest_lines.append(f"{arxiv_id}\t{mode}\t{path.name}")
        print(f"fetched {arxiv_id} [{mode}] -> {path}")

    (out_dir / "MANIFEST.tsv").write_text("\n".join(manifest_lines) + ("\n" if manifest_lines else ""), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
