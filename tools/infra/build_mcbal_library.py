#!/usr/bin/env python3
"""Build a structured local library from downloaded mcbal blog HTML files."""

from __future__ import annotations

import argparse
import datetime as dt
import html
import json
import re
from pathlib import Path
from typing import Any


def strip_tags_keep_breaks(raw_html: str) -> str:
    text = re.sub(r"(?is)<(script|style).*?>.*?</\1>", " ", raw_html)
    text = re.sub(r"(?is)<\s*br\s*/?\s*>", "\n", text)
    text = re.sub(r"(?is)</\s*p\s*>", "\n\n", text)
    text = re.sub(r"(?is)</\s*h[1-6]\s*>", "\n\n", text)
    text = re.sub(r"(?is)<[^>]+>", " ", text)
    text = html.unescape(text)
    text = re.sub(r"[ \t]+", " ", text)
    text = re.sub(r"\n{3,}", "\n\n", text)
    return text.strip()


def extract_title(raw_html: str, fallback: str) -> str:
    m = re.search(r"(?is)<title>(.*?)</title>", raw_html)
    if m:
        t = re.sub(r"\s+", " ", html.unescape(m.group(1))).strip()
        if t:
            return t
    m = re.search(r"(?is)<h1[^>]*>(.*?)</h1>", raw_html)
    if m:
        t = re.sub(r"(?is)<[^>]+>", " ", m.group(1))
        t = re.sub(r"\s+", " ", html.unescape(t)).strip()
        if t:
            return t
    return fallback


def extract_updated_and_read_time(raw_html: str) -> tuple[str | None, str | None]:
    m = re.search(r"Last updated on\s+([A-Za-z]{3}\s+\d{1,2},\s+\d{4})\s+(\d+\s+min read)", raw_html)
    if m:
        return m.group(1), m.group(2)
    plain = strip_tags_keep_breaks(raw_html)
    m2 = re.search(r"Last updated on\s+([A-Za-z]{3}\s+\d{1,2},\s+\d{4})\s+(\d+\s+min read)", plain)
    if m2:
        return m2.group(1), m2.group(2)
    return None, None


def parse_human_date(s: str | None) -> str | None:
    if not s:
        return None
    try:
        return dt.datetime.strptime(s, "%b %d, %Y").date().isoformat()
    except ValueError:
        return None


def extract_headings(raw_html: str) -> list[str]:
    out: list[str] = []
    for m in re.finditer(r"(?is)<h([2-4])[^>]*>(.*?)</h\1>", raw_html):
        txt = re.sub(r"(?is)<[^>]+>", " ", m.group(2))
        txt = re.sub(r"\s+", " ", html.unescape(txt)).strip()
        if txt:
            out.append(txt)
    return out


def extract_links(raw_html: str) -> list[str]:
    links: list[str] = []
    for m in re.finditer(r"""href=["']([^"']+)["']""", raw_html):
        href = m.group(1).strip()
        if not href:
            continue
        if href.startswith("#"):
            continue
        if href.startswith("/"):
            href = f"https://mcbal.github.io{href}"
        if href.startswith("http://") or href.startswith("https://"):
            links.append(href)
    dedup: list[str] = []
    seen: set[str] = set()
    for u in links:
        if u in seen:
            continue
        seen.add(u)
        dedup.append(u)
    return dedup


def keyword_profile(text: str) -> dict[str, int]:
    terms = [
        "transformer",
        "attention",
        "energy",
        "free energy",
        "spin",
        "hopfield",
        "mean-field",
        "entropy",
        "softmax",
        "logsumexp",
        "mixture",
        "phase transition",
        "non-equilibrium",
        "bistochastic",
        "bogoliubov",
        "majorana",
        "kramers",
        "clifford",
        "simplex",
    ]
    low = text.lower()
    profile: dict[str, int] = {}
    for t in terms:
        profile[t] = low.count(t)
    return profile


def top_nonzero(profile: dict[str, int], k: int = 12) -> list[tuple[str, int]]:
    items = [(term, n) for term, n in profile.items() if n > 0]
    items.sort(key=lambda x: (-x[1], x[0]))
    return items[:k]


def write_post_markdown(
    out_path: Path,
    *,
    title: str,
    url: str,
    source_file: str,
    updated_human: str | None,
    updated_iso: str | None,
    read_time: str | None,
    headings: list[str],
    links: list[str],
    profile: dict[str, int],
    clean_text: str,
) -> None:
    top_terms = top_nonzero(profile, k=12)
    excerpt = "\n".join(clean_text.splitlines()[:120]).strip()
    lines: list[str] = []
    lines.append(f"# {title}")
    lines.append("")
    lines.append("## Metadata")
    lines.append(f"- URL: {url}")
    lines.append(f"- Source file: `{source_file}`")
    lines.append(f"- Updated (human): {updated_human or 'unknown'}")
    lines.append(f"- Updated (ISO): {updated_iso or 'unknown'}")
    lines.append(f"- Read time: {read_time or 'unknown'}")
    lines.append("")
    lines.append("## Structural Headings")
    if headings:
        for h in headings[:80]:
            lines.append(f"- {h}")
    else:
        lines.append("- (none extracted)")
    lines.append("")
    lines.append("## Keyword Profile (Top Non-Zero)")
    if top_terms:
        for term, count in top_terms:
            lines.append(f"- `{term}`: {count}")
    else:
        lines.append("- (none)")
    lines.append("")
    lines.append("## External Links")
    if links:
        for u in links[:120]:
            lines.append(f"- {u}")
    else:
        lines.append("- (none)")
    lines.append("")
    lines.append("## Clean Text Excerpt")
    lines.append("")
    lines.append("```text")
    lines.append(excerpt)
    lines.append("```")
    lines.append("")
    out_path.write_text("\n".join(lines), encoding="utf-8")


def run(source_dir: Path, out_dir: Path) -> dict[str, Any]:
    out_posts = out_dir / "posts"
    out_posts.mkdir(parents=True, exist_ok=True)

    rows: list[dict[str, Any]] = []
    for html_path in sorted(source_dir.glob("*.html")):
        if html_path.name == "index.xml.html":
            continue
        raw = html_path.read_text(encoding="utf-8", errors="ignore")
        slug = html_path.stem
        post_url = f"https://mcbal.github.io/post/{slug}/"
        title = extract_title(raw, slug.replace("-", " "))
        updated_human, read_time = extract_updated_and_read_time(raw)
        updated_iso = parse_human_date(updated_human)
        headings = extract_headings(raw)
        links = extract_links(raw)
        clean = strip_tags_keep_breaks(raw)
        profile = keyword_profile(clean)

        md_path = out_posts / f"{slug}.md"
        write_post_markdown(
            md_path,
            title=title,
            url=post_url,
            source_file=str(html_path),
            updated_human=updated_human,
            updated_iso=updated_iso,
            read_time=read_time,
            headings=headings,
            links=links,
            profile=profile,
            clean_text=clean,
        )

        rows.append(
            {
                "slug": slug,
                "title": title,
                "url": post_url,
                "source_html": str(html_path),
                "markdown": str(md_path),
                "updated_human": updated_human,
                "updated_iso": updated_iso,
                "read_time": read_time,
                "heading_count": len(headings),
                "link_count": len(links),
                "keywords": profile,
            }
        )

    rows.sort(key=lambda r: (r.get("updated_iso") or "", r["slug"]), reverse=True)
    metadata = {"generated_at_utc": dt.datetime.utcnow().isoformat() + "Z", "posts": rows}
    (out_dir / "metadata.json").write_text(json.dumps(metadata, indent=2), encoding="utf-8")

    readme_lines: list[str] = []
    readme_lines.append("# mcbal Blog Local Library")
    readme_lines.append("")
    readme_lines.append("Generated from downloaded HTML snapshots in `external_refs/mcbal_blog/`.")
    readme_lines.append("")
    readme_lines.append("## Posts")
    for row in rows:
        rel_md = Path("posts") / (Path(row["markdown"]).stem + ".md")
        readme_lines.append(
            f"- [{row['title']}]({rel_md.as_posix()})"
            f" — {row.get('updated_iso') or 'unknown date'}"
            f" ({row.get('read_time') or 'unknown read'})"
        )
    readme_lines.append("")
    readme_lines.append("## Files")
    readme_lines.append("- `metadata.json`: machine-readable catalog and keyword profile")
    readme_lines.append("- `posts/*.md`: cleaned per-post notes with headings, links, excerpt")
    (out_dir / "README.md").write_text("\n".join(readme_lines) + "\n", encoding="utf-8")
    return metadata


def main() -> int:
    parser = argparse.ArgumentParser(description="Build local mcbal blog library")
    parser.add_argument(
        "--source-dir",
        default="external_refs/mcbal_blog",
        help="Directory containing downloaded mcbal HTML snapshots",
    )
    parser.add_argument(
        "--out-dir",
        default="external_refs/mcbal_blog/library",
        help="Output directory for local library",
    )
    args = parser.parse_args()

    source_dir = Path(args.source_dir)
    out_dir = Path(args.out_dir)
    if not source_dir.exists():
        raise SystemExit(f"missing source directory: {source_dir}")
    metadata = run(source_dir, out_dir)
    print(
        json.dumps(
            {
                "out_dir": str(out_dir),
                "post_count": len(metadata["posts"]),
                "metadata": str((out_dir / "metadata.json")),
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
