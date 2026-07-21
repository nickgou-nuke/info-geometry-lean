#!/usr/bin/env python3
"""Generate declaration raw-name/line-anchor mapping + 10-branch correspondence assets.

Outputs
-------
- `docs/automath_declaration_raw_name_map.json`
- `docs/automath_10_branch_prefix_correspondence.json`
"""

from __future__ import annotations

import json
import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
LEAN_ROOT = REPO_ROOT / "lean"


LEAN_DECL_RE = re.compile(
    r"^\s*(?:noncomputable\s+|private\s+)*"
    r"(?P<kind>theorem|lemma|def|structure|abbrev)\s+"
    r"(?P<name>[A-Za-z0-9_\.]+)"
)
DOC_TAG_RE = re.compile(r"thm:([^)\s]+)")


def find_lean_files() -> list[Path]:
    return sorted(LEAN_ROOT.rglob("*.lean"))


def extract_declarations(text: str, file: Path) -> list[dict[str, object]]:
    items: list[dict[str, object]] = []
    lines = text.splitlines()
    doc_buffer: list[str] = []
    decl_kind = None
    decl_name = None
    decl_line = None

    def flush_decl() -> None:
        nonlocal decl_kind, decl_name, decl_line
        if decl_kind and decl_name and decl_line:
            label = None
            doc_text = "\n".join(doc_buffer)
            tm = DOC_TAG_RE.search(doc_text)
            if tm:
                label = f"thm:{tm.group(1)}"
            if "." not in decl_name:
                items.append(
                    {
                        "file": str(file.relative_to(REPO_ROOT)),
                        "line": decl_line,
                        "kind": decl_kind,
                        "declaration_name": f"{file.stem}.{decl_name}",
                        "raw_name": decl_name,
                        "paper_label": label,
                        "doc_lines": list(doc_buffer),
                    }
                )
        doc_buffer.clear()
        decl_kind = None
        decl_name = None
        decl_line = None

    for i, line in enumerate(lines, start=1):
        stripped = line.lstrip()
        if stripped.startswith("/--"):
            flush_decl()
            doc_buffer.append(stripped)
            continue

        # A non-doc, non-empty, non-whitespace line terminates a run.
        if doc_buffer and stripped:
            m = LEAN_DECL_RE.search(stripped)
            if m:
                decl_kind = m.group("kind")
                decl_name = m.group("name")
                decl_line = i
                continue
            flush_decl()
            continue

    flush_decl()
    return items


def extract_10_branch_self_affine(text: str, file: Path) -> dict[str, object] | None:
    if "XiZgAddressBinarySelfAffine" not in str(file.relative_to(REPO_ROOT)):
        return None
    forced = bool(re.search(r"forced [`']10[`']", text))
    prefix10 = bool(re.search(r"prefix.*`10`|forced leading `10`", text))
    prefix_names = re.findall(
        r"^\s*(?:noncomputable\s+|private\s+)?(?:(?:def)\s+)(xi_zg_address_binary_self_affine_prefix_[A-Za-z0-9_]+)",
        text,
        flags=re.M,
    )
    decl_names = [
        m.group(1)
        for m in re.finditer(
            r"^\s*(?:noncomputable\s+|private\s+)?(?:(?:def|lemma|theorem)\s+)(xi_zg_address_binary_self_affine_[A-Za-z0-9_]+)",
            text,
            flags=re.M,
        )
    ]
    return {
        "source_file": str(file.relative_to(REPO_ROOT)),
        "topic": "forced 10 branch / binary self-affine ZG address symbolic branch correspondence",
        "prefix_names": prefix_names,
        "declaration_names": decl_names,
        "paper_label": "thm:xi-zg-address-binary-self-affine",
        "evidence_checks": {
            "forced_10_mentioned": forced,
            "prefix_10_present": prefix10,
            "injective_found": "Function.Injective" in text
            and "xi_zg_address_binary_self_affine_statement" in text,
            "disjoint_found": "Disjoint" in text,
            "prefix_map_decomp_found": "prefix_one_zero '' K" in text
            and "prefix_zero '' K" in text,
        },
    }


def main() -> None:
    docs_dir = REPO_ROOT / "docs"
    docs_dir.mkdir(exist_ok=True)

    declarations: list[dict[str, object]] = []
    correspondence_items: list[dict[str, object]] = []

    for file in find_lean_files():
        try:
            text = file.read_text(errors="ignore")
        except FileNotFoundError:
            continue
        declarations.extend(extract_declarations(text, file))
        branch_item = extract_10_branch_self_affine(text, file)
        if branch_item:
            correspondence_items.append(branch_item)

    seen: set[str] = set()
    unique_correspondence = []
    for item in correspondence_items:
        key = item["source_file"]
        if key not in seen:
            seen.add(key)
            unique_correspondence.append(item)

    raw_map_path = docs_dir / "automath_declaration_raw_name_map.json"
    correspondence_path = docs_dir / "automath_10_branch_prefix_correspondence.json"
    raw_map_path.write_text(json.dumps(declarations, indent=2))
    correspondence_path.write_text(json.dumps(unique_correspondence, indent=2))
    print(f"wrote {raw_map_path}")
    print(f"wrote {correspondence_path}")


if __name__ == "__main__":
    main()
