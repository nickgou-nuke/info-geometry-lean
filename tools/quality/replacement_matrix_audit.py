#!/usr/bin/env python3
"""Produce conservative evidence for quarantine replacement claims.

The quarantine manifest is authoritative for the *claimed* disposition.  This
tool only adds independently checkable signals; it never upgrades a claim to
"equivalent" based on a filename or topic match.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
MANIFEST = ROOT / "tools/quality/repo_lean_quarantine_manifest.json"
DEFAULT_JSON = ROOT / "reports/quality/replacement-matrix.json"
DEFAULT_MD = ROOT / "reports/quality/replacement-matrix.md"

DECL = re.compile(
    r"^\s*(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:def|theorem|lemma|abbrev|structure|class|inductive|opaque)\s+([A-Za-z_][A-Za-z0-9_'.]*)"
)
IMPORT = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)")


def lean_files() -> list[Path]:
    return sorted(path for path in (ROOT / "lean").glob("**/*.lean") if path.is_file())


def module_name(path: Path) -> str:
    rel = path.relative_to(ROOT / "lean").with_suffix("")
    return ".".join(rel.parts)


def declaration_headers(path: Path) -> dict[str, str]:
    if not path.is_file():
        return {}
    out: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
        match = DECL.match(line)
        if match:
            out[match.group(1)] = " ".join(line.strip().split())
    return out


def declarations(path: Path) -> set[str]:
    return set(declaration_headers(path))


def source_clean(path: Path) -> bool:
    if not path.is_file():
        return False
    text = path.read_text(encoding="utf-8", errors="ignore")
    masked = re.sub(r"/-.*?-/|--[^\n]*|\"(?:[^\"\\]|\\.)*\"", " ", text, flags=re.S)
    return not re.search(r"(?<![A-Za-z0-9_.])(sorry|admit|axiom)(?![A-Za-z0-9_.])", masked)


def importers(files: list[Path]) -> dict[str, list[str]]:
    result: dict[str, list[str]] = defaultdict(list)
    for path in files:
        for line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
            match = IMPORT.match(line)
            if match:
                result[match.group(1)].append(module_name(path))
    return result


def quarantine_paths() -> list[str]:
    result = subprocess.run(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "--", "*.lean.disabled"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    return sorted(raw for raw in result.stdout.splitlines() if (ROOT / raw).is_file())


def debt_count(path: Path) -> int:
    text = path.read_text(encoding="utf-8", errors="ignore") if path.is_file() else ""
    masked = re.sub(r"/-.*?-/|--[^\n]*|\"(?:[^\"\\]|\\.)*\"", " ", text, flags=re.S)
    return len(re.findall(r"(?<![A-Za-z0-9_.])(sorry|admit|axiom)(?![A-Za-z0-9_.])", masked))


def path_evidence(raw: str, imported: dict[str, list[str]]) -> dict[str, object]:
    path = ROOT / raw
    item: dict[str, object] = {
        "path": raw,
        "exists": path.is_file(),
        "source_clean": source_clean(path),
        "declarations": sorted(declarations(path)),
        "declaration_headers": declaration_headers(path),
    }
    if path.is_relative_to(ROOT / "lean"):
        mod = module_name(path)
        item["module"] = mod
        item["imported_by_count"] = len(imported.get(mod, []))
        item["imported_by"] = sorted(imported.get(mod, []))[:20]
        # Presence of the compiled artifact is evidence of a successful prior
        # build, not an independent equivalence proof.
        olean = ROOT / ".lake/build/lib/lean" / Path(*mod.split(".")).with_suffix(".olean")
        item["compiled_artifact_present"] = olean.is_file()
    else:
        item["module"] = None
        item["imported_by_count"] = 0
        item["imported_by"] = []
        item["compiled_artifact_present"] = False
    return item


def classify(record: dict[str, object], owners: list[dict[str, object]]) -> str:
    declared = str(record["replacement_status"])
    if not owners:
        return "none"
    if declared == "topic_owner_exists":
        return "candidate_owner_not_equivalence_verified"
    if declared in {"safe_owner_exists_not_equivalent_to_snapshot", "reduced_topic_owners_exist_not_equivalent_to_sandbox", "other_test4_variants_exist_not_equivalent_verified"}:
        return "explicitly_weaker_or_non_equivalent"
    if declared == "test_driver_only_not_semantic_replacement":
        return "nonsemantic_driver"
    if declared == "topic_owners_exist_split_across_modules":
        return "split_across_owners"
    return "manifest_classified"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--markdown", default=str(DEFAULT_MD))
    args = parser.parse_args()
    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    files = lean_files()
    imp = importers(files)
    rows = []
    records = {record["file"]: record for record in data["records"]}
    for raw in quarantine_paths():
        if raw not in records:
            records[raw] = {
                "file": raw,
                "finding_count": debt_count(ROOT / raw),
                "category": "unmanifested_quarantine_artifact",
                "replacement_paths": [],
                "replacement_status": "unmanifested_quarantine_debt",
            }
    for record in records.values():
        owners = [path_evidence(raw, imp) for raw in record.get("replacement_paths", [])]
        old_path = ROOT / record["file"]
        old_headers = declaration_headers(old_path)
        old_decls = sorted(old_headers)
        owner_headers: dict[str, str] = {}
        for owner in owners:
            owner_headers.update(owner["declaration_headers"])
        owner_decl_union = set(owner_headers)
        overlap = sorted(set(old_decls) & owner_decl_union)
        signature_overlap = sorted(name for name in overlap if old_headers[name] == owner_headers[name])
        row = {
            "quarantine_file": record["file"],
            "manifest_status": record["replacement_status"],
            "manifest_category": record["category"],
            "replacement_class": classify(record, owners),
            "old_file_exists": old_path.is_file(),
            "old_declaration_count": len(old_decls),
            "replacement_paths": owners,
            "declaration_name_overlap": overlap,
            "declaration_overlap_count": len(overlap),
            "signature_overlap": signature_overlap,
            "signature_overlap_count": len(signature_overlap),
            "equivalence_verified": False,
            "retirement_authorized": False,
        }
        rows.append(row)
    counts = Counter(row["replacement_class"] for row in rows)
    report = {
        "schema": 1,
        "authority": "manifest disposition plus independent filesystem/import/declaration evidence",
        "equivalence_policy": "No exact replacement is inferred automatically; Lean type/dependency review remains required.",
        "active_lean_files_scanned": len(files),
        "quarantine_records": len(rows),
        "manifest_records": len(data["records"]),
        "discovered_quarantine_files": len(quarantine_paths()),
        "class_counts": dict(sorted(counts.items())),
        "records": rows,
    }
    json_path, md_path = Path(args.json), Path(args.markdown)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    md_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    lines = [
        "# Quarantine Replacement Matrix",
        "",
        "This is a conservative evidence report. Manifest statuses are preserved; filename/topic matches are not promoted to equivalence.",
        "",
        f"- Active Lean files scanned: {len(files)}",
        f"- Quarantine records: {len(rows)}",
        f"- Equivalence claims emitted: 0",
        "",
        "| Quarantine artifact | Manifest status | Evidence class | Existing owners | Clean/compiled | Name overlap | Header overlap |",
        "|---|---|---|---:|---|---:|---:|",
    ]
    for row in rows:
        owners = row["replacement_paths"]
        good = sum(bool(x["exists"] and x["source_clean"] and x["compiled_artifact_present"]) for x in owners)
        lines.append(f"| `{row['quarantine_file']}` | `{row['manifest_status']}` | `{row['replacement_class']}` | {sum(bool(x['exists']) for x in owners)} | {good}/{len(owners)} | {row['declaration_overlap_count']} | {row['signature_overlap_count']} |")
    lines += ["", "## Policy", "", "Only an explicit declaration/type/dependency comparison can establish an exact replacement. No row in this generated report authorizes deletion or retirement."]
    md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(json.dumps({"json": str(json_path), "markdown": str(md_path), "class_counts": dict(counts)}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
