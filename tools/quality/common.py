from __future__ import annotations

import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import lean_root, repo_root
else:
    from tools.pathing import lean_root, repo_root


ROOT = repo_root()
QUALITY_SCRIPTS_DIR = ROOT / "scripts" / "quality"
QUARANTINE_MANIFEST_PATH = QUALITY_SCRIPTS_DIR / "quarantine_manifest.txt"
APPROVED_AXIOMS_PATH = QUALITY_SCRIPTS_DIR / "approved_axioms.txt"
AUDIT_AXIOMS_REPORT_PATH = QUALITY_SCRIPTS_DIR / "audit_axioms_report.lean"


def resolve_target_dir(argv: list[str]) -> str:
    return argv[1] if len(argv) > 1 else str(lean_root())


def iter_lean_files(directory_to_scan: str):
    root = Path(directory_to_scan)
    for path in sorted(root.rglob("*.lean")):
        if path.is_file():
            yield path


def print_grouped_violations(
    violations: list[tuple[str, int, str]],
    *,
    item_formatter,
) -> None:
    grouped: dict[str, list[tuple[int, str]]] = {}
    for f, l, msg in violations:
        grouped.setdefault(f, []).append((l, msg))
    for f in sorted(grouped.keys()):
        print(f"File: {f}")
        for l, msg in sorted(grouped[f]):
            print(item_formatter(l, msg))
        print()
