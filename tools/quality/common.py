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
    skip_dirs = {".elan", ".lake", ".git", ".archon", ".gemini", "lake-packages", ".lake-cache"}
    for path in sorted(root.rglob("*.lean")):
        if any(part in skip_dirs for part in path.parts):
            continue
        if path.is_file():
            yield path


def line_of(text: str, offset: int) -> int:
    """Returns 1-based line number for a character offset in text."""
    return text.count("\n", 0, offset) + 1


line_for_offset = line_of


def rel(path: Path | str, root: Path = ROOT) -> str:
    """Returns posix-style relative path from repo root."""
    p = Path(path).resolve()
    try:
        return p.relative_to(root).as_posix()
    except ValueError:
        return p.as_posix()


def module_name_of_lean(path: Path | str, root: Path = ROOT) -> str:
    """Converts a Lean file path into its dotted module name."""
    p = Path(path).resolve()
    try:
        rp = p.relative_to(root / "lean").with_suffix("").as_posix()
        return rp.replace("/", ".")
    except ValueError:
        return p.stem


def module_to_path(module: str, root: Path = ROOT) -> Path | None:
    """Resolves a dotted Lean module name to its filesystem Path."""
    lean_path = root / "lean" / Path(module.replace(".", "/")).with_suffix(".lean")
    if lean_path.exists():
        return lean_path
    direct_path = root / Path(module.replace(".", "/")).with_suffix(".lean")
    if direct_path.exists():
        return direct_path
    return None


def path_to_module(path: Path | str, root: Path = ROOT) -> str | None:
    """Resolves a Lean filesystem path to its dotted module name."""
    path_obj = Path(path).resolve()
    if path_obj.suffix != ".lean":
        return None
    try:
        rel = path_obj.relative_to(root / "lean").with_suffix("").as_posix()
        return rel.replace("/", ".")
    except ValueError:
        try:
            rel = path_obj.relative_to(root).with_suffix("").as_posix()
            return rel.replace("/", ".")
        except ValueError:
            return path_obj.stem


def load_json(path: Path | str) -> Any:
    """Loads and deserializes JSON from file."""
    import json
    return json.loads(Path(path).read_text(encoding="utf-8"))


def save_json(path: Path | str, data: Any, indent: int = 2) -> None:
    """Serializes and saves data to JSON file."""
    import json
    p = Path(path)
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(data, indent=indent), encoding="utf-8")


def strip_lean_comments(source: str, keep_docstrings: bool = False, preserve_lines: bool = True) -> str:
    """
    Strips single-line (--) and nested block (/- ... -/) comments from Lean source code.
    Preserves line structure by default for accurate 1-based line mapping.
    """
    out: list[str] = []
    i = 0
    n = len(source)
    block_depth = 0
    is_doc = False
    while i < n:
        if block_depth > 0:
            if source.startswith("/-", i):
                block_depth += 1
                if is_doc:
                    out.extend(["/", "-"])
                i += 2
                continue
            if source.startswith("-/", i):
                block_depth -= 1
                if is_doc:
                    out.extend(["-", "/"])
                if block_depth == 0:
                    is_doc = False
                i += 2
                continue
            if is_doc:
                out.append(source[i])
            elif source[i] == "\n" and preserve_lines:
                out.append("\n")
            i += 1
            continue

        if source.startswith("--", i):
            j = source.find("\n", i)
            if j == -1:
                break
            if preserve_lines:
                out.append("\n")
            i = j + 1
            continue
        if source.startswith("/-", i):
            block_depth = 1
            nnxt = source[i + 2] if i + 2 < n else ""
            if keep_docstrings and (nnxt == "-" or nnxt == "!"):
                is_doc = True
                out.extend(["/", "-"])
            i += 2
            continue

        out.append(source[i])
        i += 1

    return "".join(out)


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

