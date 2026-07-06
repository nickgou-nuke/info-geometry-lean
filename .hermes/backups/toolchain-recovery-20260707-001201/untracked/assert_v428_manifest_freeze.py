#!/usr/bin/env python3
"""Executable v4.28.0 Lean/Lake manifest freeze guard.

Default mode audits the active root build graph only: root Lean/Lake files plus
package roots named by the root manifest. It intentionally does not recursively
walk archival/scratch/external research checkouts unless --include-external is
passed. Bootstrap/build scripts call default mode before Lake operations.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.28.0"
EXPECTED_VERSION_TAG = "v4.28.0"
EXPECTED_MATHLIB_REV = "8f9d9cff6bd728b17a24e163c9402775d9e6a365"
FORBIDDEN_ROOT_PACKAGES: set[str] = set()
ROOT_FILES = {"lean-toolchain", "lakefile.lean", "lakefile.toml", "lake-manifest.json"}
VERSION_RE = re.compile(r"v4\.[0-9]+\.[0-9]+(?:-rc[0-9]+)?")
MUTABLE_REFS = {"main", "master", "HEAD"}
MUTABLE_REF_RE = re.compile(r'@\s*"(?:main|master|HEAD)"|rev\s*=\s*"(?:main|master|HEAD)"')
HEX_REV_RE = re.compile(r"^[0-9a-f]{40}$")


def rel(root: Path, path: Path) -> str:
    try:
        return str(path.relative_to(root))
    except ValueError:
        return str(path)


def git_head(path: Path) -> str | None:
    if not path.exists():
        return None
    try:
        top = subprocess.run(
            ["git", "-C", str(path), "rev-parse", "--show-toplevel"],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            check=False,
        )
        if top.returncode != 0 or Path(top.stdout.strip()).resolve() != path.resolve():
            return None
        proc = subprocess.run(
            ["git", "-C", str(path), "rev-parse", "HEAD"],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            check=False,
        )
    except OSError:
        return None
    if proc.returncode != 0:
        return None
    return proc.stdout.strip() or None


def load_json(path: Path) -> dict[str, Any] | None:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return None
    return data if isinstance(data, dict) else None


def package_root(manifest_path: Path, pkg: dict[str, Any]) -> Path | None:
    ptype = pkg.get("type")
    if ptype == "path" and isinstance(pkg.get("dir"), str):
        return (manifest_path.parent / pkg["dir"]).resolve()
    if ptype == "git" and isinstance(pkg.get("name"), str):
        return (manifest_path.parent / ".lake" / "packages" / pkg["name"]).resolve()
    return None


def default_candidate_files(root: Path) -> list[Path]:
    files: list[Path] = []
    for name in ROOT_FILES:
        p = root / name
        if p.exists():
            files.append(p)

    root_manifest = load_json(root / "lake-manifest.json")
    if root_manifest:
        for pkg in root_manifest.get("packages", []):
            if not isinstance(pkg, dict):
                continue
            base = package_root(root / "lake-manifest.json", pkg)
            if base is None or not base.exists():
                continue
            for name in ROOT_FILES:
                p = base / name
                if p.exists():
                    files.append(p)
            # Also check nested Lean package root for Paperproof-style subDir = lean.
            if isinstance(pkg.get("subDir"), str):
                sub = base / pkg["subDir"]
                for name in ROOT_FILES:
                    p = sub / name
                    if p.exists():
                        files.append(p)

    seen: set[Path] = set()
    out: list[Path] = []
    for p in files:
        rp = p.resolve()
        if rp not in seen:
            seen.add(rp)
            out.append(p)
    return sorted(out)


def recursive_candidate_files(root: Path) -> list[Path]:
    skip_parts = {".git", ".venv", ".venv-py312", "build", "dist", "__pycache__", ".mypy_cache", ".pytest_cache"}
    out: list[Path] = []
    for base in [root, root / ".lake" / "packages", root / "external_refs", root / "lib" / "InfoGeometryCore"]:
        if not base.exists():
            continue
        for p in base.rglob("*"):
            if any(part in skip_parts for part in p.parts):
                continue
            if p.is_file() and p.name in ROOT_FILES:
                out.append(p)
    return sorted(set(out))


def check_toolchain(root: Path, path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8").strip()
    if text != EXPECTED_TOOLCHAIN:
        return [f"{rel(root, path)}: lean-toolchain is '{text}', expected '{EXPECTED_TOOLCHAIN}'"]
    return []


def check_lake_text(root: Path, path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    active_lines = [
        line for line in text.splitlines()
        if not line.lstrip().startswith("--") and not line.lstrip().startswith("#")
    ]
    active_text = "\n".join(active_lines)
    problems: list[str] = []
    if MUTABLE_REF_RE.search(active_text):
        problems.append(f"{rel(root, path)}: mutable git ref (main/master/HEAD) detected")
    for lineno, line in enumerate(active_lines, start=1):
        if "leanprover/lean4:" in line and EXPECTED_TOOLCHAIN not in line:
            problems.append(f"{rel(root, path)}:{lineno}: foreign Lean toolchain tag: {line.strip()}")
        for m in VERSION_RE.findall(line):
            if m != EXPECTED_VERSION_TAG:
                problems.append(f"{rel(root, path)}:{lineno}: foreign Lean v4 tag detected: {line.strip()}")
    return problems


def check_manifest(root: Path, path: Path) -> list[str]:
    problems: list[str] = []
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:
        return [f"{rel(root, path)}: invalid JSON: {exc}"]
    is_root_manifest = path.resolve() == (root / "lake-manifest.json").resolve()
    packages = data.get("packages", [])
    if not isinstance(packages, list):
        return [f"{rel(root, path)}: packages is not a list"]
    seen_names: set[str] = set()
    for pkg in packages:
        if not isinstance(pkg, dict):
            problems.append(f"{rel(root, path)}: non-object package entry")
            continue
        name = str(pkg.get("name", "<unnamed>"))
        seen_names.add(name)
        ptype = pkg.get("type")
        rev = pkg.get("rev")
        input_rev = pkg.get("inputRev")
        if is_root_manifest and name in FORBIDDEN_ROOT_PACKAGES:
            problems.append(f"{rel(root, path)}: forbidden active package {name}; keep it out of the root build graph")
        if isinstance(input_rev, str) and input_rev in MUTABLE_REFS:
            problems.append(f"{rel(root, path)}: package {name} uses mutable inputRev '{input_rev}'")
        if isinstance(rev, str) and rev in MUTABLE_REFS:
            problems.append(f"{rel(root, path)}: package {name} uses mutable rev '{rev}'")
        if ptype == "git":
            if not isinstance(rev, str) or not HEX_REV_RE.match(rev):
                problems.append(f"{rel(root, path)}: git package {name} missing concrete 40-hex rev")
            if input_rev != rev:
                problems.append(f"{rel(root, path)}: package {name} has inputRev '{input_rev}' but concrete rev '{rev}'")
        if is_root_manifest and name == "mathlib":
            if ptype != "path" or pkg.get("dir") != ".lake/packages/mathlib":
                problems.append(f"{rel(root, path)}: mathlib must be repo-local path .lake/packages/mathlib")
            head = git_head(root / ".lake" / "packages" / "mathlib")
            if head != EXPECTED_MATHLIB_REV:
                problems.append(f".lake/packages/mathlib: HEAD is '{head}', expected v4.28.0 mathlib '{EXPECTED_MATHLIB_REV}'")
        for field in ("inputRev", "rev"):
            value = pkg.get(field)
            if isinstance(value, str):
                for m in VERSION_RE.findall(value):
                    if m != EXPECTED_VERSION_TAG:
                        problems.append(f"{rel(root, path)}: package {name} has foreign v4 tag in {field}: {value}")
    if is_root_manifest and "mathlib" not in seen_names:
        problems.append(f"{rel(root, path)}: root manifest is missing repo-local mathlib package")
    return problems


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", default=str(Path(__file__).resolve().parents[2]))
    parser.add_argument("--include-external", action="store_true", help="recursively audit external/archive-adjacent Lean package files")
    args = parser.parse_args()
    root = Path(args.root).resolve()
    files = recursive_candidate_files(root) if args.include_external else default_candidate_files(root)
    problems: list[str] = []
    for path in files:
        if path.name == "lean-toolchain":
            problems.extend(check_toolchain(root, path))
        elif path.name == "lake-manifest.json":
            problems.extend(check_manifest(root, path))
        else:
            problems.extend(check_lake_text(root, path))
    if problems:
        for problem in problems:
            print(f"error: {problem}", file=sys.stderr)
        print("error: v4.28.0 manifest freeze violated; refusing bootstrap/update/build until every active surface is immutably pinned.", file=sys.stderr)
        return 1
    scope = "root+external" if args.include_external else "root"
    print(f"v4.28.0 manifest freeze ({scope}): OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
