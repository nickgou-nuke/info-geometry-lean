#!/usr/bin/env python3
"""Read-only preflight for the pinned CI toolchain and local Lake packages.

Never resolves a missing package to a moving branch or modifies a dependency.
An existing directory is not enough: a local package must have its configured
Lake file and be represented by tracked source or an initialized gitlink.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
from typing import Any


def expected_version(toolchain: str) -> str:
    match = re.fullmatch(r"leanprover/lean4:v(\d+\.\d+\.\d+(?:-[A-Za-z0-9.-]+)?)", toolchain.strip())
    if not match:
        raise ValueError("Expected an explicit leanprover/lean4:vVERSION pin")
    return match[1]


def verify_version(toolchain: str, banner: str) -> str:
    expected = expected_version(toolchain)
    lines = banner.strip().splitlines()
    match = re.match(r"^Lean \(version ([^,\s)]+)(?=[,\s)])", lines[0]) if lines else None
    actual = match[1] if match else None
    if actual != expected:
        raise ValueError(f"Lean version mismatch: expected {expected}, received {actual!r}")
    return actual


def git(root: Path, *args: str) -> str:
    result = subprocess.run(["git", "-C", str(root), *args], check=True,
                            text=True, capture_output=True)
    return result.stdout


def contained_path(root: Path, value: str) -> Path:
    if not value or Path(value).is_absolute():
        raise ValueError(f"Expected a repository-relative path: {value!r}")
    result = (root / value).resolve()
    if not result.is_relative_to(root.resolve()):
        raise ValueError(f"Path escapes the repository: {value!r}")
    return result


def path_package_report(root: Path) -> dict[str, Any]:
    root = root.resolve()
    manifest = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))
    entries: dict[str, tuple[str, str]] = {}
    for item in git(root, "ls-files", "--stage", "-z").split("\0"):
        if not item:
            continue
        meta, path = item.split("\t", 1)
        mode, sha, stage = meta.split()
        if stage != "0":
            raise ValueError(f"Unmerged Git index entry: {path}")
        entries[path] = (mode, sha)
    rows: list[dict[str, Any]] = []
    for package in manifest["packages"]:
        if package.get("type") != "path":
            continue
        row: dict[str, Any] = {"name": package["name"], "dir": package["dir"],
                               "config": package.get("configFile", "lakefile.lean")}
        errors = []
        try:
            directory = contained_path(root, row["dir"])
            config = contained_path(directory, row["config"])
            # Keep the metadata spelling for Git lookup; validate canonical paths above.
            config_key = (Path(row["dir"]) / row["config"]).as_posix()
            entry = entries.get(row["dir"])
            is_gitlink = bool(entry and entry[0] == "160000")
            tracked_config = config_key in entries and entries[config_key][0] in {"100644", "100755"}
            row.update(directory_exists=directory.is_dir(), config_exists=config.is_file(),
                       source_kind="gitlink" if is_gitlink else "tracked" if tracked_config else "untracked")
            if not config.is_file():
                errors.append("missing_config")
            if is_gitlink:
                row["pinned_commit"] = entry[1]
                if not (directory / ".git").exists():
                    errors.append("uninitialized_gitlink")
                else:
                    actual = git(directory, "rev-parse", "HEAD").strip()
                    row["checked_out_commit"] = actual
                    if actual != entry[1]:
                        errors.append("gitlink_revision_mismatch")
                    if git(directory, "status", "--porcelain", "--untracked-files=normal").strip():
                        errors.append("dirty_gitlink")
            elif not tracked_config:
                errors.append("untracked_path_dependency")
        except (OSError, ValueError, subprocess.CalledProcessError) as exc:
            errors.append("invalid_path_dependency")
            row["detail"] = str(exc)
        row["errors"] = errors
        row["ok"] = not errors
        rows.append(row)
    return {"schema": "info_geometry.ci_path_preflight.v1",
            "revision": git(root, "rev-parse", "HEAD").strip(),
            "ok": all(row["ok"] for row in rows), "packages": rows,
            "scope": "Direct path-package availability/provenance; not compilation or a transitive dependency audit"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["version", "paths"])
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    try:
        if args.command == "version":
            version = verify_version((args.root / "lean-toolchain").read_text(), sys.stdin.read())
            print(f"[ci] Lean {version} matches lean-toolchain")
            return 0
        report = path_package_report(args.root)
        payload = json.dumps(report, indent=2) + "\n"
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(payload, encoding="utf-8")
        print(payload, end="")
        if not report["ok"]:
            print("Path dependencies are not reproducible from this checkout. Restore the recorded sources; "
                  "do not substitute an upstream branch or a stub package.", file=sys.stderr)
        return 0 if report["ok"] else 1
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as exc:
        print(f"CI preflight failed: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
