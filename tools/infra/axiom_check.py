#!/usr/bin/env python3
"""Audit compiled Lean modules with the native module-data axiom checker.

The Lean runner reads each requested .olean, imports its recorded dependencies,
replays the module constants, then checks transitive axioms, unsafe declarations,
and partial declarations.
"""

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
OLEAN_DIR = REPO_ROOT / ".lake" / "build" / "lib" / "lean"
BUILD_LOCK = Path("/tmp/info-geometry-build.lock")
LEAN_RUNNER = REPO_ROOT / "tools" / "infra" / "axiom_check.lean"
MODULE_SEGMENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")


def olean_to_module(path: Path) -> str:
    """Convert a path under the Lake Lean library to a dotted module name."""
    resolved_root = OLEAN_DIR.resolve()
    resolved_path = path.resolve()
    try:
        rel = resolved_path.relative_to(resolved_root)
    except ValueError as exc:
        raise ValueError(f".olean path is outside the build library: {path}") from exc
    if rel.suffix != ".olean":
        raise ValueError(f"expected an .olean path: {path}")
    parts = rel.with_suffix("").parts
    if not parts or any(not MODULE_SEGMENT.fullmatch(part) for part in parts):
        raise ValueError(f"invalid Lean module path: {path}")
    return ".".join(parts)


def module_to_olean(module: str) -> Path:
    """Resolve a dotted module name, rejecting traversal and symlink escapes."""
    parts = module.split(".")
    if not parts or any(not MODULE_SEGMENT.fullmatch(part) for part in parts):
        raise ValueError(f"invalid Lean module name: {module}")
    path = OLEAN_DIR.joinpath(*parts).with_suffix(".olean")
    olean_to_module(path)
    return path


def check_olean_files(olean_paths: list[Path], timeout: int = 300) -> list[dict]:
    """Check paths in one Lean process and bind each result to its .olean path."""
    results: dict[str, dict] = {}
    valid_paths: list[Path] = []
    for path in olean_paths:
        try:
            module = olean_to_module(path)
        except (OSError, ValueError) as exc:
            results[str(path)] = {"module": str(path), "passed": False, "error": str(exc)}
            continue
        if not path.is_file():
            results[str(path)] = {"module": module, "passed": False, "error": "file not found"}
            continue
        canonical = path.resolve()
        results[str(path)] = {"module": module, "passed": False, "error": "missing native module result"}
        valid_paths.append(canonical)

    if not valid_paths:
        return [results[str(path)] for path in olean_paths]
    command = [
        "flock", "-x", str(BUILD_LOCK),
        "lake", "env", "lean", "--run", str(LEAN_RUNNER),
        *[str(path) for path in valid_paths],
    ]
    try:
        result = subprocess.run(
            command,
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        for path in valid_paths:
            entry = results[str(path)]
            entry.update(error=f"timeout after {timeout}s", stdout=exc.stdout or "", stderr=exc.stderr or "")
        return [results[str(path)] for path in olean_paths]
    except OSError as exc:
        for path in valid_paths:
            results[str(path)].update(error=f"runner could not start: {exc}")
        return [results[str(path)] for path in olean_paths]

    valid_canonical_paths = {str(path) for path in valid_paths}
    by_canonical_path = {
        str(path.resolve()): results[str(path)]
        for path in olean_paths
        if str(path.resolve()) in valid_canonical_paths
    }
    seen: set[str] = set()
    for line in result.stdout.splitlines():
        if not line.startswith("MODULE_RESULT:"):
            continue
        payload = line.removeprefix("MODULE_RESULT:")
        raw_path, separator, verdict = payload.rpartition(":")
        canonical = str(Path(raw_path).resolve())
        if not separator or canonical not in by_canonical_path:
            continue
        entry = by_canonical_path[canonical]
        seen.add(canonical)
        entry["passed"] = verdict == "PASS"
        entry["returncode"] = result.returncode
        if not entry["passed"]:
            entry["error"] = "native axiom checker failed"
            entry["stdout"] = result.stdout
            entry["stderr"] = result.stderr
    for canonical, entry in by_canonical_path.items():
        if canonical not in seen:
            entry["error"] = "native checker omitted the module result"
            entry["stdout"] = result.stdout
            entry["stderr"] = result.stderr
    return [results[str(path)] for path in olean_paths]


def check_olean_file(olean_path: Path, timeout: int = 60) -> dict:
    """Compatibility helper for checking one .olean."""
    return check_olean_files([olean_path], timeout=timeout)[0]


def main():
    parser = argparse.ArgumentParser(description="Audit compiled Lean module axioms")
    parser.add_argument("modules", nargs="*", help="Dotted module names to check")
    parser.add_argument("--all", action="store_true", help="Check every .olean under the Lean build library")
    parser.add_argument("--json", action="store_true", help="Print JSON results")
    parser.add_argument("--quiet", action="store_true", help="Print only summary and failed modules")
    parser.add_argument("--batch-size", type=int, default=128, help="Maximum modules per Lean process")
    args = parser.parse_args()

    if args.modules:
        try:
            paths = [module_to_olean(module) for module in args.modules]
        except ValueError as exc:
            parser.error(str(exc))
    elif args.all:
        paths = sorted(OLEAN_DIR.rglob("*.olean"))
    else:
        paths = sorted(OLEAN_DIR.rglob("InfoGeometry/**/*.olean"))
        paths += sorted(OLEAN_DIR.rglob("InfoGeometry.lean.olean"))

    if not paths:
        print("No .olean files found.", file=sys.stderr)
        sys.exit(1)

    print(f"Checking {len(paths)} module(s)...")
    if args.batch_size < 1:
        parser.error("--batch-size must be positive")
    results = []
    for offset in range(0, len(paths), args.batch_size):
        results.extend(check_olean_files(paths[offset : offset + args.batch_size]))
    for result in results:
        status = "OK" if result["passed"] else "FAIL"
        if not args.quiet or not result["passed"]:
            print(f"  {result['module']}: {status}")
        if not result["passed"]:
            if result.get("error"):
                print(f"      error: {result['error']}")
            for line in result.get("stderr", "").splitlines():
                if line.strip():
                    print(f"      {line}")
            for line in result.get("stdout", "").splitlines():
                if line.strip():
                    print(f"      {line}")

    if args.json:
        print(json.dumps(results, indent=2))
    failed = sum(not result["passed"] for result in results)
    print(f"Axiom check summary: {len(results) - failed} passed, {failed} failed.")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
