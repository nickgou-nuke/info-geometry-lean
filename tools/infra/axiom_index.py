#!/usr/bin/env python3
"""
Axiom indexer — uses tools/infra/axiom_index.lean to scan .olean files.

Usage:
  python3 tools/infra/axiom_index.py                    # all InfoGeometry modules
  python3 tools/infra/axiom_index.py --all               # all built modules
  python3 tools/infra/axiom_index.py Module.Name         # one module
  python3 tools/infra/axiom_index.py --json              # JSON output
"""

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from collections import Counter, defaultdict
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from tools.build_lock import BuildLock
from tools.infra.run_locked_lean import resolve_cached_lean_env

REPO_ROOT = Path(__file__).resolve().parents[2]
OLEAN_DIR = REPO_ROOT / ".lake" / "build" / "lib" / "lean"
INDEX_SCRIPT = REPO_ROOT / "tools" / "infra" / "axiom_index.lean"
BUILD_LOCK = Path("/tmp/info-geometry-build.lock")
CACHED_TOOLS_DIR = REPO_ROOT / ".lake" / "cached_tools"

CANONICAL = {"propext", "Quot.sound", "Classical.choice"}

SUSPICIOUS_PATTERNS = [
    (re.compile(r"^propext$"), False),
    (re.compile(r"^Quot\.sound$"), False),
    (re.compile(r"^Classical\.choice$"), False),
    (re.compile(r"^sorryAx$"), False),
    (re.compile(r"^propext_"), True),
    (re.compile(r"^Quot\."), True),
    (re.compile(r"^Classical\.(.+)$"), lambda m: m.group(1) != "choice"),
    (re.compile(r"^[A-Z][a-z]+[A-Z]"), True),
    (re.compile(r"\.(axiom|ax)$", re.I), True),
]


def is_suspicious(name: str) -> tuple[bool, str]:
    if name in CANONICAL:
        return False, "canonical"
    if name == "sorryAx":
        return False, "sorry placeholder"
    for pat, test in SUSPICIOUS_PATTERNS:
        m = pat.match(name)
        if m:
            if callable(test):
                return test(m), f"pattern: {pat.pattern}"
            return test, f"pattern: {pat.pattern}"
    return True, "unknown"


def parse_decl_line(line: str) -> dict | None:
    m = re.match(
        r"DECL:(.+):kind=(.+):partial=(true|false):unsafe=(true|false):axiom=(true|false):axioms=#\[(.*)\]",
        line,
    )
    if not m:
        return None
    name = m.group(1)
    kind = m.group(2)
    partial = m.group(3) == "true"
    unsafe = m.group(4) == "true"
    is_axiom = m.group(5) == "true"
    axioms_str = m.group(6)
    axioms = [a.strip() for a in axioms_str.split(",") if a.strip()]
    return {
        "name": name,
        "kind": kind,
        "partial": partial,
        "unsafe": unsafe,
        "is_axiom": is_axiom,
        "axioms": axioms,
        "nonstandard": [a for a in axioms if a not in CANONICAL],
    }


def _merged_tool_env(cached_env: dict[str, str] | None) -> dict[str, str] | None:
    if not cached_env:
        return None
    env = dict(os.environ)
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LD_LIBRARY_PATH", "PATH"):
        val = cached_env.get(key)
        if val:
            env[key] = val
    return env


def ensure_compiled_axiom_index(
    cached_env: dict[str, str] | None = None,
) -> tuple[list[str], dict[str, str] | None]:
    """Build or reuse a native axiom_index executable from tools/infra/axiom_index.lean."""
    if cached_env is None:
        cached_env = resolve_cached_lean_env(REPO_ROOT)
    merged_env = _merged_tool_env(cached_env)
    if not cached_env or not INDEX_SCRIPT.is_file():
        return ["lake", "env", "lean", "--run", str(INDEX_SCRIPT)], merged_env

    lean_bin = cached_env.get("lean", "")
    leanc_bin = cached_env.get("leanc", "")
    if lean_bin and leanc_bin and Path(lean_bin).is_file() and Path(leanc_bin).is_file():
        try:
            ver = subprocess.run(
                [lean_bin, "--version"],
                cwd=REPO_ROOT,
                env=merged_env,
                capture_output=True,
                text=True,
                timeout=30,
                check=False,
            )
            script_bytes = INDEX_SCRIPT.read_bytes()
            h = hashlib.sha256()
            h.update(script_bytes)
            h.update(b"\0")
            h.update((ver.stdout if ver.returncode == 0 else lean_bin).encode("utf-8"))
            digest = h.hexdigest()[:16]
            CACHED_TOOLS_DIR.mkdir(parents=True, exist_ok=True)
            target_bin = CACHED_TOOLS_DIR / f"axiom_index_{digest}"
            if target_bin.is_file() and os.access(target_bin, os.X_OK):
                return [str(target_bin)], merged_env
            with tempfile.TemporaryDirectory(prefix="axiom_index_build_", dir=str(CACHED_TOOLS_DIR)) as tmp:
                tmp_dir = Path(tmp)
                c_file = tmp_dir / "axiom_index.c"
                bin_file = tmp_dir / "axiom_index"
                r1 = subprocess.run(
                    [lean_bin, "-c", str(c_file), str(INDEX_SCRIPT)],
                    cwd=REPO_ROOT,
                    env=merged_env,
                    capture_output=True,
                    text=True,
                    timeout=120,
                    check=False,
                )
                if r1.returncode == 0 and c_file.is_file():
                    r2 = subprocess.run(
                        [leanc_bin, str(c_file), "-lleanshared", "-o", str(bin_file)],
                        cwd=REPO_ROOT,
                        env=merged_env,
                        capture_output=True,
                        text=True,
                        timeout=120,
                        check=False,
                    )
                    if r2.returncode == 0 and bin_file.is_file():
                        os.chmod(bin_file, 0o755)
                        os.replace(bin_file, target_bin)
                        return [str(target_bin)], merged_env
        except (OSError, subprocess.SubprocessError):
            pass

    if lean_bin and Path(lean_bin).is_file():
        return [lean_bin, "--run", str(INDEX_SCRIPT)], merged_env
    return ["lake", "env", "lean", "--run", str(INDEX_SCRIPT)], merged_env


def _resolve_module_name(olean_path: Path, olean_dir: Path) -> str | None:
    try:
        rel = olean_path.resolve().relative_to(olean_dir.resolve())
    except ValueError:
        return None
    if rel.suffix != ".olean":
        return None
    return ".".join(rel.with_suffix("").parts)


def scan_olean_batch(
    olean_paths: list[Path],
    *,
    replay: bool = False,
    timeout: int = 300,
    olean_dir: Path | None = None,
    lock_path: Path | None = None,
) -> dict[Path, tuple[list[dict], str | None]]:
    """Scan a batch of `.olean` files in one Lean process under shared LOCK_SH."""
    effective_olean_dir = (olean_dir or OLEAN_DIR).resolve()
    results: dict[Path, tuple[list[dict], str | None]] = {}
    existing: list[tuple[Path, Path, str | None]] = []
    for path in olean_paths:
        if not path.exists():
            results[path] = ([], "not found")
        else:
            resolved = path.resolve()
            existing.append((path, resolved, _resolve_module_name(resolved, effective_olean_dir)))

    if not existing:
        return results

    use_fast = (not replay) and all(mod is not None for _p, _r, mod in existing)
    runner_cmd, merged_env = ensure_compiled_axiom_index()
    if use_fast:
        cli_args = ["--fast-modules", *(f"{mod}={resolved}" for _p, resolved, mod in existing)]
    else:
        cli_args = ["--replay", *(str(resolved) for _p, resolved, _mod in existing)]

    with BuildLock(lock_path or BUILD_LOCK, f"axiom-index:{os.getpid()}", block=True, shared=True):
        try:
            proc = subprocess.run(
                [*runner_cmd, *cli_args],
                cwd=REPO_ROOT,
                env=merged_env,
                capture_output=True,
                text=True,
                timeout=timeout,
                check=False,
            )
        except subprocess.TimeoutExpired:
            for orig, _resolved, _mod in existing:
                results[orig] = ([], f"timeout after {timeout}s")
            return results

    if proc.returncode != 0:
        err = f"lean error: {(proc.stderr or proc.stdout)[:300]}"
        for orig, _resolved, _mod in existing:
            results[orig] = ([], err)
        return results

    by_label: dict[str, Path] = {}
    decls_by_orig: dict[Path, list[dict]] = {orig: [] for orig, _r, _m in existing}
    for orig, resolved, _mod in existing:
        by_label[str(resolved)] = orig
        by_label[str(orig)] = orig

    current_orig: Path | None = existing[0][0] if len(existing) == 1 else None
    for line in proc.stdout.splitlines():
        if line.startswith("MODULE:"):
            label = line[len("MODULE:") :].strip()
            current_orig = by_label.get(label)
            continue
        d = parse_decl_line(line)
        if d and current_orig is not None:
            decls_by_orig[current_orig].append(d)

    for orig, _resolved, _mod in existing:
        results[orig] = (decls_by_orig[orig], None)
    return results


def scan_olean(olean_path: Path, *, replay: bool = False, timeout: int = 300) -> tuple[list[dict], str | None]:
    return scan_olean_batch([olean_path], replay=replay, timeout=timeout)[olean_path]


def main():
    parser = argparse.ArgumentParser(description="Axiom indexer")
    parser.add_argument("modules", nargs="*")
    parser.add_argument("--all", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument(
        "--batch",
        type=int,
        default=0,
        help="Modules per batch process (default: 0 = scan all modules in one batch).",
    )
    parser.add_argument(
        "--replay",
        action="store_true",
        help="Replay each .olean independently through kernel instead of shared importModules.",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=300,
        help="Subprocess timeout per batch in seconds (default: 300).",
    )
    args = parser.parse_args()

    if args.modules:
        paths = []
        for m in args.modules:
            p = OLEAN_DIR / (m.replace(".", "/") + ".olean")
            paths.append(p)
    elif args.all:
        paths = sorted(OLEAN_DIR.rglob("*.olean"))
    else:
        paths = sorted(OLEAN_DIR.rglob("InfoGeometry/**/*.olean"))

    if not paths:
        print("No .olean files found.")
        sys.exit(1)

    print(f"Scanning {len(paths)} module(s)...")

    axiom_usage = Counter()
    axiom_modules: dict[str, set[str]] = defaultdict(set)
    axiomless: list[str] = []
    suspicious: dict[str, list[tuple[str, str, str]]] = defaultdict(list)
    total_decls = 0
    total_nonstd = 0
    any_error = False

    chunks = (
        [paths]
        if args.batch <= 0
        else [paths[i : i + args.batch] for i in range(0, len(paths), args.batch)]
    )
    batch_results: dict[Path, tuple[list[dict], str | None]] = {}
    for chunk in chunks:
        batch_results.update(
            scan_olean_batch(chunk, replay=args.replay, timeout=args.timeout)
        )

    for i, p in enumerate(paths):
        decls, err = batch_results[p]
        module = str(p.relative_to(OLEAN_DIR).with_suffix("")).replace("/", ".")
        if err:
            print(f"  [{i+1}/{len(paths)}] {module}: ERROR {err}")
            any_error = True
            continue

        has_nonstandard = False
        for d in decls:
            total_decls += 1
            if d["nonstandard"]:
                total_nonstd += 1
                has_nonstandard = True
            for a in d["axioms"]:
                axiom_usage[a] += 1
                axiom_modules[a].add(module)
                susp, reason = is_suspicious(a)
                if susp:
                    suspicious[a].append((module, d["name"], reason))

        status = "!" if has_nonstandard else "✓"
        nstd = sum(1 for d in decls if d["nonstandard"])
        npart = sum(1 for d in decls if d["partial"])
        nunsafe = sum(1 for d in decls if d["unsafe"])
        print(f"  [{i+1}/{len(paths)}] {module}: {status} {len(decls)} decls, {nstd}✗ {npart}p {nunsafe}u")

        if not has_nonstandard:
            axiomless.append(module)

    # === REPORT ===
    print("\n" + "=" * 70)
    print("AXIOM INDEX REPORT")
    print("=" * 70)

    # Unique axioms
    print(f"\nAll unique axioms ({len(axiom_usage)}):")
    for ax, count in axiom_usage.most_common():
        modules = axiom_modules[ax]
        can = "ⓘ" if ax in CANONICAL else "⚠" if ax in suspicious else " "
        print(f"  {can} {ax}: {count} uses in {len(modules)} modules")

    # Suspicious
    if suspicious:
        print(f"\nSuspicious axioms ({len(suspicious)}):")
        for ax, occ in sorted(suspicious.items()):
            print(f"  ⚠ {ax}:")
            for mod, decl, reason in occ[:3]:
                print(f"      {mod} :: {decl} ({reason})")

    # Axiomless modules
    print(f"\nAxiomless modules ({len(axiomless)} / {len(paths)}):")
    for m in axiomless[:10]:
        print(f"  {m}")
    if len(axiomless) > 10:
        print(f"  ... +{len(axiomless) - 10} more")

    # Summary
    n_nonstd_decls = sum(1 for _ in axiom_usage.elements() if _ not in CANONICAL)
    print(f"\nSummary:")
    print(f"  Modules: {len(paths)}")
    print(f"  Declarations: {total_decls}")
    print(f"  Nonstandard axiom users: {total_nonstd}")
    print(f"  Unique axioms: {len(axiom_usage)}")
    print(f"  Axiomless modules: {len(axiomless)}")

    if args.json:
        print(json.dumps({
            "modules": len(paths),
            "declarations": total_decls,
            "axiom_usage": dict(axiom_usage.most_common()),
            "axiomless": axiomless[:100],
            "suspicious": {k: v[:5] for k, v in suspicious.items()},
        }, indent=2))

    if any_error:
        sys.exit(1)


if __name__ == "__main__":
    main()
