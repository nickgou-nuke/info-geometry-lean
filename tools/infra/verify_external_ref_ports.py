#!/usr/bin/env python3
"""Build and audit every production module of the three pinned external ports.

Historical notebooks are reported, not silently counted as verified. Reuses the
repository's source lexer, shared build lock, Lake wrapper, and axiom checker.
No dependency updates or cache removal are performed.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from tools.build_lock import acquire_build_lock
from tools.quality.audit_constructivity import strip_comments

PACKAGES = {
    "ExteriorPowers": ("ExteriorPowers", Path("/tmp/ExteriorPowers-build/lib/lean")),
    "ProjectiveSpace_lean4": (
        "ProjectiveSpace", ROOT / "external_refs/ProjectiveSpace_lean4/.lake/build/lib/lean"
    ),
    "AbstractSimplicialComplex": (
        "AbstractSimplicialComplex", Path("/tmp/AbstractSimplicialComplex-build/lib/lean")
    ),
}
ARCHIVES = {
    "ExteriorPowers": {
        "Multilinear.lean", "ExteriorPowers/playground.lean", "ExteriorPowers/playground2.lean"
    },
    "ProjectiveSpace_lean4": {
        "ProjectiveSpace/playground.lean",
        *(f"ProjectiveSpace/old/{name}.lean" for name in (
            "ClosedHyperplanes", "MapFromSphere", "ProjectiveSpaceGeneral",
            "ProjectiveSpaceManifold", "SmoothMaps"
        )),
    },
    "AbstractSimplicialComplex": {
        f"AbstractSimplicialComplex/playground{suffix}.lean" for suffix in ("", "1", "2")
    },
}
FORBIDDEN = re.compile(r"\b(sorry|admit|sorryAx|axiom|postulate|unsafe|partial)\b|#exit\b")


def inventory(package: str, library: str) -> tuple[list[str], list[str]]:
    cwd = ROOT / "external_refs" / package
    result = subprocess.check_output(
        ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard", "--", "*.lean"],
        cwd=cwd, text=True,
    )
    # Do not inventory vendored dependency trees or Lake-generated files.
    files = sorted({p for p in result.split("\0") if p and not any(
        part in {".lake", "lake-packages", ".git"} for part in Path(p).parts
    )})
    excluded = [p for p in files if p in ARCHIVES[package]]
    sources = [p for p in files if p not in ARCHIVES[package] and p != "lakefile.lean"]
    for p in sources:
        if p != library + ".lean" and not p.startswith(library + "/"):
            raise RuntimeError(f"Unclassified source: {package}/{p}")
        clean = strip_comments((cwd / p).read_text(), strip_strings=True,
                               strip_quoted_identifiers=True)
        match = FORBIDDEN.search(clean)
        if match:
            line = clean.count("\n", 0, match.start()) + 1
            raise RuntimeError(f"Forbidden active token: {package}/{p}:{line}: {match[0]}")
    return sources, excluded


def module_name(source: str) -> str:
    return ".".join(f"«{p}»" if "." in p else p for p in source[:-5].split("/"))


def hashes(cwd: Path, sources: list[str]) -> dict[str, str]:
    return {p: hashlib.sha256((cwd / p).read_bytes()).hexdigest() for p in sources}


def wait_for_compilers() -> None:
    while True:
        running = subprocess.check_output(["ps", "-eo", "comm="], text=True).splitlines()
        if not any(p.strip() in {"lean", "lake", "leanc", "cc1", "cc1plus", "cargo", "rustc"}
                   for p in running):
            return
        print("Waiting for existing compiler tasks; no task will be terminated.", flush=True)
        time.sleep(5)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory-only", action="store_true")
    parser.add_argument("--output-dir", type=Path, default=Path("/tmp") /
                        ("external-ref-ports-" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")))
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    receipt = {}
    for package, (library, build) in PACKAGES.items():
        cwd = ROOT / "external_refs" / package
        sources, excluded = inventory(package, library)
        entry = receipt[package] = {
            "sources_sha256": hashes(cwd, sources), "excluded_historical_sources": excluded,
            "source_scan": "PASS", "build_exit": None, "axiom_audit_exit": None,
        }
        print(f"{package}: {len(sources)} sources; {len(excluded)} historical exclusions", flush=True)
        if args.inventory_only:
            continue
        wait_for_compilers()
        with (args.output_dir / f"{package}.build.log").open("w") as log:
            result = subprocess.run(
                [sys.executable, str(ROOT / "tools/infra/run_locked_lake_build.py"),
                 "--wait-for-build-lock", *map(module_name, sources), "--", "-d", str(cwd)],
                cwd=ROOT, stdout=log, stderr=subprocess.STDOUT,
            )
        entry["build_exit"] = result.returncode
        if result.returncode == 0:
            wait_for_compilers()
            with acquire_build_lock(None, f"{package} all-declaration axiom audit", block=True):
                with (args.output_dir / f"{package}.axioms.log").open("w") as log:
                    result = subprocess.run(
                        ["lake", "env", "lean", "--run", str(ROOT / "tools/infra/axiom_check.lean"),
                         *(str(build / Path(p).with_suffix(".olean")) for p in sources)],
                        cwd=cwd, stdout=log, stderr=subprocess.STDOUT,
                    )
            entry["axiom_audit_exit"] = result.returncode
        entry["sources_unchanged"] = hashes(cwd, sources) == entry["sources_sha256"]
        (args.output_dir / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
        if entry["build_exit"] != 0 or entry["axiom_audit_exit"] != 0 or not entry["sources_unchanged"]:
            print(f"FAIL: {package}; see {args.output_dir}", flush=True)
            return 1
        print(f"PASS: {package}", flush=True)
    (args.output_dir / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"Receipt: {args.output_dir / 'receipt.json'}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
