#!/usr/bin/env python3
"""Verify the two GRH compatibility source scopes and their exact dependency pins.

This is a source/provenance check. Kernel verification is performed separately
by validate.py and the fresh Lean declaration audits.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tomllib

from audit_axioms import NATIVE_OWNERS, OWNERS

PACKAGE = Path(__file__).resolve().parent
ROOT = PACKAGE.parents[1]
GRH_REV = "72fead102f663d5c7a407964a13dc0cf9d977207"
TOOLCHAINS = {"native": "leanprover/lean4:v4.34.1", "external": "leanprover/lean4:v4.35.0"}
MATHLIB_REVS = {
    "native": "d13f23b723b8a846827a245b89c10fc7d3f11612",
    "external": "56a005855ea17e0b0958f73ec801ae140b0a1679",
}
NATIVE_TARGETS = (
    "InfoGeometry.Arithmetic.WeightedMangoldtSmoothing",
    "InfoGeometry.Arithmetic.SmoothedMangoldtMellin",
    "InfoGeometry.Arithmetic.RiemannHypothesisHalfPlaneReduction",
    "InfoGeometry.Arithmetic.RealDoubledCenteredXiReadout",
)
PINNED_REVS = {
    "native": {
        "mathlib": MATHLIB_REVS["native"],
        "plausible": "118aa17ee84656b8bd727fef7c458ee8c833385c",
        "LeanSearchClient": "ddf04cf3949fa556442341e87d47f9f6e6074707",
        "importGraph": "e928b72544873815af278d38681b31c0293588e3",
        "proofwidgets": "106ff4fafc74ef4ac99d81dbf3ab399118f497a5",
        "aesop": "355695d523e41d0554926416cba2a2b3544fbbc9",
        "Qq": "6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259",
        "batteries": "f2effa3d803fda822b1f97b806c47cf2adfbcbc2",
        "Cli": "e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204",
    },
    "external": {
        "GRH": GRH_REV,
        "mathlib": MATHLIB_REVS["external"],
        "plausible": "dfa4f38190d07c37e315953e08b90fe2d95b3c24",
        "LeanSearchClient": "d6b4c7be5be75ec4917c873ac50c756dc1436372",
        "importGraph": "a41f0e9a4dea23188ea9cc1c41ac9f8bbafe0b93",
        "proofwidgets": "df72b022e558978a1c50264cfc4d7fec86fa8e04",
        "aesop": "4a174c490d8707121c4a9290800489f105d85e07",
        "Qq": "dce0ad79c486cb1fb504af04f953c3466b0c6db8",
        "batteries": "66e469188fe07963e5cf666c7d4433f45b8131c5",
        "Cli": "c24fe6078c630e89b489bffe59b3e20ac30d12c8",
    },
}
URLS = {
    "GRH": "https://github.com/lsernau/grh-lean",
    "mathlib": "https://github.com/leanprover-community/mathlib4",
    "plausible": "https://github.com/leanprover-community/plausible",
    "LeanSearchClient": "https://github.com/leanprover-community/LeanSearchClient",
    "importGraph": "https://github.com/leanprover-community/import-graph",
    "proofwidgets": "https://github.com/leanprover-community/ProofWidgets4",
    "aesop": "https://github.com/leanprover-community/aesop",
    "Qq": "https://github.com/leanprover-community/quote4",
    "batteries": "https://github.com/leanprover-community/batteries",
    "Cli": "https://github.com/leanprover/lean4-cli",
}


class SourceFailure(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SourceFailure(message)


def git(directory: Path, *args: str) -> str:
    result = subprocess.run(["git", "-C", str(directory), *args], text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
    require(result.returncode == 0, f"git {' '.join(args)} failed in {directory}: {result.stderr.strip()}")
    return result.stdout.strip()


def lane_directory(lane: str) -> Path:
    return PACKAGE / "native" if lane == "native" else PACKAGE


def imports(path: Path) -> set[str]:
    # Imports occur in the header. Strip nested comments first so prose cannot
    # invent an import dependency; keep newlines for anchored import matching.
    text = path.read_text(encoding="utf-8")
    depth = 0
    visible: list[str] = []
    index = 0
    while index < len(text):
        if depth:
            if text.startswith("/-", index):
                depth += 1
                index += 2
            elif text.startswith("-/", index):
                depth -= 1
                index += 2
            else:
                if text[index] == "\n":
                    visible.append("\n")
                index += 1
        elif text.startswith("/-", index):
            visible.append(" ")
            depth = 1
            index += 2
        elif text.startswith("--", index):
            end = text.find("\n", index)
            index = end if end >= 0 else len(text)
        elif text[index] == '"':
            visible.append(" ")
            index += 1
            while index < len(text):
                if text[index] == "\\":
                    index += 2
                elif text[index] == '"':
                    index += 1
                    break
                else:
                    if text[index] == "\n":
                        visible.append("\n")
                    index += 1
        else:
            visible.append(text[index])
            index += 1
    return {
        module
        for line in re.findall(r"^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)",
                               "".join(visible), re.MULTILINE)
        for module in line.split()
    }


def native_closure() -> tuple[dict[str, Path], set[str]]:
    sources: dict[str, Path] = {}
    external: set[str] = set()
    pending = list(NATIVE_TARGETS)
    while pending:
        module = pending.pop()
        if module in sources:
            continue
        if not module.startswith("InfoGeometry."):
            require(module.split(".")[0] in {"Mathlib", "Lean", "Init"},
                    f"Native scope acquired an unsupported dependency: {module}")
            external.add(module)
            continue
        path = ROOT / "lean" / (module.replace(".", "/") + ".lean")
        require(path.is_file() and not path.is_symlink(), f"Missing or linked canonical source: {path}")
        sources[module] = path
        pending.extend(imports(path))
    require(set(NATIVE_OWNERS) <= sources.keys(), "Native build targets do not cover every audited owner")
    return sources, external


def integration_files() -> set[Path]:
    """Inventory package sources without descending into build/dependency caches."""
    files: set[Path] = set()
    for directory, subdirs, names in os.walk(PACKAGE):
        subdirs[:] = [name for name in subdirs
                      if name not in {".lake", "artifacts", "validation-local", "__pycache__"}]
        for name in names:
            files.add(Path(directory) / name)
    return files


def manifest(directory: Path) -> dict[str, dict]:
    value = json.loads((directory / "lake-manifest.json").read_text())
    packages = value["packages"]
    require(len(packages) == len({p["name"] for p in packages}), "Duplicate manifest package")
    require(value["packagesDir"] == ".lake/packages", "Each lane must own its dependency directory")
    return {p["name"]: p for p in packages}


def verify(lane: str, *, checkouts: bool = False) -> dict:
    directory = lane_directory(lane)
    for path in (ROOT / ".git", directory / ".lake", directory / ".lake/packages"):
        require(not path.is_symlink() and not (path.name == ".git" and path.is_file()),
                f"Linked worktree/build directory is unsupported: {path}")
    require((ROOT / "lean-toolchain").read_text().strip() == TOOLCHAINS["native"],
            "The canonical root toolchain changed")
    root_packages = json.loads((ROOT / "lake-manifest.json").read_text())["packages"]
    require(next(p["rev"] for p in root_packages if p["name"] == "mathlib") == MATHLIB_REVS["native"],
            "The canonical root Mathlib pin changed")
    require((directory / "lean-toolchain").read_text().strip() == TOOLCHAINS[lane],
            f"Wrong {lane} Lean toolchain")
    config = tomllib.loads((directory / "lakefile.toml").read_text())
    dep = "mathlib" if lane == "native" else "GRH"
    expected_requirement = {"name": dep, "git": URLS[dep], "rev": PINNED_REVS[lane][dep]}
    if lane == "external":
        expected_requirement["subDir"] = "grh"
    require(config.get("require") == [expected_requirement], f"Wrong direct {lane} dependency")
    libraries = config.get("lean_lib", [])
    expected_libraries = [
        {"name": "InfoGeometry", "srcDir": "../../../lean" if lane == "native" else "../../lean"},
        {"name": "NativeAxiomAudit" if lane == "native" else "InfoGeometryGRH"},
    ]
    require(libraries == expected_libraries, f"Unexpected {lane} source roots")
    require(config.get("defaultTargets") == (list(NATIVE_TARGETS) if lane == "native" else ["InfoGeometryGRH"]),
            f"Unexpected {lane} build targets")
    packages = manifest(directory)
    require(set(packages) == set(PINNED_REVS[lane]), f"Unexpected {lane} dependency inventory")
    for name, package in packages.items():
        require(package.get("type") == "git" and package.get("rev") == PINNED_REVS[lane][name]
                and package.get("url", "").removesuffix(".git") == URLS[name]
                and package.get("subDir") == ("grh" if name == "GRH" else None),
                f"Wrong {lane} dependency pin or source: {name}")
        if checkouts:
            checkout = directory / ".lake/packages" / name
            require(checkout.is_dir() and not checkout.is_symlink(), f"Missing or linked checkout: {checkout}")
            require(Path(git(checkout, "rev-parse", "--show-toplevel")) == checkout.resolve(),
                    f"Not an independent dependency checkout: {checkout}")
            require(git(checkout, "rev-parse", "HEAD") == package["rev"], f"Dependency HEAD mismatch: {name}")
            require(not git(checkout, "status", "--porcelain", "--untracked-files=normal"),
                    f"Modified dependency checkout: {name}")
    if checkouts and lane == "external":
        upstream = directory / ".lake/packages/GRH/grh"
        require((upstream / "lean-toolchain").read_text().strip() == TOOLCHAINS[lane],
                "Upstream GRH toolchain mismatch")
        inherited = json.loads((upstream / "lake-manifest.json").read_text())["packages"]
        require({p["name"]: p["rev"] for p in inherited} == {k: v for k, v in PINNED_REVS[lane].items() if k != "GRH"},
                "Integration dependencies differ from the pinned readable GRH manifest")
    sources, imported = native_closure()
    expected_local = {PACKAGE / (m.replace(".", "/") + ".lean") for m in OWNERS[len(NATIVE_OWNERS):]}
    expected_local |= {PACKAGE / "InfoGeometryGRH.lean", PACKAGE / "InfoGeometryGRH/AxiomAudit.lean",
                       PACKAGE / "native/NativeAxiomAudit.lean"}
    package_files = integration_files()
    actual_local = {p for p in package_files if p.suffix == ".lean"}
    require(actual_local == expected_local, "Integration Lean inventory differs from the audited scope")
    # Additional native dependencies in an adapter must be added to the native
    # targets/audit scope; they cannot silently escape hashing or gate routing.
    for path in expected_local:
        require(not path.is_symlink(), f"Linked integration proof source: {path}")
        canonical_imports = {m for m in imports(path) if m.startswith("InfoGeometry.")}
        require(canonical_imports <= sources.keys(),
                f"Integration import escapes the native verification closure: {path}")
    files = set(sources.values()) | expected_local
    files |= {ROOT / "lean-toolchain", ROOT / "lake-manifest.json", ROOT / "lakefile.lean"}
    files |= {ROOT / name for name in ("tools/build_lock.py", ".github/workflows/grh-compatibility.yml",
                                       ".githooks/pre-push", "scripts/quality/post_build_gate.sh")}
    files |= {p for p in package_files if p.suffix in {".py", ".toml", ".json"}}
    files |= {PACKAGE / "lean-toolchain", PACKAGE / "native/lean-toolchain"}
    files.add(PACKAGE / ".gitignore")
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)}
    return {"status": "PASS", "kind": "source and pin verification", "lane": lane,
            "root_commit": git(ROOT, "rev-parse", "HEAD"), "toolchain": TOOLCHAINS[lane],
            "dependency_revisions": PINNED_REVS[lane], "checkouts_verified": checkouts,
            "canonical_modules": sorted(sources), "mathlib_cache_roots": sorted(m for m in imported if m.startswith("Mathlib")),
            "source_sha256": hashes}


def affected_files(changed: list[str]) -> list[str]:
    sources, _ = native_closure()
    exact = {str(path.relative_to(ROOT)) for path in sources.values()}
    exact |= {"lean-toolchain", "lake-manifest.json", "lakefile.lean", "tools/build_lock.py",
              ".github/workflows/grh-compatibility.yml", "scripts/quality/post_build_gate.sh", ".githooks/pre-push"}
    return [path for path in changed if path in exact or path.startswith("integrations/grh/")]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lane", choices=("native", "external", "all"), default="all")
    parser.add_argument("--checkouts", action="store_true")
    parser.add_argument("--report", type=Path)
    parser.add_argument("--affected-files", action="store_true", help="Print relevant changed paths read from stdin")
    args = parser.parse_args()
    try:
        if args.affected_files:
            print("\n".join(affected_files(sys.stdin.read().splitlines())))
            return 0
        reports = [verify(lane, checkouts=args.checkouts) for lane in
                   (("native", "external") if args.lane == "all" else (args.lane,))]
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(json.dumps(reports, indent=2, sort_keys=True) + "\n")
        for report in reports:
            print(f"PASS {report['lane']}: {len(report['canonical_modules'])} canonical modules; "
                  f"{len(report['dependency_revisions'])} pinned dependencies; checkouts={args.checkouts}")
        return 0
    except (OSError, ValueError, KeyError, StopIteration) as exc:
        print(f"GRH source verification failed: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
