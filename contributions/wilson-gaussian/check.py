#!/usr/bin/env python3
"""Apply and verify the Gaussian contribution at the exact upstream pins.

The contribution repository's own Lean/Mathlib pins are not modified or used
to certify this external port. All compiler commands run in the target package.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT))
from tools.build_lock import acquire_build_lock
from tools.quality.audit_constructivity import strip_comments
from tools.quality.reviewed_audit_source import audit_source, parse_audit_output

UPSTREAM = "https://github.com/MathePhysics/4D_Wilson_Loop_RG.git"
BASE = "9a4492cc6bdf3338379123a085af59dfd8018a9c"
PACKAGE = Path("LEAN/Libraries/GaussianBlockSpin")
TOOLCHAIN = "leanprover/lean4:v4.34.0-rc2"
MATHLIB = "8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a"
TARGETS = ["GaussianBlockSpin.MatrixWeighted." + name for name in
           ("Positive", "Variational", "Composition", "Coordinates", "Kernel",
            "EffectiveForm", "Convolution", "Examples")]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(r"\b(sorry|admit|sorryAx|axiom|postulate|unsafe|native_decide)\b|#exit\b")
APPEND_IMPORT = "\nimport GaussianBlockSpin.MatrixWeighted\n"
APPEND_README = "\n## Matrix-weighted Gaussian extension\n\nSee [MATRIX_WEIGHTED.md](MATRIX_WEIGHTED.md) for the positive matrix precision,\nexact minimizer, normalized elimination and convolution, and scalar readback.\n"


def git(cwd: Path, *args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=cwd, text=True).strip()


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def overlay_files() -> list[Path]:
    return sorted(p for p in (HERE / "overlay").rglob("*") if p.is_file())


def prepare(work: Path, patch: Path | None) -> Path:
    if work.exists() and any(work.iterdir()):
        raise RuntimeError("Preparation requires a new empty destination")
    work.mkdir(parents=True, exist_ok=True)
    for args in (("init",), ("remote", "add", "origin", UPSTREAM),
                 ("fetch", "--no-tags", "--depth=1", "--filter=blob:none", "origin", BASE),
                 ("sparse-checkout", "set", str(PACKAGE)),
                 ("checkout", "--detach", BASE)):
        subprocess.run(["git", *args], cwd=work, check=True)
    project = work / PACKAGE
    if git(work, "rev-parse", "HEAD") != BASE:
        raise RuntimeError("Unexpected upstream revision")
    if (project / "lean-toolchain").read_text().strip() != TOOLCHAIN:
        raise RuntimeError("Unexpected upstream toolchain")
    if MATHLIB not in (project / "lakefile.toml").read_text():
        raise RuntimeError("Unexpected upstream Mathlib pin")
    for source in overlay_files():
        target = project / source.relative_to(HERE / "overlay")
        if target.exists():
            raise RuntimeError(f"Overlay would replace an upstream file: {target}")
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    for name, suffix in (("GaussianBlockSpin.lean", APPEND_IMPORT), ("README.md", APPEND_README)):
        path = project / name
        path.write_text(path.read_text() + suffix)
    subprocess.run(["git", "add", "--", str(PACKAGE)], cwd=work, check=True)
    subprocess.run(["git", "diff", "--cached", "--check"], cwd=work, check=True)
    patch_bytes = subprocess.check_output(["git", "diff", "--cached", "--binary"], cwd=work)
    if (HERE / "upstream.patch").exists() and (HERE / "upstream.patch").read_bytes() != patch_bytes:
        raise RuntimeError("Committed upstream patch differs from the reviewed overlay")
    if patch:
        patch.parent.mkdir(parents=True, exist_ok=True)
        patch.write_bytes(patch_bytes)
    return project


def snapshot(work: Path) -> dict[str, str]:
    names = subprocess.check_output(["git", "ls-files", "-z", "--", str(PACKAGE)], cwd=work)
    return {name: sha(work / name) for name in names.decode().split("\0") if name}


def check_exact_applied_source(work: Path) -> None:
    """Reject preexisting source edits even when HEAD still names the base."""
    base_names = subprocess.check_output(
        ["git", "ls-tree", "-rz", "--name-only", BASE, "--", str(PACKAGE)], cwd=work
    ).decode().split("\0")
    original = {name for name in base_names if name}
    additions = {str(PACKAGE / f.relative_to(HERE / "overlay")) for f in overlay_files()}
    if original & additions:
        raise RuntimeError("Overlay replaces an original upstream path")
    if set(snapshot(work)) != original | additions:
        raise RuntimeError("Target package has an unexpected tracked source set")
    suffixes = {str(PACKAGE / "GaussianBlockSpin.lean"): APPEND_IMPORT,
                str(PACKAGE / "README.md"): APPEND_README}
    for name in original:
        expected = subprocess.check_output(["git", "show", f"{BASE}:{name}"], cwd=work)
        expected += suffixes.get(name, "").encode()
        if (work / name).read_bytes() != expected:
            raise RuntimeError(f"Upstream source differs from exact base plus reviewed edits: {name}")
    project = work / PACKAGE
    lean_sources = {str(p.relative_to(work)) for p in project.rglob("*.lean")
                    if ".lake" not in p.relative_to(project).parts}
    if lean_sources != {p for p in original | additions if p.endswith(".lean")}:
        raise RuntimeError("Untracked Lean source could shadow the reviewed source closure")
    if (project / "lean-toolchain").read_text().strip() != TOOLCHAIN:
        raise RuntimeError("Toolchain pin differs from the reviewed upstream pin")
    if MATHLIB not in (project / "lakefile.toml").read_text():
        raise RuntimeError("Mathlib pin differs from the reviewed upstream pin")


def check_overlay(project: Path) -> dict[str, list[str]]:
    public = {}
    manifest = json.loads((HERE / "source-manifest.json").read_text())
    overlay_hashes = {str(f.relative_to(HERE / "overlay")): sha(f) for f in overlay_files()}
    if overlay_hashes != manifest["overlay_sha256"]:
        raise RuntimeError("Reviewed source manifest differs from the overlay")
    for source in overlay_files():
        target = project / source.relative_to(HERE / "overlay")
        if target.read_bytes() != source.read_bytes():
            raise RuntimeError(f"Applied source differs from reviewed overlay: {target}")
    for target in TARGETS:
        source = project / (target.replace(".", "/") + ".lean")
        clean = strip_comments(source.read_text(), strip_strings=True, strip_quoted_identifiers=True)
        if match := FORBIDDEN.search(clean):
            raise RuntimeError(f"Prohibited source token {match[0]} in {source}")
        namespace = re.findall(r"^namespace (\S+)\s*$", clean, re.MULTILINE)
        if len(namespace) != 1:
            raise RuntimeError(f"Unreviewed namespace shape in {source}")
        heads = re.findall(r"^(?:noncomputable\s+)?(?:def|lemma|theorem)\s+(\S+)", clean, re.MULTILINE)
        public[target] = [namespace[0] + "." + name for name in heads]
        if not heads:
            raise RuntimeError(f"No public declarations in {source}")
    if public != manifest["explicit_public_declarations"]:
        raise RuntimeError("Public declaration inventory differs from the reviewed manifest")
    return public


def package_snapshot(project: Path) -> list[dict[str, str]]:
    manifest = json.loads((project / "lake-manifest.json").read_text())
    expected = json.loads((project / ".lake/packages/mathlib/lake-manifest.json").read_text())
    expected_revs = {p["name"]: p["rev"] for p in expected["packages"]}
    expected_revs["mathlib"] = MATHLIB
    packages = manifest["packages"]
    if {p["name"]: p["rev"] for p in packages} != expected_revs:
        raise RuntimeError("Resolved dependency pins differ from the pinned Mathlib manifest")
    records = []
    for entry in packages:
        path = project / manifest["packagesDir"] / entry["name"]
        if path.is_symlink() or not (path / ".git").is_dir():
            raise RuntimeError("Dependencies must be independent ordinary checkouts")
        head = git(path, "rev-parse", "HEAD")
        if head != entry["rev"] or git(path, "status", "--porcelain", "--untracked-files=no"):
            raise RuntimeError(f"Changed dependency sources: {entry['name']}")
        records.append({"name": entry["name"], "head": head})
    return records


def verify(work: Path, output: Path) -> int:
    project = work / PACKAGE
    output.mkdir(parents=True, exist_ok=True)
    report = {"status": "queued", "commands": [], "upstream": UPSTREAM,
              "upstream_base": BASE, "toolchain": TOOLCHAIN, "mathlib": MATHLIB,
              "contribution_head": git(ROOT, "rev-parse", "HEAD"),
              "contribution_tree": git(ROOT, "rev-parse", "HEAD^{tree}"),
              "targets": TARGETS, "started_utc": datetime.now(timezone.utc).isoformat()}
    environment = os.environ.copy()
    for name in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"):
        environment.pop(name, None)

    def save() -> None:
        (output / "result.json").write_text(json.dumps(report, indent=2) + "\n")

    def run(label: str, command: list[str]) -> str:
        path = output / f"{len(report['commands']):02d}-{label}.log"
        record = {"label": label, "argv": command, "log": path.name, "status": "running"}
        report["commands"].append(record)
        save()
        print(f"[wilson-gaussian] {label}", flush=True)
        with path.open("w") as log:
            result = subprocess.run(command, cwd=project, env=environment,
                                    stdout=log, stderr=subprocess.STDOUT)
        record.update(returncode=result.returncode, status="passed" if result.returncode == 0 else "failed")
        save()
        text = path.read_text()
        if result.returncode:
            print("\n".join(text.splitlines()[-100:]), flush=True)
            raise RuntimeError(f"{label} exited {result.returncode}")
        return text

    save()
    try:
        with acquire_build_lock(None, f"wilson-gaussian:{os.getpid()}", block=True):
            if git(work, "rev-parse", "HEAD") != BASE:
                raise RuntimeError("Upstream base differs from the reviewed revision")
            for path in (work / ".git", project / ".lake", project / ".lake/packages"):
                if path.is_symlink() or (path.name == ".git" and not path.is_dir()):
                    raise RuntimeError("Linked worktrees/shared dependency roots are not supported")
            report["explicit_public_declarations"] = check_overlay(project)
            check_exact_applied_source(work)
            report["source_sha256"] = snapshot(work)
            report["status"] = "running"
            banner = run("runtime", ["lean", "--version"]).strip()
            if not re.search(r"Lean \(version 4\.34\.0-rc2(?:,|\))", banner):
                raise RuntimeError(f"Unexpected native compiler: {banner}")
            report["runtime"] = banner
            # Upstream commits no manifest for this package. Bootstrap only when
            # absent, then verify every resolved pin against Mathlib's manifest.
            if not (project / "lake-manifest.json").exists():
                run("bootstrap-pinned-manifest", ["lake", "update"])
            report["packages"] = package_snapshot(project)
            report["resolved_manifest_sha256"] = sha(project / "lake-manifest.json")
            shutil.copyfile(project / "lake-manifest.json", output / "resolved-lake-manifest.json")
            run("hydrate-pinned-cache", ["lake", "exe", "cache", "get"])
            run("selected-build", ["lake", "build", "GaussianBlockSpin.MatrixWeighted"])
            for target in TARGETS:
                run("fresh-" + target.rsplit(".", 1)[1],
                    ["lake", "env", "lean", "-DwarningAsError=true", target.replace(".", "/") + ".lean"])
            audit = output / "OwnerAudit.lean"
            audit.write_text(audit_source(TARGETS))
            report["audit_source_sha256"] = sha(audit)
            text = run("native-axiom-audit", ["lake", "env", "lean", "-DwarningAsError=true", str(audit)])
            counts = parse_audit_output(text, TARGETS)
            records = re.findall(r"^AUDIT_DECL: (\S+): (\S+)$", text, re.MULTILINE)
            if len(set(records)) != len(records) or dict(Counter(owner for owner, _ in records)) != counts:
                raise RuntimeError("Native declaration inventory does not reconcile")
            report["declaration_counts"] = counts
            report["owned_declarations"] = {target: sorted(name for owner, name in records if owner == target)
                                            for target in TARGETS}
            for target, heads in report["explicit_public_declarations"].items():
                if not set(heads) <= set(report["owned_declarations"][target]):
                    raise RuntimeError(f"Explicit declaration missing from audit: {target}")
            ax = re.findall(r"^AUDIT_AXIOMS: \[(.*)\]$", text, re.MULTILINE)
            if len(ax) != 1:
                raise RuntimeError("Missing axiom summary")
            report["axioms"] = sorted(a.strip() for a in ax[0].split(",") if a.strip())
            if not set(report["axioms"]) <= ALLOWED:
                raise RuntimeError("Nonstandard axioms in the audited owners")
            if snapshot(work) != report["source_sha256"] or check_overlay(project) != report["explicit_public_declarations"]:
                raise RuntimeError("Source changed during validation")
            if package_snapshot(project) != report["packages"]:
                raise RuntimeError("Dependency sources changed during validation")
            if sha(project / "lake-manifest.json") != report["resolved_manifest_sha256"]:
                raise RuntimeError("Resolved dependency manifest changed during validation")
            check_exact_applied_source(work)
            report["status"] = "passed"
        return 0
    except Exception as error:
        report["status"] = "failed"
        report["error"] = str(error)
        print(f"[wilson-gaussian] {error}", file=sys.stderr, flush=True)
        return 1
    finally:
        report["finished_utc"] = datetime.now(timezone.utc).isoformat()
        save()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workdir", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--prepare-only", action="store_true")
    parser.add_argument("--patch", type=Path)
    args = parser.parse_args()
    work = args.workdir.resolve()
    if args.prepare_only:
        prepare(work, args.patch.resolve() if args.patch else None)
        return 0
    if not args.output:
        parser.error("--output is required for native verification")
    return verify(work, args.output.resolve())


if __name__ == "__main__":
    raise SystemExit(main())
