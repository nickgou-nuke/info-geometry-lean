#!/usr/bin/env python3
"""Validate the Zorn/Souriau intake owners under the existing shared lock.

The focused package and its pinned manifest are unchanged. Optional official
Lake package-location overrides are accepted only for the exact pinned clean
Git checkouts, checked before and after the locked transaction.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
PROJECT = ROOT / "verification/real-matrix-split"
sys.path.insert(0, str(ROOT))

from tools.build_lock import acquire_build_lock  # noqa: E402
from tools.infra.build import (  # noqa: E402
    _interrupt_child_and_wait,
    _validate_lake_workspace_integrity,
)
from tools.quality.reviewed_audit_source import (  # noqa: E402
    audit_source,
    parse_audit_output,
    validate_targets,
)

TARGETS = [
    "InfoGeometry.Lie.SplitOctonionRegularInvertibility",
    "InfoGeometry.Lie.ZornChiralCircularFourVectorOperators",
    "InfoGeometry.Algebraic.CartanSouriauActionGroupoid",
    "InfoGeometry.Algebraic.CotangentBilinearGraph",
    "InfoGeometry.Analytic.FiniteNegativeLogPartition",
    "InfoGeometry.Canonical.ZornSouriauIntakeChecks"
]
REUSED = [
    "InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionDatum",
    "InfoGeometry.Algebra.ZornVectorMatrix.kirmse_left",
    "InfoGeometry.Algebra.ZornVectorMatrix.kirmse_right",
    "InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv_mul",
    "InfoGeometry.Lie.SplitOctonionImaginaryAction.canonical_kirmse_right",
    "Module.End.isUnit_iff",
    "MulEquiv.isUnit_map",
    "Matrix.isUnit_iff_isUnit_det",
    "InfoGeometry.Lie.SplitOctonionEllCircularQuadraticCoordinates.circularPeirceQuadratic_formula",
    "InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis",
    "InfoGeometry.Algebraic.CartanSouriauAffineCocycle.affineAction_one",
    "InfoGeometry.Algebraic.CartanSouriauAffineCocycle.affineAction_mul",
    "InfoGeometry.Algebraic.CartanSouriauAffineCocycle.theta_inv",
    "CategoryTheory.ActionCategory.objEquiv",
    "CategoryTheory.ActionCategory.homOfPair",
    "InfoGeometry.Analytic.logSumExp_sum_pos",
    "Finset.sum_mul_sq_le_sq_mul_sq"
]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
_audit_spec = importlib.util.spec_from_file_location("real_matrix_split_audit", PROJECT / "audit.py")
assert _audit_spec is not None and _audit_spec.loader is not None
PIN_AUDIT = importlib.util.module_from_spec(_audit_spec)
_audit_spec.loader.exec_module(PIN_AUDIT)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args: str, cwd: Path = ROOT) -> str:
    return subprocess.check_output(["git", *args], cwd=cwd, text=True).strip()


def source_snapshot(targets: list[str] | tuple[str, ...] = TARGETS,
                    extra_sources: tuple[str, ...] = ()) -> dict[str, str]:
    selected = subprocess.check_output(
        ["git", "ls-files", "-z", "--", "lean", "lib/InfoGeometryCore",
         "lean-toolchain", "lakefile.lean", "lake-manifest.json",
         "verification/real-matrix-split", "verification/zorn-souriau",
         "docs/ZORN_SOURIAU_INTAKE_CONTRACT.md", "docs/intake/zorn-souriau-20261124",
         "tools/build_lock.py", "tools/infra/build.py",
         "tools/quality/reviewed_audit_source.py", *extra_sources], cwd=ROOT,
    ).decode().split("\0")
    paths = {p for p in selected if p and (ROOT / p).is_file()}
    for relative in extra_sources:
        path = Path(relative)
        if path.is_absolute() or ".." in path.parts or relative not in paths:
            raise RuntimeError(f"Extra validation source must be an existing tracked file: {relative}")
    paths.update("lean/" + target.replace(".", "/") + ".lean" for target in targets)
    paths.add(str(Path(__file__).relative_to(ROOT)))
    return {p: sha256(ROOT / p) for p in sorted(paths)}


def package_snapshot(overrides: Path | None) -> list[dict[str, str]]:
    PIN_AUDIT.check_pins(PROJECT)
    root_manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    mathlib = [p for p in root_manifest["packages"] if p["name"] == "mathlib"]
    if len(mathlib) != 1 or mathlib[0]["rev"] != "d13f23b723b8a846827a245b89c10fc7d3f11612":
        raise RuntimeError("Unexpected root Mathlib pin")
    manifest = json.loads((PROJECT / "lake-manifest.json").read_text())
    packages = manifest["packages"]
    mappings = {}
    if overrides is not None:
        data = json.loads(overrides.read_text())
        for entry in data["packages"]:
            name = entry["name"]
            if name in mappings:
                raise RuntimeError(f"Duplicate package override: {name}")
            mappings[name] = entry
        if set(mappings) != {p["name"] for p in packages}:
            raise RuntimeError("Overrides must contain exactly the pinned package names")
    records = []
    for pinned in packages:
        name = pinned["name"]
        if overrides is None:
            path = (PROJECT / manifest["packagesDir"] / name).resolve()
        else:
            entry = mappings[name]
            if entry.get("type") != "path" or not Path(entry["dir"]).is_absolute():
                raise RuntimeError(f"Expected absolute local package path for {name}")
            for field in ("scope", "inherited", "configFile", "manifestFile"):
                if entry.get(field) != pinned.get(field):
                    raise RuntimeError(f"Override changes {name}.{field}")
            path = Path(entry["dir"])
        error = _validate_lake_workspace_integrity(path)
        if error or path.is_symlink() or not (path / ".git").is_dir():
            raise RuntimeError(error or f"Not an ordinary package checkout: {path}")
        head = git("rev-parse", "HEAD", cwd=path)
        if head != pinned["rev"]:
            raise RuntimeError(f"Pin mismatch for {name}: {head} != {pinned['rev']}")
        if git("status", "--porcelain", "--untracked-files=no", cwd=path):
            raise RuntimeError(f"Tracked package sources are modified: {name}")
        records.append({"name": name, "path": str(path), "head": head})
    return records


def main(*, targets: list[str] | tuple[str, ...] = TARGETS,
         reused: list[str] | tuple[str, ...] = REUSED,
         extra_sources: tuple[str, ...] = (),
         task_name: str = "zorn-souriau") -> int:
    targets = validate_targets(targets)
    reused = validate_targets(reused)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packages", type=Path)
    parser.add_argument("--output", type=Path,
                        default=ROOT / "artifacts" / task_name / "native")
    args = parser.parse_args()
    overrides = args.packages.resolve() if args.packages else None
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    run_id = f"run-{time.time_ns()}-{os.getpid()}"
    logs = output / run_id
    logs.mkdir(exist_ok=False)
    environment = os.environ.copy()
    for name in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"):
        environment.pop(name, None)
    lake = ["lake", "-d", str(PROJECT)]
    if overrides is not None:
        lake += ["--packages", str(overrides)]
    report = {
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "run_id": run_id, "targets": list(targets), "commands": [], "status": "queued",
    }
    lock = None

    def save_receipt() -> None:
        pending = logs / "receipt.tmp"
        pending.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
        pending.replace(output / "result.json")

    def run(label: str, command: list[str]) -> str:
        print(f"[{task_name}] {label}", flush=True)
        assert lock is not None
        path = logs / f"{len(report['commands']):02d}-{label}.log"
        record = {"label": label, "argv": command, "returncode": None,
                  "log": str(path.relative_to(output)), "status": "running"}
        report["commands"].append(record)
        save_receipt()
        with path.open("w") as stream:
            process = subprocess.Popen(command, cwd=ROOT, env=environment,
                                       stdout=stream, stderr=subprocess.STDOUT,
                                       start_new_session=(os.name == "posix"),
                                       pass_fds=(lock.fileno(),) if os.name == "posix" else ())
            try:
                returncode = process.wait()
            except KeyboardInterrupt:
                _interrupt_child_and_wait(process)
                raise
            finally:
                if process.poll() is None:
                    _interrupt_child_and_wait(process)
        record.update(returncode=returncode, status="passed" if returncode == 0 else "failed")
        save_receipt()
        text = path.read_text()
        if returncode:
            print("\n".join(text.splitlines()[-70:]), flush=True)
            raise RuntimeError(f"{label} exited {returncode}")
        return text

    def interrupted(_signum, _frame) -> None:
        raise KeyboardInterrupt

    previous_sigterm = signal.signal(signal.SIGTERM, interrupted)
    save_receipt()
    print(f"[{task_name}] waiting for the shared build lock", flush=True)
    try:
        lock = acquire_build_lock(None, f"{task_name}:{os.getpid()}", block=True)
        report["status"] = "running"
        save_receipt()
        for directory in (ROOT, PROJECT):
            error = _validate_lake_workspace_integrity(directory)
            if error:
                raise RuntimeError(error)
        report["head"] = git("rev-parse", "HEAD")
        report["source_sha256"] = source_snapshot(targets, extra_sources)
        report["explicit_public_declarations"] = {
            target: PIN_AUDIT.owner_declarations(target) for target in targets
        }
        report["packages"] = package_snapshot(overrides)
        report["package_override_sha256"] = sha256(overrides) if overrides else None
        if (ROOT / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.34.1":
            raise RuntimeError("Unexpected pinned toolchain")
        for label, command in (("runtime", ["lean", "--version"]),
                               ("workspace-runtime", lake + ["env", "lean", "--version"])):
            banner = run(label, command).strip()
            if not re.search(r"Lean \(version 4\.34\.1(?:,|\))", banner):
                raise RuntimeError(f"Unexpected runtime: {banner}")
            report[label] = banner
        run("target-build", lake + ["build", *targets])
        for i, target in enumerate(targets):
            source = ROOT / "lean" / (target.replace(".", "/") + ".lean")
            run(f"fresh-source-{i}", lake + ["env", "lean", "-DwarningAsError=true", str(source)])
        audit = logs / "OwnerAudit.lean"
        reused_names = ", ".join("`" + name for name in reused)
        audit.write_text(audit_source(list(targets)) + f'''
run_cmd do
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let names : Array Lean.Name := #[{reused_names}]
  for name in names do
    let info ← Lean.getConstInfo name
    if info.isUnsafe || info.isPartial then
      throwError "Unsafe or partial reused declaration: {{name}}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Disallowed reused axiom {{ax}} in {{name}}"
    logInfo m!"AUDIT_REUSED: {{name}}"
''')
        report["audit_source_sha256"] = sha256(audit)
        text = run("native-axiom-audit", lake + ["env", "lean", "-DwarningAsError=true", str(audit)])
        report["declaration_counts"] = parse_audit_output(text, list(targets))
        records = re.findall(r"^AUDIT_DECL: (\S+): (\S+)$", text, re.MULTILINE)
        if len(records) != sum(report["declaration_counts"].values()) or len(set(records)) != len(records):
            raise RuntimeError("Native declaration inventory does not reconcile")
        if dict(Counter(owner for owner, _ in records)) != report["declaration_counts"]:
            raise RuntimeError("Native per-owner declaration inventory does not reconcile")
        report["owned_declarations"] = {
            target: sorted(name for owner, name in records if owner == target) for target in targets
        }
        for target in targets:
            if not set(report["explicit_public_declarations"][target]) <= set(report["owned_declarations"][target]):
                raise RuntimeError(f"Native audit omits explicit public declarations in {target}")
        reused_records = re.findall(r"^AUDIT_REUSED: (\S+)$", text, re.MULTILINE)
        if len(reused_records) != len(reused) or set(reused_records) != set(reused):
            raise RuntimeError("Reused declaration audit does not reconcile")
        axioms = re.findall(r"^AUDIT_AXIOMS: \[(.*)\]$", text, re.MULTILINE)
        if len(axioms) != 1:
            raise RuntimeError("Missing or duplicate axiom summary")
        report["axioms"] = sorted(a.strip() for a in axioms[0].split(",") if a.strip())
        if not set(report["axioms"]) <= ALLOWED_AXIOMS:
            raise RuntimeError("Axiom summary exceeds the allowed foundations")
        report["reused_declarations"] = reused_records
        if sha256(audit) != report["audit_source_sha256"]:
            raise RuntimeError("Generated audit source changed during validation")
        if source_snapshot(targets, extra_sources) != report["source_sha256"] or git("rev-parse", "HEAD") != report["head"]:
            raise RuntimeError("Source snapshot changed during validation")
        if package_snapshot(overrides) != report["packages"]:
            raise RuntimeError("Package snapshot changed during validation")
        if overrides is not None and sha256(overrides) != report["package_override_sha256"]:
            raise RuntimeError("Package override changed during validation")
        report["status"] = "passed"
        return 0
    except KeyboardInterrupt:
        report["status"] = "interrupted"
        return 130
    except (Exception, SystemExit) as error:
        report["status"] = "failed"
        report["error"] = str(error)
        print(f"[{task_name}] {error}", file=sys.stderr, flush=True)
        return 1
    finally:
        report["finished_utc"] = datetime.now(timezone.utc).isoformat()
        save_receipt()
        if lock is not None:
            lock.release()
        signal.signal(signal.SIGTERM, previous_sigterm)


if __name__ == "__main__":
    raise SystemExit(main())
