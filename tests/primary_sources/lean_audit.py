"""Tier 3 & Tier 4 Lean kernel probes, traceability verification, locked Lake build, and axiom audits."""

from __future__ import annotations

import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Iterable

from tests.primary_sources import (
    ALLOWED_AXIOMS,
    BRIDGE_FILE_REL,
    CANONICAL_ALL_REL,
    FEATURE_SPECS,
    FOUNDER_YEAR_SPEC,
    MILESTONES,
    PILLAR_DIR_TO_KEY,
    PROBES_DIR,
    REPO_ROOT,
    REQUIRED_LEAN_COPYRIGHT_HEADER,
    TRIANGLE_BRIDGE_REL,
)
from tests.primary_sources.manifest_checker import (
    CheckOutcome,
    TraceabilityRow,
    _normalize_pillar_name,
    expand_traceability_work_ids,
)
from tests.primary_sources.quality_and_r3 import (
    LeanDecl,
    parse_lean_declarations,
    strip_lean_comments_and_strings,
)
from tools.build_lock import BuildLock, DEFAULT_BUILD_LOCK_PATH
from tools.infra.qms_evidence_pipeline import parse_axiom_audit_output

PYTHON_EXE: str = sys.executable


def lean_path_to_module(rel_path: str) -> str:
    p = Path(rel_path)
    parts = p.with_suffix("").parts
    if parts and parts[0] in ("lean", "src"):
        parts = parts[1:]
    return ".".join(parts)


def run_locked_lean_probe(
    probe_name: str,
    imports: list[str],
    body: str,
    *,
    repo_root: Path = REPO_ROOT,
    probes_dir: Path | None = None,
    timeout: int = 1200,
) -> tuple[bool, int, str, str, str]:
    """Write a temporary .lean probe under scratch/primary_sources_e2e/probes/, run under lock, and clean up."""
    target_dir = probes_dir or (repo_root / "scratch" / "primary_sources_e2e" / "probes")
    target_dir.mkdir(parents=True, exist_ok=True)
    import_lines = "\n".join(f"import {m}" for m in dict.fromkeys(imports))
    content = f"{REQUIRED_LEAN_COPYRIGHT_HEADER}{import_lines}\n\n{body.strip()}\n"
    if not content.startswith(REQUIRED_LEAN_COPYRIGHT_HEADER):
        return False, 1, "", "Probe failed byte-0 Apache header invariant", ""

    with tempfile.TemporaryDirectory(prefix=f"{probe_name}_", dir=target_dir) as tmp_dir:
        probe_path = Path(tmp_dir) / f"{probe_name}.lean"
        probe_path.write_text(content, encoding="utf-8")
        try:
            rel_probe = probe_path.relative_to(repo_root).as_posix()
        except ValueError:
            rel_probe = str(probe_path)
        proc = subprocess.run(
            [
                PYTHON_EXE,
                str(REPO_ROOT / "tools/infra/run_locked_lean.py"),
                "--wait-for-build-lock",
                rel_probe,
            ],
            cwd=repo_root,
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
        )
        return proc.returncode == 0, proc.returncode, proc.stdout, proc.stderr, rel_probe


def check_cross_pillar_bridge(repo_root: Path = REPO_ROOT) -> CheckOutcome:
    """Tier 3 check: PrimarySourceFourPillarBridge imports all 4 pillars + integrates into triangle/All."""
    bridge_path = repo_root / BRIDGE_FILE_REL
    if not bridge_path.is_file():
        return CheckOutcome(
            check_id="T3-FOUR-PILLAR-BRIDGE",
            tier=3,
            milestone="M6",
            pillar="all",
            status="FAIL",
            summary=f"Missing {BRIDGE_FILE_REL}",
            details={"missing": BRIDGE_FILE_REL},
        )

    raw = bridge_path.read_text(encoding="utf-8", errors="replace")
    stripped = strip_lean_comments_and_strings(raw)
    decls = [d for d in parse_lean_declarations(stripped, already_stripped=True) if not d.is_private]
    errors: list[str] = []

    expected_imports = [
        "InfoGeometry.Projective.GrassmannPrimarySources",
        "InfoGeometry.Erlangen.LieKleinPfaffCartanPrimary",
        "InfoGeometry.Clifford.LipschitzWittRieszPrimary",
        "InfoGeometry.Clifford.KahlerHestenesJWABSPrimary",
        "InfoGeometry.OperatorAlgebra.PeirceCartanKoszulDVPrimary",
        "InfoGeometry.Thermo.OnsagerCasimirKBMPrimary",
        "InfoGeometry.Krein.PontryaginSpace",
        "InfoGeometry.KK.KreinSpectralTriplePrimary",
    ]
    missing_imports = [m for m in expected_imports if not re.search(rf"\bimport\s+{re.escape(m)}\b", stripped)]
    if missing_imports:
        errors.append(f"{BRIDGE_FILE_REL} missing pillar imports: {missing_imports}")

    joint_thms = [d for d in decls if d.kind in {"theorem", "lemma", "def", "structure"}]
    if not joint_thms:
        errors.append(f"{BRIDGE_FILE_REL} defines no public joint cross-pillar declarations")

    tri_path = repo_root / TRIANGLE_BRIDGE_REL
    if not tri_path.is_file() or "PrimarySourceFourPillarBridge" not in tri_path.read_text(encoding="utf-8", errors="replace"):
        errors.append(f"{TRIANGLE_BRIDGE_REL} does not import/reference PrimarySourceFourPillarBridge")

    all_path = repo_root / CANONICAL_ALL_REL
    if not all_path.is_file() or "InfoGeometry.Canonical.PrimarySourceFourPillarBridge" not in all_path.read_text(encoding="utf-8", errors="replace"):
        errors.append(f"{CANONICAL_ALL_REL} does not import InfoGeometry.Canonical.PrimarySourceFourPillarBridge")

    if errors:
        return CheckOutcome(
            check_id="T3-FOUR-PILLAR-BRIDGE",
            tier=3,
            milestone="M6",
            pillar="all",
            status="FAIL",
            summary="; ".join(errors),
            details={"errors": errors},
        )
    return CheckOutcome(
        check_id="T3-FOUR-PILLAR-BRIDGE",
        tier=3,
        milestone="M6",
        pillar="all",
        status="PASS",
        summary=f"{BRIDGE_FILE_REL} bridges all 8 pillar modules and integrates into TriangleBridge & Canonical.All",
        details={"declarations": len(joint_thms)},
    )


def _mod_olean_exists(repo_root: Path, mod: str) -> bool:
    parts = mod.split(".")
    return (repo_root / ".lake" / "build" / "lib" / "lean" / Path(*parts).with_suffix(".olean")).is_file()


def _mod_source_exists(repo_root: Path, mod: str) -> bool:
    parts = mod.split(".")
    return (repo_root / "lean" / Path(*parts).with_suffix(".lean")).is_file()


def check_traceability_kernel(
    rows: list[TraceabilityRow],
    manifest: dict[str, Any] | None,
    *,
    repo_root: Path = REPO_ROOT,
    pillar_filter: str = "all",
    run_lean_kernel: bool = True,
    allow_planned: bool = False,
    include_cross_pillar: bool = False,
    incremental_partial: bool = False,
) -> CheckOutcome:
    """Tier 3 check: 100% manifest->traceability coverage + live Lean Environment resolution & collectAxioms."""
    errors: list[str] = []
    if not rows:
        return CheckOutcome(
            check_id="T3-TRACEABILITY-KERNEL",
            tier=3,
            milestone="M6",
            pillar=pillar_filter,
            status="FAIL",
            summary="No traceability matrix rows parsed from docs/PRIMARY_SOURCE_ARCHETYPES.md",
            details={},
        )

    manifest_works = None
    manifest_ids: set[str] | None = None
    manifest_status_by_id: dict[str, str] = {}
    work_pillar_by_id: dict[str, str] = {
        s.work_id: s.pillar for s in FOUNDER_YEAR_SPEC if s.work_id
    }
    if manifest:
        manifest_works = manifest.get("works") if "works" in manifest else manifest.get("entries")
        if isinstance(manifest_works, list):
            manifest_ids = set()
            for w in manifest_works:
                if not isinstance(w, dict):
                    continue
                wid = str(w.get("id", "")).strip()
                if not wid:
                    continue
                manifest_ids.add(wid)
                manifest_status_by_id[wid] = str(w.get("status") or w.get("availability_status") or "").strip().lower()
                wpk = PILLAR_DIR_TO_KEY.get(_normalize_pillar_name(str(w.get("pillar", ""))), "")
                if wpk:
                    work_pillar_by_id[wid] = wpk

    mod_pillar_map: dict[str, str] = {}
    for fspec in FEATURE_SPECS:
        for rel in (fspec.owner_file, *fspec.alt_owner_files):
            if rel.endswith(".lean"):
                mod_pillar_map[lean_path_to_module(rel)] = fspec.pillar

    def _row_pillars(r: TraceabilityRow, expanded_ids: list[str]) -> set[str]:
        if r.work_id.strip().upper().startswith("M6"):
            return {"all"}
        pillars: set[str] = set()
        for wid in expanded_ids:
            if wid in work_pillar_by_id:
                pillars.add(work_pillar_by_id[wid])
        if pillars:
            return pillars
        rp = PILLAR_DIR_TO_KEY.get(_normalize_pillar_name(r.pillar), "")
        if rp:
            return {rp}
        for m in (r.lean_modules or ((r.lean_module,) if r.lean_module else ())):
            if m in mod_pillar_map:
                pillars.add(mod_pillar_map[m])
        return pillars or {"all"}

    row_ids: set[str] = set()
    filtered_rows: list[tuple[TraceabilityRow, list[str]]] = []
    for r in rows:
        try:
            exp = expand_traceability_work_ids(r.work_id, valid_ids=manifest_ids)
        except ValueError as exc:
            errors.append(f"Row {r.work_id} (line {r.line_no}): {exc}")
            continue
        row_ids.update(exp)
        rps = _row_pillars(r, exp)
        if pillar_filter != "all":
            if rps == {"all"} and not include_cross_pillar:
                continue
            if "all" in rps and not include_cross_pillar and len(rps) == 1:
                continue
            if pillar_filter not in rps and not ("all" in rps and include_cross_pillar):
                continue
        filtered_rows.append((r, exp))

    if isinstance(manifest_works, list):
        for w in manifest_works:
            if not isinstance(w, dict):
                continue
            wid = str(w.get("id", "")).strip()
            wpk = work_pillar_by_id.get(wid, "")
            if pillar_filter != "all" and wpk != pillar_filter:
                continue
            if wid and wid not in row_ids:
                errors.append(f"MANIFEST work {wid!r} missing from traceability matrix")

    non_gap_pairs: list[tuple[str, tuple[str, ...], str]] = []
    planned_deferred = 0
    for r, exp in filtered_rows:
        status_norm = r.status.strip().lower()
        if status_norm == "gap_recorded":
            if manifest_ids is not None:
                if not exp:
                    errors.append(f"Row {r.work_id} (line {r.line_no}): gap_recorded row covers zero manifest work IDs")
                else:
                    non_gap_ids = [wid for wid in exp if manifest_status_by_id.get(wid) != "gap_recorded"]
                    if non_gap_ids:
                        errors.append(
                            f"Row {r.work_id} (line {r.line_no}): marked gap_recorded in traceability but MANIFEST.json has non-gap status for {non_gap_ids}"
                        )
            continue
        if r.module_errors:
            errors.append(f"Row {r.work_id} (line {r.line_no}): invalid Lean Module token(s): {r.module_errors}")
            continue
        row_mods = r.lean_modules or ((r.lean_module,) if r.lean_module else ())
        if not row_mods or any(not m.startswith("InfoGeometry.") for m in row_mods):
            errors.append(f"Row {r.work_id} (line {r.line_no}): invalid Lean Module {r.lean_module!r}")
            continue
        if status_norm == "planned":
            if not allow_planned:
                errors.append(f"Row {r.work_id} (line {r.line_no}): row still marked PLANNED in strict mode")
                continue
            if not r.declarations:
                planned_deferred += 1
                continue
        if not r.declarations:
            errors.append(f"Row {r.work_id} (line {r.line_no}): non-gap row lists zero Lean declarations")
            continue
        missing_src = [m for m in row_mods if not _mod_source_exists(repo_root, m)]
        if missing_src:
            errors.append(f"Row {r.work_id} (line {r.line_no}): referenced Lean module(s) missing on disk: {missing_src}")
            continue
        for decl in r.declarations:
            non_gap_pairs.append((r.work_id, tuple(row_mods), decl))

    if not non_gap_pairs and not (allow_planned and planned_deferred > 0):
        errors.append("Traceability matrix has zero non-gap (Module, Declaration) pairs")

    if errors:
        return CheckOutcome(
            check_id="T3-TRACEABILITY-KERNEL",
            tier=3,
            milestone="M6",
            pillar=pillar_filter,
            status="FAIL",
            summary="; ".join(errors[:5]),
            details={"errors": errors, "pairs": len(non_gap_pairs), "planned_deferred": planned_deferred},
        )

    if not run_lean_kernel:
        return CheckOutcome(
            check_id="T3-TRACEABILITY-KERNEL",
            tier=3,
            milestone="M6",
            pillar=pillar_filter,
            status="PASS",
            summary=(
                f"Traceability matrix syntax/coverage valid ({len(non_gap_pairs)} pairs, "
                f"{planned_deferred} planned row(s) deferred until M2-M6; kernel skipped)"
            ),
            details={"pairs": len(non_gap_pairs), "planned_deferred": planned_deferred},
        )

    probe_pairs = non_gap_pairs
    if incremental_partial:
        probe_pairs = [
            pair for pair in non_gap_pairs
            if all(_mod_olean_exists(repo_root, m) for m in pair[1])
        ]
        if not probe_pairs:
            return CheckOutcome(
                check_id="T3-TRACEABILITY-KERNEL",
                tier=3,
                milestone="M6",
                pillar=pillar_filter,
                status="PASS",
                summary=(
                    f"Traceability matrix syntax/coverage valid ({len(non_gap_pairs)} pairs, "
                    f"{planned_deferred} planned row(s) deferred; 0 built target pairs yet)"
                ),
                details={"pairs": len(non_gap_pairs), "built_pairs": 0, "planned_deferred": planned_deferred},
            )

    modules = sorted({mod for _, mods, _ in probe_pairs for mod in mods})
    pair_literals = ",\n    ".join(
        f'(#[{", ".join(f"`{m}" for m in mods)}], "{decl}")' for _, mods, decl in probe_pairs
    )
    body = f"""
section E2ETraceabilityAudit
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let ownerOf (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]!
    | none => env.mainModule
  let pairs : Array (Array Name × String) := #[
    {pair_literals}
  ]
  for (allowedMods, rawDecl) in pairs do
    let mut resolved? : Option (Name × ConstantInfo) :=
      match env.find? rawDecl.toName with
      | some info => some (rawDecl.toName, info)
      | none => none
    if resolved?.isNone then
      for modName in allowedMods do
        if resolved?.isNone then
          let cand := modName ++ rawDecl.toName
          match env.find? cand with
          | some info => resolved? := some (cand, info)
          | none => pure ()
    let some (declName, info) := resolved?
      | throwError "Traceability missing declaration in Lean Environment: {{rawDecl}} (modules {{allowedMods}})"
    let actualOwner := ownerOf declName
    unless allowedMods.contains actualOwner do
      throwError "Traceability owner mismatch for {{declName}}: expected one of {{allowedMods}}, actual {{actualOwner}}"
    if info.isUnsafe || info.isPartial then
      throwError "Traceability declaration is unsafe or partial: {{declName}}"
    if let .axiomInfo _ := info then
      throwError "Traceability declaration is a forbidden axiom: {{declName}}"
    if let .opaqueInfo _ := info then
      throwError "Traceability declaration is a forbidden opaque: {{declName}}"
    let axs ← Lean.collectAxioms declName
    for ax in axs do
      unless allowed.contains ax do
        throwError "Disallowed axiom {{ax}} in traced declaration {{declName}}"
end E2ETraceabilityAudit
"""
    ok, rc, stdout, stderr, probe_path = run_locked_lean_probe(
        "traceability_kernel_audit",
        [*modules, "Lean.Util.CollectAxioms", "Lean.Elab.Command"],
        body,
        repo_root=repo_root,
    )
    if not ok:
        snippet = (stderr or stdout).strip()[:400]
        return CheckOutcome(
            check_id="T3-TRACEABILITY-KERNEL",
            tier=3,
            milestone="M6",
            pillar=pillar_filter,
            status="FAIL",
            summary=f"Traceability kernel probe failed (rc={rc}): {snippet}",
            details={"stdout": stdout, "stderr": stderr, "probe_path": probe_path, "pairs": len(probe_pairs)},
        )
    return CheckOutcome(
        check_id="T3-TRACEABILITY-KERNEL",
        tier=3,
        milestone="M6",
        pillar=pillar_filter,
        status="PASS",
        summary=f"All {len(probe_pairs)} traceability (Module, Declaration) pairs resolved in Lean Environment with allowed axioms only",
        details={"pairs": len(probe_pairs), "modules": modules, "planned_deferred": planned_deferred},
    )


def run_r3_kernel_probe(
    modules: Iterable[str],
    *,
    repo_root: Path = REPO_ROOT,
    check_id: str = "T2-R3-KERNEL-INSPECTION",
) -> CheckOutcome:
    """Tier 2/3 Lean kernel ConstantInfo inspection verifying R3 invariants on built modules."""
    mod_list = list(dict.fromkeys(modules))
    if not mod_list:
        return CheckOutcome(
            check_id=check_id,
            tier=2,
            milestone="ALL",
            pillar="all",
            status="PASS",
            summary="No built modules selected for kernel R3 probe",
            details={},
        )
    mod_lits = ",\n    ".join(f"`{m}" for m in mod_list)
    body = f"""
section E2ER3KernelAudit
open Lean Elab Command in
private def isInternalName (s : String) : Bool :=
  s.contains "._" || s.startsWith "_private." || s.contains ".match_" ||
  s.endsWith ".rec" || s.endsWith ".casesOn" || s.endsWith ".noConfusion" ||
  s.endsWith ".ctorIdx" || s.endsWith ".below" || s.endsWith ".brecOn" || s.endsWith ".recOn"

open Lean in
private def stripLamsAndMData : Nat → Expr → Nat × Expr
  | depth, .lam _ _ b _ => stripLamsAndMData (depth + 1) b
  | depth, .mdata _ b => stripLamsAndMData depth b
  | depth, e => (depth, e)

open Lean in
private def isIdHeadConst (fn : Expr) : Bool :=
  fn.isConstOf `id || fn.isConstOf `LinearMap.id ||
  fn.isConstOf `ContinuousLinearMap.id || fn.isConstOf `LinearIsometryEquiv.refl

open Lean in
private def isIdentityExpr (pairs : Array (Name × ConstantInfo)) : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, e =>
    let (d, body) := stripLamsAndMData 0 e
    match body with
    | .bvar idx => d > 0 && idx < d
    | _ =>
      let fn := body.getAppFn
      if isIdHeadConst fn then true
      else
        match fn with
        | .const c _ =>
          match pairs.find? (fun (n, _) => n == c) with
          | some (_, .defnInfo ci) => isIdentityExpr pairs fuel ci.value
          | _ => false
        | _ => false

open Lean in
private def expandExprConsts (pairs : Array (Name × ConstantInfo)) : Nat → NameSet → NameSet
  | 0, seeds => seeds
  | fuel' + 1, seeds =>
    let next := seeds.foldl (init := seeds) (fun acc u =>
      if isInternalName u.toString then acc
      else
        match pairs.find? (fun (n, _) => n == u) with
        | some (_, .defnInfo d) =>
          let s1 := d.type.getUsedConstantsAsSet.foldl (init := acc) (fun s x => s.insert x)
          d.value.getUsedConstantsAsSet.foldl (init := s1) (fun s x => s.insert x)
        | some (_, .inductInfo ci) =>
          ci.type.getUsedConstantsAsSet.foldl (init := acc) (fun s x => s.insert x)
        | _ => acc)
    expandExprConsts pairs fuel' next

open Lean in
private def isFinTypeExpr (pairs : Array (Name × ConstantInfo)) : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, e =>
    let e' := e.consumeMData
    let fn := e'.getAppFn
    if fn.isConstOf `Fin then true
    else match fn with
      | .const c _ =>
        if isInternalName c.toString then false
        else
          match pairs.find? (fun (n, _) => n == c) with
          | some (_, .defnInfo d) => isFinTypeExpr pairs fuel d.value
          | _ => false
      | _ => false

open Lean in
private def binderHasScalarClass (bIdx : Nat) (binders : List Expr) : Bool :=
  (List.range binders.length).any fun j =>
    if j < bIdx then
      let bTy : Expr := binders[j]!
      let fn := bTy.getAppFn
      let isScalarCls :=
        fn.isConstOf `Field || fn.isConstOf `CommRing || fn.isConstOf `Ring ||
        fn.isConstOf `CommSemiring || fn.isConstOf `Semiring
      if isScalarCls then
        match (bTy.getAppArgs[0]? : Option Expr) with
        | some (Expr.bvar k) => k == bIdx - (j + 1)
        | _ => false
      else false
    else false

open Lean in
private def hasCoordFinExpr (pairs : Array (Name × ConstantInfo)) : Nat → List Expr → Expr → Bool
  | 0, _, _ => false
  | fuel + 1, binders, e =>
    let e' := e.consumeMData
    let fn := e'.getAppFn
    let qfHit :=
      if fn.isConstOf `QuadraticForm || fn.isConstOf `QuadraticMap then
        let args : Array Expr := e'.getAppArgs
        match (args[0]? : Option Expr), (args[1]? : Option Expr) with
        | some sExpr, some (Expr.forallE _ finDom cod _) =>
          isFinTypeExpr pairs fuel finDom && cod.consumeMData == sExpr.consumeMData && !(cod.consumeMData.getAppFn.isConstOf `Prod)
        | _, _ => false
      else false
    if qfHit then true
    else match e' with
      | .forallE _ dom body _ =>
        let domFinHit :=
          if isFinTypeExpr pairs fuel dom then
            let c := body.consumeMData
            if c.getAppFn.isConstOf `Prod then false
            else if c.isConstOf `Real || c.isConstOf `Complex || c.isConstOf `Rat || c.isConstOf `Nat || c.isConstOf `Int then true
            else match c with
              | .bvar k => binderHasScalarClass k binders
              | _ => false
          else false
        domFinHit || hasCoordFinExpr pairs fuel binders dom || hasCoordFinExpr pairs fuel (dom :: binders) body
      | .app f a => hasCoordFinExpr pairs fuel binders f || hasCoordFinExpr pairs fuel binders a
      | .lam _ t b _ => hasCoordFinExpr pairs fuel binders t || hasCoordFinExpr pairs fuel (t :: binders) b
      | .letE _ t v b _ => hasCoordFinExpr pairs fuel binders t || hasCoordFinExpr pairs fuel binders v || hasCoordFinExpr pairs fuel (t :: binders) b
      | .proj _ _ b => hasCoordFinExpr pairs fuel binders b
      | .const c _ =>
        if isInternalName c.toString then false
        else
          match pairs.find? (fun (n, _) => n == c) with
          | some (_, .defnInfo d) => hasCoordFinExpr pairs fuel [] d.type || hasCoordFinExpr pairs fuel [] d.value
          | _ => false
      | _ => false

open Lean in
private def isScalarBaseChangeExpr (e : Expr) : Bool :=
  let rec hasClifford (x : Expr) : Bool :=
    x.getUsedConstantsAsSet.any (fun u => u == `CliffordAlgebra)
  let rec hasTP (x : Expr) : Bool :=
    x.getUsedConstantsAsSet.any (fun u => u == `TensorProduct)
  let rec check (seenTP : Bool) : Expr → Option Bool
    | .mdata _ b => check seenTP b
    | .forallE _ d b _ => do
      let s1 ← check seenTP d
      check s1 b
    | .lam _ t b _ => do
      let s1 ← check seenTP t
      check s1 b
    | .letE _ t v b _ => do
      let s1 ← check seenTP t
      let s2 ← check s1 v
      check s2 b
    | .app f a =>
      let full := Expr.app f a
      if full.getAppFn.isConstOf `TensorProduct && full.getAppArgs.size >= 3 then
        let args : Array Expr := full.getAppArgs
        let lhs := (args[1]!).consumeMData
        let rhs := (args[2]!).consumeMData
        let isScal (x : Expr) : Bool :=
          !hasClifford x && !hasTP x &&
          (x.isConstOf `Complex || x.isConstOf `Real || x.isBVar || x.isFVar)
        let isCliff (x : Expr) : Bool :=
          x.getAppFn.isConstOf `CliffordAlgebra && !hasTP x
        if (isScal lhs && isCliff rhs) || (isScal rhs && isCliff lhs) then some true
        else none
      else do
        let s1 ← check seenTP f
        check s1 a
    | .proj _ _ b => check seenTP b
    | _ => some seenTP
  match check false e with
  | some true => true
  | _ => false

open Lean in
private def hasPositiveFaithful (e : Expr) : Bool :=
  match e.consumeMData with
  | .forallE _ _ (.const `False []) _ => false
  | _ => e.getUsedConstantsAsSet.any (fun u => u.toString.endsWith "DerivationLieLane.faithful")

open Lean in
private def hasFaithfulHypothesis : Expr → Bool
  | .mdata _ b => hasFaithfulHypothesis b
  | .forallE _ dom body _ =>
    if body.consumeMData.isConstOf `False then false
    else if hasPositiveFaithful dom then true
    else hasFaithfulHypothesis body
  | _ => false

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods : Array Name := #[
    {mod_lits}
  ]
  let mut modDecls : Std.HashMap Name (Array (Name × ConstantInfo)) := {{}}
  for m in mods do
    let some idx := env.getModuleIdx? m
      | throwError "Module {{m}} not loaded in Environment"
    let mdata := env.header.moduleData[idx.toNat]!
    let pairs := mdata.constNames.zip mdata.constants
    if pairs.isEmpty then
      throwError "Module {{m}} owns zero constants in Environment"
    for (name, info) in pairs do
      if info.isUnsafe || (info.isPartial && !name.toString.endsWith "_unsafe_rec") then
        throwError "Unsafe/partial constant in {{m}}: {{name}}"
      if let .axiomInfo _ := info then
        throwError "Forbidden axiom in {{m}}: {{name}}"
    modDecls := modDecls.insert m pairs
  -- R3.1 PontryaginSpace must exist as a non-abbrev structure/class whose .toKreinSpace projection type references KreinSpace
  if mods.contains `InfoGeometry.Krein.PontryaginSpace then
    let pairs := modDecls.getD `InfoGeometry.Krein.PontryaginSpace #[]
    let some (pName, pInfo) := pairs.find? (fun (n, _) =>
        n == `InfoGeometry.Krein.PontryaginSpace.PontryaginSpace || n.toString.endsWith ".PontryaginSpace")
      | throwError "R3.1 violation: InfoGeometry.Krein.PontryaginSpace exports no PontryaginSpace declaration"
    match pInfo with
    | .inductInfo _ => pure ()
    | _ => throwError "R3.1 violation: {{pName}} must be a structure/class extending KreinSpace, not an abbrev/def"
    let toKreinName := pName ++ `toKreinSpace
    let some (_, toKreinInfo) := pairs.find? (fun (n, _) => n == toKreinName)
      | throwError "R3.1 violation: {{pName}} missing .toKreinSpace parent projection"
    unless toKreinInfo.type.getUsedConstantsAsSet.any (fun u => u.toString.endsWith "KreinSpace") do
      throwError "R3.1 violation: {{toKreinName}} type does not reference KreinSpace"
  -- R3.1 KreinSpectralTriplePrimary must keep jCLM, gradeCLM/chi, and J_real as distinct non-identity, non-projection-only constants
  if mods.contains `InfoGeometry.KK.KreinSpectralTriplePrimary then
    let pairs := modDecls.getD `InfoGeometry.KK.KreinSpectralTriplePrimary #[]
    let hasKrein := pairs.any (fun (n, info) =>
      let s := n.toString
      !isInternalName s && !(env.isProjectionFn n) &&
      (s.endsWith ".jCLM" || s.contains "KreinSpace" || s.contains "kreinInner" ||
       info.type.getUsedConstantsAsSet.any (fun u =>
         let us := u.toString
         us.endsWith ".jCLM" || us.contains "KreinSpace" || us.contains "kreinInner")))
    let hasGrade := pairs.any (fun (n, info) =>
      let s := n.toString
      !isInternalName s && !(env.isProjectionFn n) &&
      (s.endsWith ".gradeCLM" || s.endsWith ".chi" || s.contains "ChiralGrading" || s.contains "KreinGradedModule" ||
       info.type.getUsedConstantsAsSet.any (fun u =>
         let us := u.toString
         us.endsWith ".gradeCLM" || us.endsWith ".chi" || us.contains "ChiralGrading" || us.contains "KreinGradedModule")))
    let hasReal := pairs.any (fun (n, info) =>
      let s := n.toString
      !isInternalName s && !(env.isProjectionFn n) &&
      (s.endsWith ".J_real" || s.contains "RealStructure" || s.contains "PhaseRealStructure" ||
       info.type.getUsedConstantsAsSet.any (fun u =>
         let us := u.toString
         us.endsWith ".J_real" || us.contains "RealStructure" || us.contains "PhaseRealStructure")))
    unless hasKrein && hasGrade && hasReal do
      throwError "R3.1 violation: KreinSpectralTriplePrimary must export distinct non-projection jCLM, gradeCLM/chi, and J_real"
    for (n, info) in pairs do
      let s := n.toString
      if !(env.isProjectionFn n) then
        if let .defnInfo dinfo := info then
          let expandedVal := expandExprConsts pairs 4 dinfo.value.getUsedConstantsAsSet
          let (_, unwrappedBody) := stripLamsAndMData 0 dinfo.value
          let headName := match unwrappedBody.getAppFn with | .const cn _ => cn.toString | _ => ""
          if s.endsWith ".jCLM" then
            if isIdentityExpr pairs 4 dinfo.value then
              throwError "R3.1 violation: {{n}} collapses jCLM to identity"
          if s.endsWith ".gradeCLM" || s.endsWith ".chi" then
            if isIdentityExpr pairs 4 dinfo.value then
              throwError "R3.1 violation: {{n}} collapses grading to identity"
            if headName.endsWith ".jCLM" || (expandedVal.any (fun u => u.toString.endsWith ".jCLM") && !expandedVal.any (fun u => u.toString.contains "grade" || u.toString.contains "chi" || u.toString.contains "Grade")) then
              throwError "R3.1 violation: {{n}} collapses grading to jCLM"
          if s.endsWith ".J_real" then
            if isIdentityExpr pairs 4 dinfo.value then
              throwError "R3.1 violation: {{n}} collapses J_real to identity"
            if headName.endsWith ".jCLM" || headName.endsWith ".gradeCLM" || headName.endsWith ".chi" ||
               (expandedVal.any (fun u => u.toString.endsWith ".jCLM" || u.toString.endsWith ".gradeCLM" || u.toString.endsWith ".chi") && !expandedVal.any (fun u => u.toString.contains "Real" || u.toString.contains "real")) then
              throwError "R3.1 violation: {{n}} collapses J_real to jCLM/gradeCLM/chi"
  -- R3.1 Anchor check on ClNNFredholmBridge
  if mods.contains `InfoGeometry.KK.ClNNFredholmBridge then
    if (env.find? `InfoGeometry.KK.ClNNFredholmBridge.SplitDoubledSpace).isNone then
      throwError "R3.1 anchor violation: missing SplitDoubledSpace"
  -- R3.2 GrassmannPrimarySources intrinsic decls must not depend on InnerProductSpace/NormedAddCommGroup/NormedSpace/MetricSpace/Module.Basis/hodge
  if mods.contains `InfoGeometry.Projective.GrassmannPrimarySources then
    let pairs := modDecls.getD `InfoGeometry.Projective.GrassmannPrimarySources #[]
    for (name, info) in pairs do
      let s := name.toString
      if !isInternalName s then
        let isThm := match info with | .thmInfo _ => true | _ => false
        let typeExpanded := expandExprConsts pairs 4 info.type.getUsedConstantsAsSet
        let checkSet := match info with
          | .defnInfo d => expandExprConsts pairs 4 (info.type.getUsedConstantsAsSet ++ d.value.getUsedConstantsAsSet)
          | _ => typeExpanded
        let hasMetricClass := typeExpanded.any (fun u =>
          let us := u.toString
          us == "MetricSpace" || us == "NormedSpace" || us == "NormedAddCommGroup")
        let isExplicitHodge :=
          isThm && !hasMetricClass &&
          (s.contains "hodge" || s.contains "Hodge" || checkSet.any (fun u => u.toString.endsWith ".hodge")) &&
          (s.contains "regressive" || s.contains "Regressive" || checkSet.any (fun u => u.toString.contains "Regressive" || u.toString.contains "regressive"))
        if !isExplicitHodge then
          let targetSet := if isThm then typeExpanded else checkSet
          if targetSet.any (fun u =>
            let us := u.toString
            us == "InnerProductSpace" || us == "NormedAddCommGroup" || us == "NormedSpace" || us == "MetricSpace" || us == "Module.Basis" || us.endsWith ".hodge") then
            throwError "R3.2 violation: intrinsic Grassmann declaration {{name}} depends on metric/basis/hodge"
  -- R3.2 LipschitzWittRieszPrimary declarations must not hardcode coordinate Fin/Matrix/EuclideanSpace
  if mods.contains `InfoGeometry.Clifford.LipschitzWittRieszPrimary then
    let pairs := modDecls.getD `InfoGeometry.Clifford.LipschitzWittRieszPrimary #[]
    for (name, info) in pairs do
      let s := name.toString
      if !isInternalName s then
        let seeds := match info with
          | .defnInfo d => info.type.getUsedConstantsAsSet ++ d.value.getUsedConstantsAsSet
          | _ => info.type.getUsedConstantsAsSet
        let expanded := expandExprConsts pairs 4 seeds
        let hasMatOrEuc := expanded.any (fun u => u == `Matrix || u == `EuclideanSpace)
        let hasCoordFin := hasCoordFinExpr pairs 4 [] info.type ||
          (match info with | .defnInfo d => hasCoordFinExpr pairs 4 [] d.value | _ => false)
        if hasMatOrEuc || hasCoordFin then
          throwError "R3.2 violation: universal declaration {{name}} in LipschitzWittRieszPrimary uses hardcoded coordinate Fin/Matrix/EuclideanSpace"
  -- R3.3 KahlerHestenesJWABSPrimary must use Koszul Z/2-grading / JW parity and not ungraded TensorProduct AlgHom
  if mods.contains `InfoGeometry.Clifford.KahlerHestenesJWABSPrimary then
    let pairs := modDecls.getD `InfoGeometry.Clifford.KahlerHestenesJWABSPrimary #[]
    let hasGraded := pairs.any (fun (n, info) =>
      if isInternalName n.toString then false
      else
        let typeExpanded := expandExprConsts pairs 4 info.type.getUsedConstantsAsSet
        typeExpanded.any (fun u =>
          let us := u.toString
          us.contains "GradedTensorProduct" || us.contains "CliffordAlgebra.evenOdd" || us.endsWith ".evenOdd"))
    unless hasGraded do
      throwError "R3.3 violation: KahlerHestenesJWABSPrimary exports no typed GradedTensorProduct / evenOdd constants"
    for (name, info) in pairs do
      let s := name.toString
      if !isInternalName s then
        let typeExpanded := expandExprConsts pairs 4 info.type.getUsedConstantsAsSet
        let isAlgMorphism := typeExpanded.any (fun u => u == `AlgHom || u == `AlgEquiv)
        if isAlgMorphism then
          let tpExpanded := match info with
            | .defnInfo d => expandExprConsts pairs 4 (info.type.getUsedConstantsAsSet ++ d.value.getUsedConstantsAsSet)
            | _ => typeExpanded
          let hasUngradedTP := tpExpanded.any (fun u => u == `TensorProduct)
          let hasGradedTP := typeExpanded.any (fun u =>
            let us := u.toString
            us.contains "GradedTensorProduct" || us.contains "CliffordAlgebra.evenOdd" || us.endsWith ".evenOdd")
          let isScalarBC := isScalarBaseChangeExpr info.type
          if hasUngradedTP && !hasGradedTP && !isScalarBC then
            throwError "R3.3 violation: {{name}} uses ungraded TensorProduct in AlgHom/AlgEquiv without GradedTensorProduct/evenOdd"
  -- R3.3 Anchor check on Cl11GradedTensorMorita
  if mods.contains `InfoGeometry.Clifford.Cl11GradedTensorMorita then
    if (env.find? `InfoGeometry.Clifford.Cl11GradedTensorMorita.head_tail_supercommute).isNone then
      throwError "R3.3 anchor violation: missing head_tail_supercommute"
  -- R3.4 PeirceCartanKoszulDVPrimary core CE/Koszul declarations must not require DerivationLieLane.faithful
  if mods.contains `InfoGeometry.OperatorAlgebra.PeirceCartanKoszulDVPrimary then
    for (name, info) in modDecls.getD `InfoGeometry.OperatorAlgebra.PeirceCartanKoszulDVPrimary #[] do
      let s := name.toString
      if !isInternalName s then
        if hasFaithfulHypothesis info.type then
          throwError "R3.4 violation: declaration {{name}} requires DerivationLieLane.faithful hypothesis"
        let isExplicitNonFaithful :=
          s.contains "without_faithful" || s.contains "withoutFaithful" ||
          s.contains "nonFaithful" || s.contains "non_faithful" ||
          s.contains "noFaithful" || s.contains "no_faithful"
        if !isExplicitNonFaithful then
          let used := info.getUsedConstantsAsSet
          if used.any (fun u => u.toString.endsWith "DerivationLieLane.faithful") then
            throwError "R3.4 violation: declaration {{name}} depends on DerivationLieLane.faithful"
  -- R3.4 Anchor check on DerivationLieLane
  if mods.contains `InfoGeometry.Algebra.DerivationLieLane then
    let some info := env.find? `InfoGeometry.Algebra.LieActionLane
      | throwError "R3.4 anchor violation: missing LieActionLane"
    let used := info.getUsedConstantsAsSet
    if used.any (fun u => u.toString.endsWith "DerivationLieLane.faithful") then
      throwError "R3.4 anchor violation: LieActionLane depends on DerivationLieLane.faithful"
end E2ER3KernelAudit
"""
    ok, rc, stdout, stderr, probe_path = run_locked_lean_probe(
        "r3_kernel_audit",
        [*mod_list, "Lean.Util.CollectAxioms", "Lean.Elab.Command"],
        body,
        repo_root=repo_root,
    )
    if not ok:
        snippet = (stderr or stdout).strip()[:400]
        return CheckOutcome(
            check_id=check_id,
            tier=2,
            milestone="ALL",
            pillar="all",
            status="FAIL",
            summary=f"R3 kernel inspection failed (rc={rc}): {snippet}",
            details={"stdout": stdout, "stderr": stderr, "modules": mod_list, "probe_path": probe_path},
        )
    return CheckOutcome(
        check_id=check_id,
        tier=2,
        milestone="ALL",
        pillar="all",
        status="PASS",
        summary=f"R3 kernel ConstantInfo inspection passed across {len(mod_list)} module(s)",
        details={"modules": mod_list},
    )


def run_batched_lake_build(modules: Iterable[str], repo_root: Path = REPO_ROOT) -> CheckOutcome:
    """Tier 4: Batched serialized run_locked_lake_build.py --wait-for-build-lock --wfail (never 0 targets)."""
    mod_list = list(dict.fromkeys(modules))
    if not mod_list:
        return CheckOutcome(
            check_id="T4-LAKE-BUILD",
            tier=4,
            milestone="ALL",
            pillar="all",
            status="FAIL",
            summary="Refused to invoke run_locked_lake_build.py with 0 targets",
            details={},
        )
    proc = subprocess.run(
        [
            PYTHON_EXE,
            str(REPO_ROOT / "tools/infra/run_locked_lake_build.py"),
            "--wait-for-build-lock",
            "--wfail",
            *mod_list,
        ],
        cwd=repo_root,
        capture_output=True,
        text=True,
        timeout=3600,
        check=False,
    )
    ok = proc.returncode == 0
    snippet = (proc.stderr or proc.stdout).strip()[-500:]
    return CheckOutcome(
        check_id="T4-LAKE-BUILD",
        tier=4,
        milestone="ALL",
        pillar="all",
        status="PASS" if ok else "FAIL",
        summary=f"Batched Lake build (--wfail) ok for {len(mod_list)} module(s)" if ok else f"Lake build failed (rc={proc.returncode}): {snippet}",
        details={"modules": mod_list, "returncode": proc.returncode},
    )


def _extract_leading_json_list(stdout: str) -> list[dict[str, Any]]:
    decoder = json.JSONDecoder()
    pos = 0
    while True:
        idx = stdout.find("[", pos)
        if idx == -1:
            break
        try:
            data, _ = decoder.raw_decode(stdout, idx)
        except json.JSONDecodeError:
            pos = idx + 1
            continue
        if isinstance(data, list) and all(isinstance(x, dict) for x in data):
            return data
        pos = idx + 1
    raise ValueError(f"Could not parse JSON list from stdout: {stdout[:250]!r}")


def _extract_trailing_json(stdout: str) -> dict[str, Any]:
    decoder = json.JSONDecoder()
    objs: list[tuple[dict[str, Any], int]] = []
    pos = 0
    n = len(stdout)
    while pos < n:
        idx = stdout.find("{", pos)
        if idx == -1:
            break
        # Only attempt decode at line-leading `{` (or start of stdout) to avoid matching `{` in prose
        line_start = stdout.rfind("\n", 0, idx) + 1
        if stdout[line_start:idx].strip():
            pos = idx + 1
            continue
        try:
            data, end_idx = decoder.raw_decode(stdout, idx)
        except json.JSONDecodeError:
            pos = idx + 1
            continue
        if isinstance(data, dict):
            objs.append((data, end_idx))
        pos = end_idx
    if not objs:
        raise ValueError(f"Could not parse trailing JSON object from stdout: {stdout[:250]!r}")
    if len(objs) > 1:
        raise ValueError(f"Multiple JSON objects found in axiom_index stdout ({len(objs)})")
    data, end_idx = objs[0]
    trailing = stdout[end_idx:].strip()
    if trailing:
        raise ValueError(f"Unexpected trailing text after JSON object: {trailing[:120]!r}")
    return data


_AXIOM_INDEX_LINE_RX = re.compile(
    r"^\s*\[\d+/\d+\]\s+(\S+):\s+([✓!])\s+(\d+)\s+decls,\s+(\d+)✗\s+(\d+)p\s+(\d+)u\s*$"
)
_AXIOM_INDEX_ERR_RX = re.compile(r"^\s*\[\d+/\d+\]\s+(\S+):\s+ERROR\s+(.+)$")


def parse_axiom_index_output(stdout: str, expected_modules: list[str]) -> tuple[bool, str, dict[str, Any]]:
    """Strictly parse axiom_index.py --json stdout, checking JSON + per-module decls/nstd/npart/nunsafe lines."""
    data = _extract_trailing_json(stdout)
    axiom_usage = data.get("axiom_usage")
    suspicious = data.get("suspicious")
    reported_modules = data.get("modules")
    if not isinstance(axiom_usage, dict):
        raise ValueError("axiom_index JSON missing dict 'axiom_usage'")
    if not isinstance(suspicious, dict):
        raise ValueError("axiom_index JSON missing dict 'suspicious'")

    disallowed = sorted(set(axiom_usage.keys()) - ALLOWED_AXIOMS)
    bad_lines: list[str] = []
    error_lines: list[str] = []
    seen_modules: set[str] = set()
    per_module: dict[str, dict[str, Any]] = {}

    for ln in stdout.splitlines():
        m_err = _AXIOM_INDEX_ERR_RX.match(ln)
        if m_err:
            mod, msg = m_err.groups()
            error_lines.append(f"{mod}: {msg.strip()}")
            continue
        m = _AXIOM_INDEX_LINE_RX.match(ln)
        if m:
            mod, sym, decls_s, nstd_s, npart_s, nunsafe_s = m.groups()
            decls_i, nstd_i, npart_i, nunsafe_i = int(decls_s), int(nstd_s), int(npart_s), int(nunsafe_s)
            seen_modules.add(mod)
            per_module[mod] = {
                "symbol": sym,
                "decls": decls_i,
                "nstd": nstd_i,
                "npart": npart_i,
                "nunsafe": nunsafe_i,
            }
            if decls_i == 0:
                bad_lines.append(f"{mod}(0 decls)")
            elif sym != "✓" or nstd_i > 0 or npart_i > 0 or nunsafe_i > 0:
                bad_lines.append(f"{mod}({sym},nstd={nstd_i},p={npart_i},u={nunsafe_i})")

    reported_decls = data.get("declarations")
    sum_module_decls = sum(v["decls"] for v in per_module.values())
    missing_modules = [m for m in expected_modules if m not in seen_modules]
    extra_modules = sorted(seen_modules - set(expected_modules))
    count_mismatch = (
        isinstance(reported_modules, bool)
        or not isinstance(reported_modules, int)
        or reported_modules != len(expected_modules)
    )
    decls_mismatch = (
        isinstance(reported_decls, bool)
        or not isinstance(reported_decls, int)
        or reported_decls != sum_module_decls
    )
    ok = (
        not disallowed
        and not suspicious
        and not bad_lines
        and not error_lines
        and not missing_modules
        and not extra_modules
        and not count_mismatch
        and not decls_mismatch
    )
    details = {
        **data,
        "per_module": per_module,
        "missing_modules": missing_modules,
        "extra_modules": extra_modules,
        "bad_lines": bad_lines,
        "error_lines": error_lines,
        "decls_mismatch": decls_mismatch,
    }
    summary = (
        f"axiom_index ok ({len(expected_modules)} modules, decls={data.get('declarations', '?')}, axioms={sorted(axiom_usage.keys())})"
        if ok
        else (
            f"axiom_index violation: disallowed={disallowed}, suspicious={list(suspicious.keys())}, "
            f"bad={bad_lines}, errors={error_lines}, missing={missing_modules}, extra={extra_modules}, "
            f"modules_count={reported_modules}/{len(expected_modules)}, decls={reported_decls}/{sum_module_decls}"
        )
    )
    return ok, summary, details


def run_olean_axiom_audits(
    modules: Iterable[str],
    repo_root: Path = REPO_ROOT,
    *,
    deep_replay: bool = False,
) -> list[CheckOutcome]:
    """Tier 4: Exhaustive .olean kernel audit via compiled axiom_index.py (optional --deep-replay axiom_check.py)."""
    mod_list = list(dict.fromkeys(modules))
    if not mod_list:
        return []
    outcomes: list[CheckOutcome] = []

    ai = subprocess.run(
        [PYTHON_EXE, str(REPO_ROOT / "tools/infra/axiom_index.py"), "--batch", "0", "--timeout", "600", "--json", *mod_list],
        cwd=repo_root,
        capture_output=True,
        text=True,
        timeout=900,
        check=False,
    )
    ai_ok = False
    ai_details: dict[str, Any] = {}
    ai_summary = ""
    if ai.returncode != 0:
        ai_summary = f"axiom_index error (rc={ai.returncode}): {(ai.stderr or ai.stdout).strip()[:240]}"
        ai_details = {"returncode": ai.returncode, "stdout": ai.stdout[-1000:], "stderr": ai.stderr[-1000:]}
    else:
        try:
            ai_ok, ai_summary, ai_details = parse_axiom_index_output(ai.stdout, mod_list)
        except Exception as exc:
            ai_summary = f"axiom_index JSON/output parse failure: {exc}"
            ai_details = {"stdout": ai.stdout[-1000:], "stderr": ai.stderr[-1000:]}

    outcomes.append(
        CheckOutcome(
            check_id="T4-OLEAN-AXIOM-INDEX",
            tier=4,
            milestone="ALL",
            pillar="all",
            status="PASS" if ai_ok else "FAIL",
            summary=ai_summary,
            details=ai_details,
        )
    )

    if deep_replay:
        # Optional slow independent replay check via axiom_check.py (only when explicitly requested)
        with BuildLock(DEFAULT_BUILD_LOCK_PATH, "primary_sources_e2e_axiom_check", block=True, shared=False):
            pass

        ac = subprocess.run(
            [PYTHON_EXE, str(REPO_ROOT / "tools/infra/axiom_check.py"), "--quiet", "--json", "--batch-size", "1", *mod_list],
            cwd=repo_root,
            capture_output=True,
            text=True,
            timeout=2400,
            check=False,
        )
        ac_entries = _extract_leading_json_list(ac.stdout) if ac.stdout.strip() else []
        ac_failed = [e for e in ac_entries if not bool(e.get("passed"))]
        ac_ok = ac.returncode == 0 and len(ac_entries) == len(mod_list) and not ac_failed
        outcomes.append(
            CheckOutcome(
                check_id="T4-OLEAN-AXIOM-CHECK",
                tier=4,
                milestone="ALL",
                pillar="all",
                status="PASS" if ac_ok else "FAIL",
                summary=(
                    f"axiom_check ok across {len(ac_entries)}/{len(mod_list)} module(s)"
                    if ac_ok
                    else f"axiom_check failed (rc={ac.returncode}, failed={[e.get('module') for e in ac_failed]}): {(ac.stderr or ac.stdout).strip()[:240]}"
                ),
                details={"entries": ac_entries},
            )
        )

    return outcomes


def run_print_axioms_probe(
    rel_paths: Iterable[str],
    *,
    repo_root: Path = REPO_ROOT,
    require_nonempty_theorems: bool = True,
) -> CheckOutcome:
    """Tier 4: Automated #print axioms <fqn> probe on every public theorem/lemma, parsed fail-closed."""
    files = [r for r in dict.fromkeys(rel_paths) if (repo_root / r).is_file()]
    if not files:
        return CheckOutcome(
            check_id="T4-PRINT-AXIOMS-PROBE",
            tier=4,
            milestone="ALL",
            pillar="all",
            status="PASS",
            summary="No target Lean files present for #print axioms probe",
            details={},
        )

    failures: list[str] = []
    total_theorems = 0
    per_file_counts: dict[str, int] = {}

    for rel in files:
        mod = lean_path_to_module(rel)
        raw = (repo_root / rel).read_text(encoding="utf-8", errors="replace")
        decls = parse_lean_declarations(raw)
        thms = [d.fqn for d in decls if not d.is_private and d.kind in {"theorem", "lemma"}]
        # Deduplicate while preserving order
        thms = list(dict.fromkeys(thms))
        per_file_counts[rel] = len(thms)
        if not thms:
            if require_nonempty_theorems:
                failures.append(f"{rel}: zero public theorems/lemmas extracted")
            continue

        # Batch up to 60 #print axioms lines per probe invocation
        for batch_idx in range(0, len(thms), 60):
            batch = thms[batch_idx : batch_idx + 60]
            cmds = "\n".join(f"#print axioms {fqn}" for fqn in batch)
            ok, rc, stdout, stderr, _ = run_locked_lean_probe(
                f"print_axioms_{mod.replace('.', '_')}_{batch_idx}",
                [mod],
                cmds,
                repo_root=repo_root,
            )
            if not ok:
                failures.append(f"{rel} (batch {batch_idx}): run_locked_lean rc={rc}: {(stderr or stdout).strip()[-400:]}")
                continue
            parsed, parse_errors = parse_axiom_audit_output(stdout, batch)
            if parse_errors:
                failures.append(f"{rel}: parse_axiom_audit_output errors: {parse_errors[:5]}")
                continue
            for decl_name, axioms in parsed.items():
                bad_axioms = sorted(set(axioms) - ALLOWED_AXIOMS)
                if bad_axioms:
                    failures.append(f"{rel}: {decl_name} uses disallowed axioms {bad_axioms}")
            total_theorems += len(parsed)

    if failures:
        return CheckOutcome(
            check_id="T4-PRINT-AXIOMS-PROBE",
            tier=4,
            milestone="ALL",
            pillar="all",
            status="FAIL",
            summary="; ".join(failures[:4]),
            details={"failures": failures, "per_file_counts": per_file_counts},
        )
    return CheckOutcome(
        check_id="T4-PRINT-AXIOMS-PROBE",
        tier=4,
        milestone="ALL",
        pillar="all",
        status="PASS",
        summary=f"#print axioms verified {total_theorems} public theorem(s)/lemma(s) across {len(files)} file(s) (axioms ⊆ {sorted(ALLOWED_AXIOMS)})",
        details={"total_theorems": total_theorems, "per_file_counts": per_file_counts},
    )
