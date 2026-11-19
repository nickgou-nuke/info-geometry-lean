"""Lean 4 kernel probe generator & locked-elaboration runner.

All Lean probes are materialized exclusively under scratch/e2e_reconciliation/probes/
(never under tests/, so tests/test_default_lean_sources.py remains clean) and
elaborated via `python3 tools/infra/run_locked_lean.py` (LOCK_SH, wait=True).
"""

from __future__ import annotations

import hashlib
import re
import subprocess
import sys
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Any

from tests.reconciliation_e2e import PROBES_DIR, REPO_ROOT
from tests.reconciliation_e2e.quality_runner import (
    check_apache_headers,
    check_native_decide,
    check_prop_wrappers,
    lean_path_to_module,
)
from tools.infra.opengauss_screener import _strip_lean_comments_and_strings
from tools.quality.proof_proxy_staged_gate import REQUIRED_LEAN_COPYRIGHT_HEADER

PYTHON_EXE: str = sys.executable


@dataclass
class ProbeResult:
    probe_id: str
    passed: bool
    returncode: int
    probe_path: str
    summary: str
    stdout: str = ""
    stderr: str = ""
    matched_files: tuple[str, ...] = ()


@dataclass(frozen=True)
class LeanDecl:
    fqn: str
    short_name: str
    kind: str
    is_private: bool
    start_line: int
    end_line: int
    header_text: str
    block_text: str


_PROBE_CACHE: dict[tuple[str, str], ProbeResult] = {}
_ALL_LEAN_PATHS_CACHE: list[str] | None = None
_STRIPPED_CACHE: dict[str, str] = {}
_DECLS_CACHE: dict[str, list[LeanDecl]] = {}

_BARREL_FILENAMES: frozenset[str] = frozenset({"All.lean", "AllExhaustive.lean"})

_LEAN_IDENT_SEG = r"(?:«[^»\n]+»|[^\W\d][^\s:({\[⦃=.,]*)"
_LEAN_NAME = rf"{_LEAN_IDENT_SEG}(?:\.{_LEAN_IDENT_SEG})*"
_DECL_MOD_ONLY_RX = re.compile(
    r"^[ \t]{0,4}(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s*)*$"
)
_DECL_START_RX = re.compile(
    r"^[ \t]{0,4}(?:@\[[^\]]*\]\s*)*"
    r"(?:(?P<priv>private)\s+|protected\s+|noncomputable\s+|unsafe\s+|partial\s+|scoped\s+|local\s+)*"
    r"(?P<kind>def|abbrev|theorem|lemma|structure|class|inductive|instance|opaque)\s+"
    rf"(?P<name>{_LEAN_NAME})"
)
_NS_RX = re.compile(rf"^[ \t]{{0,4}}namespace\s+({_LEAN_NAME})\s*$")
_SEC_RX = re.compile(
    rf"^[ \t]{{0,4}}(?:noncomputable\s+|private\s+|protected\s+)?section(?:\s+({_LEAN_NAME}))?\s*$"
)
_END_RX = re.compile(rf"^[ \t]{{0,4}}end(?:\s+({_LEAN_NAME}))?\s*$")
_MUTUAL_RX = re.compile(
    r"^[ \t]{0,4}(?:noncomputable\s+|private\s+|protected\s+)?mutual\s*$"
)


def _render_probe_source(imports: list[str], body: str) -> str:
    import_lines = "\n".join(f"import {mod}" for mod in imports)
    return (
        f"{REQUIRED_LEAN_COPYRIGHT_HEADER}"
        f"{import_lines}\n"
        "import Lean.Util.CollectAxioms\n"
        "import Lean.Elab.Command\n\n"
        f"{body.strip()}\n"
    )


def _axiom_audit_cmd(decl_names: list[str]) -> str:
    quoted = ",\n    ".join(f"`{name}" for name in decl_names)
    return (
        "section E2EAxiomAudit\n"
        "open Lean Elab Command in\n"
        "run_cmd do\n"
        "  let env ← getEnv\n"
        "  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]\n"
        "  let decls : Array Name := #[\n"
        f"    {quoted}\n"
        "  ]\n"
        "  for name in decls do\n"
        "    let some info := env.find? name\n"
        "      | throwError \"Missing declaration in environment: {name}\"\n"
        "    if info.isUnsafe || info.isPartial then\n"
        "      throwError \"Unsafe or partial declaration: {name}\"\n"
        "    let axioms ← Lean.collectAxioms name\n"
        "    for ax in axioms do\n"
        "      unless allowed.contains ax do\n"
        "        throwError \"Disallowed axiom {ax} in {name}\"\n"
        "end E2EAxiomAudit\n"
    )


def run_probe(probe_id: str, imports: list[str], body: str, *, use_cache: bool = True) -> ProbeResult:
    source = _render_probe_source(imports, body)
    cache_key = (probe_id, hashlib.sha256(source.encode("utf-8")).hexdigest())
    if use_cache and cache_key in _PROBE_CACHE:
        return _PROBE_CACHE[cache_key]

    PROBES_DIR.mkdir(parents=True, exist_ok=True)
    probe_path = PROBES_DIR / f"{probe_id}.lean"
    probe_path.write_text(source, encoding="utf-8")

    # Enforce probe hygiene locally before invoking Lean
    hdr = check_apache_headers([probe_path], strict_all=True)
    if not hdr.passed:
        res = ProbeResult(
            probe_id=probe_id,
            passed=False,
            returncode=1,
            probe_path=probe_path.relative_to(REPO_ROOT).as_posix(),
            summary=f"Probe header check failed: {hdr.summary}",
        )
        if use_cache:
            _PROBE_CACHE[cache_key] = res
        return res
    nd = check_native_decide([probe_path])
    if not nd.passed:
        res = ProbeResult(
            probe_id=probe_id,
            passed=False,
            returncode=1,
            probe_path=probe_path.relative_to(REPO_ROOT).as_posix(),
            summary=f"Probe native_decide check failed: {nd.summary}",
        )
        if use_cache:
            _PROBE_CACHE[cache_key] = res
        return res
    pw = check_prop_wrappers([probe_path])
    if not pw.passed:
        res = ProbeResult(
            probe_id=probe_id,
            passed=False,
            returncode=1,
            probe_path=probe_path.relative_to(REPO_ROOT).as_posix(),
            summary=f"Probe Prop-wrapper check failed: {pw.summary}",
        )
        if use_cache:
            _PROBE_CACHE[cache_key] = res
        return res

    rel_probe = probe_path.relative_to(REPO_ROOT).as_posix()
    proc = subprocess.run(
        [PYTHON_EXE, "tools/infra/run_locked_lean.py", rel_probe],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=2400,
        check=False,
    )
    passed = proc.returncode == 0
    snippet = (proc.stderr or proc.stdout or "").strip()
    if len(snippet) > 600:
        snippet = snippet[:600] + "..."
    res = ProbeResult(
        probe_id=probe_id,
        passed=passed,
        returncode=proc.returncode,
        probe_path=rel_probe,
        summary="ok" if passed else f"run_locked_lean rc={proc.returncode}: {snippet}",
        stdout=proc.stdout,
        stderr=proc.stderr,
    )
    if use_cache:
        _PROBE_CACHE[cache_key] = res
    return res


def run_r1_baseline_probe() -> ProbeResult:
    imports = [
        "InfoGeometry.OperatorAlgebra.DerivationDifferentialForms",
        "InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms",
        "InfoGeometry.OperatorAlgebra.MaurerCartanFrameTransport",
        "InfoGeometry.OperatorAlgebra.DerivationRightLogarithmicForm",
        "InfoGeometry.NCG.NoncommutativeConnectionCurvature",
        "InfoGeometry.Thermo.OnsagerDifferentialFormsBridge",
        "InfoGeometry.Optics.OperatorDerivationForms",
        "InfoGeometry.Canonical.CEBKMOnsagerGibbsNOperatorFamily",
        "InfoGeometry.Canonical.OperatorFrechetForms",
        "InfoGeometry.Canonical.OperatorFrechetDerivationJet",
        "InfoGeometry.Canonical.FrechetCECovariantConnection",
        "InfoGeometry.Algebra.DerivationLieLane",
        "InfoGeometry.Canonical.CEOneFormNOperatorBridge",
        "InfoGeometry.OperatorAlgebra.OperatorExteriorAlgebraGeneral",
    ]
    audited_decls = [
        "InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.oneFormAlternatingEquiv",
        "InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.exteriorDerivativeZero",
        "InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.exteriorDerivativeOne",
        "InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.exteriorDerivativeTwo",
        "InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.connectionCurvature_bianchi",
        "InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms.differential_mul",
        "InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms.oneForms_addHom_ext",
        "InfoGeometry.OperatorAlgebra.MaurerCartanFrameTransport.gaugeForm_product",
        "InfoGeometry.OperatorAlgebra.MaurerCartanFrameTransport.gaugeForm_flat",
        "InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.gaugeOneForm_zero_eq_neg_rightLogarithmicOneForm",
        "InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.rightLogarithmicOneForm_maurerCartan",
        "InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm_eq_neg",
        "InfoGeometry.NCG.AlgebraDerivation.maurer_cartan_flatness",
        "InfoGeometry.Thermo.OnsagerFormsBridge.onsager_casimir_1Form_master_reciprocity",
        "InfoGeometry.Thermo.OnsagerFormsBridge.reversible1Form_diag_zero",
        "InfoGeometry.Thermo.OnsagerFormsBridge.totalGenerator1Form_nonneg",
        "InfoGeometry.Canonical.CEBKMOnsagerGibbsNOperatorFamily.finiteGibbsCEFamilyNOperatorSystem_pairwise_eq_dissipation_hessian",
        "InfoGeometry.Canonical.OperatorFrechetForms.ExchangeInvolution.even_odd",
        "InfoGeometry.Canonical.OperatorFrechetForms.ExchangeInvolution.odd_even",
        "InfoGeometry.Canonical.OperatorFrechetDerivationJet.operatorFrechetJet_one_apply_eq_exteriorDerivativeZero",
        "InfoGeometry.Canonical.FrechetCECovariantConnection.covariantFrechet_eq_ce",
        "InfoGeometry.Algebra.LieActionLane.operatorAction_commutator_apply",
        "InfoGeometry.Algebra.DerivationLieLane.operatorAction_map_lie",
        "InfoGeometry.Canonical.CEOneFormNOperatorBridge.ofCEFamily",
        "InfoGeometry.Canonical.CEOneFormNOperatorBridge.component",
        "InfoGeometry.OperatorAlgebra.General.TransportTensor.onsager_casimir_reciprocity_exact",
    ]
    body = f"""
noncomputable section
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms
open InfoGeometry.OperatorAlgebra.MaurerCartanFrameTransport
open InfoGeometry.Thermo.OnsagerFormsBridge
open InfoGeometry.Optics.OperatorDerivationForms
open InfoGeometry.Canonical.CEBKMOnsagerGibbsNOperatorFamily
open InfoGeometry.Canonical.OperatorFrechetForms
open InfoGeometry.Canonical.OperatorFrechetDerivationJet
open InfoGeometry.Canonical.FrechetCECovariantConnection
open InfoGeometry.Algebra
open InfoGeometry.Canonical.CEOneFormNOperatorBridge
open InfoGeometry.OperatorAlgebra.General

#check @oneFormAlternatingEquiv
#check @exteriorDerivativeZero
#check @exteriorDerivativeOne
#check @exteriorDerivativeTwo
#check @connectionCurvature_bianchi
#check @differential_mul
#check @gaugeForm_product
#check @gaugeForm_flat
#check @gaugeOneForm_zero_eq_neg_rightLogarithmicOneForm
#check @InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm_eq_neg
#check @InfoGeometry.NCG.AlgebraDerivation.maurer_cartan_flatness
#check @onsager_casimir_1Form_master_reciprocity
#check @finiteGibbsCEFamilyNOperatorSystem_pairwise_eq_dissipation_hessian
#check @ExchangeInvolution.even_odd
#check @ExchangeInvolution.odd_even
#check @LieActionLane.operatorAction_commutator_apply
#check @DerivationLieLane.operatorAction_map_lie

-- Non-vacuous noncommuting 2x2 real matrix universal 1-form Leibniz witness
example :
    ∃ a b : Matrix (Fin 2) (Fin 2) ℝ,
      a * b ≠ b * a ∧
      leftDifferentialTensor (Matrix (Fin 2) (Fin 2) ℝ) a b ≠
        leftDifferentialTensor (Matrix (Fin 2) (Fin 2) ℝ) b a := by
  let a : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
  let b : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
  have ha : a * b = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [a, b, Matrix.mul_apply, Fin.sum_univ_two]
  have hb : b * a = a := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [a, b, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨a, b, ?_, ?_⟩
  · rw [ha, hb]
    intro hz
    have h01 := congr_fun (congr_fun hz 0) 1
    simp [a] at h01
  · intro h
    let bil : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℤ] ℝ :=
      {{ toFun := fun X =>
          {{ toFun := fun Y => X 0 1 * Y 0 0,
             map_add' := fun Y₁ Y₂ => by simp [mul_add],
             map_smul' := fun n Y => by simp [zsmul_eq_mul]; ring }},
         map_add' := fun X₁ X₂ => by ext Y; simp [add_mul],
         map_smul' := fun n X => by ext Y; simp [zsmul_eq_mul]; ring }}
    have hs := congrArg (TensorProduct.lift bil) h
    simp [bil, leftDifferentialTensor, ha, hb, a, b] at hs
    norm_num at hs

-- Non-linear NOperatorForm 2 counterexample witness (T2-F1.6-1)
example :
    ∃ ω : NOperatorForm 2 (Point := Unit) (Tangent := ℝ) (Value := ℝ),
      ω 0 () (2 : ℝ) ≠ (2 : ℝ) • ω 0 () (1 : ℝ) := by
  let ω : NOperatorForm 2 (Point := Unit) (Tangent := ℝ) (Value := ℝ) :=
    fun _ _ x => x ^ 2
  refine ⟨ω, ?_⟩
  norm_num [ω]

-- Non-trivial ExchangeInvolution projection witness on M_2(ℝ) (T2-F1.4-5)
example :
    ∃ E : ExchangeInvolution (Matrix (Fin 2) (Fin 2) ℝ),
      ∃ x : Matrix (Fin 2) (Fin 2) ℝ,
        E.exchange x ≠ x ∧ E.exchange x ≠ -x ∧
        E.even (E.odd x) = 0 ∧ E.odd (E.even x) = 0 := by
  let trEquiv : Matrix (Fin 2) (Fin 2) ℝ ≃ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
    {{ toFun := fun M => Matrix.transpose M,
       invFun := fun M => Matrix.transpose M,
       left_inv := Matrix.transpose_transpose,
       right_inv := Matrix.transpose_transpose,
       map_add' := fun M N => Matrix.transpose_add M N,
       map_smul' := fun r M => Matrix.transpose_smul r M }}
  let E : ExchangeInvolution (Matrix (Fin 2) (Fin 2) ℝ) :=
    {{ exchange := trEquiv,
       exchange_sq := Matrix.transpose_transpose }}
  let x : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 0, 0]
  refine ⟨E, x, ?_, ?_, E.even_odd x, E.odd_even x⟩
  · intro h
    have h01 := congr_fun (congr_fun h 0) 1
    norm_num [E, trEquiv, x] at h01
  · intro h
    have h00 := congr_fun (congr_fun h 0) 0
    norm_num [E, trEquiv, x] at h00

-- Non-zero faithfulness check on DerivationLieLane vs LieActionLane (T2-F1.5-5)
example {{R A : Type*}} [CommRing R] [Ring A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    (K : DerivationLieLane R A)
    (x : K.L) (hx : K.act x = 0) : x = 0 := by
  have h0 : K.act 0 = 0 := map_zero K.act
  exact K.faithful (hx.trans h0.symm)

{_axiom_audit_cmd(audited_decls)}
"""
    return run_probe("r1_baseline_probe", imports, body, use_cache=True)


def run_r3_baseline_probe() -> ProbeResult:
    imports = [
        "InfoGeometry.Clifford.Cl11Matrix",
        "InfoGeometry.Clifford.Cl11GradedMorita",
        "InfoGeometry.Clifford.Cl11GradedTensorMorita",
        "InfoGeometry.Algebra.NoncommutativeCliffordColimitMassGapSynthesis",
        "InfoGeometry.Canonical.SplitCliffordMatrixLimitSoldering",
        "InfoGeometry.Clifford.Cl11HomogeneousChains",
        "InfoGeometry.Clifford.Cl11GradedDifferential",
        "InfoGeometry.Clifford.GradedGraceContraction",
        "InfoGeometry.Canonical.ZornDifferentialFormsCliffordBridge",
        "InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation",
        "InfoGeometry.OperatorAlgebra.ErlangenDoubleCylinderSymmetryInvariants",
    ]
    audited_decls = [
        "InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat",
        "InfoGeometry.Clifford.Cl11GradedMorita.cl11StandardEquiv",
        "InfoGeometry.Clifford.Cl11GradedTensorMorita.tensorMatrixEquiv",
        "InfoGeometry.Algebra.NoncommutativeCliffordColimitMassGapSynthesis.clInf_vacuum_stabilization_and_supertrace",
        "InfoGeometry.Canonical.SplitCliffordMatrixLimitSoldering.gradedTensorSuccessor_not_algHom",
        "InfoGeometry.Clifford.Cl11HomogeneousChains.nativeChain",
        "InfoGeometry.Clifford.Cl11HomogeneousChains.nativeChain_matrix_suffixParity",
        "InfoGeometry.Clifford.Cl11HomogeneousChains.coefficientChain_matrix_suffixParity",
        "InfoGeometry.Clifford.Cl11GradedDifferential.jwDifferential_sq",
        "InfoGeometry.Clifford.Cl11GradedDifferential.jwDifferential_homotopy",
        "InfoGeometry.Clifford.Cl11GradedDifferential.jwDifferential_ne_zero",
        "InfoGeometry.Clifford.Cl11GradedDifferential.jwDifferential_range_eq_ker",
        "InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj_idem",
        "InfoGeometry.Clifford.GradedGraceContraction.clifford_ι_injective",
        "InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj_zero_eq_algebraMap_hTrace",
        "InfoGeometry.Clifford.GradedGraceContraction.not_nonneg_cliffordKreinPairing_Q31",
        "InfoGeometry.Canonical.ZornDifferentialFormsCliffordBridge.clifford_noncomm_witness",
        "InfoGeometry.Canonical.ZornDifferentialFormsCliffordBridge.cliffordMorphism_generator_square",
        "InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation.localCl11Map",
        "InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation.cl11EquivMat_splitReflectionCliffordAuto",
        "InfoGeometry.OperatorAlgebra.ErlangenDoubleCylinderSymmetryInvariants.erlangenDoubleCylinderInvariantSubring_noncommutative",
    ]
    body = f"""
noncomputable section
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11GradedMorita
open InfoGeometry.Clifford.Cl11GradedTensorMorita
open InfoGeometry.Algebra.NoncommutativeCliffordColimitMassGapSynthesis
open InfoGeometry.Canonical.SplitCliffordMatrixLimitSoldering
open InfoGeometry.Clifford.Cl11HomogeneousChains
open InfoGeometry.Clifford.Cl11GradedDifferential
open InfoGeometry.Clifford.GradedGraceContraction
open InfoGeometry.Canonical.ZornDifferentialFormsCliffordBridge
open InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation
open InfoGeometry.OperatorAlgebra.ErlangenDoubleCylinderSymmetryInvariants

#check @cl11EquivMat
#check @cl11StandardEquiv
#check @tensorMatrixEquiv
#check @gradedTensorSuccessor_not_algHom
#check @nativeChain
#check @coefficientChain_matrix_suffixParity
#check @jwDifferential_sq
#check @jwDifferential_homotopy
#check @jwDifferential_ne_zero
#check @cliffordGradeProj_idem
#check @clifford_ι_injective
#check @not_nonneg_cliffordKreinPairing_Q31
#check @clifford_noncomm_witness

-- T2-F3.1-2: Unital diagEmbed vs non-unital bottEmbed on ClTower ℝ 0
example :
    diagEmbed (1 : ClTower ℝ 0) = (1 : ClTower ℝ 1) ∧
    bottEmbed (1 : ClTower ℝ 0) ≠ (1 : ClTower ℝ 1) := by
  refine ⟨?_, ?_⟩
  · apply ext_fin2 <;> simp [diagEmbed]
  · intro h
    have h11 := congr_fun (congr_fun h 1) 1
    simp [bottEmbed] at h11

-- T2-F3.3-1: Empty chain (n=0) and zero-head chain (n=1)
example :
    nativeChain 0 Fin.elim0 = 1 ∧
    nativeChain 1 (Fin.cons 0 Fin.elim0) = 0 := by
  exact ⟨nativeChain_zero Fin.elim0, nativeChain_zero_head 0 Fin.elim0⟩

{_axiom_audit_cmd(audited_decls)}
"""
    return run_probe("r3_baseline_probe", imports, body, use_cache=True)


def run_r2_r1r2_baseline_probe() -> ProbeResult:
    imports = [
        "InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum",
        "InfoGeometry.Erlangen.SmoothCartanGeometry",
        "InfoGeometry.Krein.DoubledSpace",
        "InfoGeometry.Krein.DoubleRealKreinShearDefect",
        "InfoGeometry.Krein.DoubledMatrixSymplectic",
        "InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis",
        "InfoGeometry.KK.ClNNFredholmBridge",
        "InfoGeometry.KK.RealSplitKreinKasparovCycle",
        "InfoGeometry.KK.RealSplitKreinUnboundedCycle",
        "InfoGeometry.KK.RealSplitKreinEquivarianceBridge",
        "InfoGeometry.Canonical.ConnesNCGFormAlgebra",
        "InfoGeometry.Algebra.KreinPeirceTowerIntertwine",
        "InfoGeometry.OperatorAlgebra.KreinFrechetRiesz",
        "InfoGeometry.OperatorAlgebra.SpectralTriple",
    ]
    audited_decls = [
        "InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum.OperatorIntertwiner.target_eq_conjugated",
        "InfoGeometry.Erlangen.SmoothCartanGeometry.gl2R_maurerCartan_flat",
        "InfoGeometry.Erlangen.SmoothCartanGeometry.homothetyCartanGeometry_curvature_formula",
        "InfoGeometry.Erlangen.SmoothCartanGeometry.cartanFiberErlangen20Datum",
        "InfoGeometry.Krein.DoubleRealKreinShearDefect.componentNReal_not_krein_isometry",
        "InfoGeometry.Krein.DoubledMatrixSymplectic.matrixAction_preserves_symplectic_iff",
        "InfoGeometry.Krein.DoubledMatrixSymplectic.componentNReal_preserves_symplectic",
        "InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis.kreinMetric88_properties",
        "InfoGeometry.KK.ClNNFredholmBridge.RealSplitKreinKasparovCycle.firstStep_leftGenerator_eq_cl11Rep",
        "InfoGeometry.KK.RealSplitKreinKasparovCycle.superComm_pi_compact",
        "InfoGeometry.KK.RealSplitKreinEquivarianceBridge.action_preserves_compact_phase_defects",
        "InfoGeometry.Canonical.ConnesNCGFormAlgebra.ncDeriv_leibniz",
        "InfoGeometry.Algebra.KreinPeirceTowerIntertwine.peirce11_positive_sector_krein_positivity_and_bianchi",
        "InfoGeometry.Algebra.KreinPeirceTowerIntertwine.clTower_and_colimit_peirce_transport",
        "InfoGeometry.OperatorAlgebra.kreinToDual",
    ]
    body = f"""
noncomputable section
open InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum
open InfoGeometry.Erlangen.SmoothCartanGeometry
open InfoGeometry.Krein
open InfoGeometry.Krein.DoubleRealKreinShearDefect
open InfoGeometry.Krein.DoubledMatrixSymplectic
open InfoGeometry.Krein.DoubledSpaceMatrixClockBridge
open InfoGeometry.Krein.DoubledSpaceRealKANBridge
open InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis
open InfoGeometry.KK
open InfoGeometry.KK.ClNNFredholmBridge
open InfoGeometry.KK.RealSplitKreinEquivarianceBridge
open InfoGeometry.Canonical.ConnesNCGFormAlgebra
open InfoGeometry.Algebra.KreinPeirceTowerIntertwine
open InfoGeometry.OperatorAlgebra

#check @OperatorIntertwiner.target_eq_conjugated
#check @gl2R_maurerCartan_flat
#check @homothetyCartanGeometry_curvature_formula
#check @componentNReal_not_krein_isometry
#check @matrixAction_preserves_symplectic_iff
#check @kreinMetric88_properties
#check @RealSplitKreinKasparovCycle.firstStep_leftGenerator_eq_cl11Rep
#check @RealSplitKreinKasparovCycle.superComm_pi_compact
#check @action_preserves_compact_phase_defects
#check @ncDeriv_leibniz
#check @peirce11_positive_sector_krein_positivity_and_bianchi
#check @kreinToDual

-- T2-F2.2-1: Shear preserves symplecticForm yet fails Krein isometry on DoubledSpace ℝ
example :
    ¬ KreinSpace.IsKreinIsometry (ρclock (E := ℝ) (componentNReal 1)) := by
  exact componentNReal_not_krein_isometry (E := ℝ) 1 one_ne_zero (1 : ℝ) one_ne_zero

{_axiom_audit_cmd(audited_decls)}
"""
    return run_probe("r2_r1r2_baseline_probe", imports, body, use_cache=True)


def _is_barrel_file(rel: str) -> bool:
    p = Path(rel)
    return p.name in _BARREL_FILENAMES or rel in ("lean/InfoGeometry.lean", "lean/InfoGeometry/AllExhaustive.lean")


def _read_stripped_text(rel: str) -> str:
    if rel not in _STRIPPED_CACHE:
        p = REPO_ROOT / rel
        raw = p.read_text(encoding="utf-8", errors="replace")
        _STRIPPED_CACHE[rel] = _strip_lean_comments_and_strings(raw)
    return _STRIPPED_CACHE[rel]


def parse_declarations_from_text(source_text: str, *, already_stripped: bool = False) -> list[LeanDecl]:
    """Strip comments/strings, track namespace/section/end stack, and extract multi-line declarations."""
    stripped = source_text if already_stripped else _strip_lean_comments_and_strings(source_text)
    lines = stripped.splitlines()
    stack: list[tuple[str, str]] = []
    raw_entries: list[tuple[int, str, str, str, bool]] = []
    scope_boundaries: list[int] = []
    pending_private = False
    mutual_depth = 0

    for idx, line in enumerate(lines):
        s = line.strip()
        if not s:
            continue
        m_ns = _NS_RX.match(line)
        if m_ns:
            pending_private = False
            scope_boundaries.append(idx)
            for part in m_ns.group(1).split("."):
                stack.append(("ns", part))
            continue
        m_sec = _SEC_RX.match(line)
        if m_sec:
            pending_private = False
            scope_boundaries.append(idx)
            stack.append(("sec", m_sec.group(1) or ""))
            continue
        if _MUTUAL_RX.match(line):
            pending_private = False
            mutual_depth += 1
            continue
        m_end = _END_RX.match(line)
        if m_end:
            pending_private = False
            scope_boundaries.append(idx)
            target = m_end.group(1)
            if not target:
                if mutual_depth > 0:
                    mutual_depth -= 1
                elif stack:
                    stack.pop()
            else:
                for part in reversed(target.split(".")):
                    for k in range(len(stack) - 1, -1, -1):
                        if stack[k][1] == part:
                            del stack[k:]
                            break
            continue

        m_d = _DECL_START_RX.match(line)
        if m_d:
            is_priv = bool(m_d.group("priv")) or pending_private
            pending_private = False
            name = m_d.group("name")
            if name in ("where", "by", "of", "_"):
                continue
            ns = ".".join(p for kind_tag, p in stack if kind_tag == "ns")
            if name.startswith("_root_."):
                fqn = name[len("_root_."):]
            else:
                fqn = f"{ns}.{name}" if ns else name
            raw_entries.append((idx, fqn, name, m_d.group("kind"), is_priv))
            continue

        if _DECL_MOD_ONLY_RX.match(line):
            if re.search(r"\bprivate\b", s):
                pending_private = True
            continue
        pending_private = False

    boundary_set = sorted(set(scope_boundaries + [e[0] for e in raw_entries] + [len(lines)]))
    decls: list[LeanDecl] = []
    b_ptr = 0
    for start_idx, fqn, short_name, kind, is_priv in raw_entries:
        while b_ptr < len(boundary_set) and boundary_set[b_ptr] <= start_idx:
            b_ptr += 1
        end_idx = boundary_set[b_ptr] if b_ptr < len(boundary_set) else len(lines)
        block_lines = lines[start_idx:end_idx]
        block_text = "\n".join(block_lines)

        hdr_lines: list[str] = []
        for h_line in block_lines[:40]:
            m_sep = re.search(r":=|\bwhere\b", h_line)
            if m_sep:
                hdr_lines.append(h_line[: m_sep.start()])
                break
            hdr_lines.append(h_line)
        header_text = "\n".join(hdr_lines)

        decls.append(
            LeanDecl(
                fqn=fqn,
                short_name=short_name,
                kind=kind,
                is_private=is_priv,
                start_line=start_idx + 1,
                end_line=end_idx,
                header_text=header_text,
                block_text=block_text,
            )
        )
    return decls


def _parse_declarations(rel: str) -> list[LeanDecl]:
    if rel not in _DECLS_CACHE:
        stripped = _read_stripped_text(rel)
        _DECLS_CACHE[rel] = parse_declarations_from_text(stripped, already_stripped=True)
    return _DECLS_CACHE[rel]


def _decl_matches_pattern(decl: LeanDecl, pat_rx: re.Pattern[str], pat_rx_m: re.Pattern[str]) -> bool:
    norm_hdr = re.sub(r"\s+", " ", decl.header_text)
    if pat_rx.search(norm_hdr):
        return True
    if pat_rx_m.search(decl.block_text):
        return True
    return False


def _search_files_for_patterns(candidate_files: list[str], patterns: list[str]) -> tuple[list[str], dict[str, list[str]]]:
    """Scan existing non-barrel Lean files (comment/string-stripped) for required patterns."""
    existing: list[str] = []
    per_file_stripped: dict[str, str] = {}
    per_file_decls: dict[str, list[LeanDecl]] = {}
    for rel in candidate_files:
        if _is_barrel_file(rel):
            continue
        p = REPO_ROOT / rel
        if p.is_file():
            existing.append(rel)
            per_file_stripped[rel] = _read_stripped_text(rel)
            per_file_decls[rel] = [d for d in _parse_declarations(rel) if not d.is_private]

    matched: dict[str, list[str]] = {}
    for pat in patterns:
        rx_m = re.compile(pat, re.M)
        rx_s = re.compile(pat)
        hits: list[str] = []
        for rel in existing:
            if rx_m.search(per_file_stripped[rel]) or any(
                _decl_matches_pattern(d, rx_s, rx_m) for d in per_file_decls[rel]
            ):
                hits.append(rel)
        matched[pat] = hits
    return existing, matched


def _all_non_barrel_lean_paths() -> list[str]:
    global _ALL_LEAN_PATHS_CACHE
    if _ALL_LEAN_PATHS_CACHE is None:
        lean_root = REPO_ROOT / "lean" / "InfoGeometry"
        paths: list[str] = []
        for p in sorted(lean_root.rglob("*.lean")):
            if p.name in _BARREL_FILENAMES:
                continue
            rel = p.relative_to(REPO_ROOT).as_posix()
            if any(seg in rel for seg in ("/Unstable/", "/Archive/", "/tmp/")):
                continue
            if _is_barrel_file(rel):
                continue
            paths.append(rel)
        _ALL_LEAN_PATHS_CACHE = paths
    return _ALL_LEAN_PATHS_CACHE


def discover_candidate_owners(prefixes: tuple[str, ...], keywords: tuple[str, ...]) -> list[str]:
    """Discover existing + newly created non-barrel Lean owner files matching prefixes/keywords."""
    found: list[str] = []
    kw_lowers = tuple(kw.lower() for kw in keywords)
    for rel in _all_non_barrel_lean_paths():
        if (prefixes and rel.startswith(prefixes)) or (kw_lowers and any(kw in rel.lower() for kw in kw_lowers)):
            found.append(rel)
    return found


def run_milestone_contract_probe(check_id: str, spec: dict[str, Any]) -> ProbeResult:
    """Execute genuine M1/M2/M3 contract validation + Lean kernel probe for gated checks.

    Checks that:
    1. Required owner modules exist on disk (including new M1/M2/M3 files).
    2. Required mathematical signatures/theorems are present in comment-stripped non-barrel owners
       (enforcing `co_occur` when cross-pillar/bridge or candidate-free).
    3. Forbidden patterns are absent from matched owner files (or matched declarations).
    4. Concrete Lean declarations are extracted across multi-line signatures & nested namespaces
       (or explicit `target_decls` / `probe_body` is supplied) — failing closed if none resolve.
    5. A generated Lean probe importing the matched owner modules elaborates cleanly
       under `run_locked_lean.py` with zero disallowed axioms or sorry.
    """
    required_files: list[str] = [f for f in spec.get("required_files", []) if not _is_barrel_file(f)]
    candidate_files: list[str] = [f for f in spec.get("candidate_files", []) if not _is_barrel_file(f)]
    discover_prefixes: tuple[str, ...] = tuple(spec.get("discover_prefixes", ()))
    discover_keywords: tuple[str, ...] = tuple(spec.get("discover_keywords", ()))
    extra_discovered = (
        discover_candidate_owners(discover_prefixes, discover_keywords)
        if (discover_prefixes or discover_keywords)
        else []
    )
    all_candidates = list(dict.fromkeys(required_files + candidate_files + extra_discovered))

    missing_req = [f for f in required_files if not (REPO_ROOT / f).is_file()]
    if missing_req:
        return ProbeResult(
            probe_id=check_id,
            passed=False,
            returncode=1,
            probe_path="",
            summary=f"Missing required milestone file(s): {missing_req}",
        )

    required_patterns: list[str] = list(spec.get("required_patterns", []))
    co_occur: bool = (
        bool(spec["co_occur"])
        if "co_occur" in spec
        else ((not candidate_files and not required_files) or check_id.startswith("T3-"))
    )

    existing, matched = _search_files_for_patterns(all_candidates, required_patterns)
    unmatched = [pat for pat, hits in matched.items() if not hits]
    if unmatched:
        return ProbeResult(
            probe_id=check_id,
            passed=False,
            returncode=1,
            probe_path="",
            summary=(
                f"Milestone contract patterns not yet satisfied in {len(existing)} owner file(s): "
                f"{unmatched}"
            ),
        )

    common_files: list[str] = []
    if co_occur and required_patterns:
        common_files = [
            f for f in existing if all(f in matched[pat] for pat in required_patterns)
        ]
        if not common_files:
            return ProbeResult(
                probe_id=check_id,
                passed=False,
                returncode=1,
                probe_path="",
                summary=(
                    f"co_occur=True: no single non-barrel owner file matches all required patterns "
                    f"{required_patterns}"
                ),
            )

    # Select matched owner files (prioritizing required_files + common/matched owners)
    if co_occur and required_patterns:
        matched_files = list(dict.fromkeys(required_files + common_files[:4]))
    else:
        matched_files = list(dict.fromkeys(
            required_files + [f for hits in matched.values() for f in hits[:2]]
        ))
        if not matched_files:
            matched_files = existing[:4]

    # Extract exact qualified names across matched owners (respecting explicit target_decls).
    # Collect ALL matching non-private declarations into matched_decls for forbidden_scope="decl",
    # while keeping the 2-declaration-per-pattern cap solely for #check / E2EAxiomAudit output.
    decl_names: list[str] = list(spec.get("target_decls", []))
    matched_decls: list[LeanDecl] = []
    seen_matched_decl_keys: set[tuple[str, int, str]] = set()
    for rel in matched_files:
        file_decls = [d for d in _parse_declarations(rel) if not d.is_private]
        check_eligible = rel in matched_files[:6]
        for pat in required_patterns:
            pat_rx = re.compile(pat)
            pat_rx_m = re.compile(pat, re.M)
            found_for_pat = 0
            for d in file_decls:
                if _decl_matches_pattern(d, pat_rx, pat_rx_m):
                    d_key = (rel, d.start_line, d.fqn)
                    if d_key not in seen_matched_decl_keys:
                        seen_matched_decl_keys.add(d_key)
                        matched_decls.append(d)
                    if check_eligible and found_for_pat < 2:
                        if d.fqn not in decl_names:
                            decl_names.append(d.fqn)
                        found_for_pat += 1

    # Check optional forbidden patterns in comment-stripped matched owner files (or matched decls)
    forbidden_patterns: list[str] = list(spec.get("forbidden_patterns", []))
    if forbidden_patterns:
        f_scope = spec.get("forbidden_scope", "file")
        if f_scope == "decl" and matched_decls:
            f_hits: dict[str, list[str]] = {}
            for pat in forbidden_patterns:
                rx = re.compile(pat, re.M)
                bad_decls = [d.fqn for d in matched_decls if rx.search(d.block_text)]
                if bad_decls:
                    f_hits[pat] = bad_decls
        else:
            _, f_matched = _search_files_for_patterns(matched_files or required_files or existing, forbidden_patterns)
            f_hits = {pat: hits for pat, hits in f_matched.items() if hits}
        if f_hits:
            return ProbeResult(
                probe_id=check_id,
                passed=False,
                returncode=1,
                probe_path="",
                summary=f"Forbidden pattern(s) detected: {f_hits}",
                matched_files=tuple(matched_files),
            )

    probe_body = spec.get("probe_body")
    if not probe_body and not decl_names:
        return ProbeResult(
            probe_id=check_id,
            passed=False,
            returncode=1,
            probe_path="",
            summary=(
                "No concrete Lean declarations extracted to #check and axiom-audit "
                f"(patterns={required_patterns}, matched_files={matched_files})"
            ),
            matched_files=tuple(matched_files),
        )

    probe_imports = [lean_path_to_module(f) for f in matched_files[:8]]
    if not probe_body:
        checks = "\n".join(f"#check @{d}" for d in decl_names[:12])
        audit = _axiom_audit_cmd(decl_names[:12])
        probe_body = f"noncomputable section\n{checks}\n{audit}\n"
    elif decl_names and "E2EAxiomAudit" not in probe_body:
        probe_body = f"{probe_body.rstrip()}\n\n{_axiom_audit_cmd(decl_names[:12])}\n"

    res = run_probe(f"contract_{check_id.replace('-', '_')}", probe_imports, probe_body, use_cache=True)
    return replace(res, matched_files=tuple(matched_files))
