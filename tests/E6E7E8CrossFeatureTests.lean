/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3ZornE6RootSystem
import InfoGeometry.Algebra.H3ZornE6Simplicity
import InfoGeometry.Algebra.H3ZornE6SerreHom
import InfoGeometry.Algebra.H3OctonionZornComplexification
import InfoGeometry.Algebra.H3ZornF4Simplicity
import InfoGeometry.Algebra.H3OctonionSimplicity
import InfoGeometry.Algebra.H3ZornE6ChevalleyBruhat
import InfoGeometry.Algebra.H3ZornMinusculeCFSGBridge
import InfoGeometry.Algebra.H3ZornF4DimensionClosure
import InfoGeometry.Algebra.H3ZornReducedStructureLieAlgebra
import InfoGeometry.Algebra.H3ZornStructureGroup
import InfoGeometry.Algebra.CompactOctonion
import InfoGeometry.Algebra.H3Octonion
import InfoGeometry.Algebra.H3OctonionStructureGroup
import InfoGeometry.Algebra.H3OctonionLieAlgebra
import InfoGeometry.Canonical.H3ZornJordanTripleBridge
import InfoGeometry.Canonical.H3ZornTKKNative
import InfoGeometry.Algebra.H3ZornFreudenthalQuartic
import InfoGeometry.Algebra.H3ZornFreudenthalScaling
import InfoGeometry.Algebra.H3ZornFreudenthalQuarticPolarization
import InfoGeometry.Algebra.H3ZornFreudenthalLeviAction
import InfoGeometry.Algebra.H3ZornFreudenthalE7Group
import InfoGeometry.Exceptional.FreudenthalChargeLinear
import InfoGeometry.Canonical.NativeTitsE8Carrier
import InfoGeometry.Canonical.SplitFreudenthalTitsE8Carrier
import InfoGeometry.Lie.CanonicalZornIsKilling
import InfoGeometry.Lie.SplitG2RealFormCapstone
import InfoGeometry.Lie.SplitOctonionStandardDerivation
import InfoGeometry.Algebra.JordanTKKLieAlgebra
import InfoGeometry.Canonical.H3ZornTKKLieAlgebra
import InfoGeometry.Algebra.H3OctonionTKKLieAlgebra
import InfoGeometry.Algebra.H3ZornE7RootSystem
import InfoGeometry.Algebra.H3ZornE7Simplicity
import InfoGeometry.Algebra.MagicSquareTitsBracket
import InfoGeometry.Algebra.SplitE8RootSystem
import InfoGeometry.Algebra.SplitE8Simplicity

/-!
# E2E Baseline Cross-Feature & End-to-End Scenario Tests (`E₆` / `E₇` / `E₈`)

Covers all `[IMMEDIATE]` Tier 3 pairwise cross-feature interactions and Tier 4
end-to-end baseline mathematical scenarios across existing verified owners:
- Tier 3: `E₆` `str₀` (78D) ⊂ `str` (79D), `Str/Str₀ ≃* ℝˣ`, `Aut ⊂ Str₀` strict inclusion,
  split vs compact Albert non-isomorphism + Killing trace-square separation,
  `F₄ ↪ E₆` + Chevalley degree-2 nilpotency, TKK/Freudenthal/cubic-norm bridge,
  and Tits `E₈` 248D carrier pairing `G₂(2)` Killing + `F₄(4)` 52D
- Tier 4: Exceptional tower dimensions (`8 < 14 < 27 < 52 < 78 < 79 < 248`),
  Freudenthal strata + symplectic nondegeneracy + `U_X ∈ Str₀`,
  split vs compact real-form dichotomy, and `G₂ ⊕ (Im 𝕆_s ⊗ H₃⁰) ⊕ F₄` synthesis

All 6 milestone cross-feature contracts (`[M1-CONTRACT]` through `[M6-CONTRACT]`) are
integrated below, covering Serre `E₆`, complexification & compact simplicity, `E₆(6)`
Chevalley/Bruhat generation & 56D Levi descent, 133D TKK `𝔈₇(7)`/`𝔈₇(-25)`, 56D Freudenthal
`E₇(7)`, and 248D Magic Square `𝔈₈(8)`.
-/

set_option autoImplicit false

namespace InfoGeometry.Tests.E6E7E8CrossFeature

open InfoGeometry.Algebra
open InfoGeometry.Algebra.SplitAlbertStructureOperators
open InfoGeometry.Exceptional.CFSGPort.Chevalley
open InfoGeometry.Exceptional.Freudenthal

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## Tier 3: Pairwise Cross-Feature Interactions (`[IMMEDIATE]`) -/

theorem cross_e6_str0_inside_str_and_multiplier_quotient :
    Module.finrank ℝ h3zornCubicStabilizer = 78 ∧
    Module.finrank ℝ structureOperatorLieSubalgebra = 79 ∧
    h3zornCubicStabilizer ≤ structureOperatorLieSubalgebra ∧
    Function.Surjective h3zornStructureGroupMultiplier := by
  refine ⟨finrank_h3zornCubicStabilizer, finrank_structureOperatorLieSubalgebra, ?_,
    h3zornStructureGroupMultiplier_surjective⟩
  intro T hT
  change T ∈ h3zornCubicStabilizer.toSubmodule at hT
  change T ∈ structureOperatorLieSubalgebra.toSubmodule
  rw [h3zornCubicStabilizer_eq_sup] at hT
  rw [structureOperatorLieSubalgebra_eq_sup]
  refine (sup_le_sup_left (by rintro S ⟨a, _, rfl⟩; exact ⟨a, rfl⟩)
    H3ZornF4Derivations.toSubmodule) hT

noncomputable def cross_str_quotient_multiplier_iso :
    StructureGroup ℝ (H3Zorn ℝ) ⧸ h3zornStructureGroupMultiplier.ker ≃* ℝˣ :=
  h3zornStructureGroupQuotientKernelEquivMultiplier

noncomputable def cross_aut_fix_one_iso :
    H3ZornJordanAut ≃* h3zornReducedStructureFixOne :=
  h3zornJordanAutMulEquivReducedStructureFixOne

private noncomputable def strWitnessX : H3Zorn ℝ := H3Zorn.diagCartan 1 2 (1 / 2 : ℝ)

private theorem normCubic_strWitnessX : H3Zorn.normCubic strWitnessX = 1 := by
  have h := (H3Zorn.diagCartan_quadratic_U_peirce_laplace_mellin_and_semigroup
    (1 : ℝ) 2 (1 / 2) 1 1 1 1).2.1
  change H3Zorn.normCubic strWitnessX = 1 * 2 * (1 / 2) at h
  rw [h]
  norm_num

private theorem strWitnessX_norm_ne_zero : H3Zorn.normCubic strWitnessX ≠ 0 := by
  rw [normCubic_strWitnessX]
  norm_num

theorem cross_aut_strictly_inside_str0 (e : H3ZornJordanAut) :
    H3ZornJordanAut.toLinearEquiv e ∈ h3zornReducedStructureGroup ∧
    h3zornULinearEquiv strWitnessX strWitnessX_norm_ne_zero ∈ h3zornReducedStructureGroup ∧
    h3zornULinearEquiv strWitnessX strWitnessX_norm_ne_zero 1 ≠ 1 := by
  refine ⟨H3ZornJordanAut.mem_reducedStructureGroup e,
    h3zornULinearEquiv_mem_reducedStructureGroup strWitnessX strWitnessX_norm_ne_zero
      (Or.inl normCubic_strWitnessX), ?_⟩
  intro h1
  have ha := congrArg (fun W : H3Zorn ℝ => W.α₂) h1
  rw [h3zornULinearEquiv_apply] at ha
  have hU := (H3Zorn.diagCartan_quadratic_U_peirce_laplace_mellin_and_semigroup
    (1 : ℝ) 2 (1 / 2) 1 1 1 (1 : H3Zorn ℝ)).2.2.1
  change H3Zorn.U strWitnessX (1 : H3Zorn ℝ) = _ at hU
  rw [hU] at ha
  change (2 : ℝ) * 2 * (1 : H3Zorn ℝ).α₂ = (1 : H3Zorn ℝ).α₂ at ha
  have h1a2 : (1 : H3Zorn ℝ).α₂ = 1 := rfl
  rw [h1a2] at ha
  norm_num at ha

theorem cross_split_vs_compact_real_form_separation (D : H3OctonionF4Derivations) :
    IsEmpty (H3Octonion ℝ ≃+* H3Zorn ℝ) ∧
    LinearMap.trace ℝ (H3Octonion ℝ) (D.1 * D.1) ≤ 0 ∧
    LinearMap.trace ℝ (H3Zorn ℝ) (splitF4TracePosWitness.1 * splitF4TracePosWitness.1) = 3 / 2 ∧
    Module.finrank ℝ H3OctonionF4Derivations = Module.finrank ℝ H3ZornF4Derivations ∧
    Module.finrank ℝ h3OctonionCubicStabilizer = Module.finrank ℝ h3zornCubicStabilizer := by
  refine ⟨H3Octonion.no_jordanIso_H3Octonion_H3Zorn,
    compactF4_trace_sq_nonpos D,
    splitF4TracePosWitness_trace_sq, ?_, ?_⟩
  · rw [finrank_H3OctonionF4Derivations, finrank_H3ZornF4Derivations]
  · rw [finrank_h3OctonionCubicStabilizer, finrank_h3zornCubicStabilizer]

theorem cross_e6_chevalley_adjoint_and_f4_inclusion
    (i : Fin 6) (c : ℝ) (Y : h3zornCubicStabilizer) :
    H3ZornF4Derivations ≤ h3zornCubicStabilizer ∧
    h3zornChevalleyEquiv (hVec .E6 ℝ i) = e6SimpleH i ∧
    (e6SimpleE i : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0 ∧
    h3zornAdjointAction (h3zornSimpleX i c) Y =
      Y + c • ⁅e6SimpleE i, Y⁆ + (c ^ 2 / 2) • ⁅e6SimpleE i, ⁅e6SimpleE i, Y⁆⁆ :=
  ⟨H3ZornF4Derivations_le_h3zornCubicStabilizer,
    h3zornChevalleyEquiv_hVec i,
    e6RootVec_sq_zero (eSimpleIdx i),
    h3zornAdjointAction_simpleX i c Y⟩

theorem cross_tkk_freudenthal_and_cubic_norm_U (X Y : H3Zorn ℝ) (u v : H3Zorn ℝ) :
    H3Zorn.normCubic (H3Zorn.U X Y) = H3Zorn.normCubic X ^ 2 * H3Zorn.normCubic Y ∧
    H3Zorn.normCubic X =
      (-1 / 4 : ℝ) * H3ZornFreudenthal.quarticInvariant (H3ZornFreudenthal.electricCharge 1 X) ∧
    ⁅InfoGeometry.Canonical.H3ZornJordanTripleBridge.innerDerivation u v,
      InfoGeometry.Canonical.H3ZornJordanTripleBridge.jordanTripleD X Y⁆ =
      InfoGeometry.Canonical.H3ZornJordanTripleBridge.jordanTripleD
        (InfoGeometry.Canonical.H3ZornJordanTripleBridge.innerDerivation u v X) Y +
      InfoGeometry.Canonical.H3ZornJordanTripleBridge.jordanTripleD
        X (InfoGeometry.Canonical.H3ZornJordanTripleBridge.innerDerivation u v Y) :=
  ⟨normCubic_U X Y,
    H3ZornFreudenthal.cubicNorm_from_quartic X,
    InfoGeometry.Canonical.H3ZornTKKNative.innerDerivation_lie_jordanTripleD u v X Y⟩

theorem cross_tits_e8_carrier_pairs_g2_killing_and_f4_52d :
    LieAlgebra.IsKilling ℝ InfoGeometry.Lie.CanonicalZornIsKilling.Der ∧
    Module.finrank ℝ InfoGeometry.Lie.CanonicalZornIsKilling.Der = 14 ∧
    Module.finrank ℝ H3ZornF4Derivations = 52 ∧
    Module.finrank ℝ InfoGeometry.Canonical.NativeTitsE8Carrier.NativeTitsCarrier = 248 ∧
    Module.finrank ℝ InfoGeometry.Canonical.SplitFreudenthalTitsE8Carrier.SplitTitsE8Carrier = 248 :=
  ⟨InfoGeometry.Lie.CanonicalZornIsKilling.der_isKilling,
    InfoGeometry.Lie.SplitG2RealFormCapstone.parameter_model_is_fourteen_dimensional,
    finrank_H3ZornF4Derivations,
    InfoGeometry.Canonical.NativeTitsE8Carrier.finrank_nativeTitsCarrier_of_f4
      finrank_H3ZornF4Derivations,
    InfoGeometry.Canonical.SplitFreudenthalTitsE8Carrier.splitTitsE8Carrier_finrank⟩

/-! ## Tier 4: Baseline End-to-End Mathematical Scenarios (`[IMMEDIATE]`) -/

theorem scenario1_baseline_exceptional_tower_dimensions_and_nonvacuity :
    Module.finrank ℝ (CompactOctonion ℝ) = 8 ∧
    Module.finrank ℝ InfoGeometry.Lie.CanonicalZornIsKilling.Der = 14 ∧
    Module.finrank ℝ (H3Zorn ℝ) = 27 ∧
    Module.finrank ℝ H3ZornF4Derivations = 52 ∧
    Module.finrank ℝ h3zornCubicStabilizer = 78 ∧
    Module.finrank ℝ structureOperatorLieSubalgebra = 79 ∧
    Module.finrank ℝ InfoGeometry.Canonical.NativeTitsE8Carrier.NativeTitsCarrier = 248 ∧
    LieAlgebra.IsSimple ℝ h3zornCubicStabilizer ∧
    LieAlgebra.IsKilling ℝ InfoGeometry.Lie.CanonicalZornIsKilling.Der ∧
    h3zornWeylElt 0 1 * h3zornWeylElt 2 1 ≠ h3zornWeylElt 2 1 * h3zornWeylElt 0 1 := by
  refine ⟨CompactOctonion.finrank_compactOctonion,
    InfoGeometry.Lie.SplitG2RealFormCapstone.parameter_model_is_fourteen_dimensional,
    InfoGeometry.Algebra.finrank_h3zorn,
    finrank_H3ZornF4Derivations,
    ?_,
    finrank_structureOperatorLieSubalgebra,
    InfoGeometry.Canonical.NativeTitsE8Carrier.finrank_nativeTitsCarrier_of_f4
      finrank_H3ZornF4Derivations,
    h3zornCubicStabilizer_isSimple,
    InfoGeometry.Lie.CanonicalZornIsKilling.der_isKilling,
    h3zornWeylElt_noncomm_witness⟩
  rw [Module.finrank_eq_card_basis e6ChevalleyBasis]
  simp

theorem scenario2_baseline_freudenthal_strata_symplectic_and_str0 :
    H3ZornFreudenthal.Regular (H3ZornFreudenthal.electricCharge 1 (1 : H3Zorn ℝ)) ∧
    H3ZornFreudenthal.Boundary (H3ZornFreudenthal.electricCharge 1 (H3Zorn.diagCartan 1 0 0)) ∧
    (∀ Q : H3ZornFreudenthal.Charge,
      (∀ P : H3ZornFreudenthal.Charge, H3ZornFreudenthal.symplecticForm Q P = 0) → Q = 0) ∧
    (∀ Q : H3ZornFreudenthal.Charge,
      H3ZornFreudenthal.quarticPolarization (fun _ => Q) =
        H3ZornFreudenthal.quarticInvariant Q) ∧
    h3zornULinearEquiv strWitnessX strWitnessX_norm_ne_zero ∈ h3zornReducedStructureGroup := by
  refine ⟨?_, ?_, ?_, H3ZornFreudenthal.quarticPolarization_diagonal, ?_⟩
  · change H3ZornFreudenthal.quarticInvariant (H3ZornFreudenthal.electricCharge 1 1) ≠ 0
    rw [H3ZornFreudenthal.unit_electric_quartic]
    norm_num
  · have hN : H3Zorn.normCubic (H3Zorn.diagCartan (1 : ℝ) 0 0) = 0 := by
      have h := (H3Zorn.diagCartan_quadratic_U_peirce_laplace_mellin_and_semigroup
        (1 : ℝ) 0 0 1 1 1 1).2.1
      rw [h]
      norm_num
    refine ⟨?_, ?_⟩
    · change H3ZornFreudenthal.quarticInvariant
        (H3ZornFreudenthal.electricCharge 1 (H3Zorn.diagCartan 1 0 0)) = 0
      rw [H3ZornFreudenthal.quarticInvariant_electricCharge, hN]
      norm_num
    · intro hz
      have hα := congrArg FreudenthalCharge.alpha hz
      change (1 : ℝ) = 0 at hα
      norm_num at hα
  · exact symplecticForm_nondegenerate_of_traceBilin_nondegenerate h3zornCubicJordanDatum
      H3Zorn.eq_zero_of_traceBilin_left
  · exact h3zornULinearEquiv_mem_reducedStructureGroup strWitnessX strWitnessX_norm_ne_zero
      (Or.inl normCubic_strWitnessX)

theorem scenario3_baseline_split_vs_compact_real_form_dichotomy
    (x y : CompactOctonion ℝ) (a b : H3Octonion ℝ) (D : H3OctonionF4Derivations) :
    (CompactOctonion.mul x y = 0 ↔ x = 0 ∨ y = 0) ∧
    (a * a + b * b = 0 → a = 0 ∧ b = 0) ∧
    LinearMap.trace ℝ (H3Octonion ℝ) (D.1 * D.1) ≤ 0 ∧
    0 < LinearMap.trace ℝ (H3Zorn ℝ) (splitF4TracePosWitness.1 * splitF4TracePosWitness.1) ∧
    IsEmpty (H3Octonion ℝ ≃+* H3Zorn ℝ) :=
  ⟨CompactOctonion.mul_eq_zero_iff x y,
    H3Octonion.formal_reality a b,
    compactF4_trace_sq_nonpos D,
    splitF4TracePosWitness_trace_sq_pos,
    H3Octonion.no_jordanIso_H3Octonion_H3Zorn⟩

theorem scenario4_baseline_g2_f4_tits_e8_synthesis
    (D : InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations) (s t : ℝ) :
    InfoGeometry.Lie.SplitOctonionStandardDerivation.standardDerivationSpan = ⊤ ∧
    Fintype.card InfoGeometry.Lie.CanonicalZornRootSystemComparison.RootIndex = 12 ∧
    InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge.zornFlowRealAut D (s + t) =
      InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge.zornFlowRealAut D s *
        InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge.zornFlowRealAut D t ∧
    f4BasisSpan = H3ZornF4Derivations.toSubmodule ∧
    Module.finrank ℝ InfoGeometry.Canonical.NativeTitsE8Carrier.NativeTitsCarrier = 248 :=
  ⟨InfoGeometry.Lie.SplitOctonionStandardDerivation.standardDerivations_span_top,
    InfoGeometry.Lie.SplitG2RealFormCapstone.split_g2_cartan_root_data.1,
    InfoGeometry.Lie.SplitG2RealFormCapstone.split_g2_flow_is_one_parameter_subgroup D s t,
    f4BasisSpan_eq_H3ZornF4Derivations,
    InfoGeometry.Canonical.NativeTitsE8Carrier.finrank_nativeTitsCarrier_of_f4
      finrank_H3ZornF4Derivations⟩

section M5CrossFeatureTests

open InfoGeometry.Algebra.H3ZornFreudenthal

/-! ## [M5-CONTRACT] Tier 3 Pairwise: `E₆` Chevalley × 56D Levi × `E₇(7)` Generators -/

theorem cross_e6_chevalley_levi_56d
    (h : h3zornChevalleyE6) (Q Q₁ Q₂ : Charge) :
    chevalleyE6ChargeSubgroup ≤ leviChargeSubgroup ∧
    Function.Injective chevalleyE6ChargeEquiv ∧
    symplecticForm (chevalleyE6InvariantAction.act h Q₁)
      (chevalleyE6InvariantAction.act h Q₂) = symplecticForm Q₁ Q₂ ∧
    quarticInvariant (chevalleyE6InvariantAction.act h Q) = quarticInvariant Q ∧
    (let t2 : ℝˣ := Units.mk0 (2 : ℝ) (by norm_num)
     let gT : h3zornChevalleyE6 :=
       ⟨h3zornTorusElt 0 t2, h3zornTorusElt_mem_chevalleyE6 0 t2⟩
     chevalleyE6ChargeEquiv gT (electricCharge 1 (h3ZornBasis 0)) ≠
       electricCharge 1 (h3ZornBasis 0)) ∧
    (let w0 : h3zornChevalleyE6 :=
       ⟨h3zornWeylElt 0 1, h3zornWeylElt_mem_chevalleyE6 0 1⟩
     let w2 : h3zornChevalleyE6 :=
       ⟨h3zornWeylElt 2 1, h3zornWeylElt_mem_chevalleyE6 2 1⟩
     chevalleyE6ChargeGL w0 * chevalleyE6ChargeGL w2 ≠
       chevalleyE6ChargeGL w2 * chevalleyE6ChargeGL w0) :=
  ⟨chevalleyE6ChargeSubgroup_le_leviChargeSubgroup, chevalleyE6ChargeEquiv_injective,
    chevalleyE6InvariantAction.preserves_symplecticForm h Q₁ Q₂,
    chevalleyE6InvariantAction.preserves_quarticInvariant h Q,
    chevalleyE6_torus_nontrivial_witness.1,
    chevalleyE6_weyl_noncomm_witness.2⟩

theorem cross_levi_conj_e7_generators
    (g : h3zornReducedStructureGroup) (A B : H3Zorn ℝ) :
    leviChargeEquiv g * freudenthalUpperTrans A * (leviChargeEquiv g)⁻¹ =
      freudenthalUpperTrans (g.1 A) ∧
    leviChargeEquiv g * freudenthalLowerTrans B * (leviChargeEquiv g)⁻¹ =
      freudenthalLowerTrans (h3zornTraceInverseAdjoint g.1 B) ∧
    freudenthalInversion * leviChargeEquiv g * freudenthalInversion⁻¹ =
      leviChargeEquiv (h3zornTraceInverseAdjointReduced g) ∧
    leviChargeGL g ∈ freudenthalE7Group ∧
    freudenthalE7Group ≤ freudenthalInvariantSubgroup :=
  ⟨levi_conj_upperTrans g A, levi_conj_lowerTrans g B, inversion_conj_levi g,
    leviChargeGL_mem_freudenthalE7Group g, freudenthalE7Group_le_invariantSubgroup⟩

/-! ## [M5-CONTRACT] Tier 4 Scenario 2 (M5 Portion): `E₇(7)` Word Composition & Strata -/

theorem scenario2_m5_e7_word_strata_and_noncommutativity
    (Q Q₁ Q₂ : Charge) :
    let uDiag : h3zornReducedStructureGroup :=
      ⟨h3zornULinearEquiv strWitnessX strWitnessX_norm_ne_zero,
        h3zornULinearEquiv_mem_reducedStructureGroup strWitnessX strWitnessX_norm_ne_zero
          (Or.inl normCubic_strWitnessX)⟩
    let gL : freudenthalE7Group := ⟨leviChargeGL uDiag, leviChargeGL_mem_freudenthalE7Group uDiag⟩
    let gUp : freudenthalE7Group :=
      ⟨glUpperTrans (Multiplicative.ofAdd (1 : H3Zorn ℝ)), glUpperTrans_mem_freudenthalE7Group 1⟩
    let gLow : freudenthalE7Group :=
      ⟨glLowerTrans (Multiplicative.ofAdd (1 : H3Zorn ℝ)), glLowerTrans_mem_freudenthalE7Group 1⟩
    let gJ : freudenthalE7Group := ⟨glInversion, glInversion_mem_freudenthalE7Group⟩
    let gWord : freudenthalE7Group := gL * gUp * gJ * gLow
    symplecticForm (gWord.1 • Q₁) (gWord.1 • Q₂) = symplecticForm Q₁ Q₂ ∧
    symplecticForm (gWord.1 • scalarCharge 1 0) (gWord.1 • scalarCharge 0 1) = 1 ∧
    quarticInvariant (gWord.1 • Q) = quarticInvariant Q ∧
    quarticInvariant (gWord.1 • (⟨1, 1, (1 : H3Zorn ℝ), (1 : H3Zorn ℝ)⟩ : Charge)) = -16 ∧
    Regular (gWord.1 • electricCharge 1 (1 : H3Zorn ℝ)) ∧
    Boundary (gWord.1 • electricCharge 0 (H3Zorn.diagCartan 1 0 0)) ∧
    glUpperTrans (Multiplicative.ofAdd (1 : H3Zorn ℝ)) *
        glLowerTrans (Multiplicative.ofAdd (1 : H3Zorn ℝ)) *
        (glUpperTrans (Multiplicative.ofAdd (1 : H3Zorn ℝ)))⁻¹ *
        (glLowerTrans (Multiplicative.ofAdd (1 : H3Zorn ℝ)))⁻¹ ≠ 1 ∧
    leviChargeEquiv uDiag (electricCharge 1 1) ≠ electricCharge 1 1 := by
  intro uDiag gL gUp gLow gJ gWord
  have hsymp : symplecticForm (gWord.1 • Q₁) (gWord.1 • Q₂) = symplecticForm Q₁ Q₂ :=
    freudenthalE7GroupAction.preserves_symplecticForm gWord Q₁ Q₂
  have hsymp_scalar :
      symplecticForm (gWord.1 • scalarCharge 1 0) (gWord.1 • scalarCharge 0 1) = 1 := by
    rw [(freudenthalE7Group_le_invariantSubgroup gWord.2).1, symplecticForm_expanded]
    simp [scalarCharge]
  have hq : quarticInvariant (gWord.1 • Q) = quarticInvariant Q :=
    freudenthalE7GroupAction.preserves_quarticInvariant gWord Q
  have htr1 : H3Zorn.traceBilin (1 : H3Zorn ℝ) 1 = 3 := by
    rw [H3Zorn.traceBilin_one]
    change (1 : ℝ) + 1 + 1 = 3
    norm_num
  have hmix : quarticInvariant (gWord.1 • (⟨1, 1, (1 : H3Zorn ℝ), (1 : H3Zorn ℝ)⟩ : Charge)) =
      -16 := by
    rw [(freudenthalE7Group_le_invariantSubgroup gWord.2).2, quarticInvariant_expanded]
    simp only [H3Zorn.normCubic_one, H3Zorn.adjointQuad_one, htr1]
    norm_num
  have hreg : Regular (gWord.1 • electricCharge 1 (1 : H3Zorn ℝ)) := by
    refine (freudenthalE7GroupAction.regular_iff gWord (electricCharge 1 1)).2 ?_
    change quarticInvariant (electricCharge 1 1) ≠ 0
    rw [unit_electric_quartic]
    norm_num
  have hbd : Boundary (gWord.1 • electricCharge 0 (H3Zorn.diagCartan 1 0 0)) := by
    refine (freudenthalE7GroupAction.boundary_iff gWord
      (electricCharge 0 (H3Zorn.diagCartan 1 0 0))).2 ?_
    refine ⟨?_, ?_⟩
    · change quarticInvariant (electricCharge 0 (H3Zorn.diagCartan 1 0 0)) = 0
      rw [quarticInvariant_electricCharge]
      norm_num
    · intro hz
      have hx := congrArg FreudenthalCharge.x hz
      have hα₁ := congrArg H3Zorn.α₁ hx
      change (1 : ℝ) = 0 at hα₁
      norm_num at hα₁
  have hlevi_ne : leviChargeEquiv uDiag (electricCharge 1 1) ≠ electricCharge 1 1 := by
    intro heq
    have hx := congrArg FreudenthalCharge.x heq
    rw [leviChargeEquiv_apply, leviChargeLinearEquiv_x] at hx
    dsimp [uDiag, electricCharge] at hx
    rw [h3zornULinearEquiv_apply] at hx
    have hU := (H3Zorn.diagCartan_quadratic_U_peirce_laplace_mellin_and_semigroup
      (1 : ℝ) 2 (1 / 2) 1 1 1 (1 : H3Zorn ℝ)).2.2.1
    change H3Zorn.U strWitnessX (1 : H3Zorn ℝ) = _ at hU
    rw [hU] at hx
    have ha := congrArg (fun W : H3Zorn ℝ => W.α₂) hx
    change (2 : ℝ) * 2 * (1 : H3Zorn ℝ).α₂ = (1 : H3Zorn ℝ).α₂ at ha
    have h1a2 : (1 : H3Zorn ℝ).α₂ = 1 := rfl
    rw [h1a2] at ha
    norm_num at ha
  exact ⟨hsymp, hsymp_scalar, hq, hmix, hreg, hbd,
    glUpperTrans_glLowerTrans_commutator_ne_one, hlevi_ne⟩

end M5CrossFeatureTests

section M1CrossFeatureTests

open InfoGeometry.Algebra.H3ZornFreudenthal

private theorem m1_serre_equiv_H (i : Fin 6) :
    h3zornE6SerreEquiv (e6SerreH i) = e6SimpleH i :=
  h3zornE6SerreQuotientMap_H i

private theorem m1_serre_equiv_E (i : Fin 6) :
    h3zornE6SerreEquiv (e6SerreE i) = e6SimpleE i :=
  h3zornE6SerreQuotientMap_E i

private theorem m1_serre_equiv_F (i : Fin 6) :
    h3zornE6SerreEquiv (e6SerreF i) = e6SimpleF i :=
  h3zornE6SerreQuotientMap_F i

/-! ## `[M1-CONTRACT]` Tier 3 Pairwise: `E₆` Serre × Chevalley/Root × 56D Levi -/

theorem cross_e6_serre_chevalley_and_root_system
    (i : Fin 6) (r : Fin 72) :
    LieAlgebra.IsSimple ℝ (LieAlgebra.e₆ ℝ) ∧
    Module.finrank ℝ (LieAlgebra.e₆ ℝ) = 78 ∧
    Module.finrank ℝ (RootModule .E6 ℝ) = 78 ∧
    Module.finrank ℝ h3zornCubicStabilizer = 78 ∧
    h3zornChevalleyEquiv.symm (h3zornE6SerreEquiv (e6SerreH i)) = hVec .E6 ℝ i ∧
    h3zornChevalleyEquiv.symm (h3zornE6SerreEquiv (e6SerreE i)) =
      rootVec .E6 ℝ (e6RootCoord (eSimpleIdx i)) ∧
    h3zornChevalleyEquiv.symm (h3zornE6SerreEquiv (e6SerreF i)) =
      (fSimpleSign i : ℝ) • rootVec .E6 ℝ (e6RootCoord (fSimpleIdx i)) ∧
    h3zornE6SerreEquiv.symm (h3zornChevalleyEquiv (rootVec .E6 ℝ (e6RootCoord r))) ≠ 0 ∧
    h3zornChevalleyEquiv.symm (h3zornE6SerreEquiv ⁅e6SerreE i, e6SerreF i⁆) =
      hVec .E6 ℝ i ∧
    h3zornChevalleyEquiv.symm ⁅h3zornE6SerreEquiv (e6SerreH 0),
      h3zornE6SerreEquiv (e6SerreE 0)⁆ ≠ 0 := by
  have he6Root_dim : Module.finrank ℝ (RootModule .E6 ℝ) = 78 := by
    rw [LinearEquiv.finrank_eq h3zornChevalleyEquiv, finrank_h3zornCubicStabilizer]
  have hH_map : h3zornChevalleyEquiv.symm (h3zornE6SerreEquiv (e6SerreH i)) = hVec .E6 ℝ i := by
    rw [m1_serre_equiv_H i, ← h3zornChevalleyEquiv_hVec i,
      h3zornChevalleyEquiv.symm_apply_apply]
  have hE_map :
      h3zornChevalleyEquiv.symm (h3zornE6SerreEquiv (e6SerreE i)) =
        rootVec .E6 ℝ (e6RootCoord (eSimpleIdx i)) := by
    rw [m1_serre_equiv_E i]
    change h3zornChevalleyEquiv.symm (e6RootVec (eSimpleIdx i)) = _
    rw [← h3zornChevalleyEquiv_rootVec (eSimpleIdx i), h3zornChevalleyEquiv.symm_apply_apply]
  have hF_map :
      h3zornChevalleyEquiv.symm (h3zornE6SerreEquiv (e6SerreF i)) =
        (fSimpleSign i : ℝ) • rootVec .E6 ℝ (e6RootCoord (fSimpleIdx i)) := by
    rw [m1_serre_equiv_F i]
    change h3zornChevalleyEquiv.symm ((fSimpleSign i : ℝ) • e6RootVec (fSimpleIdx i)) = _
    rw [map_smul, ← h3zornChevalleyEquiv_rootVec (fSimpleIdx i),
      h3zornChevalleyEquiv.symm_apply_apply]
  have hr_ne :
      h3zornE6SerreEquiv.symm (h3zornChevalleyEquiv (rootVec .E6 ℝ (e6RootCoord r))) ≠ 0 := by
    rw [h3zornChevalleyEquiv_rootVec r]
    intro h0
    have h1 := congrArg h3zornE6SerreEquiv h0
    rw [h3zornE6SerreEquiv.apply_symm_apply, map_zero] at h1
    exact e6RootVec_ne_zero r h1
  have hEF_map :
      h3zornChevalleyEquiv.symm (h3zornE6SerreEquiv ⁅e6SerreE i, e6SerreF i⁆) =
        hVec .E6 ℝ i := by
    rw [LieEquiv.map_lie, m1_serre_equiv_E i, m1_serre_equiv_F i, e6Simple_bracket_EF_same,
      ← h3zornChevalleyEquiv_hVec i, h3zornChevalleyEquiv.symm_apply_apply]
  have hHE_ne :
      h3zornChevalleyEquiv.symm ⁅h3zornE6SerreEquiv (e6SerreH 0),
        h3zornE6SerreEquiv (e6SerreE 0)⁆ ≠ 0 := by
    rw [m1_serre_equiv_H 0, m1_serre_equiv_E 0, e6Simple_bracket_HE]
    have hc : Tag.cartan .E6 (0 : Fin 6) (0 : Fin 6) = 2 := by decide
    rw [hc]
    intro h0
    have h1 := h3zornChevalleyEquiv.symm.injective (h0.trans (map_zero _).symm)
    have h2 : (2 : ℝ) • e6SimpleE 0 = 0 := by simpa using h1
    have he := (smul_eq_zero.mp h2).resolve_left (by norm_num)
    exact e6RootVec_ne_zero (eSimpleIdx 0) he
  exact ⟨e6Serre_isSimple, finrank_e6_serre, he6Root_dim, finrank_h3zornCubicStabilizer,
    hH_map, hE_map, hF_map, hr_ne, hEF_map, hHE_ne⟩

theorem cross_e6_serre_to_56d_levi_compatibility
    (g : h3zornReducedStructureGroup) (h : h3zornChevalleyE6)
    (i : Fin 6) (c : ℝ) (x : LieAlgebra.e₆ ℝ) (Q Q₁ Q₂ : Charge) :
    h3zornAdjointAction g (h3zornE6SerreEquiv x) ∈ Set.range h3zornE6SerreEquiv ∧
    h3zornAdjointAction (h3zornSimpleX i c) (h3zornE6SerreEquiv x) =
      h3zornE6SerreEquiv
        (x + c • ⁅e6SerreE i, x⁆ + (c ^ 2 / 2) • ⁅e6SerreE i, ⁅e6SerreE i, x⁆⁆) ∧
    (∀ t : ℝˣ, ∀ j : Fin 6,
      h3zornAdjointAction (h3zornTorusElt i t) (h3zornE6SerreEquiv (e6SerreH j)) =
        h3zornE6SerreEquiv (e6SerreH j)) ∧
    chevalleyE6ChargeEquiv h Q = leviChargeEquiv h.1 Q ∧
    symplecticForm (chevalleyE6InvariantAction.act h Q₁)
      (chevalleyE6InvariantAction.act h Q₂) = symplecticForm Q₁ Q₂ ∧
    quarticInvariant (chevalleyE6InvariantAction.act h Q) = quarticInvariant Q ∧
    (let gX : h3zornChevalleyE6 := ⟨h3zornSimpleX i c, h3zornSimpleX_mem_chevalleyE6 i c⟩
     symplecticForm (chevalleyE6InvariantAction.act gX Q₁)
       (chevalleyE6InvariantAction.act gX Q₂) = symplecticForm Q₁ Q₂ ∧
     quarticInvariant (chevalleyE6InvariantAction.act gX Q) = quarticInvariant Q) ∧
    h3zornAdjointAction (h3zornSimpleX 0 1) (h3zornE6SerreEquiv (e6SerreF 0)) ≠
      h3zornE6SerreEquiv (e6SerreF 0) := by
  have himg : h3zornAdjointAction g (h3zornE6SerreEquiv x) ∈ Set.range h3zornE6SerreEquiv :=
    ⟨h3zornE6SerreEquiv.symm (h3zornAdjointAction g (h3zornE6SerreEquiv x)),
      h3zornE6SerreEquiv.apply_symm_apply _⟩
  have hadX :
      h3zornAdjointAction (h3zornSimpleX i c) (h3zornE6SerreEquiv x) =
        h3zornE6SerreEquiv
          (x + c • ⁅e6SerreE i, x⁆ + (c ^ 2 / 2) • ⁅e6SerreE i, ⁅e6SerreE i, x⁆⁆) := by
    rw [h3zornAdjointAction_simpleX i c]
    have hE : e6SimpleE i = h3zornE6SerreEquiv (e6SerreE i) := (m1_serre_equiv_E i).symm
    rw [hE, ← LieEquiv.map_lie, ← LieEquiv.map_lie,
      ← map_smul, ← map_smul, ← map_add, ← map_add]
  have htor : ∀ (t : ℝˣ) (j : Fin 6),
      h3zornAdjointAction (h3zornTorusElt i t) (h3zornE6SerreEquiv (e6SerreH j)) =
        h3zornE6SerreEquiv (e6SerreH j) := by
    intro t j
    rw [m1_serre_equiv_H j, h3zornAdjointAction_torusElt_hVec i j t]
  have hnon_triv :
      h3zornAdjointAction (h3zornSimpleX 0 1) (h3zornE6SerreEquiv (e6SerreF 0)) ≠
        h3zornE6SerreEquiv (e6SerreF 0) := by
    rw [m1_serre_equiv_F 0, h3zornAdjointAction_simpleX 0 1]
    intro heq
    rw [e6Simple_bracket_EF_same, ← lie_skew, e6Simple_bracket_HE] at heq
    have hc : Tag.cartan .E6 (0 : Fin 6) (0 : Fin 6) = 2 := by decide
    rw [hc] at heq
    have hsub : (e6SimpleH 0 - e6SimpleE 0 : h3zornCubicStabilizer) = 0 := by
      have hdiff := sub_eq_zero.mpr heq
      norm_num at hdiff
      rw [← hdiff]
      module
    have hH_eq : e6SimpleH 0 = e6SimpleE 0 := sub_eq_zero.mp hsub
    have hbr : ⁅e6SimpleH 0, e6SimpleE 0⁆ = 0 := by
      rw [← hH_eq, lie_self]
    rw [e6Simple_bracket_HE, hc] at hbr
    have h2 : (2 : ℝ) • e6SimpleE 0 = 0 := by simpa using hbr
    have he := (smul_eq_zero.mp h2).resolve_left (by norm_num)
    exact e6RootVec_ne_zero (eSimpleIdx 0) he
  refine ⟨himg, hadX, htor, chevalleyE6ChargeEquiv_apply h Q,
    chevalleyE6InvariantAction.preserves_symplecticForm h Q₁ Q₂,
    chevalleyE6InvariantAction.preserves_quarticInvariant h Q,
    ⟨chevalleyE6InvariantAction.preserves_symplecticForm _ Q₁ Q₂,
      chevalleyE6InvariantAction.preserves_quarticInvariant _ Q⟩,
    hnon_triv⟩

end M1CrossFeatureTests

section M2CrossFeatureTests

open scoped TensorProduct

private noncomputable def lieEquivBaseChange {L₁ L₂ : Type*}
    [LieRing L₁] [LieAlgebra ℝ L₁] [LieRing L₂] [LieAlgebra ℝ L₂]
    (e : L₁ ≃ₗ⁅ℝ⁆ L₂) :
    ℂ ⊗[ℝ] L₁ ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] L₂ :=
  let f := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℂ ℂ) e.toLinearEquiv
  { f with
    map_lie' := fun {x y} => by
      change f ⁅x, y⁆ = ⁅f x, f y⁆
      induction x using TensorProduct.inductionOn generalizing y with
      | tmul z₁ a₁ =>
        induction y using TensorProduct.inductionOn with
        | tmul z₂ a₂ =>
          change (z₁ * z₂) ⊗ₜ[ℝ] e ⁅a₁, a₂⁆ = (z₁ * z₂) ⊗ₜ[ℝ] ⁅e a₁, e a₂⁆
          rw [e.map_lie]
        | add b₁ b₂ hb₁ hb₂ =>
          rw [lie_add (L := ℂ ⊗[ℝ] L₁), f.map_add, hb₁, hb₂, f.map_add,
            lie_add (L := ℂ ⊗[ℝ] L₂)]
      | add x₁ x₂ hx₁ hx₂ =>
        rw [add_lie (M := ℂ ⊗[ℝ] L₁), f.map_add, hx₁, hx₂, f.map_add,
          add_lie (M := ℂ ⊗[ℝ] L₂)] }

noncomputable def cross_m2_serre_to_compact_e6_complex_equiv :
    ℂ ⊗[ℝ] LieAlgebra.e₆ ℝ ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] h3OctonionCubicStabilizer :=
  (lieEquivBaseChange h3zornE6SerreEquiv).trans h3OctonionCubicStabilizerBaseChangeEquiv.symm

/-! ## `[M2-CONTRACT]` Tier 3 Pairwise: Complexification × `E₆` Serre × `F₄` Simplicity -/

theorem cross_m2_complexification_e6_and_f4_unification
    (i : Fin 6) (a b : LieAlgebra.e₆ ℝ)
    (D₁ D₂ : ℂ ⊗[ℝ] H3OctonionF4Derivations)
    (x y : H3Octonion ℂ) (u : ℂ ⊗[ℝ] H3Octonion ℝ) :
    LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] LieAlgebra.e₆ ℝ) ∧
    LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] h3zornCubicStabilizer) ∧
    LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] h3OctonionCubicStabilizer) ∧
    LieAlgebra.IsSimple ℝ H3ZornF4Derivations ∧
    LieAlgebra.IsSimple ℝ H3OctonionF4Derivations ∧
    LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] H3ZornF4Derivations) ∧
    LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] H3OctonionF4Derivations) ∧
    Module.finrank ℂ (ℂ ⊗[ℝ] LieAlgebra.e₆ ℝ) = 78 ∧
    Module.finrank ℂ (ℂ ⊗[ℝ] h3OctonionCubicStabilizer) = 78 ∧
    Module.finrank ℂ (ℂ ⊗[ℝ] H3ZornF4Derivations) = 52 ∧
    Module.finrank ℂ (ℂ ⊗[ℝ] H3OctonionF4Derivations) = 52 ∧
    cross_m2_serre_to_compact_e6_complex_equiv
      ⁅(1 : ℂ) ⊗ₜ[ℝ] a, (1 : ℂ) ⊗ₜ[ℝ] b⁆ =
        ⁅cross_m2_serre_to_compact_e6_complex_equiv ((1 : ℂ) ⊗ₜ[ℝ] a),
          cross_m2_serre_to_compact_e6_complex_equiv ((1 : ℂ) ⊗ₜ[ℝ] b)⁆ ∧
    ⁅cross_m2_serre_to_compact_e6_complex_equiv ((1 : ℂ) ⊗ₜ[ℝ] e6SerreH i),
      cross_m2_serre_to_compact_e6_complex_equiv ((1 : ℂ) ⊗ₜ[ℝ] e6SerreE i)⁆ ≠ 0 ∧
    h3OctonionF4DerivationsBaseChangeEquiv ⁅D₁, D₂⁆ =
      ⁅h3OctonionF4DerivationsBaseChangeEquiv D₁,
        h3OctonionF4DerivationsBaseChangeEquiv D₂⁆ ∧
    ⁅h3OctonionF4DerivationsBaseChangeEquiv.symm ((1 : ℂ) ⊗ₜ[ℝ] f4SimpleH 0),
      h3OctonionF4DerivationsBaseChangeEquiv.symm ((1 : ℂ) ⊗ₜ[ℝ] f4SimpleE 0)⁆ ≠ 0 ∧
    H3Zorn.normCubic (h3OctonionComplexEquiv x) = H3Octonion.normCubic x ∧
    H3Zorn.traceBilin (h3OctonionComplexEquiv x) (h3OctonionComplexEquiv y) =
      H3Octonion.traceBilin x y ∧
    H3Zorn.normCubic (tensorEquivH3Zorn (h3OctonionTensorEquivH3Zorn u)) =
      H3Octonion.normCubic (tensorEquivH3Octonion u) := by
  have hserreSimple : LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] LieAlgebra.e₆ ℝ) :=
    LieEquiv.isSimple cross_m2_serre_to_compact_e6_complex_equiv.symm
  have hdim_e6_oct : Module.finrank ℂ (ℂ ⊗[ℝ] h3OctonionCubicStabilizer) = 78 := by
    rw [h3OctonionCubicStabilizerBaseChangeEquiv.toLinearEquiv.finrank_eq,
      Module.finrank_eq_card_basis (e6ChevalleyBasis.baseChange ℂ),
      Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  have hdim_e6_serre : Module.finrank ℂ (ℂ ⊗[ℝ] LieAlgebra.e₆ ℝ) = 78 := by
    rw [cross_m2_serre_to_compact_e6_complex_equiv.toLinearEquiv.finrank_eq, hdim_e6_oct]
  have hdim_f4_zorn : Module.finrank ℂ (ℂ ⊗[ℝ] H3ZornF4Derivations) = 52 := by
    rw [Module.finrank_eq_card_basis (f4ChevalleyBasis.baseChange ℂ),
      Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  have hdim_f4_oct : Module.finrank ℂ (ℂ ⊗[ℝ] H3OctonionF4Derivations) = 52 := by
    rw [h3OctonionF4DerivationsBaseChangeEquiv.toLinearEquiv.finrank_eq, hdim_f4_zorn]
  have he6_ne : ⁅cross_m2_serre_to_compact_e6_complex_equiv ((1 : ℂ) ⊗ₜ[ℝ] e6SerreH i),
      cross_m2_serre_to_compact_e6_complex_equiv ((1 : ℂ) ⊗ₜ[ℝ] e6SerreE i)⁆ ≠ 0 := by
    rw [← LieEquiv.map_lie]
    intro h0
    have h1 : ⁅(1 : ℂ) ⊗ₜ[ℝ] e6SerreH i, (1 : ℂ) ⊗ₜ[ℝ] e6SerreE i⁆ = 0 :=
      cross_m2_serre_to_compact_e6_complex_equiv.injective (h0.trans (map_zero _).symm)
    have h2 := congrArg (lieEquivBaseChange h3zornE6SerreEquiv) h1
    rw [LieEquiv.map_lie, map_zero] at h2
    change ⁅(1 : ℂ) ⊗ₜ[ℝ] h3zornE6SerreEquiv (e6SerreH i),
      (1 : ℂ) ⊗ₜ[ℝ] h3zornE6SerreEquiv (e6SerreE i)⁆ = 0 at h2
    rw [m1_serre_equiv_H i, m1_serre_equiv_E i,
      LieAlgebra.ExtendScalars.bracket_tmul, one_mul, e6Simple_bracket_HE] at h2
    have hdiag : Tag.cartan .E6 i i = 2 := by fin_cases i <;> decide
    rw [hdiag, TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul ℂ ((2 : ℤ) : ℝ)] at h2
    have h2c : ((2 : ℤ) : ℂ) ≠ 0 := by norm_num
    have hsm : (1 : ℂ) ⊗ₜ[ℝ] e6SimpleE i = 0 := (smul_eq_zero.mp h2).resolve_left h2c
    have hbas : (1 : ℂ) ⊗ₜ[ℝ] e6SimpleE i =
        (e6ChevalleyBasis.baseChange ℂ) (Sum.inr (eSimpleIdx i)) := by
      simp [e6SimpleE]
    rw [hbas] at hsm
    exact (e6ChevalleyBasis.baseChange ℂ).ne_zero _ hsm
  have hf4_ne :
      ⁅h3OctonionF4DerivationsBaseChangeEquiv.symm ((1 : ℂ) ⊗ₜ[ℝ] f4SimpleH 0),
        h3OctonionF4DerivationsBaseChangeEquiv.symm ((1 : ℂ) ⊗ₜ[ℝ] f4SimpleE 0)⁆ ≠ 0 := by
    rw [← LieEquiv.map_lie]
    intro h0
    have h1 := congrArg h3OctonionF4DerivationsBaseChangeEquiv h0
    rw [h3OctonionF4DerivationsBaseChangeEquiv.apply_symm_apply, map_zero,
      LieAlgebra.ExtendScalars.bracket_tmul, one_mul, f4Simple_bracket_HE] at h1
    have hdiag : Tag.cartan .F4 (0 : Fin 4) (0 : Fin 4) = 2 := by decide
    rw [hdiag, TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul ℂ ((2 : ℤ) : ℝ)] at h1
    have h2c : ((2 : ℤ) : ℂ) ≠ 0 := by norm_num
    have hsm : (1 : ℂ) ⊗ₜ[ℝ] f4SimpleE 0 = 0 := (smul_eq_zero.mp h1).resolve_left h2c
    have hbas : (1 : ℂ) ⊗ₜ[ℝ] f4SimpleE 0 =
        (f4ChevalleyBasis.baseChange ℂ) (Sum.inr (f4ESimpleIdx 0)) := by
      simp [f4SimpleE, f4ESimpleSign]
    rw [hbas] at hsm
    exact (f4ChevalleyBasis.baseChange ℂ).ne_zero _ hsm
  exact ⟨hserreSimple, complexH3zornCubicStabilizer_isSimple,
    complexH3OctonionCubicStabilizer_isSimple, h3ZornF4Derivations_isSimple,
    h3OctonionF4Derivations_isSimple, complexH3ZornF4Derivations_isSimple,
    complexH3OctonionF4Derivations_isSimple, hdim_e6_serre, hdim_e6_oct, hdim_f4_zorn,
    hdim_f4_oct, cross_m2_serre_to_compact_e6_complex_equiv.map_lie _ _, he6_ne,
    h3OctonionF4DerivationsBaseChangeEquiv.map_lie D₁ D₂, hf4_ne,
    h3OctonionComplexEquiv_normCubic x, h3OctonionComplexEquiv_traceBilin x y,
    h3OctonionTensorEquivH3Zorn_normCubic u⟩

/-! ## `[M2-CONTRACT]` Tier 4 Scenario 4 (M2 Portion): Split vs Compact Real-Form Dichotomy -/

theorem scenario4_m2_split_vs_compact_real_form_dichotomy
    (D : H3OctonionF4Derivations) (x y : H3Octonion ℂ) (u : ℂ ⊗[ℝ] H3Octonion ℝ) :
    IsEmpty (H3Octonion ℝ ≃+* H3Zorn ℝ) ∧
    LinearMap.trace ℝ (H3Octonion ℝ) (D.1 * D.1) ≤ 0 ∧
    0 < LinearMap.trace ℝ (H3Zorn ℝ) (splitF4TracePosWitness.1 * splitF4TracePosWitness.1) ∧
    LieAlgebra.IsSimple ℝ H3ZornF4Derivations ∧
    LieAlgebra.IsSimple ℝ h3OctonionCubicStabilizer ∧
    LieAlgebra.IsSimple ℝ H3OctonionF4Derivations ∧
    LieAlgebra.center ℝ H3ZornF4Derivations = ⊥ ∧
    LieAlgebra.center ℝ h3OctonionCubicStabilizer = ⊥ ∧
    LieAlgebra.center ℝ H3OctonionF4Derivations = ⊥ ∧
    Module.finrank ℂ (H3Octonion ℂ) = 27 ∧
    Module.finrank ℂ (H3Zorn ℂ) = 27 ∧
    H3Zorn.normCubic (h3OctonionComplexEquiv x) = H3Octonion.normCubic x ∧
    H3Zorn.traceBilin (h3OctonionComplexEquiv x) (h3OctonionComplexEquiv y) =
      H3Octonion.traceBilin x y ∧
    h3OctonionComplexEquiv (candidateJordanMulOctℂ x y) =
      candidateJordanMulZornℂ (h3OctonionComplexEquiv x) (h3OctonionComplexEquiv y) ∧
    H3Zorn.normCubic (tensorEquivH3Zorn (h3OctonionTensorEquivH3Zorn u)) =
      H3Octonion.normCubic (tensorEquivH3Octonion u) ∧
    Nonempty (ℂ ⊗[ℝ] h3OctonionCubicStabilizer ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] h3zornCubicStabilizer) ∧
    Nonempty (ℂ ⊗[ℝ] H3OctonionF4Derivations ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] H3ZornF4Derivations) ∧
    Nonempty (ℂ ⊗[ℝ] LieAlgebra.e₆ ℝ ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] h3OctonionCubicStabilizer) ∧
    (∃ A B : Matrix (Fin 27) (Fin 27) ℝ, A * B ≠ B * A) := by
  have hdim_oct : Module.finrank ℂ (H3Octonion ℂ) = 27 := by
    rw [← tensorEquivH3Octonion.finrank_eq,
      Module.finrank_eq_card_basis (H3Octonion.h3OctonionBasis.baseChange ℂ), Fintype.card_fin]
  have hdim_zorn : Module.finrank ℂ (H3Zorn ℂ) = 27 := by
    rw [← h3OctonionComplexEquiv.finrank_eq, hdim_oct]
  exact ⟨H3Octonion.no_jordanIso_H3Octonion_H3Zorn, compactF4_trace_sq_nonpos D,
    splitF4TracePosWitness_trace_sq_pos, h3ZornF4Derivations_isSimple,
    h3OctonionCubicStabilizer_isSimple, h3OctonionF4Derivations_isSimple,
    center_h3ZornF4Derivations_eq_bot, center_h3OctonionCubicStabilizer_eq_bot,
    center_h3OctonionF4Derivations_eq_bot, hdim_oct, hdim_zorn,
    h3OctonionComplexEquiv_normCubic x, h3OctonionComplexEquiv_traceBilin x y,
    h3OctonionComplexEquiv_jordanMul x y, h3OctonionTensorEquivH3Zorn_normCubic u,
    ⟨h3OctonionCubicStabilizerBaseChangeEquiv⟩, ⟨h3OctonionF4DerivationsBaseChangeEquiv⟩,
    ⟨cross_m2_serre_to_compact_e6_complex_equiv⟩, f4_matrix27_real_noncomm_witness⟩

end M2CrossFeatureTests

section M4CrossFeatureTests

open scoped TensorProduct
open InfoGeometry.Canonical.H3ZornTKKLieAlgebra
open InfoGeometry.Algebra.H3ZornFreudenthal

/-- Composed Lie homomorphism from Mathlib's `LieAlgebra.e₆ ℝ` via `h3zornE6SerreEquiv` into
133D `H3ZornTKKLie` (`𝔈₇(7)`). -/
noncomputable def cross_m4_e6_serre_to_e7_tkk :
    LieAlgebra.e₆ ℝ →ₗ⁅ℝ⁆ H3ZornTKKLie :=
  h3zornCubicStabilizerToTKK.comp (h3zornE6SerreEquiv : LieAlgebra.e₆ ℝ →ₗ⁅ℝ⁆ h3zornCubicStabilizer)

/-! ## `[M4-CONTRACT]` Tier 3 Pairwise: `E₆` Serre × `𝔈₇(7)` TKK × `E₇` Cartan/Root System -/

theorem cross_m4_e6_serre_into_e7_tkk_and_7d_cartan
    (x y : LieAlgebra.e₆ ℝ) (i j : Fin 7) (k : Fin 6) :
    Function.Injective cross_m4_e6_serre_to_e7_tkk ∧
    Function.Injective (h3zornTKKToNative ∘ cross_m4_e6_serre_to_e7_tkk) ∧
    cross_m4_e6_serre_to_e7_tkk ⁅x, y⁆ =
      ⁅cross_m4_e6_serre_to_e7_tkk x, cross_m4_e6_serre_to_e7_tkk y⁆ ∧
    h3zornTKKToNative (cross_m4_e6_serre_to_e7_tkk ⁅x, y⁆) =
      InfoGeometry.Canonical.H3ZornTKKNative.tkkBracket
        (h3zornTKKToNative (cross_m4_e6_serre_to_e7_tkk x))
        (h3zornTKKToNative (cross_m4_e6_serre_to_e7_tkk y)) ∧
    cross_m4_e6_serre_to_e7_tkk (e6SerreE k) = e7SimpleE k.castSucc ∧
    cross_m4_e6_serre_to_e7_tkk (e6SerreF k) = e7SimpleF k.castSucc ∧
    cross_m4_e6_serre_to_e7_tkk (e6SerreH k) = e7SimpleH k.castSucc ∧
    Module.finrank ℝ (LieAlgebra.e₆ ℝ) = 78 ∧
    Module.finrank ℝ H3ZornTKKLie = 133 ∧
    h3zornTKKGradeOp ∉ Set.range h3zornCubicStabilizerToTKK ∧
    h3zornTKKGradeOp ∉ Set.range cross_m4_e6_serre_to_e7_tkk ∧
    Module.finrank ℝ h3zornCartan = 6 ∧
    Module.finrank ℝ h3zornE7Cartan = 7 ∧
    h3zornE7Cartan.toSubmodule =
      h3zornCartan.toSubmodule.map h3zornCubicStabilizerToTKK.toLinearMap ⊔
        Submodule.span ℝ {h3zornTKKGradeOp} ∧
    Fintype.card h3zornE7Cartan.root = 126 ∧
    h3zornE7RootSystemBase.cartanMatrix.reindex
      h3zornE7BaseSupportEquiv.symm h3zornE7BaseSupportEquiv.symm = CartanMatrix.E 7 ∧
    h3zornE7RootSystem.pairing (e7SimpleMathlibRoot i) (e7SimpleMathlibRoot j) =
      (CartanMatrix.E 7 i j : ℝ) ∧
    LieAlgebra.IsSimple ℝ H3ZornTKKLie := by
  have hinj1 : Function.Injective cross_m4_e6_serre_to_e7_tkk :=
    h3zornCubicStabilizerToTKK_injective.comp h3zornE6SerreEquiv.injective
  have hinj2 : Function.Injective (h3zornTKKToNative ∘ cross_m4_e6_serre_to_e7_tkk) :=
    h3zornTKKToNative_injective.comp hinj1
  have hE : cross_m4_e6_serre_to_e7_tkk (e6SerreE k) = e7SimpleE k.castSucc := by
    change h3zornCubicStabilizerToTKK (h3zornE6SerreEquiv (e6SerreE k)) = e7SimpleE k.castSucc
    rw [m1_serre_equiv_E k, e7SimpleE_castSucc]
  have hF : cross_m4_e6_serre_to_e7_tkk (e6SerreF k) = e7SimpleF k.castSucc := by
    change h3zornCubicStabilizerToTKK (h3zornE6SerreEquiv (e6SerreF k)) = e7SimpleF k.castSucc
    rw [m1_serre_equiv_F k, e7SimpleF_castSucc]
  have hH : cross_m4_e6_serre_to_e7_tkk (e6SerreH k) = e7SimpleH k.castSucc := by
    change h3zornCubicStabilizerToTKK (h3zornE6SerreEquiv (e6SerreH k)) = e7SimpleH k.castSucc
    rw [m1_serre_equiv_H k, e7SimpleH_castSucc]
  have hnot1 : h3zornTKKGradeOp ∉ Set.range h3zornCubicStabilizerToTKK := by
    rintro ⟨T, hT⟩
    have h0 : (h3zornCubicStabilizerToTKK T).zero.1 = h3zornTKKGradeOp.zero.1 :=
      congrArg (fun Z : H3ZornTKKLie => Z.zero.1) hT
    change T.1 = h3zornStrOne.1 at h0
    exact h3zornStrOne_not_mem_cubicStabilizer (h0 ▸ T.2)
  have hnot2 : h3zornTKKGradeOp ∉ Set.range cross_m4_e6_serre_to_e7_tkk := by
    rintro ⟨z, hz⟩
    exact hnot1 ⟨h3zornE6SerreEquiv z, hz⟩
  exact ⟨hinj1, hinj2, cross_m4_e6_serre_to_e7_tkk.map_lie x y,
    by rw [cross_m4_e6_serre_to_e7_tkk.map_lie, h3zornTKKToNative_bracket],
    hE, hF, hH, finrank_e6_serre, finrank_H3ZornTKKLie, hnot1, hnot2,
    finrank_h3zornCartan, finrank_h3zornE7Cartan, h3zornE7Cartan_eq_sup,
    card_h3zornE7Cartan_root, h3zornE7RootSystemBase_cartanMatrix_eq,
    h3zornE7RootSystem_pairing_simple i j, h3zornTKKLie_isSimple⟩

/-! ## `[M4-CONTRACT]` Tier 3 Pairwise: Compact `𝔈₇(-25)` vs Split `𝔈₇(7)` Real Forms -/

theorem cross_m4_compact_vs_split_e7_real_forms
    (T₁ T₂ : h3OctonionCubicStabilizer) (S₁ S₂ : h3zornCubicStabilizer) :
    Module.finrank ℝ H3OctonionTKKLie = 133 ∧
    Module.finrank ℝ H3ZornTKKLie = 133 ∧
    LieAlgebra.IsKilling ℝ H3OctonionTKKLie ∧
    LieAlgebra.center ℝ H3OctonionTKKLie = ⊥ ∧
    Module.finrank ℝ h3OctonionCartanCompactSubalgebra = 79 ∧
    Module.finrank ℝ h3OctonionCartanNoncompactSubmodule = 54 ∧
    (Module.finrank ℝ h3OctonionCartanNoncompactSubmodule : ℤ) -
      Module.finrank ℝ h3OctonionCartanCompactSubalgebra = -25 ∧
    LieAlgebra.IsSimple ℝ H3ZornTKKLie ∧
    h3zornE7Cartan.IsCartanSubalgebra ∧
    LieModule.IsTriangularizable ℝ h3zornE7Cartan H3ZornTKKLie ∧
    Function.Injective h3OctonionCubicStabilizerToTKK ∧
    h3OctonionCubicStabilizerToTKK ⁅T₁, T₂⁆ =
      ⁅h3OctonionCubicStabilizerToTKK T₁, h3OctonionCubicStabilizerToTKK T₂⁆ ∧
    h3OctonionTKKGradeOp ∉ Set.range h3OctonionCubicStabilizerToTKK ∧
    Function.Injective h3zornCubicStabilizerToTKK ∧
    h3zornCubicStabilizerToTKK ⁅S₁, S₂⁆ =
      ⁅h3zornCubicStabilizerToTKK S₁, h3zornCubicStabilizerToTKK S₂⁆ ∧
    IsEmpty (H3Octonion ℝ ≃+* H3Zorn ℝ) ∧
    Nonempty (ℂ ⊗[ℝ] h3OctonionCubicStabilizer ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] h3zornCubicStabilizer) ∧
    killingForm ℝ H3OctonionTKKLie
      (H3OctonionTKKLie.negInj (1 : H3Octonion ℝ) - H3OctonionTKKLie.posInj (1 : H3Octonion ℝ))
      (H3OctonionTKKLie.negInj (1 : H3Octonion ℝ) - H3OctonionTKKLie.posInj (1 : H3Octonion ℝ)) <
      0 ∧
    0 < killingForm ℝ H3OctonionTKKLie
      (H3OctonionTKKLie.negInj (1 : H3Octonion ℝ) + H3OctonionTKKLie.posInj (1 : H3Octonion ℝ))
      (H3OctonionTKKLie.negInj (1 : H3Octonion ℝ) + H3OctonionTKKLie.posInj (1 : H3Octonion ℝ)) ∧
    ⁅e7SimpleH 0, e7SimpleE 0⁆ ≠ 0 := by
  have hnot_oct : h3OctonionTKKGradeOp ∉ Set.range h3OctonionCubicStabilizerToTKK := by
    rintro ⟨T₀, hT₀⟩
    have h0 : (h3OctonionCubicStabilizerToTKK T₀).zero.1 = h3OctonionTKKGradeOp.zero.1 :=
      congrArg (fun X : H3OctonionTKKLie => X.zero.1) hT₀
    change T₀.1 = h3OctonionStrOne.1 at h0
    exact h3OctonionStrOne_not_mem_cubicStabilizer (h0 ▸ T₀.2)
  exact ⟨finrank_H3OctonionTKKLie, finrank_H3ZornTKKLie, instIsKillingH3OctonionTKKLie,
    center_H3OctonionTKKLie_eq_bot, finrank_h3OctonionCartanCompactSubalgebra,
    finrank_h3OctonionCartanNoncompactSubmodule, h3OctonionCartan_signature_eq_neg_25,
    h3zornTKKLie_isSimple, h3zornE7Cartan_isCartanSubalgebra, h3zornE7Cartan_isTriangularizable,
    h3OctonionCubicStabilizerToTKK_injective,
    h3OctonionCubicStabilizerToTKK.map_lie (x := T₁) (y := T₂), hnot_oct,
    h3zornCubicStabilizerToTKK_injective,
    h3zornCubicStabilizerToTKK.map_lie (x := S₁) (y := S₂),
    H3Octonion.no_jordanIso_H3Octonion_H3Zorn, ⟨h3OctonionCubicStabilizerBaseChangeEquiv⟩,
    killingForm_compact_witness_neg, killingForm_noncompact_witness_pos,
    h3zornE7_noncomm_witness⟩

/-! ## `[M4-CONTRACT]` Tier 4 Scenario 3: Serre `E₆` → 27D → 133D `𝔈₇(7)` → 56D Levi + `E₇` Group -/

theorem scenario3_m4_serre_to_27d_133d_and_56d_levi
    (x y : LieAlgebra.e₆ ℝ) (v : H3Zorn ℝ) (g : h3zornReducedStructureGroup)
    (gE7 : freudenthalE7Group) (Q Q₁ Q₂ : Charge) :
    Module.finrank ℝ (LieAlgebra.e₆ ℝ) = 78 ∧
    Module.finrank ℝ (H3Zorn ℝ) = 27 ∧
    Module.finrank ℝ H3ZornTKKLie = 133 ∧
    Module.finrank ℝ Charge = 56 ∧
    Function.Bijective h3zornE6SerreEquiv ∧
    ⁅cross_m4_e6_serre_to_e7_tkk x, negInj v⁆ = negInj ((h3zornE6SerreEquiv x).1 v) ∧
    h3zornTKKToNative (cross_m4_e6_serre_to_e7_tkk ⁅x, y⁆) =
      InfoGeometry.Canonical.H3ZornTKKNative.tkkBracket
        (h3zornTKKToNative (cross_m4_e6_serre_to_e7_tkk x))
        (h3zornTKKToNative (cross_m4_e6_serre_to_e7_tkk y)) ∧
    LieAlgebra.IsSimple ℝ H3ZornTKKLie ∧
    h3zornE7RootSystem.IsRootSystem ∧
    h3zornE7RootSystem.IsIrreducible ∧
    Fintype.card h3zornE7Cartan.root = 126 ∧
    h3zornE7RootSystemBase.cartanMatrix.reindex
      h3zornE7BaseSupportEquiv.symm h3zornE7BaseSupportEquiv.symm = CartanMatrix.E 7 ∧
    leviChargeGL g ∈ freudenthalE7Group ∧
    symplecticForm (leviChargeEquiv g Q₁) (leviChargeEquiv g Q₂) = symplecticForm Q₁ Q₂ ∧
    quarticInvariant (leviChargeEquiv g Q) = quarticInvariant Q ∧
    symplecticForm (freudenthalE7GroupAction.act gE7 Q₁)
      (freudenthalE7GroupAction.act gE7 Q₂) = symplecticForm Q₁ Q₂ ∧
    quarticInvariant (freudenthalE7GroupAction.act gE7 Q) = quarticInvariant Q ∧
    quarticInvariant
      (freudenthalE7GroupAction.act gE7 (⟨1, 1, (1 : H3Zorn ℝ), (1 : H3Zorn ℝ)⟩ : Charge)) =
      -16 ∧
    Regular (freudenthalE7GroupAction.act gE7 (electricCharge 1 (1 : H3Zorn ℝ))) := by
  have hact27 :
      ⁅cross_m4_e6_serre_to_e7_tkk x, negInj v⁆ = negInj ((h3zornE6SerreEquiv x).1 v) := by
    change ⁅zeroInj ⟨(h3zornE6SerreEquiv x).1,
        h3zornCubicStabilizer_le_structureOperatorLieSubalgebra (h3zornE6SerreEquiv x).2⟩,
      negInj v⁆ = _
    rw [zeroInj_bracket_negInj]
  have htr1 : H3Zorn.traceBilin (1 : H3Zorn ℝ) 1 = 3 := by
    rw [H3Zorn.traceBilin_one]
    change (1 : ℝ) + 1 + 1 = 3
    norm_num
  have hmix :
      quarticInvariant
        (freudenthalE7GroupAction.act gE7 (⟨1, 1, (1 : H3Zorn ℝ), (1 : H3Zorn ℝ)⟩ : Charge)) =
        -16 := by
    have hq := freudenthalE7GroupAction.preserves_quarticInvariant gE7
      (⟨1, 1, (1 : H3Zorn ℝ), (1 : H3Zorn ℝ)⟩ : Charge)
    change quarticInvariant
        (freudenthalE7GroupAction.act gE7 (⟨1, 1, (1 : H3Zorn ℝ), (1 : H3Zorn ℝ)⟩ : Charge)) =
        quarticInvariant (⟨1, 1, (1 : H3Zorn ℝ), (1 : H3Zorn ℝ)⟩ : Charge) at hq
    rw [hq, quarticInvariant_expanded]
    simp only [H3Zorn.normCubic_one, H3Zorn.adjointQuad_one, htr1]
    norm_num
  have hreg : Regular (freudenthalE7GroupAction.act gE7 (electricCharge 1 (1 : H3Zorn ℝ))) := by
    refine (freudenthalE7GroupAction.regular_iff gE7 (electricCharge 1 1)).2 ?_
    change quarticInvariant (electricCharge 1 1) ≠ 0
    rw [unit_electric_quartic]
    norm_num
  exact ⟨finrank_e6_serre, InfoGeometry.Algebra.finrank_h3zorn, finrank_H3ZornTKKLie,
    finrank_charge, h3zornE6SerreEquiv.bijective, hact27,
    by rw [cross_m4_e6_serre_to_e7_tkk.map_lie, h3zornTKKToNative_bracket],
    h3zornTKKLie_isSimple, h3zornE7RootSystem_isRootSystem, h3zornE7RootSystem_isIrreducible,
    card_h3zornE7Cartan_root, h3zornE7RootSystemBase_cartanMatrix_eq,
    leviChargeGL_mem_freudenthalE7Group g,
    (freudenthalE7Group_le_invariantSubgroup (leviChargeGL_mem_freudenthalE7Group g)).1 Q₁ Q₂,
    (freudenthalE7Group_le_invariantSubgroup (leviChargeGL_mem_freudenthalE7Group g)).2 Q,
    freudenthalE7GroupAction.preserves_symplecticForm gE7 Q₁ Q₂,
    freudenthalE7GroupAction.preserves_quarticInvariant gE7 Q, hmix, hreg⟩

end M4CrossFeatureTests

section M6CrossFeatureTests

open scoped TensorProduct
open InfoGeometry.Algebra.MagicSquareTitsBracket
open InfoGeometry.Canonical.NativeTitsE8Carrier
open InfoGeometry.Canonical.SplitFreudenthalTitsE8Carrier
open InfoGeometry.Canonical.H3ZornTKKLieAlgebra
open InfoGeometry.Algebra.H3ZornFreudenthal
open InfoGeometry.Exceptional.CFSGPort.Chevalley

/-! ## `[M6-CONTRACT]` Tier 3 Pairwise: `G₂(2)` × `F₄(4)` × `SplitE8Lie` (`248D`) -/

theorem cross_m6_g2_f4_subalgebras_in_e8
    (D D₁ D₂ : G2DerivationCarrier) (E E₁ E₂ : F4DerivationCarrier) :
    Function.Injective embedG2 ∧
    Function.Injective embedF4 ∧
    embedG2 ⁅D₁, D₂⁆ = ⁅embedG2 D₁, embedG2 D₂⁆ ∧
    embedF4 ⁅E₁, E₂⁆ = ⁅embedF4 E₁, embedF4 E₂⁆ ∧
    ⁅embedG2 D, embedF4 E⁆ = 0 ∧
    ⁅embedF4 E, embedG2 D⁆ = 0 ∧
    Module.finrank ℝ G2DerivationCarrier = 14 ∧
    LieAlgebra.IsKilling ℝ InfoGeometry.Lie.CanonicalZornIsKilling.Der ∧
    Fintype.card InfoGeometry.Lie.CanonicalZornRootSystemComparison.RootIndex = 12 ∧
    Module.finrank ℝ F4DerivationCarrier = 52 ∧
    LieAlgebra.IsSimple ℝ H3ZornF4Derivations ∧
    Fintype.card {v : Fin (Tag.rank .F4) → ℤ // IsRoot .F4 v} = 48 ∧
    Module.finrank ℝ SplitE8Lie = 248 ∧
    Module.finrank ℝ splitE8Cartan = 8 ∧
    Fintype.card splitE8Cartan.root = 240 ∧
    LieAlgebra.IsSimple ℝ SplitE8Lie :=
  ⟨fun _ _ h => congrArg projG2 h,
   fun _ _ h => congrArg projF4 h,
   (bracket_g2_g2 D₁ D₂).symm,
   (bracket_f4_f4 E₁ E₂).symm,
   bracket_g2_f4 D E,
   bracket_f4_g2 E D,
   finrank_g2DerivationCarrier,
   InfoGeometry.Lie.CanonicalZornIsKilling.der_isKilling,
   InfoGeometry.Lie.SplitG2RealFormCapstone.split_g2_cartan_root_data.1,
   finrank_f4DerivationCarrier,
   h3ZornF4Derivations_isSimple,
   card_isRoot .F4,
   finrank_splitE8Lie,
   finrank_splitE8Cartan,
   card_splitE8Cartan_root,
   splitE8Lie_isSimple⟩

/-! ## `[M6-CONTRACT]` Tier 3 Pairwise: `F₄ < E₆ < E₇ < E₈` Dimension, Rank & Root Tower -/

theorem cross_m6_e6_e7_e8_dimension_and_rank_tower :
    Module.finrank ℝ H3ZornF4Derivations = 52 ∧
    Module.finrank ℝ h3zornCubicStabilizer = 78 ∧
    Module.finrank ℝ H3ZornTKKLie = 133 ∧
    Module.finrank ℝ SplitE8Lie = 248 ∧
    Module.finrank ℝ H3ZornF4Derivations < Module.finrank ℝ h3zornCubicStabilizer ∧
    Module.finrank ℝ h3zornCubicStabilizer < Module.finrank ℝ H3ZornTKKLie ∧
    Module.finrank ℝ H3ZornTKKLie < Module.finrank ℝ SplitE8Lie ∧
    Module.finrank ℝ f4Cartan < Module.finrank ℝ h3zornCartan ∧
    Module.finrank ℝ h3zornCartan < Module.finrank ℝ h3zornE7Cartan ∧
    Module.finrank ℝ h3zornE7Cartan < Module.finrank ℝ splitE8Cartan ∧
    Fintype.card {v : Fin (Tag.rank .F4) → ℤ // IsRoot .F4 v} <
      Fintype.card {v : Fin (Tag.rank .E6) → ℤ // IsRoot .E6 v} ∧
    Fintype.card {v : Fin (Tag.rank .E6) → ℤ // IsRoot .E6 v} <
      Fintype.card h3zornE7Cartan.root ∧
    Fintype.card h3zornE7Cartan.root < Fintype.card splitE8Cartan.root ∧
    LieAlgebra.IsSimple ℝ H3ZornF4Derivations ∧
    LieAlgebra.IsSimple ℝ h3zornCubicStabilizer ∧
    LieAlgebra.IsSimple ℝ H3ZornTKKLie ∧
    LieAlgebra.IsSimple ℝ SplitE8Lie ∧
    Nonempty (LieAlgebra.e₆ ℝ ≃ₗ⁅ℝ⁆ h3zornCubicStabilizer) ∧
    H3ZornF4Derivations ≤ h3zornCubicStabilizer ∧
    Function.Injective h3zornCubicStabilizerToTKK ∧
    Function.Injective embedF4 := by
  have hdim_f4 : Module.finrank ℝ H3ZornF4Derivations = 52 := finrank_H3ZornF4Derivations
  have hdim_e6 : Module.finrank ℝ h3zornCubicStabilizer = 78 := finrank_h3zornCubicStabilizer
  have hdim_e7 : Module.finrank ℝ H3ZornTKKLie = 133 := finrank_H3ZornTKKLie
  have hdim_e8 : Module.finrank ℝ SplitE8Lie = 248 := finrank_splitE8Lie
  have hrk_f4 : Module.finrank ℝ f4Cartan = 4 := finrank_f4Cartan
  have hrk_e6 : Module.finrank ℝ h3zornCartan = 6 := finrank_h3zornCartan
  have hrk_e7 : Module.finrank ℝ h3zornE7Cartan = 7 := finrank_h3zornE7Cartan
  have hrk_e8 : Module.finrank ℝ splitE8Cartan = 8 := finrank_splitE8Cartan
  have hrt_f4 : Fintype.card {v : Fin (Tag.rank .F4) → ℤ // IsRoot .F4 v} = 48 := card_isRoot .F4
  have hrt_e6 : Fintype.card {v : Fin (Tag.rank .E6) → ℤ // IsRoot .E6 v} = 72 := card_isRoot .E6
  have hrt_e7 : Fintype.card h3zornE7Cartan.root = 126 := card_h3zornE7Cartan_root
  have hrt_e8 : Fintype.card splitE8Cartan.root = 240 := card_splitE8Cartan_root
  refine ⟨hdim_f4, hdim_e6, hdim_e7, hdim_e8, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    h3ZornF4Derivations_isSimple, h3zornCubicStabilizer_isSimple, h3zornTKKLie_isSimple,
    splitE8Lie_isSimple, ⟨h3zornE6SerreEquiv⟩, H3ZornF4Derivations_le_h3zornCubicStabilizer,
    h3zornCubicStabilizerToTKK_injective, fun _ _ h => congrArg projF4 h⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

/-! ## `[M6-CONTRACT]` Tier 4 Scenario 1: Complete `𝕆_s/𝕆 → H₃ → F₄ → E₆ → E₇ → E₈` Tower -/

theorem scenario1_m6_complete_exceptional_jordan_to_lie_tower
    (gE7 : freudenthalE7Group) (Q Q₁ Q₂ : Charge) :
    Module.finrank ℝ (CompactOctonion ℝ) = 8 ∧
    Module.finrank ℝ InfoGeometry.Lie.CanonicalZornIsKilling.Der = 14 ∧
    LieAlgebra.IsKilling ℝ InfoGeometry.Lie.CanonicalZornIsKilling.Der ∧
    Fintype.card InfoGeometry.Lie.CanonicalZornRootSystemComparison.RootIndex = 12 ∧
    IsCommJordan (H3Octonion ℝ) ∧
    IsCommJordan (H3Zorn ℝ) ∧
    Module.finrank ℝ (H3Octonion ℝ) = 27 ∧
    Module.finrank ℝ (H3Zorn ℝ) = 27 ∧
    IsEmpty (H3Octonion ℝ ≃+* H3Zorn ℝ) ∧
    Nonempty (H3Octonion ℂ ≃ₗ[ℂ] H3Zorn ℂ) ∧
    Nonempty (ℂ ⊗[ℝ] H3Octonion ℝ ≃ₗ[ℂ] ℂ ⊗[ℝ] H3Zorn ℝ) ∧
    LieAlgebra.IsSimple ℝ H3ZornF4Derivations ∧
    LieAlgebra.IsSimple ℝ H3OctonionF4Derivations ∧
    Nonempty (LieAlgebra.e₆ ℝ ≃ₗ⁅ℝ⁆ h3zornCubicStabilizer) ∧
    LieAlgebra.IsSimple ℝ h3OctonionCubicStabilizer ∧
    Module.finrank ℝ H3ZornTKKLie = 133 ∧
    LieAlgebra.IsSimple ℝ H3ZornTKKLie ∧
    Fintype.card h3zornE7Cartan.root = 126 ∧
    h3zornE7RootSystemBase.cartanMatrix.reindex
      h3zornE7BaseSupportEquiv.symm h3zornE7BaseSupportEquiv.symm = CartanMatrix.E 7 ∧
    Module.finrank ℝ H3OctonionTKKLie = 133 ∧
    (Module.finrank ℝ h3OctonionCartanNoncompactSubmodule : ℤ) -
      Module.finrank ℝ h3OctonionCartanCompactSubalgebra = -25 ∧
    Module.finrank ℝ Charge = 56 ∧
    symplecticForm (freudenthalE7GroupAction.act gE7 Q₁)
      (freudenthalE7GroupAction.act gE7 Q₂) = symplecticForm Q₁ Q₂ ∧
    quarticInvariant (freudenthalE7GroupAction.act gE7 Q) = quarticInvariant Q ∧
    quarticInvariant (electricCharge 1 (1 : H3Zorn ℝ)) = -4 ∧
    Module.finrank ℝ SplitE8Lie = 248 ∧
    Module.finrank ℝ splitE8Cartan = 8 ∧
    Fintype.card splitE8Cartan.root = 240 ∧
    splitE8RootSystemBase.cartanMatrix.reindex
      splitE8BaseSupportEquiv.symm splitE8BaseSupportEquiv.symm = CartanMatrix.E 8 ∧
    LieAlgebra.IsSimple ℝ SplitE8Lie :=
  ⟨CompactOctonion.finrank_compactOctonion,
   InfoGeometry.Lie.SplitG2RealFormCapstone.parameter_model_is_fourteen_dimensional,
   InfoGeometry.Lie.CanonicalZornIsKilling.der_isKilling,
   InfoGeometry.Lie.SplitG2RealFormCapstone.split_g2_cartan_root_data.1,
   inferInstance,
   h3Zorn_isCommJordan,
   H3Octonion.finrank_h3Octonion,
   InfoGeometry.Algebra.finrank_h3zorn,
   H3Octonion.no_jordanIso_H3Octonion_H3Zorn,
   ⟨h3OctonionComplexEquiv⟩,
   ⟨h3OctonionTensorEquivH3Zorn⟩,
   h3ZornF4Derivations_isSimple,
   h3OctonionF4Derivations_isSimple,
   ⟨h3zornE6SerreEquiv⟩,
   h3OctonionCubicStabilizer_isSimple,
   finrank_H3ZornTKKLie,
   h3zornTKKLie_isSimple,
   card_h3zornE7Cartan_root,
   h3zornE7RootSystemBase_cartanMatrix_eq,
   finrank_H3OctonionTKKLie,
   h3OctonionCartan_signature_eq_neg_25,
   finrank_charge,
   freudenthalE7GroupAction.preserves_symplecticForm gE7 Q₁ Q₂,
   freudenthalE7GroupAction.preserves_quarticInvariant gE7 Q,
   unit_electric_quartic,
   finrank_splitE8Lie,
   finrank_splitE8Cartan,
   card_splitE8Cartan_root,
   splitE8RootSystemBase_cartanMatrix_eq,
   splitE8Lie_isSimple⟩

/-! ## `[M6-CONTRACT]` Tier 4 Scenario 5: Freudenthal–Tits Magic Square `E₈(8)` Synthesis -/

theorem scenario5_m6_magic_square_e8_synthesis
    (D : G2DerivationCarrier) (E : F4DerivationCarrier) (X Y Z : SplitE8Lie) :
    InfoGeometry.Lie.SplitOctonionStandardDerivation.standardDerivationSpan = ⊤ ∧
    Module.finrank ℝ H3ZornF4Derivations = 52 ∧
    Module.finrank ℝ MixedCarrier = 182 ∧
    Nonempty (NativeTitsCarrier ≃ₗ[ℝ] SplitTitsE8Carrier) ∧
    Nonempty (SplitE8Lie ≃ₗ[ℝ] NativeTitsCarrier) ∧
    Module.finrank ℝ SplitE8Lie = 248 ∧
    magicBracketLM X (magicBracketLM Y Z) =
      magicBracketLM (magicBracketLM X Y) Z + magicBracketLM Y (magicBracketLM X Z) ∧
    (∃ x y : SplitE8Lie, ⁅x, y⁆ ≠ 0) ∧
    ⁅embedG2 D, embedF4 E⁆ = 0 ∧
    Module.finrank ℝ splitE8Cartan = 8 ∧
    splitE8Cartan.IsCartanSubalgebra ∧
    LieModule.IsTriangularizable ℝ splitE8Cartan SplitE8Lie ∧
    splitE8RootSystem.IsRootSystem ∧
    splitE8RootSystem.IsCrystallographic ∧
    splitE8RootSystem.IsReduced ∧
    splitE8RootSystem.IsIrreducible ∧
    Fintype.card splitE8Cartan.root = 240 ∧
    splitE8RootSystemBase.cartanMatrix.reindex
      splitE8BaseSupportEquiv.symm splitE8BaseSupportEquiv.symm = CartanMatrix.E 8 ∧
    LieAlgebra.IsSimple ℝ SplitE8Lie :=
  ⟨InfoGeometry.Lie.SplitOctonionStandardDerivation.standardDerivations_span_top,
   finrank_H3ZornF4Derivations,
   finrank_mixedCarrier,
   ⟨nativeToSplitTitsE8Equiv⟩,
   ⟨splitE8LinearEquiv⟩,
   finrank_splitE8Lie,
   magicBracketLM_leibniz X Y Z,
   exists_bracket_ne_zero,
   bracket_g2_f4 D E,
   finrank_splitE8Cartan,
   splitE8Cartan_isCartanSubalgebra,
   splitE8Cartan_isTriangularizable,
   splitE8RootSystem_isRootSystem,
   splitE8RootSystem_isCrystallographic,
   splitE8RootSystem_isReduced,
   splitE8RootSystem_isIrreducible,
   card_splitE8Cartan_root,
   splitE8RootSystemBase_cartanMatrix_eq,
   splitE8Lie_isSimple⟩

end M6CrossFeatureTests

section M3CrossFeatureTests

open InfoGeometry.Algebra.H3ZornFreudenthal

private noncomputable def m3SerreAdjointEquiv (g : h3zornReducedStructureGroup) :
    LieAlgebra.e₆ ℝ ≃ₗ⁅ℝ⁆ LieAlgebra.e₆ ℝ :=
  h3zornE6SerreEquiv.trans ((h3zornAdjointAction g).trans h3zornE6SerreEquiv.symm)

/-! ## `[M1+M3-CONTRACT]` Tier 3 Pairwise: `E₆` Serre × Chevalley Generation × Bruhat × Adjoint -/

theorem cross_m3_serre_chevalley_bruhat_and_adjoint
    (g : h3zornReducedStructureGroup) (i : Fin 6) (c : ℝ) (x y : LieAlgebra.e₆ ℝ) :
    g ∈ h3zornChevalleyE6 ∧
    (∃ b₁ ∈ h3zornBorel, ∃ w ∈ h3zornWeylSubgroup, ∃ b₂ ∈ h3zornBorel, g = b₁ * w * b₂) ∧
    Function.Injective h3zornAdjointAction ∧
    m3SerreAdjointEquiv g ⁅x, y⁆ = ⁅m3SerreAdjointEquiv g x, m3SerreAdjointEquiv g y⁆ ∧
    Function.Injective m3SerreAdjointEquiv ∧
    m3SerreAdjointEquiv (h3zornSimpleX i c) x =
      x + c • ⁅e6SerreE i, x⁆ + (c ^ 2 / 2) • ⁅e6SerreE i, ⁅e6SerreE i, x⁆⁆ ∧
    m3SerreAdjointEquiv (h3zornSimpleX 2 1) (e6SerreH 2) =
      e6SerreH 2 - (2 : ℝ) • e6SerreE 2 ∧
    (∀ t : ℝˣ, ∀ j : Fin 6, m3SerreAdjointEquiv (h3zornTorusElt i t) (e6SerreH j) = e6SerreH j) := by
  have hg : g ∈ h3zornChevalleyE6 := by
    rw [h3zornChevalleyE6_eq_top]
    trivial
  have hm3_inj : Function.Injective m3SerreAdjointEquiv := by
    intro g₁ g₂ heq
    apply h3zornAdjointAction_injective
    apply LieEquiv.ext
    intro Y
    have h1 := congrArg (fun e : LieAlgebra.e₆ ℝ ≃ₗ⁅ℝ⁆ LieAlgebra.e₆ ℝ =>
      h3zornE6SerreEquiv (e (h3zornE6SerreEquiv.symm Y))) heq
    simpa [m3SerreAdjointEquiv] using h1
  have hadX : m3SerreAdjointEquiv (h3zornSimpleX i c) x =
      x + c • ⁅e6SerreE i, x⁆ + (c ^ 2 / 2) • ⁅e6SerreE i, ⁅e6SerreE i, x⁆⁆ := by
    dsimp [m3SerreAdjointEquiv]
    rw [h3zornAdjointAction_simpleX i c]
    have hE : e6SimpleE i = h3zornE6SerreEquiv (e6SerreE i) :=
      (h3zornE6SerreQuotientMap_E i).symm
    change h3zornE6SerreEquiv.symm
      (h3zornE6SerreEquiv x + c • ⁅e6SimpleE i, h3zornE6SerreEquiv x⁆ +
        (c ^ 2 / 2) • ⁅e6SimpleE i, ⁅e6SimpleE i, h3zornE6SerreEquiv x⁆⁆) = _
    rw [hE, ← LieEquiv.map_lie, ← LieEquiv.map_lie,
      ← map_smul, ← map_smul, ← map_add, ← map_add,
      h3zornE6SerreEquiv.symm_apply_apply]
  have had2 : m3SerreAdjointEquiv (h3zornSimpleX 2 1) (e6SerreH 2) =
      e6SerreH 2 - (2 : ℝ) • e6SerreE 2 := by
    dsimp [m3SerreAdjointEquiv]
    change h3zornE6SerreEquiv.symm
      (h3zornAdjointAction (h3zornSimpleX 2 1) (h3zornE6SerreEquiv (e6SerreH 2))) = _
    rw [show h3zornE6SerreEquiv (e6SerreH 2) = e6SimpleH 2 from h3zornE6SerreQuotientMap_H 2,
      h3zornAdjointAction_simpleX 2 1, one_smul, one_pow]
    have h1 : ⁅e6SimpleE 2, e6SimpleH 2⁆ = (-2 : ℝ) • e6SimpleE 2 := by
      rw [← lie_skew, e6Simple_bracket_HE]
      have hc : Tag.cartan .E6 (2 : Fin 6) (2 : Fin 6) = 2 := by decide
      rw [hc]
      module
    rw [h1, lie_smul, lie_self, smul_zero, smul_zero, add_zero,
      ← show h3zornE6SerreEquiv (e6SerreH 2) = e6SimpleH 2 from h3zornE6SerreQuotientMap_H 2,
      ← show h3zornE6SerreEquiv (e6SerreE 2) = e6SimpleE 2 from h3zornE6SerreQuotientMap_E 2,
      ← map_smul, ← map_add, h3zornE6SerreEquiv.symm_apply_apply]
    module
  have htor : ∀ (t : ℝˣ) (j : Fin 6),
      m3SerreAdjointEquiv (h3zornTorusElt i t) (e6SerreH j) = e6SerreH j := by
    intro t j
    dsimp [m3SerreAdjointEquiv]
    change h3zornE6SerreEquiv.symm
      (h3zornAdjointAction (h3zornTorusElt i t) (h3zornE6SerreEquiv (e6SerreH j))) = _
    rw [show h3zornE6SerreEquiv (e6SerreH j) = e6SimpleH j from h3zornE6SerreQuotientMap_H j,
      h3zornAdjointAction_torusElt_hVec i j t,
      ← show h3zornE6SerreEquiv (e6SerreH j) = e6SimpleH j from h3zornE6SerreQuotientMap_H j,
      h3zornE6SerreEquiv.symm_apply_apply]
  exact ⟨hg, h3zornBruhat_decomposition g, h3zornAdjointAction_injective,
    (m3SerreAdjointEquiv g).map_lie x y, hm3_inj, hadX, had2, htor⟩

/-! ## `[M3+M5-CONTRACT]` Tier 3 Pairwise: `Str₀ = E₆(6)` Bruhat Descent onto 56D Levi -/

theorem cross_m3_bruhat_descent_onto_56d_levi
    (g : h3zornReducedStructureGroup) (Q Q₁ Q₂ : Charge) :
    leviChargeSubgroup = chevalleyE6ChargeSubgroup ∧
    leviChargeGL g ∈ chevalleyE6ChargeSubgroup ∧
    (∃ b₁ ∈ h3zornBorel, ∃ w ∈ h3zornWeylSubgroup, ∃ b₂ ∈ h3zornBorel,
      leviChargeGL g = leviChargeGL b₁ * leviChargeGL w * leviChargeGL b₂ ∧
      leviChargeEquiv g Q = leviChargeEquiv b₁ (leviChargeEquiv w (leviChargeEquiv b₂ Q))) ∧
    symplecticForm (leviChargeGL g • Q₁) (leviChargeGL g • Q₂) = symplecticForm Q₁ Q₂ ∧
    quarticInvariant (leviChargeGL g • Q) = quarticInvariant Q ∧
    Function.Injective leviChargeGL ∧
    chevalleyE6ChargeSubgroup < freudenthalE7Group := by
  have heq_sub : leviChargeSubgroup = chevalleyE6ChargeSubgroup := by
    apply le_antisymm
    · rintro _ ⟨h, rfl⟩
      have hh : h ∈ h3zornChevalleyE6 := by
        rw [h3zornChevalleyE6_eq_top]
        trivial
      exact ⟨⟨h, hh⟩, rfl⟩
    · exact chevalleyE6ChargeSubgroup_le_leviChargeSubgroup
  have hmem : leviChargeGL g ∈ chevalleyE6ChargeSubgroup := by
    rw [← heq_sub]
    exact ⟨g, rfl⟩
  have hbru : ∃ b₁ ∈ h3zornBorel, ∃ w ∈ h3zornWeylSubgroup, ∃ b₂ ∈ h3zornBorel,
      leviChargeGL g = leviChargeGL b₁ * leviChargeGL w * leviChargeGL b₂ ∧
      leviChargeEquiv g Q = leviChargeEquiv b₁ (leviChargeEquiv w (leviChargeEquiv b₂ Q)) := by
    obtain ⟨b₁, hb₁, w, hw, b₂, hb₂, rfl⟩ := h3zornBruhat_decomposition g
    refine ⟨b₁, hb₁, w, hw, b₂, hb₂, ?_, ?_⟩
    · rw [map_mul, map_mul]
    · simp only [map_mul, LinearEquiv.mul_apply]
  have hsymp : symplecticForm (leviChargeGL g • Q₁) (leviChargeGL g • Q₂) =
      symplecticForm Q₁ Q₂ :=
    leviChargeEquiv_symplecticForm g Q₁ Q₂
  have hq : quarticInvariant (leviChargeGL g • Q) = quarticInvariant Q :=
    leviChargeEquiv_quarticInvariant g Q
  have hle_e7 : chevalleyE6ChargeSubgroup ≤ freudenthalE7Group := by
    rintro _ ⟨h, rfl⟩
    exact leviChargeGL_mem_freudenthalE7Group h.1
  have hlt_e7 : chevalleyE6ChargeSubgroup < freudenthalE7Group := by
    refine lt_of_le_of_ne hle_e7 ?_
    intro heq
    have hJ : glInversion ∈ chevalleyE6ChargeSubgroup := by
      rw [heq]
      exact glInversion_mem_freudenthalE7Group
    rcases hJ with ⟨h, hh⟩
    have hα := congrArg (fun e : ChargeGL => (e • scalarCharge 1 0).alpha) hh
    have hL : (chevalleyE6ChargeGL h • scalarCharge 1 0).alpha = 1 := rfl
    have hR : (glInversion • scalarCharge 1 0).alpha = 0 := by
      rw [glInversion_smul, freudenthalInversion_alpha]
      simp [scalarCharge]
    rw [hL, hR] at hα
    norm_num at hα
  exact ⟨heq_sub, hmem, hbru, hsymp, hq, leviChargeGL_injective, hlt_e7⟩

/-! ## `[M3+M5-CONTRACT]` Tier 4 Scenario 2: Full `E₆(6)` Bruhat → 56D Freudenthal `E₇(7)` Orbit Descent -/

private noncomputable def m3m5NondiagX : H3Zorn ℝ :=
  ⟨1, 2, 1, ZornVectorMatrix.one, ZornVectorMatrix.zero, ZornVectorMatrix.zero⟩

private theorem m3m5NondiagX_normCubic : H3Zorn.normCubic m3m5NondiagX = 1 := by
  simp [H3Zorn.normCubic, m3m5NondiagX, ZornVectorMatrix.norm, ZornVectorMatrix.trace,
    ZornVectorMatrix.mul, ZornVectorMatrix.one, ZornVectorMatrix.zero, ZornVec3.dot]
  norm_num

private theorem m3m5NondiagX_norm_ne_zero : H3Zorn.normCubic m3m5NondiagX ≠ 0 := by
  rw [m3m5NondiagX_normCubic]
  norm_num

theorem scenario2_m3_m5_full_bruhat_freudenthal_orbit_descent
    (g : h3zornReducedStructureGroup) (A B : H3Zorn ℝ) (Q Q₁ Q₂ : Charge) :
    let uNondiag : h3zornReducedStructureGroup :=
      ⟨h3zornULinearEquiv m3m5NondiagX m3m5NondiagX_norm_ne_zero,
        h3zornULinearEquiv_mem_reducedStructureGroup m3m5NondiagX
          m3m5NondiagX_norm_ne_zero (Or.inl m3m5NondiagX_normCubic)⟩
    g ∈ h3zornChevalleyE6 ∧
    uNondiag ∈ h3zornChevalleyE6 ∧
    uNondiag ∉ h3zornReducedStructureFixOne ∧
    (∃ b₁ ∈ h3zornBorel, ∃ w ∈ h3zornWeylSubgroup, ∃ b₂ ∈ h3zornBorel, g = b₁ * w * b₂) ∧
    (∃ b₁ ∈ h3zornBorel, ∃ w ∈ h3zornWeylSubgroup, ∃ b₂ ∈ h3zornBorel, uNondiag = b₁ * w * b₂) ∧
    (let gL : freudenthalE7Group := ⟨leviChargeGL g, leviChargeGL_mem_freudenthalE7Group g⟩
     let gU : freudenthalE7Group :=
       ⟨leviChargeGL uNondiag, leviChargeGL_mem_freudenthalE7Group uNondiag⟩
     let gUp : freudenthalE7Group :=
       ⟨glUpperTrans (Multiplicative.ofAdd A), glUpperTrans_mem_freudenthalE7Group A⟩
     let gLow : freudenthalE7Group :=
       ⟨glLowerTrans (Multiplicative.ofAdd B), glLowerTrans_mem_freudenthalE7Group B⟩
     let gJ : freudenthalE7Group := ⟨glInversion, glInversion_mem_freudenthalE7Group⟩
     let gWord : freudenthalE7Group := gL * gUp * gJ * gLow * gU
     symplecticForm (gWord.1 • Q₁) (gWord.1 • Q₂) = symplecticForm Q₁ Q₂ ∧
     quarticInvariant (gWord.1 • Q) = quarticInvariant Q ∧
     quarticInvariant (gWord.1 • (⟨1, 1, (1 : H3Zorn ℝ), (1 : H3Zorn ℝ)⟩ : Charge)) = -16 ∧
     Regular (gWord.1 • electricCharge 1 (1 : H3Zorn ℝ)) ∧
     Boundary (gWord.1 • electricCharge 0 (H3Zorn.diagCartan 1 0 0))) ∧
    h3zornReducedStructureFixOne < h3zornChevalleyE6 ∧
    leviChargeSubgroup < freudenthalE7Group := by
  intro uNondiag
  have hg_mem : g ∈ h3zornChevalleyE6 := by
    rw [h3zornChevalleyE6_eq_top]
    trivial
  have hu_mem : uNondiag ∈ h3zornChevalleyE6 :=
    h3zornULinearEquiv_one_mem_chevalleyE6 m3m5NondiagX
      m3m5NondiagX_norm_ne_zero m3m5NondiagX_normCubic
  have hu_not_fix : uNondiag ∉ h3zornReducedStructureFixOne := by
    intro hf
    have hf1 : uNondiag.1 1 = 1 := hf
    have hU : H3Zorn.U m3m5NondiagX 1 = 1 := by
      rw [← h3zornULinearEquiv_apply m3m5NondiagX m3m5NondiagX_norm_ne_zero 1]
      exact hf1
    have h1eq : (1 : H3Zorn ℝ) =
        ⟨1, 1, 1, ZornVectorMatrix.zero, ZornVectorMatrix.zero, ZornVectorMatrix.zero⟩ := rfl
    rw [h1eq] at hU
    have ha := congrArg (fun W : H3Zorn ℝ => W.a.a) hU
    simp [H3Zorn.U, H3Zorn.traceBilin, H3Zorn.crossProduct, H3Zorn.adjointQuad,
      m3m5NondiagX, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
      ZornVectorMatrix.trace, ZornVectorMatrix.norm, ZornVectorMatrix.one, ZornVectorMatrix.zero,
      ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.smul, ZornVectorMatrix.neg,
      ZornVec3.dot] at ha
    change (1 + 2 + 1 : ℝ) * 1 - (2 - (2 - 1) - 0) = 0 at ha
    norm_num at ha
  have htr1 : H3Zorn.traceBilin (1 : H3Zorn ℝ) 1 = 3 := by
    rw [H3Zorn.traceBilin_one]
    change (1 : ℝ) + 1 + 1 = 3
    norm_num
  have haut_lt : h3zornReducedStructureFixOne < h3zornChevalleyE6 :=
    lt_of_le_of_ne (fun f hf => h3zornReducedStructureFixOne_le_chevalleyE6 hf)
      (fun heq => hu_not_fix (heq ▸ hu_mem))
  have hlevi_lt : leviChargeSubgroup < freudenthalE7Group := by
    have h := (cross_m3_bruhat_descent_onto_56d_levi g Q Q₁ Q₂)
    rw [← h.1] at h
    exact h.2.2.2.2.2.2
  refine ⟨hg_mem, hu_mem, hu_not_fix, h3zornBruhat_decomposition g,
    h3zornBruhat_decomposition uNondiag, ?_, haut_lt, hlevi_lt⟩
  intro gL gU gUp gLow gJ gWord
  have hsymp : symplecticForm (gWord.1 • Q₁) (gWord.1 • Q₂) = symplecticForm Q₁ Q₂ :=
    freudenthalE7GroupAction.preserves_symplecticForm gWord Q₁ Q₂
  have hq : quarticInvariant (gWord.1 • Q) = quarticInvariant Q :=
    freudenthalE7GroupAction.preserves_quarticInvariant gWord Q
  have hmix :
      quarticInvariant (gWord.1 • (⟨1, 1, (1 : H3Zorn ℝ), (1 : H3Zorn ℝ)⟩ : Charge)) = -16 := by
    rw [(freudenthalE7Group_le_invariantSubgroup gWord.2).2, quarticInvariant_expanded]
    simp only [H3Zorn.normCubic_one, H3Zorn.adjointQuad_one, htr1]
    norm_num
  have hreg : Regular (gWord.1 • electricCharge 1 (1 : H3Zorn ℝ)) := by
    refine (freudenthalE7GroupAction.regular_iff gWord (electricCharge 1 1)).2 ?_
    change quarticInvariant (electricCharge 1 1) ≠ 0
    rw [unit_electric_quartic]
    norm_num
  have hbd : Boundary (gWord.1 • electricCharge 0 (H3Zorn.diagCartan 1 0 0)) := by
    refine (freudenthalE7GroupAction.boundary_iff gWord
      (electricCharge 0 (H3Zorn.diagCartan 1 0 0))).2 ?_
    refine ⟨?_, ?_⟩
    · change quarticInvariant (electricCharge 0 (H3Zorn.diagCartan 1 0 0)) = 0
      rw [quarticInvariant_electricCharge]
      norm_num
    · intro hz
      have hx := congrArg FreudenthalCharge.x hz
      have hα₁ := congrArg H3Zorn.α₁ hx
      change (1 : ℝ) = 0 at hα₁
      norm_num at hα₁
  exact ⟨hsymp, hq, hmix, hreg, hbd⟩

end M3CrossFeatureTests

end InfoGeometry.Tests.E6E7E8CrossFeature
