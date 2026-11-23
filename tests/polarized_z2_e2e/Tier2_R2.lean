/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Lean.Util.CollectAxioms
import Lean.Elab.Command
import InfoGeometry.Canonical.CurvedZ2GradedDGA
import InfoGeometry.Canonical.PeirceBoundaryComplex
import InfoGeometry.Algebra.GradedNullconeAlgebra

set_option autoImplicit false

/-!
# E2E Tier 2 (R2): Boundary Value Analysis & R5 Separations (Features F6–F8)

Opaque-box boundary, degenerate-case, and R5 separation tests for Requirement R2:
* F6: Even Lie vs odd Jordan restriction, `F = 0` boundary, centrality equivalence for `∂_F² = 0`,
  non-flat Bianchi preservation, and opposite-sign odd-generator anticommutator.
* F7: Mutual exclusivity of the three curvature regimes, negative-unit central curvature (`h = -1`),
  directed Peirce corner flatness with nonzero differential, non-central `4 × 4` witness, and
  ambient matrix noncommutativity.
* F8: `G² = 0 ⇒ D_G²(x) = -(G x G + G x G)`, explicit `M₂(ℝ)` nilpotent `D_G² ≠ 0` vs `∂_G² = 0`,
  product-evaluation discrepancy, odd-element `2 x F` discrepancy, and universal obstruction.
-/

namespace PolarizedZ2E2E.Tier2R2

attribute [local instance 100] LieRing.ofAssociativeRing

open InfoGeometry.Canonical.CurvedZ2GradedDGA
open InfoGeometry.Canonical.PeirceBoundaryComplex
open InfoGeometry.Algebra.GradedNullconeAlgebra
open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.Core.PeirceGrading
open InfoGeometry.Core.JordanMultiplicationClosure

/-! ## Feature F6: Boundary & Degenerate DGA Behavior -/

theorem t2_f6_even_vs_odd_action_split
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (D : CurvedZ2GradedDGA R A) (x : A) :
    D.diff 1 = 0 ∧
    (D.IsEven x → D.diff x = LieAlgebra.ad R A D.oddGen x) ∧
    (D.IsOdd x → D.diff x = jordanLeft (R := R) D.oddGen x) :=
  ⟨D.diff_one, fun hx => D.diff_of_even_eq_ad hx, fun hx => D.diff_of_odd_eq_jordanLeft hx⟩

theorem t2_f6_zero_oddGen_degenerate_boundary
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {Γ : A} (hΓ : Γ * Γ = 1) :
    let h0 : parityConj Γ (0 : A) = -(0 : A) := by simp [parityConj_apply]
    let D := CurvedZ2GradedDGA.ofParityConj (R := R) hΓ h0
    D.curvature = 0 ∧ D.diff = 0 ∧ D.diff ^ 2 = 0 := by
  dsimp only
  refine ⟨by simp, ?_, ?_⟩
  · ext x
    simp only [CurvedZ2GradedDGA.ofParityConj_diff_apply, gradedInnerDiff, zero_mul, mul_zero,
      sub_self, LinearMap.zero_apply]
  · exact CurvedZ2GradedDGA.diff_sq_eq_zero_of_curvature_eq_zero _ (by simp)

theorem t2_f6_diff_sq_zero_iff_commutes_boundary
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (D : CurvedZ2GradedDGA R A) :
    (D.diff ^ 2 = 0 ↔ ∀ x : A, D.curvature * x = x * D.curvature) ∧
    (IsCentralNonzeroRegime D.curvature → D.diff ^ 2 = 0 ∧ D.curvature ≠ 0) :=
  ⟨D.diff_sq_eq_zero_iff_commutes, isCentralNonzeroRegime_implies_diff_sq_zero D⟩

theorem t2_f6_nonflat_bianchi_still_holds :
    nonCentralMat4DGA.diff ^ 2 ≠ 0 ∧
    nonCentralMat4DGA.diff nonCentralMat4DGA.curvature = 0 ∧
    nonCentralBlockDGA.diff ^ 2 ≠ 0 ∧
    nonCentralBlockDGA.diff nonCentralBlockDGA.curvature = 0 :=
  ⟨nonCentralMat4DGA_diff_sq_ne_zero, nonCentralMat4DGA_bianchi,
    nonCentralBlockDGA_diff_sq_ne_zero, nonCentralBlockDGA_bianchi⟩

theorem t2_f6_diff_anticommutator_opposite_signs
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {Γ F : A} (hΓ : Γ * Γ = 1) (hF : parityConj Γ F = -F) :
    let D₁ := CurvedZ2GradedDGA.ofParityConj (R := R) hΓ hF
    let D₂ := CurvedZ2GradedDGA.ofParityConj (R := R) hΓ
      (show parityConj Γ (-F) = -(-F) by
        rw [parityConj_apply, mul_neg, neg_mul, ← parityConj_apply, hF])
    D₁.diff + D₂.diff = 0 ∧
    D₁.diff * D₂.diff + D₂.diff * D₁.diff = LieAlgebra.ad R A (-(F * F + F * F)) := by
  intro D₁ D₂
  constructor
  · ext x
    simp [D₁, D₂, CurvedZ2GradedDGA.diff_apply, CurvedZ2GradedDGA.ofParityConj_oddGen,
      CurvedZ2GradedDGA.ofParityConj_parity]
  · have hα : D₁.parity = D₂.parity := rfl
    have hanti := CurvedZ2GradedDGA.diff_anticommutator D₁ D₂ hα
    rw [hanti]
    simp only [D₁, D₂, CurvedZ2GradedDGA.ofParityConj_oddGen, mul_neg, neg_mul, ← neg_add]

/-! ## Feature F7: Regime Mutual Exclusivity & Boundary Witnesses -/

theorem t2_f7_regimes_mutually_exclusive_concrete :
    ¬ IsCentralNonzeroRegime flatMat2DGA.curvature ∧
    ¬ IsNonCentralRegime flatMat2DGA.curvature ∧
    ¬ IsFlatRegime centralMat2DGA.curvature ∧
    ¬ IsNonCentralRegime centralMat2DGA.curvature ∧
    ¬ IsFlatRegime nonCentralMat4DGA.curvature ∧
    ¬ IsCentralNonzeroRegime nonCentralMat4DGA.curvature := by
  have h1 := curvatureRegime_trichotomy flatMat2DGA.curvature
  have h2 := curvatureRegime_trichotomy centralMat2DGA.curvature
  have h3 := curvatureRegime_trichotomy nonCentralMat4DGA.curvature
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun hc => h1.2.1 ⟨flatMat2DGA_isFlat, hc⟩
  · exact fun hnc => h1.2.2.1 ⟨flatMat2DGA_isFlat, hnc⟩
  · exact fun hf => h2.2.1 ⟨hf, centralMat2DGA_isCentralNonzero⟩
  · exact fun hnc => h2.2.2.2 ⟨centralMat2DGA_isCentralNonzero, hnc⟩
  · exact fun hf => h3.2.2.1 ⟨hf, nonCentralMat4DGA_isNonCentral⟩
  · exact fun hc => h3.2.2.2 ⟨hc, nonCentralMat4DGA_isNonCentral⟩

theorem t2_f7_central_skew_negative_unit_curvature :
    centralSkewMat2DGA.curvature = -1 ∧
    IsCentralNonzeroRegime centralSkewMat2DGA.curvature ∧
    classifyRegime centralSkewMat2DGA.curvature = .centralNonzero ∧
    centralSkewMat2DGA.diff ^ 2 = 0 :=
  ⟨centralSkewMat2DGA_curvature_eq_neg_one,
    centralSkewMat2DGA_isCentralNonzero,
    (classifyRegime_eq_centralNonzero_iff _).mpr centralSkewMat2DGA_isCentralNonzero,
    centralSkewMat2DGA_diff_sq⟩

theorem t2_f7_peirce_corner_flat_nonzero_diff :
    let p : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
    let hp : IsIdempotentElem p := by
      change p * p = p
      ext i j
      fin_cases i <;> fin_cases j <;> simp [p, Matrix.mul_apply, Fin.sum_univ_two]
    let hu : atomNeg2 ∈ peirce10 p := by
      refine ⟨atomNeg2, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [complementIdempotent, p, atomNeg2, Matrix.mul_apply, Fin.sum_univ_two]
    IsFlatRegime (ofPeirce10 (R := ℝ) hp hu).curvature ∧
    (ofPeirce10 (R := ℝ) hp hu).diff ^ 2 = 0 ∧
    (ofPeirce10 (R := ℝ) hp hu).diff ≠ 0 := by
  intro p hp hu
  have hu0 : atomNeg2 ≠ 0 := by
    intro h
    have h01 := congrFun (congrFun h 0) 1
    simp [atomNeg2] at h01
  exact ⟨ofPeirce10_isFlat hp hu, ofPeirce10_diff_sq hp hu, ofPeirce10_diff_ne_zero hp hu hu0⟩

theorem t2_f7_noncentral_mat4_explicit_witness_element :
    nonCentralMat4DGA.curvature = !![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] ∧
    nonCentralMat4DGA.diff (nonCentralMat4DGA.diff nonCentralTest4) = nonCentralTest4 ∧
    nonCentralTest4 ≠ 0 ∧
    nonCentralMat4DGA.diff ^ 2 ≠ 0 :=
  ⟨nonCentralMat4DGA_curvature,
    nonCentralMat4DGA_diff_sq_test,
    nonCentralMat4DGA_test4_ne_zero,
    nonCentralMat4DGA_diff_sq_ne_zero⟩

theorem t2_f7_matrix_noncommutativity_for_curvatures :
    (∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A) ∧
    (∃ A B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ, A * B ≠ B * A) ∧
    (∃ A B : Matrix (Fin 4) (Fin 4) ℝ, A * B ≠ B * A) :=
  ⟨mat2R_noncommutative_witness, mat2Sum2R_mul_noncommutative, mat4R_mul_noncommutative⟩

/-! ## Feature F8: R5 Commutator vs Curved Differential Separations -/

theorem t2_f8_sq_zero_commutator_deriv_formula
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {G : A} (hG : G * G = 0) (x : A) :
    commutatorDeriv (R := R) G (commutatorDeriv (R := R) G x) = -(G * x * G + G * x * G) :=
  commutatorDeriv_sq_of_sq_zero hG x

theorem t2_f8_nilpotent_mat2_explicit_D_G_sq_vs_curved_sq :
    atomNeg2 * atomNeg2 = 0 ∧
    commutatorDeriv (R := ℝ) atomNeg2 (commutatorDeriv (R := ℝ) atomNeg2 atomPos2) =
      !![0, -2; 0, 0] ∧
    commutatorDeriv (R := ℝ) atomNeg2 (commutatorDeriv (R := ℝ) atomNeg2 atomPos2) ≠ 0 ∧
    (flatMat2DGA.diff ^ 2) atomPos2 = 0 := by
  have h := nilpotent_commutatorDeriv_sq_ne_zero
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  rw [flatMat2DGA_diff_sq, LinearMap.zero_apply]

theorem t2_f8_product_evaluation_separation :
    flatMat2DGA.diff (atomPos2 * !![1, 0; 0, 0]) ≠
      commutatorDeriv (R := ℝ) atomNeg2 (atomPos2 * !![1, 0; 0, 0]) ∧
    flatMat2DGA.diff (atomPos2 * !![1, 0; 0, 0]) = 1 ∧
    commutatorDeriv (R := ℝ) atomNeg2 (atomPos2 * !![1, 0; 0, 0]) = gammaCut2 := by
  have hprod : atomPos2 * (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) = atomPos2 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [atomPos2, Matrix.mul_apply, Fin.sum_univ_two]
  have hcomm : commutatorDeriv (R := ℝ) atomNeg2 atomPos2 = gammaCut2 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [commutatorDeriv_apply, atomNeg2, atomPos2, gammaCut2]
  refine ⟨nilpotent_commutatorDeriv_sq_ne_zero.2.2.2.2.2, ?_, ?_⟩
  · rw [hprod, flatMat2DGA_diff_atomPos2]
  · rw [hprod, hcomm]

theorem t2_f8_commutator_vs_curved_on_odd_nonzero :
    centralMat2DGA.IsOdd atomPos2 ∧
    centralMat2DGA.diff atomPos2 - commutatorDeriv (R := ℝ) gammaMir2 atomPos2 =
      (2 : ℝ) • (atomPos2 * gammaMir2) ∧
    (2 : ℝ) • (atomPos2 * gammaMir2) ≠ 0 := by
  have hOdd : centralMat2DGA.IsOdd atomPos2 := by
    change parityConj gammaCut2 atomPos2 = -atomPos2
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [parityConj_apply, gammaCut2, atomPos2, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨hOdd, curvedDiff_sub_commutatorDeriv_of_odd centralMat2DGA hOdd, ?_⟩
  intro h0
  have h11 := congrFun (congrFun h0 1) 1
  simp [atomPos2, gammaMir2] at h11

theorem t2_f8_universal_obstruction_blocks_any_G
    (G : Matrix (Fin 2) (Fin 2) ℝ) :
    flatMat2DGA.diff = commutatorDeriv (R := ℝ) G →
      (atomNeg2 - flatMat2DGA.parity atomNeg2) * flatMat2DGA.diff atomPos2 = 0 ∧ False := by
  intro h
  have hobs := curvedDiff_eq_commutatorDeriv_obstruction flatMat2DGA h atomNeg2 atomPos2
  exact ⟨hobs, flatMat2DGA_diff_ne_commutatorDeriv G h⟩

end PolarizedZ2E2E.Tier2R2

section E2EAxiomAudit
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut audited : Nat := 0
  for (name, info) in env.constants do
    if (env.getModuleIdxFor? name).isSome then continue
    if name.toString.startsWith "_private." then continue
    match info with
    | .thmInfo _ | .defnInfo _ =>
      if info.isUnsafe || info.isPartial then
        throwError "Unsafe or partial E2E declaration: {name}"
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Disallowed axiom {ax} in E2E declaration {name}"
      audited := audited + 1
    | .axiomInfo _ =>
      throwError "Disallowed axiom declaration in E2E file: {name}"
    | _ => pure ()
  if audited == 0 then
    throwError "E2EAxiomAudit found 0 declarations in current module"
  logInfo m!"E2E_AXIOM_AUDIT_PASS: {audited} local declarations verified"
end E2EAxiomAudit
