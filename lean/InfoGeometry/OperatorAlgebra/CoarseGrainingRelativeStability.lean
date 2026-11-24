/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CoarseGrainingVariational
import Mathlib.Analysis.Matrix.Order

/-!
# Relative stability of positive operator coarse-graining

The observation map `Q` is rectangular and fixed. The fine precision `A` and
coarse observation precision `R` are full positive definite matrices over an
`RCLike` field. The exact quadratic minimizer transports simultaneous scalar
lower and upper bounds to the coarse precision, with the same constants.

The proof uses the existing variational characterization and the native
positive-semidefinite matrix predicate. No commutation assumption is imposed.
The relative bounds are hypotheses on the finite-stage perturbations.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PositiveCoarseGraining

open Matrix
open scoped ComplexOrder MatrixOrder

variable {𝕜 n m : Type*} [RCLike 𝕜]
variable [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

private theorem posSemidef_of_re_quadratic_nonneg
    {ι : Type*} [Fintype ι] {M : Matrix ι ι 𝕜}
    (hM : M.IsHermitian)
    (h : ∀ x : ι → 𝕜, 0 ≤ RCLike.re (star x ⬝ᵥ (M *ᵥ x))) :
    M.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hM fun x => ?_
  refine RCLike.nonneg_iff.mpr ⟨h x, ?_⟩
  apply RCLike.conj_eq_iff_im.mp
  exact hM.star_dotProduct_mulVec_comm x x

private theorem re_quadratic_mono
    {ι : Type*} [Fintype ι] {B C : Matrix ι ι 𝕜}
    (hBC : (C - B).PosSemidef) (x : ι → 𝕜) :
    RCLike.re (star x ⬝ᵥ (B *ᵥ x)) ≤
      RCLike.re (star x ⬝ᵥ (C *ᵥ x)) := by
  have h := hBC.re_dotProduct_nonneg x
  simpa only [Matrix.sub_mulVec, dotProduct_sub, map_sub, sub_nonneg] using h

variable {A A' : Matrix n n 𝕜} {R R' : Matrix m m 𝕜} (Q : Matrix m n 𝕜)

omit [DecidableEq n] [DecidableEq m] in
/-- Increasing both precision matrices increases every fine-state energy. -/
theorem quadraticEnergy_mono (hA : (A' - A).PosSemidef)
    (hR : (R' - R).PosSemidef) (y : m → 𝕜) (x : n → 𝕜) :
    quadraticEnergy A R Q y x ≤ quadraticEnergy A' R' Q y x := by
  exact add_le_add (re_quadratic_mono hA x)
    (re_quadratic_mono hR (y - Q *ᵥ x))

omit [DecidableEq n] [DecidableEq m] in
/-- Simultaneous real scaling of both precisions scales the entire energy. -/
theorem quadraticEnergy_smul (c : ℝ) (y : m → 𝕜) (x : n → 𝕜) :
    quadraticEnergy (c • A) (c • R) Q y x = c * quadraticEnergy A R Q y x := by
  simp only [quadraticEnergy, Matrix.smul_mulVec, dotProduct_smul,
    RCLike.smul_re, mul_add]

/-- A common nonnegative lower factor for the two input precisions is a lower
factor for the coarse precision. -/
theorem coarsePrecision_scaled_lower_bound
    (hA : A.PosDef) (hR : R.PosDef) (hA' : A'.PosDef) (hR' : R'.PosDef)
    {c : ℝ} (hc : 0 ≤ c)
    (hAA' : (A' - c • A).PosSemidef) (hRR' : (R' - c • R).PosSemidef) :
    (coarsePrecision A' R' Q - c • coarsePrecision A R Q).PosSemidef := by
  apply posSemidef_of_re_quadratic_nonneg
    ((coarsePrecision_posDef Q hA' hR').isHermitian.sub
      ((coarsePrecision_posDef Q hA hR).isHermitian.smul (IsSelfAdjoint.all c)))
  intro y
  have hmin := mul_le_mul_of_nonneg_left
    (quadraticEnergy_lower_bound Q hA hR y (harmonicExtension A' R' Q *ᵥ y)) hc
  have henergy := quadraticEnergy_mono Q hAA' hRR' y
    (harmonicExtension A' R' Q *ᵥ y)
  rw [quadraticEnergy_smul,
    quadraticEnergy_at_harmonicExtension Q hA' hR' y] at henergy
  simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul, map_sub, RCLike.smul_re] using sub_nonneg.mpr (hmin.trans henergy)

/-- A common nonnegative upper factor for the two input precisions is an upper
factor for the coarse precision. -/
theorem coarsePrecision_scaled_upper_bound
    (hA : A.PosDef) (hR : R.PosDef) (hA' : A'.PosDef) (hR' : R'.PosDef)
    {c : ℝ} (hc : 0 ≤ c)
    (hAA' : (c • A - A').PosSemidef) (hRR' : (c • R - R').PosSemidef) :
    (c • coarsePrecision A R Q - coarsePrecision A' R' Q).PosSemidef := by
  apply posSemidef_of_re_quadratic_nonneg
    (((coarsePrecision_posDef Q hA hR).isHermitian.smul (IsSelfAdjoint.all c)).sub
      (coarsePrecision_posDef Q hA' hR').isHermitian)
  intro y
  have hmin := quadraticEnergy_lower_bound Q hA' hR' y
    (harmonicExtension A R Q *ᵥ y)
  have henergy := quadraticEnergy_mono Q hAA' hRR' y
    (harmonicExtension A R Q *ᵥ y)
  rw [quadraticEnergy_smul] at henergy
  have hbase := mul_le_mul_of_nonneg_left
    (le_of_eq (quadraticEnergy_at_harmonicExtension Q hA hR y)) hc
  simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul, map_sub, RCLike.smul_re] using
    sub_nonneg.mpr ((hmin.trans henergy).trans hbase)

/-- Coarse precision is jointly monotone in the two precision matrices. -/
theorem coarsePrecision_mono
    (hA : A.PosDef) (hR : R.PosDef) (hA' : A'.PosDef) (hR' : R'.PosDef)
    (hAA' : (A' - A).PosSemidef) (hRR' : (R' - R).PosSemidef) :
    (coarsePrecision A' R' Q - coarsePrecision A R Q).PosSemidef := by
  simpa only [one_smul] using
    coarsePrecision_scaled_lower_bound Q hA hR hA' hR'
      (c := 1) zero_le_one (by simpa only [one_smul] using hAA')
      (by simpa only [one_smul] using hRR')

/-- Positive simultaneous scaling is exactly homogeneous for coarse precision. -/
theorem coarsePrecision_smul (hA : A.PosDef) (hR : R.PosDef)
    {c : ℝ} (hc : 0 < c) :
    coarsePrecision (c • A) (c • R) Q = c • coarsePrecision A R Q := by
  have hA' : (c • A).PosDef := hA.smul hc
  have hR' : (c • R).PosDef := hR.smul hc
  have hzeroA : (c • A - c • A).PosSemidef := by
    simpa only [sub_self] using (Matrix.PosSemidef.zero : (0 : Matrix n n 𝕜).PosSemidef)
  have hzeroR : (c • R - c • R).PosSemidef := by
    simpa only [sub_self] using (Matrix.PosSemidef.zero : (0 : Matrix m m 𝕜).PosSemidef)
  apply le_antisymm
  · exact Matrix.le_iff.mpr
      (coarsePrecision_scaled_upper_bound Q hA hR hA' hR' hc.le hzeroA hzeroR)
  · exact Matrix.le_iff.mpr
      (coarsePrecision_scaled_lower_bound Q hA hR hA' hR' hc.le hzeroA hzeroR)

/-- Positive simultaneous scaling preserves the unique harmonic extension. -/
theorem harmonicExtension_smul (hA : A.PosDef) (hR : R.PosDef)
    {c : ℝ} (hc : 0 < c) :
    harmonicExtension (c • A) (c • R) Q = harmonicExtension A R Q := by
  apply Matrix.ext_iff_mulVec.mpr
  intro y
  symm
  apply (is_minimizer_iff Q (hA.smul hc) (hR.smul hc) y _).1
  intro x
  simp only [quadraticEnergy_smul]
  exact mul_le_mul_of_nonneg_left
    ((is_minimizer_iff Q hA hR y _).2 rfl x) hc.le

/-- Relative Loewner perturbations of both precisions pass through exact
elimination with the same radius, for a fixed rectangular observation map. -/
theorem coarsePrecision_relative_sandwich
    (hA : A.PosDef) (hR : R.PosDef) (hA' : A'.PosDef) (hR' : R'.PosDef)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hAlo : (A' - (1 - r) • A).PosSemidef)
    (hAhi : ((1 + r) • A - A').PosSemidef)
    (hRlo : (R' - (1 - r) • R).PosSemidef)
    (hRhi : ((1 + r) • R - R').PosSemidef) :
    (coarsePrecision A' R' Q - (1 - r) • coarsePrecision A R Q).PosSemidef ∧
      ((1 + r) • coarsePrecision A R Q - coarsePrecision A' R' Q).PosSemidef := by
  constructor
  · exact coarsePrecision_scaled_lower_bound Q hA hR hA' hR'
      (sub_nonneg.mpr hr1.le) hAlo hRlo
  · exact coarsePrecision_scaled_upper_bound Q hA hR hA' hR'
      (add_nonneg zero_le_one hr) hAhi hRhi

end InfoGeometry.OperatorAlgebra.PositiveCoarseGraining
