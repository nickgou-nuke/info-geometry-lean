/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixEntropyUnitaryOrbit
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Klein's inequality for the actual matrix logarithm

The source and reference are arbitrary strictly positive complex matrices.
Their independently chosen eigenbases are related by a unitary matrix. Its
squared-entry overlaps form a doubly stochastic array, and retain the relative
position of the two spectral resolutions. No common eigenbasis or commutation
hypothesis is imposed.

The resulting trace inequality applies to the actual native CFC logarithms.
For trace-one inputs it gives nonnegative Umegaki relative entropy. This owner
does not construct a tensor-product erasure process or prove a joint-system
Landauer theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.MatrixRelativeEntropy

open Matrix
open MatrixEntropyUnitaryOrbit
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℂ

/-- The overlap of two spectral bases, expressed in their relative unitary. -/
def unitaryOverlap (U : unitary Mat) (i j : n) : ℝ :=
  Complex.normSq ((U : Mat) i j)

theorem unitaryOverlap_nonneg (U : unitary Mat) (i j : n) :
    0 ≤ unitaryOverlap U i j :=
  Complex.normSq_nonneg _

theorem unitaryOverlap_row_sum (U : unitary Mat) (i : n) :
    ∑ j, unitaryOverlap U i j = 1 := by
  have h := congrArg (fun A : Mat => (A i i).re) (Unitary.coe_mul_star_self U)
  simpa only [Unitary.coe_star, Matrix.mul_apply, Matrix.star_apply, Complex.star_def,
    Complex.mul_conj, Complex.re_sum, Complex.ofReal_re,
    Matrix.one_apply_eq, Complex.one_re, unitaryOverlap] using h

theorem unitaryOverlap_column_sum (U : unitary Mat) (j : n) :
    ∑ i, unitaryOverlap U i j = 1 := by
  have h := congrArg (fun A : Mat => (A j j).re) (Unitary.coe_star_mul_self U)
  simpa only [Matrix.mul_apply, Matrix.star_apply, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.re_sum, Complex.ofReal_re,
    Matrix.one_apply_eq, Complex.one_re, unitaryOverlap] using h

private theorem overlap_row_weighted_sum (U : unitary Mat) (a : n → ℝ) :
    (∑ i, ∑ j, a i * unitaryOverlap U i j) = ∑ i, a i := by
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum, unitaryOverlap_row_sum, mul_one]

private theorem overlap_column_weighted_sum (U : unitary Mat) (b : n → ℝ) :
    (∑ i, ∑ j, b j * unitaryOverlap U i j) = ∑ j, b j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_sum, unitaryOverlap_column_sum, mul_one]

private theorem scalar_log_lower_bound (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a - b ≤ a * (Real.log a - Real.log b) := by
  have h := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hb ha)) ha.le
  rw [Real.log_div hb.ne' ha.ne'] at h
  have hdiv : a * (b / a - 1) = b - a := by
    field_simp [ha.ne']
  rw [hdiv] at h
  nlinarith

/-- The scalar log bound is summed against the full relative spectral overlaps. -/
theorem unitaryOverlap_log_lower_bound (U : unitary Mat) (a b : n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) :
    (∑ i, a i) - (∑ j, b j) ≤
      (∑ i, a i * Real.log (a i)) -
        ∑ i, ∑ j, a i * Real.log (b j) * unitaryOverlap U i j := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      mul_le_mul_of_nonneg_right
        (scalar_log_lower_bound (a i) (b j) (ha i) (hb j))
        (unitaryOverlap_nonneg U i j)))
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib] at h
  rw [overlap_row_weighted_sum, overlap_column_weighted_sum,
    overlap_row_weighted_sum] at h
  exact h

private theorem trace_diagonal_mul_conjugate (U : unitary Mat) (a b : n → ℝ) :
    (Matrix.trace (Matrix.diagonal (fun i => (a i : ℂ)) *
      ((U : Mat) * Matrix.diagonal (fun j => (b j : ℂ)) * star (U : Mat)))).re =
        ∑ i, ∑ j, a i * b j * unitaryOverlap U i j := by
  have hentry (i : n) :
      ((U : Mat) * Matrix.diagonal (fun j => (b j : ℂ)) * star (U : Mat)) i i =
        ∑ j, (U : Mat) i j * (b j : ℂ) * star ((U : Mat) i j) := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.star_apply]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, hentry,
    Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hm : (a i : ℂ) * ((U : Mat) i j * (b j : ℂ) * star ((U : Mat) i j)) =
      ((a i * b j : ℝ) : ℂ) *
        ((U : Mat) i j * star ((U : Mat) i j)) := by
    push_cast
    ring
  rw [hm, Complex.star_def, Complex.mul_conj]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, unitaryOverlap]

private theorem trace_conjugate_mul_conjugate
    (U V : unitary Mat) (a b : n → ℝ) :
    (Matrix.trace
      (((U : Mat) * Matrix.diagonal (fun i => (a i : ℂ)) * star (U : Mat)) *
        ((V : Mat) * Matrix.diagonal (fun j => (b j : ℂ)) * star (V : Mat)))).re =
      ∑ i, ∑ j, a i * b j * unitaryOverlap (star U * V) i j := by
  let A : Mat := Matrix.diagonal (fun i => (a i : ℂ))
  let B : Mat := Matrix.diagonal (fun j => (b j : ℂ))
  have htrace :
      Matrix.trace (((U : Mat) * A * star (U : Mat)) *
        ((V : Mat) * B * star (V : Mat))) =
      Matrix.trace (A * (((star U * V : unitary Mat) : Mat) * B *
        star ((star U * V : unitary Mat) : Mat))) := by
    calc
      Matrix.trace (((U : Mat) * A * star (U : Mat)) *
          ((V : Mat) * B * star (V : Mat))) =
          Matrix.trace ((U : Mat) *
            (A * star (U : Mat) * (V : Mat) * B * star (V : Mat))) := by
              simp only [mul_assoc]
      _ = Matrix.trace ((A * star (U : Mat) * (V : Mat) * B * star (V : Mat)) *
          (U : Mat)) := Matrix.trace_mul_comm _ _
      _ = _ := by
        simp only [Submonoid.coe_mul, Unitary.coe_star, star_mul, star_star, mul_assoc]
  change (Matrix.trace (((U : Mat) * A * star (U : Mat)) *
    ((V : Mat) * B * star (V : Mat)))).re = _
  rw [htrace]
  exact trace_diagonal_mul_conjugate (star U * V) a b

/-- Mixed functional-calculus trace keeps both independent spectral resolutions. -/
theorem trace_mul_cfc_eq_overlap_sum (A B : Mat)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℝ) :
    (Matrix.trace (A * cfc f B)).re =
      ∑ i, ∑ j, hA.eigenvalues i * f (hB.eigenvalues j) *
        unitaryOverlap (star hA.eigenvectorUnitary * hB.eigenvectorUnitary) i j := by
  have hprod : A * cfc f B =
      ((hA.eigenvectorUnitary : Mat) *
        Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) *
          star (hA.eigenvectorUnitary : Mat)) *
      ((hB.eigenvectorUnitary : Mat) *
        Matrix.diagonal (fun j => (f (hB.eigenvalues j) : ℂ)) *
          star (hB.eigenvectorUnitary : Mat)) :=
    congrArg₂ (· * ·) hA.spectral_theorem (hB.cfc_eq f)
  rw [hprod]
  exact trace_conjugate_mul_conjugate hA.eigenvectorUnitary hB.eigenvectorUnitary
    hA.eigenvalues (fun j => f (hB.eigenvalues j))

/-- A state and its own functional calculus share the state spectral basis. -/
theorem trace_mul_cfc_self (A : Mat) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (Matrix.trace (A * cfc f A)).re = ∑ i, hA.eigenvalues i * f (hA.eigenvalues i) := by
  let φ := Unitary.conjStarAlgAut ℂ Mat hA.eigenvectorUnitary
  let D : Mat := Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))
  let E : Mat := Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ))
  have hmul : A * cfc f A = φ (D * E) := by
    rw [map_mul]
    congr 1
    · exact hA.spectral_theorem
    · exact hA.cfc_eq f
  rw [hmul]
  change (Matrix.trace ((hA.eigenvectorUnitary : Mat) * (D * E) *
    star (hA.eigenvectorUnitary : Mat))).re = _
  rw [trace_unitary_conjugate]
  simp [D, E, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]

/-- Klein's inequality for two arbitrary strictly positive full matrices. -/
theorem relativeLogTrace_ge_trace_sub (A B : Mat)
    (hA : IsStrictlyPositive A) (hB : IsStrictlyPositive B) :
    (Matrix.trace (A - B)).re ≤
      (Matrix.trace (A * (CFC.log A - CFC.log B))).re := by
  have hAp : A.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp hA
  have hBp : B.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp hB
  let a := hAp.isHermitian.eigenvalues
  let b := hBp.isHermitian.eigenvalues
  let U := star hAp.isHermitian.eigenvectorUnitary * hBp.isHermitian.eigenvectorUnitary
  have ha : ∀ i, 0 < a i := hAp.eigenvalues_pos
  have hb : ∀ j, 0 < b j := hBp.eigenvalues_pos
  have htrA : (Matrix.trace A).re = ∑ i, a i := by
    rw [hAp.isHermitian.trace_eq_sum_eigenvalues]
    simp only [Complex.re_sum, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re, a]
  have htrB : (Matrix.trace B).re = ∑ j, b j := by
    rw [hBp.isHermitian.trace_eq_sum_eigenvalues]
    simp only [Complex.re_sum, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re, b]
  calc
    (Matrix.trace (A - B)).re = (∑ i, a i) - (∑ j, b j) := by
      rw [Matrix.trace_sub, Complex.sub_re, htrA, htrB]
    _ ≤ (∑ i, a i * Real.log (a i)) -
        ∑ i, ∑ j, a i * Real.log (b j) * unitaryOverlap U i j :=
      unitaryOverlap_log_lower_bound U a b ha hb
    _ = (Matrix.trace (A * (CFC.log A - CFC.log B))).re := by
      simp only [CFC.log]
      rw [mul_sub, Matrix.trace_sub, Complex.sub_re,
        trace_mul_cfc_self A hAp.isHermitian,
        trace_mul_cfc_eq_overlap_sum A B hAp.isHermitian hBp.isHermitian]

/-- Actual Umegaki nonnegativity for faithful trace-one matrix states. -/
theorem relativeLogTrace_nonneg (A B : Mat)
    (hA : IsStrictlyPositive A) (hB : IsStrictlyPositive B)
    (htA : Matrix.trace A = 1) (htB : Matrix.trace B = 1) :
    0 ≤ (Matrix.trace (A * (CFC.log A - CFC.log B))).re := by
  have h := relativeLogTrace_ge_trace_sub A B hA hB
  simpa only [Matrix.trace_sub, htA, htB, sub_self, Complex.zero_re] using h

/-- Compatibility with the existing actual entropy owner. -/
theorem relativeLogTrace_eq_neg_entropy_sub_crossLog (A B : Mat) :
    (Matrix.trace (A * (CFC.log A - CFC.log B))).re =
      -matrixEntropy A - (Matrix.trace (A * CFC.log B)).re := by
  rw [mul_sub, Matrix.trace_sub, Complex.sub_re, matrixEntropy_eq, neg_neg]

end InfoGeometry.Canonical.MatrixRelativeEntropy
