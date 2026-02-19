import InfoGeometry.Jordan.SPD
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

/-!
# Log-Det Barrier and Burg Divergence on SPD

Matrix-level convex potential and its canonical Bregman/Burg divergence for
real symmetric positive-definite matrices.
-/

namespace InfoGeometry.Jordan

open Matrix
open scoped MatrixOrder

section SPD

variable {n : ℕ}

/-- Log-determinant barrier on SPD matrices. -/
noncomputable def logDetBarrier (X : SPD n) : ℝ :=
  -Real.log (Matrix.det X.mat)

lemma SPD.det_pos (X : SPD n) : 0 < Matrix.det X.mat :=
  X.pos.det_pos

lemma SPD.det_ne_zero (X : SPD n) : Matrix.det X.mat ≠ 0 :=
  X.det_pos.ne'

/-- Distortion matrix `Y⁻¹X` used by the Burg/log-det divergence. -/
noncomputable def normalizedDistortion (X Y : SPD n) :
    Matrix (Fin n) (Fin n) ℝ :=
  Y.mat⁻¹ * X.mat

lemma normalizedDistortion_det_pos (X Y : SPD n) :
    0 < Matrix.det (normalizedDistortion X Y) := by
  unfold normalizedDistortion
  have hYinv : 0 < Matrix.det (Y.mat⁻¹) := (Y.pos.inv).det_pos
  have hX : 0 < Matrix.det X.mat := X.det_pos
  calc
    0 < Matrix.det (Y.mat⁻¹) * Matrix.det X.mat := mul_pos hYinv hX
    _ = Matrix.det (Y.mat⁻¹ * X.mat) := by
          symm
          exact Matrix.det_mul (Y.mat⁻¹) X.mat

/-- Log-det/Burg matrix divergence:
`tr(Y⁻¹X) - log det(Y⁻¹X) - n`. -/
noncomputable def logDetBregman (X Y : SPD n) : ℝ :=
  Matrix.trace (normalizedDistortion X Y)
    - Real.log (Matrix.det (normalizedDistortion X Y))
    - (n : ℝ)

/-- Scalar nonnegativity template: `tr(A) - log det(A) - n ≥ 0` for positive-definite `A`. -/
lemma trace_sub_logdet_sub_dim_nonneg_of_posDef
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) :
    0 ≤ Matrix.trace A - Real.log (Matrix.det A) - (n : ℝ) := by
  let hH : A.IsHermitian := hA.isHermitian
  have htrace : Matrix.trace A = ∑ i : Fin n, hH.eigenvalues i := by
    simpa [hH] using Matrix.IsHermitian.trace_eq_sum_eigenvalues (A := A) hH
  have hdet : Matrix.det A = ∏ i : Fin n, hH.eigenvalues i := by
    simpa [hH] using hH.det_eq_prod_eigenvalues
  have hpos : ∀ i : Fin n, 0 < hH.eigenvalues i := fun i => by
    simpa [hH] using hA.eigenvalues_pos i
  have hlogdet : Real.log (Matrix.det A) = ∑ i : Fin n, Real.log (hH.eigenvalues i) := by
    rw [hdet]
    calc
      Real.log (∏ i : Fin n, hH.eigenvalues i)
          = Real.log (∏ i ∈ (Finset.univ : Finset (Fin n)), hH.eigenvalues i) := by
              simp
      _ = ∑ i ∈ (Finset.univ : Finset (Fin n)), Real.log (hH.eigenvalues i) := by
            exact Real.log_prod
              (s := (Finset.univ : Finset (Fin n)))
              (f := fun i => hH.eigenvalues i)
              (by
                intro i hi
                exact (hpos i).ne')
      _ = ∑ i : Fin n, Real.log (hH.eigenvalues i) := by
            simp
  have hterm :
      ∀ i : Fin n, 0 ≤ hH.eigenvalues i - Real.log (hH.eigenvalues i) - 1 := by
    intro i
    have hlog : Real.log (hH.eigenvalues i) ≤ hH.eigenvalues i - 1 :=
      Real.log_le_sub_one_of_pos (hpos i)
    linarith
  have hsum_nonneg :
      0 ≤ ∑ i : Fin n, (hH.eigenvalues i - Real.log (hH.eigenvalues i) - 1) := by
    refine Finset.sum_nonneg ?_
    intro i hi
    exact hterm i
  have hrewrite :
      Matrix.trace A - Real.log (Matrix.det A) - (n : ℝ)
        = ∑ i : Fin n, (hH.eigenvalues i - Real.log (hH.eigenvalues i) - 1) := by
    rw [htrace, hlogdet]
    have hcard : (n : ℝ) = ∑ _i : Fin n, (1 : ℝ) := by simp
    rw [hcard]
    calc
      (∑ i : Fin n, hH.eigenvalues i) - (∑ i : Fin n, Real.log (hH.eigenvalues i))
          - (∑ _i : Fin n, (1 : ℝ))
          = (∑ i : Fin n, (hH.eigenvalues i - Real.log (hH.eigenvalues i)))
              - (∑ _i : Fin n, (1 : ℝ)) := by
              rw [Finset.sum_sub_distrib]
      _ = ∑ i : Fin n, ((hH.eigenvalues i - Real.log (hH.eigenvalues i)) - 1) := by
            rw [← Finset.sum_sub_distrib]
      _ = ∑ i : Fin n, (hH.eigenvalues i - Real.log (hH.eigenvalues i) - 1) := by
            simp
  rw [hrewrite]
  exact hsum_nonneg

/-- Nonnegativity of the Burg divergence in the commuting SPD case. -/
lemma logDetBregman_nonneg_of_commute
    (X Y : SPD n)
    (hcomm : Commute X.mat Y.mat⁻¹) :
    0 ≤ logDetBregman X Y := by
  have hprodPos : (Y.mat⁻¹ * X.mat).PosDef := by
    exact
      ((Y.pos.inv.isStrictlyPositive.commute_iff X.pos.isStrictlyPositive).1 hcomm.symm).posDef
  simpa [logDetBregman, normalizedDistortion] using
    trace_sub_logdet_sub_dim_nonneg_of_posDef (A := Y.mat⁻¹ * X.mat) hprodPos

/-- Unconditional nonnegativity of the Burg divergence on SPD matrices. -/
lemma logDetBregman_nonneg
    (X Y : SPD n) :
    0 ≤ logDetBregman X Y := by
  let U : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt (Y.mat⁻¹)
  have hYinv_nonneg : 0 ≤ Y.mat⁻¹ := Y.pos.inv.posSemidef.nonneg
  have hU_nonneg : 0 ≤ U := by
    simp [U]
  have hU_posSemidef : U.PosSemidef := hU_nonneg.posSemidef
  have hU_star : star U = U := by
    calc
      star U = Uᴴ := Matrix.star_eq_conjTranspose U
      _ = U := hU_posSemidef.isHermitian.eq
  have hU_sq : U * U = Y.mat⁻¹ := by
    simpa [U] using CFC.sqrt_mul_sqrt_self (a := Y.mat⁻¹) (ha := hYinv_nonneg)
  have hU_unit : IsUnit U := by
    simpa [U] using (CFC.isUnit_sqrt_iff (a := Y.mat⁻¹) (ha := hYinv_nonneg)).2 (Y.pos.inv.isUnit)
  have hA_pos : (U * X.mat * U).PosDef := by
    have hA' : (star U * X.mat * U).PosDef :=
      (Matrix.IsUnit.posDef_star_left_conjugate_iff (U := U) (x := X.mat) hU_unit).2 X.pos
    simpa [hU_star, mul_assoc] using hA'
  have hbase :
      0 ≤ Matrix.trace (U * X.mat * U)
        - Real.log (Matrix.det (U * X.mat * U))
        - (n : ℝ) :=
    trace_sub_logdet_sub_dim_nonneg_of_posDef (A := U * X.mat * U) hA_pos
  have htrace :
      Matrix.trace (normalizedDistortion X Y) = Matrix.trace (U * X.mat * U) := by
    calc
      Matrix.trace (normalizedDistortion X Y)
          = Matrix.trace ((Y.mat⁻¹) * X.mat) := by simp [normalizedDistortion]
      _ = Matrix.trace ((U * U) * X.mat) := by simp [hU_sq]
      _ = Matrix.trace (U * U * X.mat) := by simp [mul_assoc]
      _ = Matrix.trace (X.mat * U * U) := by
            simpa [mul_assoc] using Matrix.trace_mul_cycle U U X.mat
      _ = Matrix.trace (U * X.mat * U) := by
            simpa [mul_assoc] using Matrix.trace_mul_cycle X.mat U U
      _ = Matrix.trace (U * X.mat * U) := by simp [mul_assoc]
  have hdet :
      Matrix.det (normalizedDistortion X Y) = Matrix.det (U * X.mat * U) := by
    calc
      Matrix.det (normalizedDistortion X Y)
          = Matrix.det (Y.mat⁻¹ * X.mat) := by simp [normalizedDistortion]
      _ = Matrix.det ((U * U) * X.mat) := by simp [hU_sq]
      _ = Matrix.det (U * X.mat * U) := by
            simp [Matrix.det_mul, mul_assoc, mul_left_comm, mul_comm]
  have hrewrite :
      logDetBregman X Y
        = Matrix.trace (U * X.mat * U)
            - Real.log (Matrix.det (U * X.mat * U))
            - (n : ℝ) := by
    unfold logDetBregman
    rw [htrace, hdet]
  rw [hrewrite]
  exact hbase

@[simp]
lemma logDetBregman_self (X : SPD n) :
    logDetBregman X X = 0 := by
  unfold logDetBregman normalizedDistortion
  have hmul : X.mat⁻¹ * X.mat = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    letI : Invertible X.mat := X.pos.isUnit.invertible
    simp
  simp [hmul]

end SPD

end InfoGeometry.Jordan
