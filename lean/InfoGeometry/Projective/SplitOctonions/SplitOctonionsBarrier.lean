import InfoGeometry.Projective.SplitOctonions.ZornInstance
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# InfoGeometry.Projective.SplitOctonions.SplitOctonionsBarrier

Concrete logarithmic barrier lemmas for the diagonal Zorn slice.

This file proves the actual algebraic/analytic facts needed for the
information-geometric reconciliation:

* the diagonal Zorn determinant is `a*b`;
* the barrier is `-log a - log b = -log(detZ)` on the positive diagonal cone;
* the first derivative in the `a` coordinate is `-a⁻¹`;
* the Hessian entry is `a⁻¹^2`, hence positive in the interior;
* convergence of `-log(det)` implies convergence of the barrier to `+∞`.

It does not claim full self-concordance. Full self-concordance requires the
third-derivative inequality and should be proved separately.
-/

noncomputable section

namespace InfoGeometry.Projective.SplitOctonions

namespace ZornCell

variable {V : Type*}
variable [AddCommGroup V] [Module ℝ V]

/--
The diagonal Zorn cell

`[ a  0 ]`
`[ 0  b ]`.
-/
def diagonalCell (a b : ℝ) : ZornCell ℝ V :=
  { a := a, b := b, v := 0, w := 0 }

/-- The Zorn determinant on the diagonal slice is `a*b`. -/
@[simp] theorem detZ_diagonalCell
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (a b : ℝ) :
    ZornCell.detZ B (diagonalCell (V := V) a b) = a * b := by
  simp [diagonalCell, ZornCell.detZ]

/--
Positive diagonal cone.

This is the interior where the logarithmic barrier is finite.
-/
def diagonalInCone (a b : ℝ) : Prop :=
  0 < a ∧ 0 < b

/--
The diagonal logarithmic barrier:

`F(a,b) = -log a - log b`.
-/
def diagonalBarrier (a b : ℝ) : ℝ :=
  -Real.log a - Real.log b

/--
The determinant logarithmic barrier:

`F(X) = -log(detZ X)`.
-/
def detBarrier
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (X : ZornCell ℝ V) : ℝ :=
  -Real.log (ZornCell.detZ B X)

/--
On the positive diagonal cone,

`-log a - log b = -log(a*b) = -log(detZ(diag(a,b)))`.
-/
theorem diagonalBarrier_eq_detBarrier
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    {a b : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    diagonalBarrier a b = detBarrier B (diagonalCell (V := V) a b) := by
  unfold diagonalBarrier detBarrier
  rw [detZ_diagonalCell]
  rw [Real.log_mul ha hb]
  ring

/-- Same theorem with positivity hypotheses. -/
theorem diagonalBarrier_eq_detBarrier_of_pos
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    {a b : ℝ}
    (hcone : diagonalInCone a b) :
    diagonalBarrier a b = detBarrier B (diagonalCell (V := V) a b) := by
  exact diagonalBarrier_eq_detBarrier (V := V) B hcone.1.ne' hcone.2.ne'

/--
First derivative in the `a` coordinate:

`∂/∂a (-log a - log b) = -a⁻¹`.
-/
theorem diagonalBarrier_hasDerivAt_a
    {a b : ℝ} (ha : a ≠ 0) :
    HasDerivAt (fun x : ℝ => diagonalBarrier x b) (-(a⁻¹)) a := by
  unfold diagonalBarrier
  have hlog : HasDerivAt Real.log (a⁻¹) a := by
    simpa [one_div] using Real.hasDerivAt_log ha
  have hconst : HasDerivAt (fun _ : ℝ => Real.log b) 0 a :=
    hasDerivAt_const a (Real.log b)
  change HasDerivAt ((fun x : ℝ => -Real.log x) - (fun _ : ℝ => Real.log b)) (-(a⁻¹)) a
  simpa using hlog.neg.sub hconst

/--
First derivative in the `b` coordinate:

`∂/∂b (-log a - log b) = -b⁻¹`.
-/
theorem diagonalBarrier_hasDerivAt_b
    {a b : ℝ} (hb : b ≠ 0) :
    HasDerivAt (fun y : ℝ => diagonalBarrier a y) (-(b⁻¹)) b := by
  unfold diagonalBarrier
  have hconst : HasDerivAt (fun _ : ℝ => -Real.log a) 0 b :=
    hasDerivAt_const b (-Real.log a)
  have hlog : HasDerivAt Real.log (b⁻¹) b := by
    simpa [one_div] using Real.hasDerivAt_log hb
  change HasDerivAt ((fun _ : ℝ => -Real.log a) - (fun y : ℝ => Real.log y)) (-(b⁻¹)) b
  simpa using hconst.sub hlog

/--
Derivative of the `a`-gradient:

`d/da (-a⁻¹) = a⁻¹^2`.

This is the diagonal Hessian entry of the logarithmic barrier.
-/
theorem diagonalBarrier_hessian_a
    {a : ℝ} (ha : a ≠ 0) :
    HasDerivAt (fun x : ℝ => -(x⁻¹)) (a⁻¹ ^ 2) a := by
  have hinv : HasDerivAt (fun x : ℝ => x⁻¹) (-(a ^ 2)⁻¹) a := hasDerivAt_inv ha
  have hneg : HasDerivAt (fun x : ℝ => -(x⁻¹)) ((a ^ 2)⁻¹) a := by
    simpa using hinv.neg
  have hpow : (a ^ 2)⁻¹ = a⁻¹ ^ 2 := by
    field_simp [ha]
  rw [← hpow]
  exact hneg

/--
Derivative of the `b`-gradient:

`d/db (-b⁻¹) = b⁻¹^2`.
-/
theorem diagonalBarrier_hessian_b
    {b : ℝ} (hb : b ≠ 0) :
    HasDerivAt (fun y : ℝ => -(y⁻¹)) (b⁻¹ ^ 2) b := by
  have hinv : HasDerivAt (fun y : ℝ => y⁻¹) (-(b ^ 2)⁻¹) b := hasDerivAt_inv hb
  have hneg : HasDerivAt (fun y : ℝ => -(y⁻¹)) ((b ^ 2)⁻¹) b := by
    simpa using hinv.neg
  have hpow : (b ^ 2)⁻¹ = b⁻¹ ^ 2 := by
    field_simp [hb]
  rw [← hpow]
  exact hneg

/-- The `a` Hessian entry is strictly positive in the cone interior. -/
theorem diagonalBarrier_hessian_a_pos
    {a : ℝ} (ha : a ≠ 0) :
    0 < a⁻¹ ^ 2 := by
  exact sq_pos_of_ne_zero (inv_ne_zero ha)

/-- The `b` Hessian entry is strictly positive in the cone interior. -/
theorem diagonalBarrier_hessian_b_pos
    {b : ℝ} (hb : b ≠ 0) :
    0 < b⁻¹ ^ 2 := by
  exact sq_pos_of_ne_zero (inv_ne_zero hb)

/--
The diagonal barrier agrees pointwise with the negative log determinant product.

This is the exact algebraic bridge used to transfer limit statements about
`-log(det)` to the diagonal Zorn barrier.
-/
theorem diagonalBarrier_eq_negLog_product_of_pos
    {a b : ℝ} (hcone : diagonalInCone a b) :
    diagonalBarrier a b = -Real.log (a * b) := by
  unfold diagonalBarrier
  rw [Real.log_mul hcone.1.ne' hcone.2.ne']
  ring

/--
If the negative logarithm of the diagonal determinant tends to `+∞`, then the
diagonal barrier tends to `+∞`.

This is the robust repository-level limit lemma. The separate analytic fact
`-log t → +∞` as `t → 0⁺` can be plugged into the hypothesis without hiding it
inside this file.
-/
theorem diagonalBarrier_tendsto_atTop_of_negLog_det
    (a b : ℕ → ℝ)
    (hcone : ∀ n : ℕ, diagonalInCone (a n) (b n))
    (hlog :
      Filter.Tendsto
        (fun n : ℕ => -Real.log (a n * b n))
        Filter.atTop
        Filter.atTop) :
    Filter.Tendsto
      (fun n : ℕ => diagonalBarrier (a n) (b n))
      Filter.atTop
      Filter.atTop := by
  convert hlog using 1
  ext n
  exact diagonalBarrier_eq_negLog_product_of_pos (hcone n)

end ZornCell

end InfoGeometry.Projective.SplitOctonions
