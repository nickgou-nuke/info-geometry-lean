/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Architecture.MatrixSymmetricConeFisherRao
import InfoGeometry.Analysis.FiniteMatrixJacobiDerivative
import InfoGeometry.Quantum.OperatorTraceShapeDecomposition
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Trace

/-!
# Real matrix radial geometry and determinant-level tangents

The existing real affine Fisher bilinear form pairs the radial tangent `S`
with a tangent `X` as one half of `trace (S⁻¹ * X)`. Jacobi's actual derivative
formula identifies this trace with the derivative of `log |det|`, so tangents
with zero logarithmic determinant derivative are orthogonal to the radial
direction for that form.

The full bilinear split reuses `OperatorTraceShapeDecomposition.shapePart` on
the native endomorphism associated to `S⁻¹ * X`. The coordinate conversion is
explicit and no second shape carrier or metric is introduced. All products
retain their order; no simultaneous diagonalization or commutation hypothesis
is imposed. Algebraic identities hold at arbitrary invertible real matrices.
They do not assert positivity of this form outside the positive symmetric
cone, or identify determinant-level sets with arbitrary entropy-level sets.
-/

noncomputable section

namespace InfoGeometry.Geometry.RealMatrixFisherRadial

open InfoGeometry.Architecture.MatrixSymmetricCone
open InfoGeometry.Analysis.FiniteMatrixJacobiDerivative
open InfoGeometry.Quantum.OperatorTraceShapeDecomposition

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℝ

/-- The existing Fisher form makes the radial tangent dual to one half of
the logarithmic determinant differential. -/
theorem fisherRaoMetric_radial (S X : Mat) (hS : IsUnit S) :
    fisherRaoMetric S⁻¹ S X = (1 / 2 : ℝ) * Matrix.trace (S⁻¹ * X) := by
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS
  unfold fisherRaoMetric
  rw [Matrix.nonsing_inv_mul S hdet, one_mul]

/-- The squared radial length has the dimension factor of the existing
normalization of the Fisher form. -/
theorem fisherRaoMetric_radial_self (S : Mat) (hS : IsUnit S) :
    fisherRaoMetric S⁻¹ S S = (Fintype.card n : ℝ) / 2 := by
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS
  rw [fisherRaoMetric_radial S S hS, Matrix.nonsing_inv_mul S hdet,
    Matrix.trace_one]
  ring

/-- Radial orthogonality is exactly the trace-kernel condition on the
relative tangent, with no commutation assumption. -/
theorem fisherRaoMetric_radial_eq_zero_iff (S X : Mat) (hS : IsUnit S) :
    fisherRaoMetric S⁻¹ S X = 0 ↔ Matrix.trace (S⁻¹ * X) = 0 := by
  rw [fisherRaoMetric_radial S X hS, mul_eq_zero]
  norm_num

/-- Native Jacobi and the real logarithm chain rule give the actual
derivative of logarithmic absolute determinant along a matrix path. -/
theorem hasDerivAt_logAbsDet
    {J : ℝ → Mat} {Jdot : Mat} {t : ℝ}
    (hJ : ∀ i j : n, HasDerivAt (fun u : ℝ => J u i j) (Jdot i j) t)
    (hinv : IsUnit (J t)) :
    HasDerivAt (fun u : ℝ => Real.log |(J u).det|)
      (Matrix.trace ((J t)⁻¹ * Jdot)) t := by
  have hdet := hasDerivAt_det_of_hasDerivAt_matrix hJ hinv
  have hunitdet : IsUnit (J t).det :=
    (Matrix.isUnit_iff_isUnit_det (J t)).mp hinv
  have hdet_ne : (J t).det ≠ 0 := isUnit_iff_ne_zero.mp hunitdet
  have hlog := (Real.hasDerivAt_log hdet_ne).comp t hdet
  have hderiv :
      ((J t).det)⁻¹ * ((J t).det * Matrix.trace ((J t)⁻¹ * Jdot)) =
        Matrix.trace ((J t)⁻¹ * Jdot) := by
    rw [← mul_assoc, inv_mul_cancel₀ hdet_ne, one_mul]
  convert! hlog.congr_deriv hderiv using 1
  simp only [Real.log_abs, Function.comp_def]

/-- In particular, the affine curve realizes the logarithmic determinant
differential in every real matrix direction. -/
theorem hasDerivAt_logAbsDet_affine (S X : Mat) (hS : IsUnit S) :
    HasDerivAt (fun u : ℝ => Real.log |(S + u • X).det|)
      (Matrix.trace (S⁻¹ * X)) 0 := by
  have hJ : ∀ i j : n,
      HasDerivAt (fun u : ℝ => (S + u • X) i j) (X i j) 0 := by
    intro i j
    simpa [Pi.smul_apply, smul_eq_mul, add_comm] using
      (((hasDerivAt_id' (0 : ℝ)).mul_const (X i j)).const_add (S i j))
  have hinv : IsUnit ((fun u : ℝ => S + u • X) 0) := by simpa using hS
  simpa using hasDerivAt_logAbsDet (J := fun u : ℝ => S + u • X) hJ hinv

/-- Radial pairing reads the actual derivative along any differentiable
matrix path through an invertible point. -/
theorem fisherRaoMetric_radial_eq_half_logAbsDet_deriv
    {J : ℝ → Mat} {Jdot : Mat} {t : ℝ}
    (hJ : ∀ i j : n, HasDerivAt (fun u : ℝ => J u i j) (Jdot i j) t)
    (hinv : IsUnit (J t)) :
    fisherRaoMetric (J t)⁻¹ (J t) Jdot =
      (1 / 2 : ℝ) * deriv (fun u : ℝ => Real.log |(J u).det|) t := by
  rw [fisherRaoMetric_radial (J t) Jdot hinv,
    (hasDerivAt_logAbsDet hJ hinv).deriv]

/-- A tangent to a path with zero logarithmic determinant derivative is
orthogonal to the radial direction for the existing Fisher form. -/
theorem radial_orthogonal_of_logAbsDet_derivative_zero
    {J : ℝ → Mat} {Jdot : Mat} {t : ℝ}
    (hJ : ∀ i j : n, HasDerivAt (fun u : ℝ => J u i j) (Jdot i j) t)
    (hinv : IsUnit (J t))
    (hzero : HasDerivAt (fun u : ℝ => Real.log |(J u).det|) 0 t) :
    fisherRaoMetric (J t)⁻¹ (J t) Jdot = 0 := by
  have htrace : Matrix.trace ((J t)⁻¹ * Jdot) = 0 :=
    (hasDerivAt_logAbsDet hJ hinv).unique hzero
  rw [fisherRaoMetric_radial (J t) Jdot hinv, htrace, mul_zero]

/-- Exact coordinate expression of the already existing native operator
shape part. This converts its carrier; it does not define a new shape part. -/
theorem toMatrix_shapePart_toLin (A : Mat) :
    LinearMap.toMatrix' (shapePart (Matrix.toLin' A)) =
      A - ((Fintype.card n : ℝ)⁻¹ * Matrix.trace A) • (1 : Mat) := by
  simp [shapePart, scalarTracePart]

/-- The existing operator trace-zero theorem survives the native coordinate
conversion. -/
theorem trace_toMatrix_shapePart_toLin [Nonempty n] (A : Mat) :
    Matrix.trace (LinearMap.toMatrix' (shapePart (Matrix.toLin' A))) = 0 := by
  have hdim : Module.finrank ℝ (n → ℝ) ≠ 0 := by
    rw [Module.finrank_pi]
    exact Fintype.card_ne_zero
  rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_toMatrix']
  exact trace_shapePart (Matrix.toLin' A) hdim

/-- Pulling the native shape part back by `S` gives the actual tangent
remainder after removing its radial component. -/
theorem radial_shape_tangent_decomposition (S X : Mat) (hS : IsUnit S) :
    ((Fintype.card n : ℝ)⁻¹ * Matrix.trace (S⁻¹ * X)) • S +
      S * LinearMap.toMatrix' (shapePart (Matrix.toLin' (S⁻¹ * X))) = X := by
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS
  rw [toMatrix_shapePart_toLin]
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
  rw [← mul_assoc, Matrix.mul_nonsing_inv S hdet, one_mul]
  abel

/-- The transported native shape tangent is orthogonal to the radial
direction, using the existing trace-zero shape theorem. -/
theorem fisherRaoMetric_radial_nativeShape [Nonempty n]
    (S X : Mat) (hS : IsUnit S) :
    fisherRaoMetric S⁻¹ S
      (S * LinearMap.toMatrix' (shapePart (Matrix.toLin' (S⁻¹ * X)))) = 0 := by
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS
  rw [fisherRaoMetric_radial S _ hS, ← mul_assoc,
    Matrix.nonsing_inv_mul S hdet, one_mul,
    trace_toMatrix_shapePart_toLin, mul_zero]

/-- The trace pairing decomposes into its scalar and native traceless
operator components, preserving the order of `A * B`. -/
theorem trace_mul_radial_shape_split [Nonempty n] (A B : Mat) :
    Matrix.trace (A * B) =
      Matrix.trace A * Matrix.trace B / (Fintype.card n : ℝ) +
        Matrix.trace
          (LinearMap.toMatrix' (shapePart (Matrix.toLin' A)) *
            LinearMap.toMatrix' (shapePart (Matrix.toLin' B))) := by
  have hdim : (Fintype.card n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [toMatrix_shapePart_toLin, toMatrix_shapePart_toLin]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_one, smul_eq_mul]
  field_simp [hdim]
  ring

/-- Full radial/shape split of the existing real matrix Fisher bilinear form.
The shape components are the existing native endomorphism shape parts of the
relative tangents `S⁻¹ * X` and `S⁻¹ * Y`. -/
theorem fisherRaoMetric_radial_shape_split [Nonempty n] (S X Y : Mat) :
    fisherRaoMetric S⁻¹ X Y =
      (Matrix.trace (S⁻¹ * X) * Matrix.trace (S⁻¹ * Y)) /
          (2 * (Fintype.card n : ℝ)) +
        (1 / 2 : ℝ) * Matrix.trace
          (LinearMap.toMatrix' (shapePart (Matrix.toLin' (S⁻¹ * X))) *
            LinearMap.toMatrix' (shapePart (Matrix.toLin' (S⁻¹ * Y)))) := by
  change (1 / 2 : ℝ) * Matrix.trace (S⁻¹ * X * S⁻¹ * Y) = _
  rw [mul_assoc (S⁻¹ * X) S⁻¹ Y,
    trace_mul_radial_shape_split (S⁻¹ * X) (S⁻¹ * Y)]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- The sum of the two actual logarithmic volume rates is the common
coefficient of the existing paired operator decomposition, with weight `2d`.
The relative velocities retain the order `J⁻¹ * Jdot`. -/
theorem hasDerivAt_paired_logAbsDet_sum [Nonempty n]
    {Jplus Jminus : ℝ → Mat} {JdotPlus JdotMinus : Mat} {t : ℝ}
    (hJplus : ∀ i j : n,
      HasDerivAt (fun u : ℝ => Jplus u i j) (JdotPlus i j) t)
    (hJminus : ∀ i j : n,
      HasDerivAt (fun u : ℝ => Jminus u i j) (JdotMinus i j) t)
    (hplusInv : IsUnit (Jplus t)) (hminusInv : IsUnit (Jminus t)) :
    HasDerivAt
      (fun u : ℝ => Real.log |(Jplus u).det| + Real.log |(Jminus u).det|)
      (2 * (Fintype.card n : ℝ) *
        pairedCommonCoefficient
          (Matrix.toLin' ((Jplus t)⁻¹ * JdotPlus))
          (Matrix.toLin' ((Jminus t)⁻¹ * JdotMinus))) t := by
  have hdim : (Fintype.card n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hrate :
      Matrix.trace ((Jplus t)⁻¹ * JdotPlus) +
          Matrix.trace ((Jminus t)⁻¹ * JdotMinus) =
        2 * (Fintype.card n : ℝ) *
          pairedCommonCoefficient
            (Matrix.toLin' ((Jplus t)⁻¹ * JdotPlus))
            (Matrix.toLin' ((Jminus t)⁻¹ * JdotMinus)) := by
    unfold pairedCommonCoefficient pairedTrace
    rw [Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq, Module.finrank_pi]
    field_simp [hdim]
  have hsum := (hasDerivAt_logAbsDet hJplus hplusInv).add
    (hasDerivAt_logAbsDet hJminus hminusInv)
  convert! hsum.congr_deriv hrate using 1

/-- The difference of the two actual logarithmic volume rates is the
relative/grading coefficient of the existing paired operator decomposition,
with the same dimension weight. -/
theorem hasDerivAt_paired_logAbsDet_difference [Nonempty n]
    {Jplus Jminus : ℝ → Mat} {JdotPlus JdotMinus : Mat} {t : ℝ}
    (hJplus : ∀ i j : n,
      HasDerivAt (fun u : ℝ => Jplus u i j) (JdotPlus i j) t)
    (hJminus : ∀ i j : n,
      HasDerivAt (fun u : ℝ => Jminus u i j) (JdotMinus i j) t)
    (hplusInv : IsUnit (Jplus t)) (hminusInv : IsUnit (Jminus t)) :
    HasDerivAt
      (fun u : ℝ => Real.log |(Jplus u).det| - Real.log |(Jminus u).det|)
      (2 * (Fintype.card n : ℝ) *
        pairedRelativeCoefficient
          (Matrix.toLin' ((Jplus t)⁻¹ * JdotPlus))
          (Matrix.toLin' ((Jminus t)⁻¹ * JdotMinus))) t := by
  have hdim : (Fintype.card n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hrate :
      Matrix.trace ((Jplus t)⁻¹ * JdotPlus) -
          Matrix.trace ((Jminus t)⁻¹ * JdotMinus) =
        2 * (Fintype.card n : ℝ) *
          pairedRelativeCoefficient
            (Matrix.toLin' ((Jplus t)⁻¹ * JdotPlus))
            (Matrix.toLin' ((Jminus t)⁻¹ * JdotMinus)) := by
    unfold pairedRelativeCoefficient pairedSupertrace
    rw [Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq, Module.finrank_pi]
    field_simp [hdim]
  have hdifference := (hasDerivAt_logAbsDet hJplus hplusInv).sub
    (hasDerivAt_logAbsDet hJminus hminusInv)
  convert! hdifference.congr_deriv hrate using 1

end InfoGeometry.Geometry.RealMatrixFisherRadial
