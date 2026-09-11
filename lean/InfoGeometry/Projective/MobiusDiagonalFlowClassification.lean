import InfoGeometry.Projective.MobiusMatrixSpectralClassification
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Classification of the determinant-one diagonal Möbius flow

This owner classifies only the existing diagonal family `flow (complexRapidity η θ)`.
It does not classify arbitrary elements of `PGL₂` and does not assign a
non-trivial Jordan/parabolic class to a diagonal matrix.
-/

namespace InfoGeometry.Projective.MobiusDiagonalFlowClassification

open InfoGeometry.Projective.MobiusLoxodromicSpectralParameter
open InfoGeometry.Projective.MobiusMatrixSpectralClassification

noncomputable section

theorem flow_det_one (κ : ℂ) :
    (flow κ).det = 1 :=
  InfoGeometry.Projective.MobiusMatrixSpectralClassification.flow_det_one κ

theorem flow_characteristicPolynomial (κ : ℂ) :
    characteristicPolynomialEval (flow κ) =
      fun z => (z - Complex.exp κ) * (z - Complex.exp (-κ)) :=
  InfoGeometry.Projective.MobiusMatrixSpectralClassification.flow_characteristicPolynomial κ

theorem flow_eigenvalues (κ : ℂ) :
    (flow κ).mulVec plusVector = (Complex.exp κ) • plusVector ∧
      (flow κ).mulVec minusVector = (Complex.exp (-κ)) • minusVector :=
  InfoGeometry.Projective.MobiusMatrixSpectralClassification.flow_eigenvalues κ

theorem flow_eigenvalue_ratio (κ : ℂ) :
    Complex.exp κ / Complex.exp (-κ) = Complex.exp (2 * κ) :=
  InfoGeometry.Projective.MobiusMatrixSpectralClassification.flow_eigenvalue_ratio κ

theorem flow_trace_discriminant (κ : ℂ) :
    traceDiscriminant (flow κ) =
      (Complex.exp κ - Complex.exp (-κ)) ^ 2 :=
  InfoGeometry.Projective.MobiusMatrixSpectralClassification.flow_traceDiscriminant κ

theorem flow_semisimple_of_ne_exp_two_kappa {κ : ℂ}
    (hκ : Complex.exp (2 * κ) ≠ 1) :
    (flowEnd κ).IsSemisimple :=
  InfoGeometry.Projective.MobiusMatrixSpectralClassification.flow_semisimple_of_ne_exp_two_kappa hκ

inductive DiagonalMobiusClass
  | identity
  | elliptic
  | hyperbolic
  | loxodromic
  deriving DecidableEq, Repr

def diagonalMobiusClass (η θ : ℝ) : DiagonalMobiusClass :=
  if η = 0 then
    if θ = 0 then DiagonalMobiusClass.identity
    else DiagonalMobiusClass.elliptic
  else if θ = 0 then DiagonalMobiusClass.hyperbolic
  else DiagonalMobiusClass.loxodromic

theorem diagonalMobiusClass_zero_zero :
    diagonalMobiusClass 0 0 = DiagonalMobiusClass.identity := by
  simp [diagonalMobiusClass]

theorem diagonalMobiusClass_elliptic {θ : ℝ} (hθ : θ ≠ 0) :
    diagonalMobiusClass 0 θ = DiagonalMobiusClass.elliptic := by
  simp [diagonalMobiusClass, hθ]

theorem diagonalMobiusClass_hyperbolic {η : ℝ} (hη : η ≠ 0) :
    diagonalMobiusClass η 0 = DiagonalMobiusClass.hyperbolic := by
  simp [diagonalMobiusClass, hη]

theorem diagonalMobiusClass_loxodromic {η θ : ℝ}
    (hη : η ≠ 0) (hθ : θ ≠ 0) :
    diagonalMobiusClass η θ = DiagonalMobiusClass.loxodromic := by
  simp [diagonalMobiusClass, hη, hθ]

theorem complexRapidity_classification (η θ : ℝ) :
    diagonalMobiusClass η θ =
      if η = 0 then
        if θ = 0 then DiagonalMobiusClass.identity
        else DiagonalMobiusClass.elliptic
      else if θ = 0 then DiagonalMobiusClass.hyperbolic
      else DiagonalMobiusClass.loxodromic := by
  rfl

theorem flow_complexRapidity_det_one (η θ : ℝ) :
    (flow (complexRapidity η θ)).det = 1 := by
  exact flow_det_one (complexRapidity η θ)

theorem flow_complexRapidity_characteristicPolynomial (η θ z : ℝ) :
    characteristicPolynomialEval (flow (complexRapidity η θ)) (z : ℂ) =
      ((z : ℂ) - Complex.exp (complexRapidity η θ)) *
        ((z : ℂ) - Complex.exp (-complexRapidity η θ)) := by
  exact flow_characteristicPolynomialEval (complexRapidity η θ) (z : ℂ)

theorem flow_spectral_values_distinct_of {κ : ℂ}
    (hκ : Complex.exp (2 * κ) ≠ 1) :
    Complex.exp κ ≠ Complex.exp (-κ) := by
  intro heq
  apply hκ
  rw [← flow_eigenvalue_ratio κ]
  rw [heq]
  exact div_self (Complex.exp_ne_zero _)

theorem flow_complexRapidity_spectral_values_distinct_of
    {η θ : ℝ}
    (hκ : Complex.exp (2 * complexRapidity η θ) ≠ 1) :
    Complex.exp (complexRapidity η θ) ≠
      Complex.exp (-complexRapidity η θ) := by
  exact flow_spectral_values_distinct_of hκ

theorem flow_complexRapidity_isSemisimple_of_distinct
    {η θ : ℝ}
    (hκ : Complex.exp (2 * complexRapidity η θ) ≠ 1) :
    (flowEnd (complexRapidity η θ)).IsSemisimple := by
  apply flowEnd_isSemisimple_of_distinct
  exact flow_complexRapidity_spectral_values_distinct_of hκ

end

end InfoGeometry.Projective.MobiusDiagonalFlowClassification
