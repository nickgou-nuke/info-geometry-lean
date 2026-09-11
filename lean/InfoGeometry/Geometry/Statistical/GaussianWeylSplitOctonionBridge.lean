import InfoGeometry.Geometry.Statistical.GaussianScaleDerivationDecomposition
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Geometry.Statistical.WeylSplitOctonionDualFlatBridge

/-!
# Gaussian scale/derivation representation of dual-flat curvature

This owner is only the composition theorem between existing owners.  It does
not choose a Gaussian measure and does not identify the scalar coordinate with
a geometric Weyl field without an explicit representation hypothesis.
-/

namespace InfoGeometry.Geometry.Statistical.GaussianWeylSplitOctonionBridge

noncomputable section

open InfoGeometry.Geometry.Statistical
open InfoGeometry.Geometry.Statistical.GaussianScaleDerivationDecomposition
open InfoGeometry.Geometry.Statistical.GaussianSplitOctonionDerivationField

abbrev CZ := InfoGeometry.Lie.CanonicalZornDerivation.CZ
abbrev ScaleDerivationParams :=
  GaussianScaleDerivationDecomposition.ScaleDerivationParams
abbrev EndCZ := Module.End ℝ CZ
abbrev Der := InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations

theorem curvature_eq_neg_quarter_gaussian_operator_commutator
    (C : DualFlatCurvatureDatum (T := CZ))
    (parameter : CZ → ScaleDerivationParams)
    (difference_eq : ∀ X,
      differenceOperator C.nabla C.nablaStar X =
        scaleDerivationOperator (parameter X))
    (X Y : CZ) :
    C.R0 X Y = (-1 / 4 : ℝ) •
      operatorCommutator
        (scaleDerivationOperator (parameter X))
        (scaleDerivationOperator (parameter Y)) := by
  rw [C.curvature_eq_neg_quarter_difference X Y,
    difference_eq X, difference_eq Y]

theorem curvature_eq_neg_gaussian_derivation_bracket
    (C : DualFlatCurvatureDatum (T := CZ))
    (parameter : CZ → ScaleDerivationParams)
    (difference_eq : ∀ X,
      differenceOperator C.nabla C.nablaStar X =
        scaleDerivationOperator (parameter X))
    (X Y : CZ) :
    C.R0 X Y =
      -((⁅(derivationOfCoordinates (parameter X).2 : Der),
          (derivationOfCoordinates (parameter Y).2 : Der)⁆ : Der) : EndCZ) := by
  rw [curvature_eq_neg_quarter_gaussian_operator_commutator
    C parameter difference_eq X Y,
    scaleDerivationOperator_commutator_eq_derivation_bracket]
  simp only [smul_smul]
  norm_num

theorem curvature_eq_neg_gaussian_derivation_bracket_of_same_derivation_coordinates
    (C : DualFlatCurvatureDatum (T := CZ))
    (parameter representative : CZ → ScaleDerivationParams)
    (difference_eq : ∀ X,
      differenceOperator C.nabla C.nablaStar X =
        scaleDerivationOperator (parameter X))
    (same_derivation_coordinates : ∀ X,
      (representative X).2 = (parameter X).2)
    (X Y : CZ) :
    C.R0 X Y =
      -((⁅(derivationOfCoordinates (representative X).2 : Der),
          (derivationOfCoordinates (representative Y).2 : Der)⁆ : Der) : EndCZ) := by
  rw [curvature_eq_neg_gaussian_derivation_bracket
    C parameter difference_eq X Y,
    same_derivation_coordinates X,
    same_derivation_coordinates Y]

end
end InfoGeometry.Geometry.Statistical.GaussianWeylSplitOctonionBridge
