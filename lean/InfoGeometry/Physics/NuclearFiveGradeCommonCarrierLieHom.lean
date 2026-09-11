import InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Native Lie homomorphism for the concrete nuclear five-grading

The multiplicative common-carrier representation transports the associative
matrix commutator to the endomorphism commutator.  This file bundles that fact
as a Mathlib `LieHom` and records grade preservation on the named five lanes.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearFiveGradeCommonCarrierLieHom

open InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel
open InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation

/-- The concrete five-grade matrix algebra acts on the common carrier by a
native real Lie-algebra homomorphism. -/
def commonRepresentationLieHom : M4R →ₗ⁅ℝ⁆ Operator where
  toLinearMap := representationLinear
  map_lie' := by
    intro X Y
    change representation (X * Y - Y * X) =
      representation X * representation Y -
        representation Y * representation X
    exact representation_commutator X Y

@[simp] theorem commonRepresentationLieHom_apply (X : M4R) :
    commonRepresentationLieHom X = representation X := rfl

/-- Injectivity is not required for grade preservation, but the common action
is faithful because the coefficient module contains a nonzero scalar copy of
each standard coordinate vector.  The present interface records the exact
operational equality needed downstream without presupposing a basis theorem. -/
theorem commonRepresentationLieHom_map_lie (X Y : M4R) :
    commonRepresentationLieHom ⁅X, Y⁆ =
      ⁅commonRepresentationLieHom X,
        commonRepresentationLieHom Y⁆ :=
  commonRepresentationLieHom.map_lie X Y

/-- Named grade extrema remain adjoint eigenoperators after applying the Lie
representation. -/
theorem commonRepresentationLieHom_extreme_grades :
    RepresentedHasGrade 2 (commonRepresentationLieHom pairCreation) ∧
      RepresentedHasGrade (-2)
        (commonRepresentationLieHom pairAnnihilation) := by
  exact ⟨representation_preserves_grade pairCreation_grade,
    representation_preserves_grade pairAnnihilation_grade⟩

/-- Compact Lie-representation packet. -/
theorem common_lie_representation_packet (X Y : M4R) :
    commonRepresentationLieHom ⁅X, Y⁆ =
        ⁅commonRepresentationLieHom X,
          commonRepresentationLieHom Y⁆ ∧
      RepresentedHasGrade 2
        (commonRepresentationLieHom pairCreation) ∧
      RepresentedHasGrade (-2)
        (commonRepresentationLieHom pairAnnihilation) := by
  exact ⟨commonRepresentationLieHom.map_lie X Y,
    representation_preserves_grade pairCreation_grade,
    representation_preserves_grade pairAnnihilation_grade⟩

end InfoGeometry.Physics.NuclearFiveGradeCommonCarrierLieHom
