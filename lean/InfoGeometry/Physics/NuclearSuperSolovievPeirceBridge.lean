import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearOperatorSuperSoloviev
import InfoGeometry.Physics.Algebra.TripotentFiveGradingDecomposition

/-!
# Peirce/five-grade interface for operator Soloviev channels

The repository already provides a genuine five-projector direct-sum
decomposition associated with a tripotent element `e`.

This module does not identify Soloviev coefficients with Peirce sectors by
fiat.  Instead it packages that identification as proof-carrying data:

* both diagonal energy channels lie in the grade-zero range;
* the forward transition lies in grade `+1`;
* the reverse transition lies in grade `-1`.

Under those hypotheses, the native Peirce/five-grade projectors recover the
four channels exactly.  Every coefficient also retains the full canonical
five-grade decomposition supplied by the existing owner.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearSuperSolovievPeirceBridge

open InfoGeometry.Physics.NuclearOperatorSuperSoloviev
open InfoGeometry.Physics.Algebra

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Proof-carrying assignment of a Soloviev operator block to the repository's
tripotent five-grade decomposition. -/
structure PeirceCompatibleBlock (e : A) where
  tripotent : e * e * e = e
  E0 : A
  E1 : A
  V : A
  W : A
  E0_grade_zero : E0 ∈ fiveGradeRange e .zero
  E1_grade_zero : E1 ∈ fiveGradeRange e .zero
  V_grade_posOne : V ∈ fiveGradeRange e .posOne
  W_grade_negOne : W ∈ fiveGradeRange e .negOne

namespace PeirceCompatibleBlock

variable {e : A} (H : PeirceCompatibleBlock e)

/-- Associated operator-valued Soloviev block. -/
def toHamiltonian : Block2 A :=
  blockHamiltonian H.E0 H.E1 H.V H.W

/-- Grade-zero projection fixes the lower diagonal energy coefficient. -/
theorem project_E0 :
    fiveGradeProjector e .zero H.E0 = H.E0 := by
  exact fiveGradeProjector_apply_range_self H.tripotent .zero
    ⟨H.E0, H.E0_grade_zero⟩

/-- Grade-zero projection fixes the upper diagonal energy coefficient. -/
theorem project_E1 :
    fiveGradeProjector e .zero H.E1 = H.E1 := by
  exact fiveGradeProjector_apply_range_self H.tripotent .zero
    ⟨H.E1, H.E1_grade_zero⟩

/-- Positive-one projection fixes the forward transition channel. -/
theorem project_V :
    fiveGradeProjector e .posOne H.V = H.V := by
  exact fiveGradeProjector_apply_range_self H.tripotent .posOne
    ⟨H.V, H.V_grade_posOne⟩

/-- Negative-one projection fixes the reverse transition channel. -/
theorem project_W :
    fiveGradeProjector e .negOne H.W = H.W := by
  exact fiveGradeProjector_apply_range_self H.tripotent .negOne
    ⟨H.W, H.W_grade_negOne⟩

/-- A diagonal coefficient has no positive-one component. -/
theorem E0_posOne_eq_zero :
    fiveGradeProjector e .posOne H.E0 = 0 := by
  exact fiveGradeProjector_apply_range_eq_zero_of_ne H.tripotent
    (by decide) ⟨H.E0, H.E0_grade_zero⟩

/-- A diagonal coefficient has no negative-one component. -/
theorem E1_negOne_eq_zero :
    fiveGradeProjector e .negOne H.E1 = 0 := by
  exact fiveGradeProjector_apply_range_eq_zero_of_ne H.tripotent
    (by decide) ⟨H.E1, H.E1_grade_zero⟩

/-- The forward transition has no grade-zero component. -/
theorem V_zero_eq_zero :
    fiveGradeProjector e .zero H.V = 0 := by
  exact fiveGradeProjector_apply_range_eq_zero_of_ne H.tripotent
    (by decide) ⟨H.V, H.V_grade_posOne⟩

/-- The reverse transition has no grade-zero component. -/
theorem W_zero_eq_zero :
    fiveGradeProjector e .zero H.W = 0 := by
  exact fiveGradeProjector_apply_range_eq_zero_of_ne H.tripotent
    (by decide) ⟨H.W, H.W_grade_negOne⟩

/-- The canonical five-grade decomposition of `E0` recomposes exactly. -/
theorem E0_recompose :
    fiveGradeRecomposeLinear e (fiveGradeDecomposeLinear e H.E0) = H.E0 := by
  exact fiveGrade_recompose_decompose e H.E0

/-- The canonical five-grade decomposition of `V` recomposes exactly. -/
theorem V_recompose :
    fiveGradeRecomposeLinear e (fiveGradeDecomposeLinear e H.V) = H.V := by
  exact fiveGrade_recompose_decompose e H.V

/-- Consolidated Peirce-sector separation packet. -/
theorem peirce_channel_packet :
    fiveGradeProjector e .zero H.E0 = H.E0 ∧
      fiveGradeProjector e .zero H.E1 = H.E1 ∧
      fiveGradeProjector e .posOne H.V = H.V ∧
      fiveGradeProjector e .negOne H.W = H.W ∧
      fiveGradeProjector e .zero H.V = 0 ∧
      fiveGradeProjector e .zero H.W = 0 :=
  ⟨H.project_E0, H.project_E1, H.project_V, H.project_W,
    H.V_zero_eq_zero, H.W_zero_eq_zero⟩

end PeirceCompatibleBlock

end InfoGeometry.Physics.NuclearSuperSolovievPeirceBridge

end noncomputable section
