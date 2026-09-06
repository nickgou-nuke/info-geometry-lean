import InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinAdjoint

/-!
# Complementary chiral sheets on the doubled real Krein carrier

This owner records the finite projector and Witt-pairing consequences of the
real doubled model.  It does not assert a von Neumann commutant or a Tomita
standard-form theorem.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinComplements

open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinAdjoint

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev H₂ := DoubledSpace E
abbrev EndH₂ := H₂ (E := E) →L[ℝ] H₂ (E := E)

theorem leftChiralProjector_add_rightChiralProjector :
    leftChiralProjector (E := E) + rightChiralProjector (E := E) =
      ContinuousLinearMap.id ℝ (H₂ (E := E)) := by
  apply ContinuousLinearMap.ext
  intro u
  simp [leftChiralProjector, rightChiralProjector, sub_eq_add_neg]
  module

theorem leftChiralProjector_comp_rightChiralProjector :
    (leftChiralProjector (E := E)).comp (rightChiralProjector (E := E)) = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [leftChiralProjector, rightChiralProjector, gamma5,
      spectral_epsilon, one_div, sub_eq_add_neg] <;> module

theorem rightChiralProjector_comp_leftChiralProjector :
    (rightChiralProjector (E := E)).comp (leftChiralProjector (E := E)) = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [leftChiralProjector, rightChiralProjector, gamma5,
      spectral_epsilon, one_div, sub_eq_add_neg] <;> module

theorem leftChiralProjector_idempotent :
    (leftChiralProjector (E := E)).comp (leftChiralProjector (E := E)) =
      leftChiralProjector (E := E) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [leftChiralProjector, gamma5, spectral_epsilon, one_div,
      sub_eq_add_neg] <;> module

theorem rightChiralProjector_idempotent :
    (rightChiralProjector (E := E)).comp (rightChiralProjector (E := E)) =
      rightChiralProjector (E := E) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [rightChiralProjector, gamma5, spectral_epsilon, one_div,
      sub_eq_add_neg] <;> module

theorem etaChiral_comp_leftChiralProjector_comp_etaChiral :
    (etaChiral (E := E)).comp
        ((leftChiralProjector (E := E)).comp (etaChiral (E := E))) =
      rightChiralProjector (E := E) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [etaChiral, leftChiralProjector, rightChiralProjector, gamma5,
      modular_j, spectral_epsilon, one_div, sub_eq_add_neg] <;> module

theorem chiralKreinForm_left_projected_left_projected (u v : H₂ (E := E)) :
    chiralKreinForm (E := E)
        ((leftChiralProjector (E := E)) u)
        ((leftChiralProjector (E := E)) v) = 0 := by
  have hu : to_doubled (WithLp.fst u) (WithLp.snd u) = u :=
    DoubledSpace.ext rfl rfl
  have hv : to_doubled (WithLp.fst v) (WithLp.snd v) = v :=
    DoubledSpace.ext rfl rfl
  rw [← hu, ← hv, leftChiralProjector_to_doubled,
    leftChiralProjector_to_doubled]
  exact chiralKreinForm_left_isotropic _ _

theorem chiralKreinForm_right_projected_right_projected (u v : H₂ (E := E)) :
    chiralKreinForm (E := E)
        ((rightChiralProjector (E := E)) u)
        ((rightChiralProjector (E := E)) v) = 0 := by
  have hu : to_doubled (WithLp.fst u) (WithLp.snd u) = u :=
    DoubledSpace.ext rfl rfl
  have hv : to_doubled (WithLp.fst v) (WithLp.snd v) = v :=
    DoubledSpace.ext rfl rfl
  rw [← hu, ← hv, rightChiralProjector_to_doubled,
    rightChiralProjector_to_doubled]
  exact chiralKreinForm_right_isotropic _ _

theorem chiralKreinForm_left_right_projected (u v : H₂ (E := E)) :
    chiralKreinForm (E := E)
        ((leftChiralProjector (E := E)) u)
        ((rightChiralProjector (E := E)) v) =
      inner ℝ (WithLp.fst u) (WithLp.snd v) := by
  have hu : to_doubled (WithLp.fst u) (WithLp.snd u) = u :=
    DoubledSpace.ext rfl rfl
  have hv : to_doubled (WithLp.fst v) (WithLp.snd v) = v :=
    DoubledSpace.ext rfl rfl
  rw [← hu, ← hv, leftChiralProjector_to_doubled,
    rightChiralProjector_to_doubled]
  exact chiralKreinForm_left_right _ _

theorem chiralKreinForm_right_left_projected (u v : H₂ (E := E)) :
    chiralKreinForm (E := E)
        ((rightChiralProjector (E := E)) u)
        ((leftChiralProjector (E := E)) v) =
      inner ℝ (WithLp.snd u) (WithLp.fst v) := by
  have hu : to_doubled (WithLp.fst u) (WithLp.snd u) = u :=
    DoubledSpace.ext rfl rfl
  have hv : to_doubled (WithLp.fst v) (WithLp.snd v) = v :=
    DoubledSpace.ext rfl rfl
  rw [← hu, ← hv, rightChiralProjector_to_doubled,
    leftChiralProjector_to_doubled]
  exact chiralKreinForm_right_left _ _

end InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinComplements
