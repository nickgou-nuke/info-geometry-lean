import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Exceptional.FreudenthalSymplecticContactRepresentation

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

theorem symplecticContactBracket_add_left
    (u v w : FiveGradedCarrier D) :
    symplecticContactBracket D (u + v) w =
      symplecticContactBracket D u w + symplecticContactBracket D v w := by
  apply symplecticContactRepresentation_injective D
  simp only [map_add, symplecticContactRepresentation_bracket]
  noncomm_ring

theorem symplecticContactBracket_add_right
    (u v w : FiveGradedCarrier D) :
    symplecticContactBracket D u (v + w) =
      symplecticContactBracket D u v + symplecticContactBracket D u w := by
  apply symplecticContactRepresentation_injective D
  simp only [map_add, symplecticContactRepresentation_bracket]
  noncomm_ring

theorem symplecticContactBracket_smul_right
    (c : ℝ) (u v : FiveGradedCarrier D) :
    symplecticContactBracket D u (c • v) =
      c • symplecticContactBracket D u v := by
  apply symplecticContactRepresentation_injective D
  simp only [map_smul, symplecticContactRepresentation_bracket]
  simp [smul_sub]

theorem symplecticContactBracket_self
    (u : FiveGradedCarrier D) :
    symplecticContactBracket D u u = 0 := by
  apply symplecticContactRepresentation_injective D
  simp [symplecticContactRepresentation_bracket]

theorem symplecticContactBracket_leibniz
    (u v w : FiveGradedCarrier D) :
    symplecticContactBracket D u (symplecticContactBracket D v w) =
      symplecticContactBracket D (symplecticContactBracket D u v) w +
        symplecticContactBracket D v (symplecticContactBracket D u w) := by
  apply symplecticContactRepresentation_injective D
  simpa only [map_add, symplecticContactRepresentation_bracket, Ring.lie_def] using
    (LieRing.leibniz_lie (symplecticContactRepresentation D u)
      (symplecticContactRepresentation D v)
      (symplecticContactRepresentation D w))

noncomputable instance symplecticContactLieRing :
    LieRing (FiveGradedCarrier D) where
  bracket := symplecticContactBracket D
  add_lie := symplecticContactBracket_add_left D
  lie_add := symplecticContactBracket_add_right D
  lie_self := symplecticContactBracket_self D
  leibniz_lie := symplecticContactBracket_leibniz D

noncomputable instance symplecticContactLieAlgebra :
    LieAlgebra ℝ (FiveGradedCarrier D) where
  lie_smul := symplecticContactBracket_smul_right D

@[simp] theorem symplecticContact_lieBracket_eq
    (u v : FiveGradedCarrier D) :
    ⁅u, v⁆ = symplecticContactBracket D u v := rfl

def symplecticContactRepresentationLieHom :
    FiveGradedCarrier D →ₗ⁅ℝ⁆ SymplecticContactEnd (J := J) where
  toLinearMap := symplecticContactRepresentation D
  map_lie' := by
    intro u v
    simpa [Ring.lie_def] using
      symplecticContactRepresentation_bracket D u v

theorem symplecticContactRepresentationLieHom_injective :
    Function.Injective (symplecticContactRepresentationLieHom D) := by
  intro u v h
  apply symplecticContactRepresentation_injective D
  exact h

end InfoGeometry.Exceptional.Freudenthal
