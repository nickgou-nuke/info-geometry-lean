import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Exceptional.FreudenthalChargeLinear
import InfoGeometry.Exceptional.FreudenthalSymplecticContactRepresentation

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

theorem symplecticContactBracket_add_left
    (u v w : FiveGradedCarrier D) :
    symplecticContactBracket D (u + v) w =
      symplecticContactBracket D u w + symplecticContactBracket D v w := by
  apply symplecticContactRepresentation_injective D
  rw [map_add]
  iterate 3 rw [symplecticContactRepresentation_bracket]
  rw [map_add]
  exact LieRing.add_lie
    (symplecticContactRepresentation D u)
    (symplecticContactRepresentation D v)
    (symplecticContactRepresentation D w)

theorem symplecticContactBracket_add_right
    (u v w : FiveGradedCarrier D) :
    symplecticContactBracket D u (v + w) =
      symplecticContactBracket D u v + symplecticContactBracket D u w := by
  apply symplecticContactRepresentation_injective D
  rw [map_add]
  iterate 3 rw [symplecticContactRepresentation_bracket]
  rw [map_add]
  exact LieRing.lie_add
    (symplecticContactRepresentation D u)
    (symplecticContactRepresentation D v)
    (symplecticContactRepresentation D w)

theorem symplecticContactBracket_smul_right
    (c : ℝ) (u v : FiveGradedCarrier D) :
    symplecticContactBracket D u (c • v) =
      c • symplecticContactBracket D u v := by
  apply symplecticContactRepresentation_injective D
  rw [map_smul]
  iterate 2 rw [symplecticContactRepresentation_bracket]
  rw [map_smul]
  exact LieAlgebra.lie_smul c
    (symplecticContactRepresentation D u)
    (symplecticContactRepresentation D v)

theorem symplecticContactBracket_self
    (u : FiveGradedCarrier D) :
    symplecticContactBracket D u u = 0 := by
  apply symplecticContactRepresentation_injective D
  rw [symplecticContactRepresentation_bracket, map_zero, sub_self]

theorem symplecticContactBracket_leibniz
    (u v w : FiveGradedCarrier D) :
    symplecticContactBracket D u (symplecticContactBracket D v w) =
      symplecticContactBracket D (symplecticContactBracket D u v) w +
        symplecticContactBracket D v (symplecticContactBracket D u w) := by
  apply symplecticContactRepresentation_injective D
  rw [map_add]
  iterate 6 rw [symplecticContactRepresentation_bracket]
  exact LieRing.leibniz_lie
    (symplecticContactRepresentation D u)
    (symplecticContactRepresentation D v)
    (symplecticContactRepresentation D w)

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
    change symplecticContactRepresentation D (symplecticContactBracket D u v) =
      symplecticContactRepresentation D u * symplecticContactRepresentation D v -
        symplecticContactRepresentation D v * symplecticContactRepresentation D u
    exact symplecticContactRepresentation_bracket D u v

theorem symplecticContactRepresentationLieHom_injective (D : CubicJordanDatum J) :
    Function.Injective (symplecticContactRepresentationLieHom D) := by
  intro u v h
  apply symplecticContactRepresentation_injective D
  exact h

end InfoGeometry.Exceptional.Freudenthal
