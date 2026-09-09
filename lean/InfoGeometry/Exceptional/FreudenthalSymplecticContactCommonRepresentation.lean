import InfoGeometry.Exceptional.FreudenthalSymplecticContactCommonCARCCR
import InfoGeometry.Exceptional.FreudenthalSymplecticContactLieAlgebra

noncomputable section
namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-- The faithful symplectic-contact action transported coefficientwise to the
common CAR--CCR carrier.  The two transports are separate native Lie maps;
their composition is the actual common-carrier representation. -/
def symplecticContactCommonRepresentationLieHom :
    FiveGradedCarrier D →ₗ⁅ℝ⁆
      SymplecticContactCommonEnd (J := J) :=
  (symplecticContactCommonLiftLieHom (J := J)).comp
    (symplecticContactRepresentationLieHom D)

theorem symplecticContactCommonRepresentationLieHom_apply
    (u : FiveGradedCarrier D) :
    symplecticContactCommonRepresentationLieHom D u =
      symplecticContactCommonLift
        (symplecticContactRepresentation D u) := rfl

theorem symplecticContactCommonRepresentationLieHom_injective :
    Function.Injective
      (symplecticContactCommonRepresentationLieHom D) := by
  exact (symplecticContactCommonLiftLieHom_injective (J := J)).comp
    (symplecticContactRepresentationLieHom_injective D)

theorem symplecticContactCommonRepresentation_map_lie
    (u v : FiveGradedCarrier D) :
    symplecticContactCommonRepresentationLieHom D ⁅u, v⁆ =
      ⁅symplecticContactCommonRepresentationLieHom D u,
        symplecticContactCommonRepresentationLieHom D v⁆ := by
  exact (symplecticContactCommonRepresentationLieHom D).map_lie u v

abbrev symplecticContactCommonRepresentation (D : CubicJordanDatum J) :=
  symplecticContactCommonRepresentationLieHom D

theorem symplecticContactCommonRepresentation_injective (D : CubicJordanDatum J) :
    Function.Injective (symplecticContactCommonRepresentation D) :=
  symplecticContactCommonRepresentationLieHom_injective D

theorem symplecticContactCommonRepresentation_bracket
    (u v : FiveGradedCarrier D) :
    symplecticContactCommonRepresentation D ⁅u, v⁆ =
      symplecticContactCommonRepresentation D u *
          symplecticContactCommonRepresentation D v -
        symplecticContactCommonRepresentation D v *
          symplecticContactCommonRepresentation D u := by
  have h := symplecticContactCommonRepresentation_map_lie D u v
  exact h

end InfoGeometry.Exceptional.Freudenthal
