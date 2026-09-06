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

end InfoGeometry.Exceptional.Freudenthal
