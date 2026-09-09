import InfoGeometry.Exceptional.FreudenthalSymplecticContactCommonCARCCR
import InfoGeometry.Exceptional.FreudenthalSymplecticContactGrading

noncomputable section
namespace InfoGeometry.Exceptional.Freudenthal
variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

abbrev contactRho : FiveGradedCarrier D →ₗ⁅ℝ⁆ SymplecticContactEnd (J := J) :=
  symplecticContactRepresentationLieHom D

theorem contactRho_injective :
    Function.Injective (contactRho D) :=
  symplecticContactRepresentationLieHom_injective D

theorem contactRho_map_lie (u v : FiveGradedCarrier D) :
    contactRho D ⁅u, v⁆ = ⁅contactRho D u, contactRho D v⁆ :=
  (contactRho D).map_lie u v

theorem common_carrier_CAR_CCR :
    contactFermionAnnihilation (J := J) *
        contactFermionCreation (J := J) +
      contactFermionCreation (J := J) *
        contactFermionAnnihilation (J := J) = 1 ∧
      contactBosonAnnihilation (J := J) *
          contactBosonCreation (J := J) -
        contactBosonCreation (J := J) *
          contactBosonAnnihilation (J := J) = 1 :=
  ⟨contactFermion_CAR (J := J), contactBoson_CCR (J := J)⟩

theorem symplectic_contact_verified_closure_packet (u v : FiveGradedCarrier D) :
    contactRho D ⁅u, v⁆ = ⁅contactRho D u, contactRho D v⁆ ∧
      Function.Injective (contactRho D) :=
  ⟨contactRho_map_lie D u v, contactRho_injective D⟩

end InfoGeometry.Exceptional.Freudenthal
