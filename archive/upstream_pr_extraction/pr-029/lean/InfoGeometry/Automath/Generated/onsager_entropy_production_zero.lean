import InfoGeometry.Canonical.SouriauTheoremTranslatorPacket

namespace Automath.Generated

open InfoGeometry.Canonical.SouriauThermodynamics
open InfoGeometry.GrandCanonical
open InfoGeometry.Canonical.SouriauTheoremTranslatorPacket

/--
Instance construction for StrictOnsagerEquilibriumGate under positive definiteness,
proven natively using repository owner modules (no axioms).
-/
noncomputable def onsager_gate_instance
    {α : Type*} [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α)
    (T : GeometricTemperature)
    (hPD : (souriauFisherResponseMatrix M T).PositiveDefinite) :
    StrictOnsagerEquilibriumGate M T := by
  refine
    { forceIsZero := fun xβ xμ => xβ = 0 ∧ xμ = 0
      entropyProduction_eq_zero_iff_force_zero := ?_ }
  intro xβ xμ
  change
    (souriauFisherResponseMatrix M T).entropyProduction xβ xμ = 0 ↔
      xβ = 0 ∧ xμ = 0
  have h :=
    ResponseMatrix2.entropyProduction_eq_zero_iff_force_zero_of_positiveDefinite hPD xβ xμ
  exact h

end Automath.Generated