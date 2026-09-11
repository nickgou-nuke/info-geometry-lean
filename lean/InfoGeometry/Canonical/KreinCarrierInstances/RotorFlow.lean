import InfoGeometry.Canonical.KreinCarrierInstances.Datum
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HestenesKreinModularGeometry
import Mathlib.Tactic

open InfoGeometry.Canonical.HestenesKreinModularGeometry

noncomputable section

def concreteRotorFlowKlein_rotor : ℝ → RealEnd KleinBottleCarrier :=
  fun _ => ContinuousLinearMap.id ℝ KleinBottleCarrier

def concreteRotorFlowKlein_rotorInv : ℝ → RealEnd KleinBottleCarrier :=
  fun _ => ContinuousLinearMap.id ℝ KleinBottleCarrier

theorem concreteRotorFlowKlein_rotor_zero :
    concreteRotorFlowKlein_rotor 0 = ContinuousLinearMap.id ℝ KleinBottleCarrier := rfl

theorem concreteRotorFlowKlein_rotorInv_zero :
    concreteRotorFlowKlein_rotorInv 0 = ContinuousLinearMap.id ℝ KleinBottleCarrier := rfl

theorem concreteRotorFlowKlein_rotor_left_inv (t : ℝ) :
    concreteRotorFlowKlein_rotorInv t * concreteRotorFlowKlein_rotor t = ContinuousLinearMap.id ℝ KleinBottleCarrier := by
  ext; simp [concreteRotorFlowKlein_rotor, concreteRotorFlowKlein_rotorInv]

theorem concreteRotorFlowKlein_rotor_right_inv (t : ℝ) :
    concreteRotorFlowKlein_rotor t * concreteRotorFlowKlein_rotorInv t = ContinuousLinearMap.id ℝ KleinBottleCarrier := by
  ext; simp [concreteRotorFlowKlein_rotor, concreteRotorFlowKlein_rotorInv]

theorem concreteRotorFlowKlein_rotor_group (s t : ℝ) :
    concreteRotorFlowKlein_rotor (s + t) = concreteRotorFlowKlein_rotor s * concreteRotorFlowKlein_rotor t := by
  ext; simp [concreteRotorFlowKlein_rotor]

def concreteRotorFlowKlein_fixedByFlow
    (D : KreinHestenesModularDatum KleinBottleCarrier) : RealEnd KleinBottleCarrier → Prop :=
  fun A => D.modularGenerator * A = A * D.modularGenerator

theorem concreteRotorFlowKlein_fixedByFlow_iff_monogenic
    (D : KreinHestenesModularDatum KleinBottleCarrier) (A : RealEnd KleinBottleCarrier) :
    concreteRotorFlowKlein_fixedByFlow D A ↔ KreinHestenesModularDatum.IsMonogenic D A := by
  exact (KreinHestenesModularDatum.isMonogenic_iff_commutes D A).symm

/-- Trivial identity rotor flow, with the fixed predicate identified with monogenicity. -/
def concreteRotorFlowKlein
    (D : KreinHestenesModularDatum KleinBottleCarrier) : HestenesRotorFlow D where
  rotor := concreteRotorFlowKlein_rotor
  rotorInv := concreteRotorFlowKlein_rotorInv
  rotor_zero := concreteRotorFlowKlein_rotor_zero
  rotorInv_zero := concreteRotorFlowKlein_rotorInv_zero
  rotor_left_inv := concreteRotorFlowKlein_rotor_left_inv
  rotor_right_inv := concreteRotorFlowKlein_rotor_right_inv
  rotor_group := concreteRotorFlowKlein_rotor_group
  fixedByFlow := concreteRotorFlowKlein_fixedByFlow D
  fixedByFlow_iff_monogenic := concreteRotorFlowKlein_fixedByFlow_iff_monogenic D

end
