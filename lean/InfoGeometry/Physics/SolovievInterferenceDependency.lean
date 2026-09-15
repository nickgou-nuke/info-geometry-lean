import InfoGeometry.Physics.SolovievDressedInterference

namespace InfoGeometry.Physics.SolovievDressedInterference.ProofDependency

inductive Archetype
  | circularCoefficients
  | phononCAR
  | operatorSplit
  | complexStrength
  | cocyclicTransport
  | dressedInterference
  | phaseInvariantCommutator
  deriving DecidableEq, Fintype

open Archetype

def prerequisites : Archetype → Finset Archetype
  | circularCoefficients => {circularCoefficients}
  | phononCAR => {phononCAR}
  | operatorSplit => {circularCoefficients, phononCAR, operatorSplit}
  | complexStrength => {complexStrength}
  | cocyclicTransport => {cocyclicTransport}
  | dressedInterference => {complexStrength, cocyclicTransport, dressedInterference}
  | phaseInvariantCommutator => {phononCAR, complexStrength, phaseInvariantCommutator}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

instance : DecidableLE Archetype := fun earlier later =>
  inferInstanceAs (Decidable (prerequisites earlier ⊆ prerequisites later))

theorem causal_branches :
    circularCoefficients < operatorSplit ∧ phononCAR < operatorSplit ∧
    complexStrength < dressedInterference ∧ cocyclicTransport < dressedInterference ∧
    phononCAR < phaseInvariantCommutator ∧ complexStrength < phaseInvariantCommutator := by
  simp only [lt_iff_le_not_ge]
  decide

theorem interference_and_commutator_incomparable :
    ¬ dressedInterference ≤ phaseInvariantCommutator ∧
    ¬ phaseInvariantCommutator ≤ dressedInterference := by
  decide

theorem no_cycle {earlier later : Archetype} (forward : earlier < later) :
    ¬ later < earlier := lt_asymm forward

end InfoGeometry.Physics.SolovievDressedInterference.ProofDependency
