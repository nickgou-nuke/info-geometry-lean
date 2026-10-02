import InfoGeometry.Geometry.RelationalQuantumKinematics

namespace InfoGeometry.Geometry.RelationalQuantumKinematics.ProofDependency

inductive Archetype
  | equivariantFrame
  | particleNormalization
  | actionCocycle
  | cocyclicFrameTransport
  | circleNormPreservation
  | particleWaveCovariance
  deriving DecidableEq, Fintype

open Archetype

def prerequisites : Archetype → Finset Archetype
  | equivariantFrame => {equivariantFrame}
  | particleNormalization => {equivariantFrame, particleNormalization}
  | actionCocycle => {actionCocycle}
  | cocyclicFrameTransport => {equivariantFrame, actionCocycle, cocyclicFrameTransport}
  | circleNormPreservation =>
      {equivariantFrame, actionCocycle, cocyclicFrameTransport, circleNormPreservation}
  | particleWaveCovariance => Finset.univ

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
    equivariantFrame < particleNormalization ∧
    equivariantFrame < cocyclicFrameTransport ∧
    actionCocycle < cocyclicFrameTransport ∧
    cocyclicFrameTransport < circleNormPreservation ∧
    particleNormalization < particleWaveCovariance ∧
    circleNormPreservation < particleWaveCovariance := by
  simp only [lt_iff_le_not_ge]
  decide

theorem normalization_and_cocycle_incomparable :
    ¬ particleNormalization ≤ actionCocycle ∧ ¬ actionCocycle ≤ particleNormalization := by
  decide

theorem no_dependency_cycle {earlier later : Archetype}
    (forward : earlier < later) : ¬ later < earlier := lt_asymm forward

end InfoGeometry.Geometry.RelationalQuantumKinematics.ProofDependency
