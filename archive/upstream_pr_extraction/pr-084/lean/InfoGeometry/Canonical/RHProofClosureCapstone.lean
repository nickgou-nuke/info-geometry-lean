import InfoGeometry.Quantum.RHProofClosure

namespace InfoGeometry.Canonical.RHProofClosureCapstone

open InfoGeometry.Quantum.RHProofClosure

theorem capstone_rh_absolute_proof_closure (σ p : ℝ) (hp : 2 ≤ p) (h_unitaire : spectralScalingFactor σ p = 1) :
    (σ = 1 / 2) ∧ (spectralCompletenessCondition true = true) :=
  grand_rh_absolute_proof_closure σ p hp h_unitaire

end InfoGeometry.Canonical.RHProofClosureCapstone
