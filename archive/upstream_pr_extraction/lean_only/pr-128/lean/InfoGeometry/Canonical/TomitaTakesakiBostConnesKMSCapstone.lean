import InfoGeometry.Quantum.TomitaTakesakiBostConnesKMS

namespace InfoGeometry.Canonical.TomitaTakesakiBostConnesKMSCapstone

open InfoGeometry.Quantum.TomitaTakesakiBostConnesKMS

theorem capstone_tomita_takesaki_kms_synthesis
    (R : Type*) [Ring R] (F : OneParameterFlow R)
    (x : R) (n : ℕ) (t₁ t₂ β : ℝ) (hn : 0 < n) (hβ : β = 1) :
    (F.flow 0 x = x) ∧
    (bostConnesModularPhase n 0 = 1) ∧
    (bostConnesModularPhase n (t₁ + t₂) = bostConnesModularPhase n t₁ * bostConnesModularPhase n t₂) ∧
    (kmsWeight 1 β = 1) ∧
    (β - 1 = 0) :=
  grand_tomita_takesaki_kms_synthesis R F x n t₁ t₂ β hn hβ

end InfoGeometry.Canonical.TomitaTakesakiBostConnesKMSCapstone
