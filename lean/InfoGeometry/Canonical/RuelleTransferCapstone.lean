import InfoGeometry.Ergodic.RuelleTransfer
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

open InfoGeometry.Ergodic.RuelleTransfer

/-- Canonical packaging of the finite symbolic transfer identities. -/
theorem ruelle_transfer_canonical_capstone
    {n : ℕ}
    (φ f f₁ f₂ : BitWord (n + 1) → ℝ)
    (ν : BitWord n → ℝ) (c : ℝ) (x : BitWord n) (b : Bool) :
    (shiftWord (extendWord b x) = x) ∧
    (ruelleTransfer φ (fun y => f₁ y + f₂ y) x =
      ruelleTransfer φ f₁ x + ruelleTransfer φ f₂ x) ∧
    (ruelleTransfer φ (fun y => c * f y) x = c * ruelleTransfer φ f x) ∧
    (ruelleTransfer (fun _ => 0) (fun _ => 1) x = 2) ∧
    (ruelleTransfer φ f x * ν x =
      f (extendWord false x) * dualTransfer φ ν (extendWord false x) +
      f (extendWord true x) * dualTransfer φ ν (extendWord true x)) := by
  exact ⟨shift_extend_word b x,
    ruelle_transfer_add φ f₁ f₂ x,
    ruelle_transfer_smul φ f c x,
    transfer_markov_unweighted x,
    ruelle_dual_symmetry φ f ν x⟩

end InfoGeometry.Canonical
