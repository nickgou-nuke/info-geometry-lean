/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Ergodic.RuelleTransfer

namespace InfoGeometry.Canonical

open InfoGeometry.Ergodic.RuelleTransfer

/--
Canonical projection capstone for the Ruelle transfer operator and symbolic thermodynamics:
1. Exact topological recovery: shiftWord (extendWord b x) = x.
2. Additive linearity of the transfer operator.
3. Scalar multiplicativity.
4. Unweighted Markov conservation: ruelleTransfer 0 1 = 2.
5. Exact local dual pairing with the Perron-Frobenius measure operator.
-/
theorem ruelle_transfer_canonical_capstone
    {n : ℕ}
    (φ f f₁ f₂ : BitWord (n + 1) → ℝ)
    (ν : BitWord n → ℝ)
    (c : ℝ)
    (x : BitWord n)
    (b : Bool) :
    -- 1. Exact topological recovery
    (shiftWord (extendWord b x) = x) ∧
    -- 2. Linearity
    (ruelleTransfer φ (fun y => f₁ y + f₂ y) x =
      ruelleTransfer φ f₁ x + ruelleTransfer φ f₂ x) ∧
    -- 3. Scalar multiplication
    (ruelleTransfer φ (fun y => c * f y) x = c * ruelleTransfer φ f x) ∧
    -- 4. Markov property
    (ruelleTransfer (fun _ => 0) (fun _ => 1) x = 2) ∧
    -- 5. Exact local dual pairing
    (ruelleTransfer φ f x * ν x =
      f (extendWord false x) * dualTransfer φ ν (extendWord false x) +
      f (extendWord true x) * dualTransfer φ ν (extendWord true x)) := by
  exact ⟨
    shift_extend_word b x,
    ruelle_transfer_add φ f₁ f₂ x,
    ruelle_transfer_smul φ f c x,
    transfer_markov_unweighted x,
    ruelle_dual_symmetry φ f ν x
  ⟩

end InfoGeometry.Canonical
