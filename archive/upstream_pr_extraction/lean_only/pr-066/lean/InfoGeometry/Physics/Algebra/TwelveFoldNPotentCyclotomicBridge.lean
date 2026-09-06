import InfoGeometry.Canonical.TwelveFoldAdditiveCharacter
import InfoGeometry.Canonical.AffineConformalHullNPotencyBridge
import InfoGeometry.Physics.Algebra.NPotentCyclotomicSpinHullBridge

/-!
# Twelve-fold cyclotomic phase in the n-potent hull

This is the explicit compatibility wire between the existing `C12` phase
owner and the general n-potent hull API.  It keeps the cyclic phase carrier
(`ZMod 12` and a primitive twelfth root) separate from the hexagonal dihedral
(`D6`) carrier, while recording the exact consequence
`zeta12 ^ 13 = zeta12`.
-/

noncomputable section

namespace InfoGeometry.Physics.Algebra.TwelveFoldNPotentCyclotomicBridge

open InfoGeometry.Canonical.AffineConformalHullNPotencyBridge
open InfoGeometry.Canonical.TwelveFoldAdditiveCharacter

/-- The primitive C12 phase is a nonzero root of the 13-potent polynomial. -/
theorem zeta12_in_thirteenPotentHull :
    inHull 13 zeta12 := by
  rw [inHull_iff_zero_or_rootOfUnity 13 (by norm_num)]
  right
  exact zeta12_primitive.pow_eq_one

/-- Explicit polynomial form of the C12-to-n-potent compatibility. -/
theorem zeta12_thirteenPotent_equation :
    zeta12 ^ 13 = zeta12 :=
  zeta12_in_thirteenPotentHull

/-- The C12 phase is not in any smaller nontrivial potency degree. -/
theorem zeta12_minimal_nPotency :
    zeta12 ^ 13 = zeta12 ∧
      ∀ n : ℕ, 1 < n → n < 13 → zeta12 ^ n ≠ zeta12 := by
  refine ⟨zeta12_thirteenPotent_equation, ?_⟩
  intro n hn1 hn13 hEq
  have hsub : n - 1 + 1 = n := by omega
  have hpow : zeta12 ^ (n - 1) = 1 := by
    have hmul : zeta12 ^ (n - 1) * zeta12 = 1 * zeta12 := by
      rw [← pow_succ, hsub]
      simpa [hEq]
    exact mul_right_cancel₀ (by exact zeta12_primitive.ne_zero (by norm_num)) hmul
  have hdvd : 12 ∣ n - 1 := zeta12_primitive.dvd_of_pow_eq_one (n - 1) hpow
  have hpos : 0 < n - 1 := by omega
  have hlt : n - 1 < 12 := by omega
  obtain ⟨k, hk⟩ := hdvd
  omega

end InfoGeometry.Physics.Algebra.TwelveFoldNPotentCyclotomicBridge
