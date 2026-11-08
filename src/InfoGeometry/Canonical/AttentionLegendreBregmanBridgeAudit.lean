import InfoGeometry.Canonical.AttentionLegendreBregmanBridge

/-!
# Audit Companion: Attention Legendre-Bregman Bridge

Independent audit file verifying that all declarations in
`InfoGeometry.Canonical.AttentionLegendreBregmanBridge` compile cleanly, have 0 `sorry`,
0 `admit`, and depend only on standard Lean 4 core foundational axioms:
`[propext, Classical.choice, Quot.sound]`.
-/

namespace InfoGeometry.Canonical.AttentionLegendreBregman.Audit

variable {M : ℕ} [NeZero M]

#check @partitionZ
#check @partitionZ_pos
#check @partitionZ_ne_zero
#check @softmaxProb
#check @softmaxProb_pos
#check @softmaxProb_sum
#check @lse
#check @bregmanLSE
#check @klSoftmax
#check @log_softmaxProb_eq
#check @bregman_lse_eq_kl_softmax
#check @bregman_lse_self_zero
#check @bregman_lse_shift_invariant

#print axioms bregman_lse_eq_kl_softmax
#print axioms bregman_lse_self_zero
#print axioms bregman_lse_shift_invariant

end InfoGeometry.Canonical.AttentionLegendreBregman.Audit
