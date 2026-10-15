import InfoGeometry.QuantumContext.PetzRecoveryMartingale

/-!
# Audit Companion: Petz Recovery Map, FlashAttention Martingale Filtration & Jones Subfactor Index

This module verifies the kernel axiomatic footprint and non-vacuity of
`InfoGeometry.QuantumContext.PetzMartingale`.
-/

namespace InfoGeometry.QuantumContext.PetzMartingale.Audit

open InfoGeometry.QuantumContext.PetzMartingale

#check @compile_petz_recovery_martingale
#check @petz_recovery_idempotent
#check @petz_recovery_exact_on_support
#check @petz_channel_composition
#check @eviction_channel_annihilates_Q
#check @petz_annihilates_eviction_ideal
#check @martingale_filtration_collapse
#check @connes_radon_nikodym_support_action
#check @jones_index_pos
#check @jones_index_ge_one
#check @jones_index_eq_mul
#check @flashattention_jones_index_value

#print axioms compile_petz_recovery_martingale
#print axioms petz_recovery_idempotent
#print axioms petz_recovery_exact_on_support
#print axioms petz_channel_composition
#print axioms eviction_channel_annihilates_Q
#print axioms petz_annihilates_eviction_ideal
#print axioms martingale_filtration_collapse
#print axioms jones_index_pos
#print axioms jones_index_ge_one
#print axioms flashattention_jones_index_value

end InfoGeometry.QuantumContext.PetzMartingale.Audit
