import InfoGeometry.Quantum.HeisenbergAsanoRandomLoopSynthesis

namespace InfoGeometry.Quantum.HeisenbergAsanoRandomLoopSynthesis

/-!
# Kernel Axiom Audit for `HeisenbergAsanoRandomLoopSynthesis`

This audit companion prints the transitive kernel axiom dependencies of all
23 theorems in `HeisenbergAsanoRandomLoopSynthesis.lean` (`[propext, Classical.choice, Quot.sound]`,
with zero custom axioms or proof holes).
-/

#print axioms pauliX_mul_pauliZ_ne_pauliZ_mul_pauliX
#print axioms commutator_pauliX_pauliY
#print axioms spinSwapMatrix_sq
#print axioms trace_spinSwapMatrix
#print axioms toth_pauli_exchange_identity
#print axioms tothLoopWeight_pos
#print axioms tothLoopWeight_add
#print axioms real_pow_lt_one_of_lt_one
#print axioms singleLoopFugacityFactor_ne_zero_of_norm_lt_one
#print axioms configLoopPoly_ne_zero_of_norm_lt_one
#print axioms singleLoopFugacityFactor_inv
#print axioms singleLoopFugacityFactor_zero_iff_inv_zero
#print axioms singleLoopFugacityFactor_root_norm_eq_one
#print axioms configLoopPoly_zero_iff_inv_zero
#print axioms configLoopPoly_root_norm_eq_one
#print axioms configLoopPoly_root_to_critical_line
#print axioms ferromagnetic_asanoContract_root_iff
#print axioms ferromagnetic_asanoContract_root_on_unitCircle
#print axioms ferromagnetic_asanoContract_ne_zero_in_openDisk
#print axioms asano_rankOne_contracted_root_radius_bound
#print axioms loopMagnetization_ge_quarter_spin
#print axioms loopMagnetization_ge_eighth_of_spin_half
#print axioms loopMagnetization_pos_of_spin_half

end InfoGeometry.Quantum.HeisenbergAsanoRandomLoopSynthesis
