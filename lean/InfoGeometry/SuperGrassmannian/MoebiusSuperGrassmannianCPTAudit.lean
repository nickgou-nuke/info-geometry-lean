import InfoGeometry.SuperGrassmannian.MoebiusSuperGrassmannianCPT

/-!
# Axiom readback for finite reflection identities

These commands expose the kernel axiom dependencies of the declarations in
`MoebiusReflection`. They are audit output, not a claim of a separate bundle,
spin-structure, or total CPT construction.
-/

namespace InfoGeometry.SuperGrassmannian.MoebiusReflection.Audit

open InfoGeometry.SuperGrassmannian.MoebiusReflection

#check tau_sq
#check tau_conj_adH
#check tau_reverses_adH_eigenvalue
#check tau_jordanPairPlus_covariant
#check tau_jordanPairMinus_covariant
#check tau_intertwines_ospPairingElement
#check supertrace_tau_invariant
#check compile_moebius_matrix_reflection

#print axioms tau_sq
#print axioms tau_conj_adH
#print axioms tau_reverses_adH_eigenvalue
#print axioms tau_jordanPairPlus_covariant
#print axioms tau_jordanPairMinus_covariant
#print axioms tau_intertwines_ospPairingElement
#print axioms supertrace_tau_invariant
#print axioms compile_moebius_matrix_reflection

end InfoGeometry.SuperGrassmannian.MoebiusReflection.Audit
