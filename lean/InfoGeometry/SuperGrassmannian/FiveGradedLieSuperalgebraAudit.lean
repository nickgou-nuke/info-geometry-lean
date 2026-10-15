import InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra

/-!
# Audit Companion for 5-Graded Lie Superalgebra and Kantor–Tanaka Derivation

This module audits the axiomatic footprint of all theorems in
`FiveGradedLieSuperalgebra.lean`.
-/

namespace InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra.Audit

open InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra

-- Section 1: Polynomial Factorization and Roots
#print axioms quintic_polynomial_factorization
#print axioms five_grade_roots_expansion
#print axioms three_grade_bosonic_roots
#print axioms odd_fermionic_roots

-- Section 2: Concrete 3x3 Commutator Action
#print axioms adH_00
#print axioms adH_01
#print axioms adH_02
#print axioms adH_10
#print axioms adH_11
#print axioms adH_12
#print axioms adH_20
#print axioms adH_21
#print axioms adH_22

-- Section 3: Quintic Identity on General 3x3 Matrices
#print axioms adH_quintic_identity

-- Section 4 & 5: Bosonic and Fermionic Stratification
#print axioms adH_bosonic_cubic
#print axioms adH_fermionic_cubic

-- Section 6: Ideal Handedness — Automorphisms vs Anti-Automorphisms
#print axioms inner_automorphism_mul
#print axioms anti_automorphism_ideal_flip

-- Section 7: Central Identity Hamiltonian & Vanishing Supertrace
#print axioms identity_hamiltonian_central
#print axioms identity_hamiltonian_supertrace_zero

-- Section 8: Master Certificate
#print axioms compile_five_graded_lie_superalgebra

end InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra.Audit
