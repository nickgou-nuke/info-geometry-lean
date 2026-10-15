import InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian

/-!
# Audit Companion for Section 85: Kantor–Tanaka Super-Grassmannian Lie Bracket

This module audits the axiomatic footprint of all theorems in
`KantorTanakaSuperGrassmannian.lean`.
-/

namespace InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian.Audit

open InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian

-- Section 2: General Bracket Identities
#print axioms bracket_skew
#print axioms bracket_self
#print axioms jacobi_identity
#print axioms derivation_identity

-- Section 3: The Fundamental Tanaka-Kantor Graded Brackets
#print axioms odd_contact_bracket
#print axioms odd_contact_bracket_conjugate
#print axioms extremal_bracket_generates_H
#print axioms spinor_bilinear_01_10
#print axioms spinor_bilinear_12_21
#print axioms spinor_bilinear_sum_eq_H

-- Section 4: Grade Truncation Beyond the 5-Graded Boundary
#print axioms grade_truncation_2_1a
#print axioms grade_truncation_2_1b
#print axioms grade_truncation_neg2_neg1a
#print axioms grade_truncation_neg2_neg1b

-- Section 5: The Krein / Paracomplex Sheet-Swap Involution J
#print axioms JX_apply
#print axioms XJ_apply
#print axioms swap_apply
#print axioms J_involutive
#print axioms J_inverts_H
#print axioms J_inverts_grade_two
#print axioms J_inverts_grade_one_a
#print axioms J_inverts_grade_one_b
#print axioms J_lie_automorphism

-- Section 6: Graded Supertrace and Invariant Duality Pairing
#print axioms supertrace_H
#print axioms supertrace_E02_E20
#print axioms supertrace_E02_E01_orthogonal
#print axioms supertrace_E01_E01_orthogonal
#print axioms supertrace_E02_E02_orthogonal

-- Section 7: Master Certificate
#print axioms compile_kantor_tanaka_super_grassmannian

end InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian.Audit
