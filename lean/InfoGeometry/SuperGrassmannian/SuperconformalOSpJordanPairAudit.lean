import InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair

/-!
# Audit Companion for Section 86: Superconformal 𝔬𝔰𝔭(1|2) and Jordan Pair Architecture

This module audits the axiomatic footprint of all theorems in
`SuperconformalOSpJordanPair.lean`.
-/

namespace InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.Audit

open InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair

-- Explicit even/odd support for the permuted `(2|1)` matrix grading.
#print axioms H_gen_even
#print axioms E_gen_even
#print axioms F_gen_even
#print axioms Q_plus_odd
#print axioms Q_minus_odd
#print axioms superBracket_H_E
#print axioms superBracket_Qplus_Qplus
#print axioms superBracket_Qminus_Qminus
#print axioms superBracket_Qplus_Qminus

-- Section 1 & 2: Bosonic sl(2) Subalgebra Identities
#print axioms anticomm_symm
#print axioms osp_sl2_H_E
#print axioms osp_sl2_H_F
#print axioms osp_sl2_E_F

-- Section 3: Fermionic Anticommutation & Supercharge Closing
#print axioms osp_anticomm_plus_plus
#print axioms osp_anticomm_minus_minus
#print axioms osp_anticomm_plus_minus
#print axioms osp_anticomm_minus_plus

-- Section 4: Super-Adjoint Grading and Ladder Actions
#print axioms osp_grad_H_Q_plus
#print axioms osp_grad_H_Q_minus
#print axioms osp_ladder_E_Q_minus
#print axioms osp_ladder_F_Q_plus
#print axioms osp_annihilate_E_Q_plus
#print axioms osp_annihilate_F_Q_minus

-- Section 5: The Kantor Jordan Pair & Trilinear Products
#print axioms jordan_pair_plus_eval
#print axioms jordan_pair_minus_eval
#print axioms contactTriplePlus_fundamental
#print axioms contactTripleMinus_fundamental
#print axioms contactJordanPair
#print axioms jordan_pair_plus_scalar_readout
#print axioms jordan_pair_minus_scalar_readout

-- Section 6: Graded Supertrace and Invariant Cancellation
#print axioms supertrace_H
#print axioms supertrace_anticomm_plus_minus
#print axioms supertrace_Q_plus_sq
#print axioms supertrace_Q_minus_sq

-- Section 7: scalar-pair realization by the matrix contact operations
#print axioms contact_jordan_pair_matrix_realization

-- Section 8: closure of the concrete even and odd matrix spans
#print axioms MatrixSpans.span_pair_closure
#print axioms MatrixSpans.even_even_span_closed
#print axioms MatrixSpans.even_odd_span_closed
#print axioms MatrixSpans.odd_even_span_closed
#print axioms MatrixSpans.odd_odd_span_closed

end InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.Audit
