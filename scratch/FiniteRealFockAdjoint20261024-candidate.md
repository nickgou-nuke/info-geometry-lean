# Finite real coordinate adjointness — uncompiled candidate

NEW candidate imports intended native InfoGeometry.Clifford.FiniteFockSignedBasisActions
(pending promotion and serial QA) and accepted native FiniteRealFockMetric.
The signed-action interface was read from scratch/FiniteFockSignedBasisActions20261024v2.lean.
No copied dependency proofs or fallback import. Compile only after parent promotes
the signed-action owner. Earlier research contract is preserved unchanged.

Four separate lemmas, no bundle:
- fock_signed_basis_inner_left / right translate the SAME integer-unit sign
  into its real scalar coefficient using the native induced basis metric;
- fock_extAction_intAction_inner_basis compares actual native operator actions;
- fock_extAction_intAction_inner extends that equality by finite basis sums.

The basis proof splits occupied/unoccupied coordinates. Only the nonzero case
S=T.erase i needs sign agreement: after substitution both actions use the identical
fockInsertSign n i (T.erase i), with proof-irrelevant absence witnesses. Thus no
sign-count identity, arbitrary sign, assumed action or adjointness is introduced.
All other cases vanish by the actual orthonormal basis formula and membership.

The target is precisely inner ℝ (extAction e_i x) y = inner ℝ x (intAction proj_i y)
on existing SpinorSpace(Vector n), under fockNormedAddCommGroup and
fockInnerProductSpace activated LOCALLY. No global instance, new operator carrier,
zero-quadratic metric, complexification, norm bound, continuous adjoint operator,
completed colimit, or coupled-family result. All n are retained; coordinate
statements have i:Fin n, without a Nonempty assumption.

Source-backed reuse: native FiniteRealFockMetric fock_exteriorBasis_inner and its
finite expansion proof; queued signed-action insert/erase and occupied/absent-zero
lemmas; Mathlib Units.smul_def, Int.cast_smul_eq_zsmul, real_inner_smul_left/right,
Finset.insert_erase and Basis.sum_repr. No build/test/live edit or budgets added.
Independent QA must check elaboration after dependency promotion.
