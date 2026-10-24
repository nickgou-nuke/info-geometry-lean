# Signed finite Fock basis actions — uncompiled algebraic candidate

Imports only native FockTailExteriorBasis. Exact existing SpinorSpace(Vector n),
Pi.basisFun.ExteriorAlgebra, extAction and intAction; no metric dependency,
new carrier, hAction assumption, or adjoint/continuity assertion.

Sign convention is Mathlib's actual Set.powersetCard.permOfDisjoint.sign : ℤˣ
for singleton {i} followed by S. Named fockInsertSign records this concrete sign;
it is not an arbitrary parameter or new carrier. This chooses the permutation
route from FiniteRealFockAdjoint20261024.md. The further identity with
(-1)^card(S.filter (fun j => j<i)) is NOT claimed proved here or needed for the
matching insert/delete coefficients. No sign is discarded or replaced by +1.

Small independent lemmas: singleton basis generator; contraction kills a wedge
word whose letters all have zero covector pairing; absent-coordinate contraction;
fresh-index creation with sorting sign; occupied-index creation zero;
contraction of inserted index with SAME sign; occupied-coordinate erase formula.
The contraction sign is derived via native CAR, absent contraction, and inversion
of the integer-unit permutation sign (Int.units_inv_eq_self). No deletion formula
is assumed. The generic word lemma includes m=0. There is no Nonempty(Fin n)
assumption; coordinate statements quantify i:Fin n and hence are vacuous at n=0,
while the vacuum word base case is covered honestly.

Sources actually read: ChevalleySpinorBlueprint extAction/intAction/CAR;
Mathlib ExteriorAlgebra.Basis basis_apply_ofCard and basis_mul_of_(not_)disjoint;
ExteriorAlgebra.Basic ιMulti_zero/succ; CliffordAlgebra.Contraction
contractLeft_ι_mul/one; Order.Hom.PowersetCard permOfDisjoint;
Algebra.Module.LinearMap.Defs map_zsmul_unit and native units inverse law.

No builds/tests/live edits, no budgets/global instances. Candidate elaboration
(in particular dependent powerset-card coercions) requires independent QA.
Later metric adjointness can use the two matching coefficients directly without
first proving the sign-count characterization. All previous work preserved.
