# Finite real Fock creation/contraction adjointness — source contract only

No proof candidate, builds/tests, live edits, scalar refactor, or global instances.
Metric dependency is the exact induced structures in the queued
scratch/FiniteRealFockMetric20261024v2.lean, not a presumed accepted metric owner.
Batch-1 InfoGeometry.Clifford.FockTailExteriorBasis is native/accepted per parent.

## Exact target (first batch)
Use the EXISTING SpinorSpace (ClNNNeutralChevalleyBridge.Vector n).
Activate fockNormedAddCommGroup / fockInnerProductSpace locally after their
acceptance. Let e_i=(Pi.basisFun ℝ (Fin n)) i and epsilon_i=LinearMap.proj i.
Proposed named theorem, with no adjointness hypothesis:

  fock_extAction_intAction_inner (n) (i : Fin n) (x y : SpinorSpace (Vector n)) :
    inner ℝ (InfoGeometry.Clifford.extAction e_i x) y =
      inner ℝ x (InfoGeometry.Clifford.intAction epsilon_i y).

The contraction covector is the coordinate evaluation, NOT Q.associated e_i:
Q=0 would make that covector zero and yield the wrong operator. No arbitrary
covector can be the adjoint of a fixed vector unless its pairing is specified.
No definition of new creation/annihilation operators is necessary.

## Existing declarations: proved source versus scope
- Clifford/ChevalleySpinorBlueprint.lean:32 SpinorSpace is CliffordAlgebra 0;
  :38 extAction is left multiplication by CliffordAlgebra.ι 0 u;
  :46 intAction is CliffordAlgebra.contractLeft f;
  :50 ext_int_anticommutator proves CAR from the native contraction recursion;
  :65 ext_sq_zero and :72 int_sq_zero supply nilpotence. These are algebraic,
  not inner-product adjointness assertions.
- Clifford/Cl55ChevalleyCoordinateCAR.lean:chevalleyCoordinateCovector_apply_basis
  and chevalley_coordinate_CAR specialize coordinate CAR at five modes.
- Clifford/SplitClifford55ExteriorSpinor.lean:wedge, contract, dualBasisVector_apply,
  contract_wedge, wedge_sq, contract_sq are the five-mode exterior realization.
- Clifford/Cl55ExteriorContractionGrading.lean:contraction_wedge_homotopy and
  differential_ιMulti_succ_mem prove Koszul recursion/degree lowering. They do
  not provide a normalized Finset-basis signed deletion coefficient.
- Clifford/ClNNNeutralChevalleyBridge.lean:fockTailMap_generator and
  fockTailMap_contractLeft give actual generator/covector-tail naturality.
- Clifford/FockTailHeadAnnihilation.lean:contractLeft_head_fockTailMap and
  head_number_fockTailMap are algebraic new-head annihilation identities.
- Clifford/FockTailExteriorBasis.lean:fockTailMap_exteriorBasis transports the
  exact increasing Finset basis by Fin.succEmb; no Hilbert assertion by itself.
- Clifford/ExteriorZornCARIntertwiner.lean:creationMap_basis, fockToZorn_wedge,
  coordinate contraction intertwining, and signed fockPreimage are genuine
  three-mode Zorn/exterior bridges. They do not supply an all-rank basis metric
  or adjoint relation on the exact carrier; do not replace the carrier by Zorn.
- Queued metric v2:fock_exteriorBasis_inner gives Kronecker inner products;
  fockTailMap_inner and fockTailLinearIsometry concern only the tail embedding.
  Their acceptance is a dependency, not claimed from this source research.

Bounded search: CAR/Chevalley/Fock/Exterior owner paths; exact-word extAction,
intAction, contractLeft combined with inner/adjoint/basis/insert/erase/sign;
Mathlib exterior algebra/power and Clifford contraction owners. No all-n signed
Finset insert/erase action or this induced-metric adjoint theorem was located.
This does not assert absence of adjoints on other Hilbert or doubled carriers.

## Small reusable algebraic deltas
Write b S=(Pi.basisFun ℝ (Fin n)).ExteriorAlgebra S and
r(i,S)=(S.filter (fun j => j < i)).card, epsilon(i,S)=(-1:ℝ)^r(i,S).
No new carrier or theorem-packet structure; r/epsilon can remain expressions.

1. Creation basis action:
   extAction e_i (b S) =
     if i ∈ S then 0 else epsilon(i,S) • b (insert i S).
2. Contraction basis action:
   intAction (LinearMap.proj i) (b S) =
     if i ∈ S then epsilon(i,S) • b (S.erase i) else 0.

The sign counts occupied indices STRICTLY BEFORE i, because multiplication is
on the left and the exterior basis uses increasing order. For i=0 both nonzero
signs are +1. An index in position k has contraction sign (-1)^k. Erasing i
does not change the count of indices below i; inserting absent i does not either.
These facts align the two matrix coefficients, not just their absolute values.

Possible minimal proof factoring:
- increasing wedge word split at its least element, plus basis singleton/empty
  identities derived from basis_apply_ofCard / ιMulti_family;
- derive insert/delete formulas by increasing-list recursion, moving a creation
  generator past the preceding distinct generators, and applying contractLeft_ι_mul
  at each step. At the matched coordinate use projection e_i=1; all others zero.
- if using the existing basis multiplication theorem instead, prove the
  singleton permutation sign equals (-1)^r(i,S) as a distinct combinatorial
  helper. Do not assume this equality or silently discard its sign.
Use whichever route yields less new combinatorics; both require source proofs.
No need to prove a full arbitrary-covector deletion-sum formula first.

## Exact Mathlib reuse
LinearAlgebra/ExteriorAlgebra/Basis.lean:basis_apply_ofCard,
basis_mul_of_not_disjoint, basis_mul_of_disjoint. The latter already uses
Set.powersetCard.permOfDisjoint.sign, not the explicit before-index count.
Order/Hom/PowersetCard.lean:70 defines that permutation by concatenation and
sorting. Its singleton sign-to-count identity was not found in this inspected API.
LinearAlgebra/ExteriorAlgebra/Basic.lean:ιMulti_apply is ordered List.ofFn.prod;
ιMulti_zero_apply, ιMulti_succ_apply and ι_mul_ιMulti_anticomm provide word rules.
LinearAlgebra/CliffordAlgebra/Contraction.lean:125 contractLeft_ι_mul is
 d(ι v*x)=d(v)•x-ι v*d(x); contractLeft_ι, contractLeft_algebraMap,
contractLeft_one and linearity supply the recursion base and evaluation.
Analysis/InnerProductSpace/ExteriorPower.lean supplies degree metrics but no
creation/contraction adjoint theorem located in that file; importing it does not
identify its metrics with the queued full Fock metric automatically.

## From algebraic formulas to the metric theorem
First prove the target on b S,b T by both action formulas and
fock_exteriorBasis_inner. Nonzero coefficients occur precisely when i ∉ S and
T=insert i S (equivalently i ∈ T and S=T.erase i); the before-index counts agree.
Then extend using Basis.sum_repr twice and linearity/real inner scalar laws,
as in the metric tail proof. No adjoint or positivity field is assumed.

A later optional arbitrary-vector statement uses the explicitly defined native
covector sum i, u i • LinearMap.proj i, and coordinate expansion of u. It is not
needed for the first coordinate theorem. ContinuousLinearMap adjoints require
additional boundedness/completeness packaging and are deliberately deferred.
No norm bound, completed real or complex colimit, coupled Hamiltonian, or Dirac
construction follows merely from this contract. Existing native operators and
basis remain the owners; no master bundle or global complexification.
