# Native Fock Hilbert upgrade — source-grounded finite contract

Read-only research, 2026-10-24. No implementation, builds, or kernel-pass claim.
This contract preserves the existing real algebraic Fock carrier and does not
assume a positive inner product, adjoint law, or Hilbert bonding isometry.

## Exact carriers and existing basis APIs
`Clifford/ChevalleySpinorBlueprint.lean:32` defines
SpinorSpace L := CliffordAlgebra (0 : QuadraticForm ℝ L).
`ClNNNeutralChevalleyBridge.Vector n` is Fin n → ℝ, and `fockTailMap n` is the
CliffordAlgebra.map of vectorHeadZero n. This is definitionally the actual
ExteriorAlgebra ℝ (Fin n → ℝ), not a replacement coordinate carrier.

Mathlib LinearAlgebra/ExteriorAlgebra/Basis.lean already constructs
`Module.Basis.ExteriorAlgebra : Basis (Finset I) R (ExteriorAlgebra R M)`
from an ordered basis b:I→M. Thus use
  b n := (Pi.basisFun ℝ (Fin n)).ExteriorAlgebra.
Do not rebuild the graded direct sum or invent a Fin(2^n) spinor proxy.
`ExteriorAlgebra.basis_apply`, `basis_apply_powersetCard`,
`basis_mul_of_disjoint`, `basis_mul_of_not_disjoint` are available.
`Module.Basis.equivFun` supplies the finite coordinate linear equivalence.

Native `SplitClifford55ExteriorDegrees.exteriorAlgebraBasisFinset` already gives
the rank-five basis through a graded direct sum and reindexing. It is not an
all-rank Hilbert construction. Do not silently identify different enumeration
conventions if later connecting to its matrix readout owners. The all-rank
Mathlib basis construction avoids copying that specialized basis machinery.

## Finite metric construction on the same carrier
Form the explicit linear equivalence
  q n : SpinorSpace (Vector n) ≃ₗ[ℝ]
        EuclideanSpace ℝ (Finset (Fin n))
by composing (b n).equivFun with (WithLp.linearEquiv 2 ℝ _).symm.
This exact WithLp direction is used by native ClNNToDoubledKreinTransport's
vector-to-Euclidean equivalence, although that owner concerns the base vector
space rather than exterior Fock space.

Pull back the ℓ² inner product: <x,y> := <q n x,q n y>.
Positive definiteness follows from q n.injective and the native ℓ² norm;
no positivity premise is allowed. Use a named InnerProductSpace.Core and its
canonical toNormedAddCommGroup/ofCore, or carefully aligned native induced norm
APIs (InnerProductSpace.induced, NormedAddCommGroup.induced with injectivity).
Keep instances locally/scoped until parent review; do not install a second
incompatible norm on an existing owner. CompleteSpace follows from finite
dimensionality over complete ℝ; the basis itself proves finite dimensionality.

Mathlib Analysis/InnerProductSpace/ExteriorPower.lean is real-only and already
has canonical finite-dimensional exterior-power inner products and
OrthonormalBasis.exteriorPower. It does NOT, in that file, give a full exterior
algebra Hilbert structure or creation/contraction adjoint theorem. Its graded
pairings should agree with the proposed orthonormal whole-exterior basis; do not
reprove their positivity or pretend a complex exterior-power instance exists.

## Smallest useful proof batches (separate statements)
1. Basis transport, using native inclusion:
   fockTailMap n (b n S) = b (n+1) (S.map Fin.succEmb).
   Fin.succ preserves order, hence no permutation sign. Native
   fockTailMap_generator and vectorHeadZero_coordinate_succ provide the generator
   case; Mathlib exteriorPower.map_apply_ιMulti and map_apply_ιMulti_family expose
   naturality of the ordered wedge. Bridge the full-algebra map to those facts,
   or use its generator/product recursion; do not assume basis naturality.
2. Coordinate zero extension along the injective subset map, then
   inner (fockTailMap n x) (fockTailMap n y) = inner x y.
   Bundle this ACTUAL map as a real LinearIsometry and reuse existing
   fockStageMap_refl/fockStageMap_apply_trans for coherence.
3. Creation/contraction adjointness. For i:Fin n, e_i=Pi.single i (1:ℝ),
   C_i x=CliffordAlgebra.ι 0 e_i*x and
   A_i x=CliffordAlgebra.contractLeft (LinearMap.proj i) x.
   Prove <C_i x,y>=<x,A_i y> for the constructed metric, first on b n S,b n T.
   Creation inserts i with sign (-1)^#{j∈S | j<i} if i∉S, otherwise zero;
   contraction deletes i with the same sign if i∈S, otherwise zero.
   Derive these from actual basis multiplication and contractLeft_ι_mul; do not
   import a matrix transpose identity through an unproved basis identification.
   Finite dimensionality makes the linear maps continuous; native
   ContinuousLinearMap.adjoint_inner_right then identifies the genuine adjoint.
   The same coefficient formula gives ||C_i||≤1 and ||A_i||≤1, useful for a
   uniform coupled-family bound. General real vectors follow by linearity and
   the Euclidean dual pairing. Complex extension needs conjugate-dual conventions.

The accepted `Clifford/FockTailHeadAnnihilation.lean` already proves new-head
contraction and number annihilation. Reuse it; it does not imply the metric or
adjoint laws. Native Clifford/Chevalley and ClNNFockRepresentation already own
creation/contraction and primal-sheet transport; do not duplicate those actions.

## Existing colimit architecture and exact scalar mismatch
`ClNNFockDirectLimitRepresentation` owns real algebraic FockStage, fockStageMap,
fockDirectedSystem, FockInfinity, fockToInfinity and descended Clifford action.
Preserve these. A normed colimit presentation must explicitly identify its
algebraic stage injections with this existing colimit; do not silently replace it.

The current Canonical owners are specialized to ℂ:
- FilteredIsometricInnerProductColimit.IsometricDirectSystem: complex linear isometries;
  RealDirectLimit is a real MODULE colimit of complex stages, not a real-stage API.
- FilteredIsometricInnerProductDirectLimit: descends a complex-valued pairing,
  then constructs SMul/Module ℂ and IsScalarTower ℝ ℂ on the real direct limit;
  positivity explicitly uses Complex.re.
- FilteredIsometricHilbertCompletion: InnerProductSpace.Core ℂ and completion.
- FilteredCompatibleOperatorColimit and FilteredCompatibleOperatorSelfAdjoint:
  complex-linear stage operators and adjoints.
Consequently changing only the scalar argument at the consumer will not work.
The real Fock stage at n=0 has dimension one over ℝ: it cannot carry a compatible
complex-vector-space structure. Do not install a fake ℂ action on the real tower.

Option A, preserving the real Fock carrier directly: parent-reviewed scalar
parameterization of the EXISTING generic isometric/compatible-operator owners to
RCLike 𝕜, preserving their current ℂ APIs. This is a multi-owner infrastructure
change, not a two-line consumer repair. Choose a coherent direct-limit scalar
presentation and prove any comparison with native real FockInfinity. No parallel
replacement hierarchy should be introduced merely to avoid that review.

Option B, if the actual consumer requires complex quantum dynamics: explicit
scalar extension ℂ ⊗[ℝ] SpinorSpace(Vector n), with maps 1⊗fockStageMap and a
proved injective real-to-complex stage embedding, transported basis/Hermitian
metric and action/adjoint naturality. Mathlib
CliffordAlgebra.equivBaseChange (LinearAlgebra/CliffordAlgebra/BaseChange.lean:183)
relates this tensor extension to the base-changed Clifford algebra. It supplies
algebraic equivalence, not the Hilbert metric or completed covariance for free.
This is a genuine scalar extension with an explicit map, not identification of
the real source with a substitute complex carrier. Do not relabel ℝ coordinates
as ℂ or bypass proof transport. No all-rank native Fock complexification/Hilbert
upgrade was found in the inspected Fock/tower owners and scalar-extension searches.

Recommendation: first prove batches 1–3 on the existing REAL finite Fock stages.
Choose A vs B only with the next consumer's scalar requirement and parent review.
The finite metric/isometry/adjoint bridge is useful to either path.

## Coupled-family scope
A new-head number N annihilates the old embedded Fock space. An old even
selfadjoint observable times N can therefore be a nonzero coupled increment
while preserving that space; commuting factors and the proved adjoint laws give
selfadjointness. Summable weights and explicit local norm bounds then give a
uniform bound. These additional conclusions are NOT proved by the current
algebraic annihilation lemmas or this contract. The trace-GNS centralizing-
increment obstruction is not a universal impossibility of coupled Fock models.

Search scope: actual ClNNNeutralChevalleyBridge/FockRepresentation/FockDirectLimit,
Cl55 exterior basis/readout/matrix intertwiners, native vacuum and Hodge-Fock
embedding owners, all filtered isometric completion owners, plus Mathlib exterior
basis/power inner-product/contraction/base-change/PiL2 APIs. No compiler was run.
