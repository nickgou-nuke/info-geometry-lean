# Finite real coordinate Fock bounds and CLM packaging — research contract

Status: source research only. No builds/tests/live edits/new proof. The real
metric owner is native; signed-action final native QA and adjoint candidate QA
remain parent-managed dependencies. Do not infer their acceptance from this file.

## Exact carrier and dependency
Use existing InfoGeometry.Clifford.SpinorSpace (ClNNNeutralChevalleyBridge.Vector n),
with LOCAL activation of native fockNormedAddCommGroup and fockInnerProductSpace.
Let C_i be existing extAction ((Pi.basisFun ℝ (Fin n)) i), and D_i be existing
intAction (LinearMap.proj i : Module.Dual ℝ (Vector n)). These are notation for
native linear maps, not proposed new algebraic operators or carriers.

The required adjoint theorem is the queued
fock_extAction_intAction_inner n i x y :
 inner ℝ (C_i x) y = inner ℝ x (D_i y).
Invoke its actual proved declaration once promoted; do not take it as a field or
hypothesis of the final bounds. No norm or action hypothesis may be added.

## Smallest theorem sequence
1. fock_coordinate_norm_sq_split n i x:
   norm(C_i x)^2 + norm(D_i x)^2 = norm(x)^2.
2. fock_extAction_norm_le n i x: norm(C_i x) <= norm(x).
3. fock_intAction_norm_le n i x: norm(D_i x) <= norm(x).
4. Two native CLM constructions, e.g. fockExtActionCLM n i and
   fockIntActionCLM n i, made by C_i.mkContinuous 1 / D_i.mkContinuous 1 using
   the proved bounds (normalize 1*norm x). Their carrier remains SpinorSpace.
5. Separate rfl application or toLinearMap lemmas identifying those CLMs with
   the original actions, and separate op-norm <=1 lemmas from mkContinuous_norm_le.

These are distinct reusable declarations, not a conjunction bundle. The exact
constant is for coordinate modes of unit pairing; arbitrary unnormalized u or
covectors are not claimed to have operator norm <=1. All n allowed; i:Fin n
makes coordinate statements vacuous at n=0 without adding Nonempty assumptions.

## Proof of the key split, with signs and order explicit
Native ext_int_anticommutator gives
 C_i(D_i x) + D_i(C_i x) = x
because (LinearMap.proj i)(Pi.basisFun ... i)=1. This is the existing positive
CAR convention (not the negative Zorn convention).
Apply inner with x in the second slot and use inner_add_left:
 inner(C_i(D_i x),x) + inner(D_i(C_i x),x) = inner(x,x).
First term equals inner(D_i x,D_i x) by adjointness at (D_i x,x).
Second term equals inner(C_i x,C_i x) by real_inner_comm followed by adjointness
at (x,C_i x). Replace all self-inners by squared norms and commute the sum.
This proves the split without using C_i^2=0 or D_i^2=0 (those exist but are
unnecessary here), and without defining a continuous adjoint first.

Each squared norm is <= norm(x)^2 by nonnegativity of the other square. Pass to
norm bounds using nonnegative norms, e.g. sq_le_sq₀ / nlinarith with norm_nonneg
and sq_nonneg. No estimate on multiplication in the exterior algebra is used.
The metric is positive by its induced-coordinate construction, NOT by Q=0.

## Native owners and what they already cover
- Clifford/ChevalleySpinorBlueprint.lean:38 extAction; :46 intAction;
  :50 ext_int_anticommutator. Already genuine native linear maps and CAR.
- Clifford/FiniteRealFockMetric.lean:fockNormedAddCommGroup,
  fockInnerProductSpace, fock_exteriorBasis_inner, fockTailMap_norm.
  Tail-map norm preservation is proved for a different map; it does not imply
  creation/contraction contractivity without the new argument.
- Clifford/FiniteFockSignedBasisActions.lean is present after parent promotion;
  signed insert/delete formulas are its exact action API. Parent handles final QA.
- scratch/FiniteRealFockAdjoint20261024.lean supplies proposed coordinate inner
  adjointness; semantic AA passed per parent, kernel acceptance still pending.
- Clifford/FockSpaceCAR.lean:creation / annihilation are transported via
  fockExteriorEquiv. fockExteriorEquiv_zero_apply and zero_symm_apply identify the
  zero-form equivalence with identity; creation_apply_ι_mul and
  annihilation_apply_contractLeft identify the resulting actual actions. These
  are algebraic APIs, not norm/CLM bounds. Future consumers may use these laws
  rather than duplicating operators.
- Clifford/ClNNFockRepresentation.lean transports the primal-sheet algebraic
  representation; no relevant coordinate metric bound was found there.
- Quantum/Fock.lean:creationOp/annihilationOp are gradePlusProj/gradeMinusProj
  on DoubledSpace E, with assumed Hilbert E. Their complementary-projector laws
  are NOT the nilpotent exterior coordinate actions. Do not reuse their norms
  as a substitute for this carrier's theorem.

Search scope: relevant Fock/Chevalley/CAR owner paths; exact extAction/intAction
norm queries; broader coordinate creation/annihilation norm queries in Clifford,
OperatorAlgebra and Quantum; read native FockSpaceCAR, ClNNFockRepresentation,
metric and CAR definitions. No corresponding coordinate norm<=1/CLM packaging
on this induced exterior metric was located in that bounded search. Not a
repo-wide assertion that other CAR norm theorems are absent.

## Mathlib APIs actually read
Analysis/InnerProductSpace/Basic.lean:
 real_inner_self_eq_norm_sq, real_inner_comm, inner_add_left.
Analysis/Normed/Operator/ContinuousLinearMap.lean:55:
 LinearMap.mkContinuous C (h : forall x, norm(f x)<=C*norm x).
 :81 mkContinuous_coe and :86 mkContinuous_apply are rfl identifications.
Analysis/Normed/Operator/Basic.lean:475:
 LinearMap.mkContinuous_norm_le f (hC:0<=C) h gives norm(f.mkContinuous C h)<=C.
ContinuousLinearMap.opNorm_le_bound is an alternative once the CLM exists.
Analysis/InnerProductSpace/Adjoint.lean has apply_norm_sq_eq_inner_adjoint_left/right
for continuous maps in its Hilbert setting, but using it here first would add
unnecessary continuity/completeness prerequisites. Prefer the proven inner
identity and mkContinuous; no CompleteSpace is needed for this packaging.

## Boundaries / later consumers
Do not assert norm=1 (although basis witnesses may support a later sharpness
lemma), arbitrary-mode bounds, continuous adjoint equality, completion extensions,
complexification, coupled Hamiltonians, or Dirac-family compatibility in this
batch. No global metric/CLM instance on the algebra, no false NormedRing claim,
no new completion carrier. Completion/coupling remain separate tasks.
