# Completed actual Fock CAR and adjoint: next source-grounded contract

Contract only; no implementation, builds or live edits. Consume the pending
RealFockCompletedCoordinateAction operators on accepted RealFockCompletion.
Reactivate the exact native metric instances and bounded-action v2's
fockInfinityMetricUniformSpace/fockInfinityMetricTopology. No new carrier,
replacement operators, metric, or assumed CAR/adjoint premises.

## Actual finite owners

Clifford/FiniteFockCLMReflexivePair.lean, namespace ClNNNeutralChevalleyBridge:
- fockIntActionCLM_sq_zero n i (21): D*D=0.
- fockExtActionCLM_sq_zero n i (26): C*C=0.
- fock_coordinate_CLM_CAR n i (32): D*C+C*D=1 on the entire finite SpinorSpace.
- fockIntActionCLM_reflexive (47), fockExtActionCLM_reflexive (54) already follow
  from these relations. Do not duplicate a new finite pair owner.
Clifford/FiniteRealFockAdjoint.lean:76, fock_extAction_intAction_inner n i x y:
  inner real (extAction basis_i x) y = inner real x (intAction proj_i y).
The finite CLM apply lemmas in FiniteRealFockNormBounds identify those exact maps.

For multi-mode extensions, existing Clifford/FockSpaceCAR.lean has
creation_anticommute:84, annihilation_anticommute:117,
creation_annihilation_CAR:143. Its carrier is ExteriorAlgebra; native
fockExteriorEquiv_zero_apply/symm_apply:60/65 and creation_apply_ι_mul /
annihilation_apply_contractLeft identify these with the actual zero-form
SpinorSpace actions. Alternatively use Mathlib's Clifford anticommutation and
contractLeft_contractLeft plus ChevalleySpinorBlueprint.ext_int_anticommutator.
Do not create another exterior carrier or rebuild finite CAR from coordinates.

## Minimal completed signatures

All C,D below are EXISTING fockCompletedCreationCLM m i and
fockCompletedContractionCLM m i, not new aliases or fields.
For m:nat and i:Fin m, prove independent lemmas:
1. C*C=0 : equality in RealFockCompletion ->L[real] RealFockCompletion.
2. D*D=0 in that same CLM ring.
3. D*C+C*D=1 (the full identity, not a support placeholder).
4. forall x y:RealFockCompletion,
     inner real (C x) y = inner real x (D y).
5. ContinuousLinearMap.adjoint C = D.
6. ContinuousLinearMap.adjoint D = C.
No new master bundle is needed. Reflexivity is already a short algebraic
consequence; only add a concrete existing-interface consumer if requested.

## Density proof obligations, not assumptions

For 1-3, use explicit ContinuousLinearMap.ext (stop at actual vectors), then
Completion.induction_on with a closed equality of continuous maps. At an
algebraic representative x of stage n, move x to k=max(m,n), using
fockToInfinity_transition / fockStageToCompletion_transition. Repeated
fockCompletedCreationCLM_stage / fockCompletedContractionCLM_stage evaluates
both nested operators at k with the SAME shifted i. Apply the finite CLM
identity to the finite vector and map its equality by fockStageToCompletion k;
linearity supplies addition/zero/identity readback. Do not require n>=m as an
extra premise on an arbitrary completion vector.

For 4, first prove the inner identity on two finite representatives of possibly
different stages n,p. Move BOTH to k=max m (max n p), then use completed stage
readback, fockStageToCompletion_inner, and native finite adjoint identity.
Extend in each variable by density/closed equality (continuous inner product
and actual completed CLMs). A single-variable density argument with the other
variable assumed finite does not yet prove the full statement.

Mathlib Analysis/InnerProductSpace/Adjoint.lean supplies
ContinuousLinearMap.adjoint_inner_right:127 and eq_adjoint_iff:163.
The latter says A=B.adjoint iff forall x y, inner(A x)y=inner x(B y).
Thus 4 directly gives C=D.adjoint; symmetry gives theorem 6, and adjoint
involution gives theorem 5. Alternatively ext_inner plus adjoint_inner_right
proves 5 directly. Track this orientation explicitly; avoid swapping C/D by
naming intuition. Actual CompleteSpace is provided by RealFockCompletion.

## Cross-mode scope

Optional SAME-BIRTH-stage signatures for i,j:Fin m:
 C_i*C_j+C_j*C_i=0; D_i*D_j+D_j*D_i=0;
 D_i*C_j+C_j*D_i=(if i=j then 1 else 0).
Need an actual fockModeShift_injective proof (Nat.le induction + Fin.succ
injectivity) to preserve the Kronecker equality test in later stages; this is
not in the frozen coordinate transport candidate. For DIFFERENT birth stages,
compare shifted indices at a common upper stage, not raw indices or i.val=j.val.
Prove shift composition/coherence before asserting independence of that stage.
These are useful later scope, not required for minimal same-mode closure.

This contract identifies genuine density consumers of native operators. It
claims no new kernel receipt and does not authorize redundant finite owners.
