# Completed creation/contraction: existing-action extension contract

Read-only source grounding; NEW contract only. No implementation, builds or live
owner edits. Use existing root FockInfinity and RealFockCompletion throughout.
Native completion has parent-reported sandbox acceptance and queued native QA.

## Existing owners to consume

Clifford/ClNNFockDirectLimitRepresentation.lean:
- towerSpinorRep_stageMap (236): for m<=n, a:SplitClNNAlg m, psi:FockStage m,
  fockStageMap m n h (towerSpinorRep m a psi) =
  towerSpinorRep n (splitCliffordMap m n h a) (fockStageMap m n h psi).
- splitCliffordFockAction (254) is ALREADY DirectLimit.map₂ on the actual
  SplitCliffordInfinity and FockInfinity. Do not construct a second action.
- splitCliffordFockAction_of (267) and generator_of (290) give exact finite
  readback. grade_equivariant (515) demonstrates moving arbitrary algebra and
  Fock representatives to max(n,m), with Algebra.of_f and Module.of_f.

Clifford/ClNNFockDirectLimitRepresentationLinearityWave16.lean:
- splitCliffordFockAction_add_right (20) proves additivity for every aInf.
- splitCliffordFockAction_smul_right (91) proves real homogeneity for every aInf.
Thus right-linearity is NOT a missing theorem. Import and use it when bundling
that exact existing function as a LinearMap; do not reprove via another lift.
Bounded searches for an existing norm/CLM bundle of this action did not locate
one in the inspected owners/dependents; no repo-wide nonexistence assertion.

Clifford/ClNNNeutralChevalleyBridge.lean:
- towerSpinorRep (246) is the existing algebra hom into real Module.End.
- towerSpinorRep_generator (255) evaluates iota x as spinorAction of
  (neutralToSplit n).symm x.
- vectorTail (563), dualTailMap (570): dualTailMap n phi = phi.comp(vectorTail n).
- fockTailMap_generator (640), contractLeft (650), spinorAction (697) prove
  actual creation/contraction naturality under zero-head inclusion.
- neutralToSplit_tail (714) aligns the neutral and split vector transitions.
- towerSpinorRep_tail (865) is already consumed by all-index stageMap.
Clifford/FockTailExteriorBasis.lean:22 already proves vectorHeadZero_basisFun:
  vectorHeadZero n (basisFun i) = basisFun i.succ.
Do not duplicate that basis identity.

Clifford/FiniteRealFockNormBounds.lean:
- fock_extAction_norm_le (49), fock_intAction_norm_le (60): pointwise <=norm
  for EVERY vector at a finite stage and EVERY coordinate mode.
- fockExtActionCLM (71), fockIntActionCLM (78), apply readbacks (84/88),
  operator norm bounds <=1 (94/100).
Clifford/RealFockHilbertCompletion.lean:
- named local metric/scalar-continuity instances must be enabled exactly.
- fockToInfinity_norm, fockStageToCompletion_apply/norm/transition,
  fockInfinity_denseRange_completion, dense_iUnion_range_fockStageToCompletion.

## Smallest next concrete lemma and prerequisite

The smallest coordinate prerequisite not found in this bounded search is:
  dualTailMap n (LinearMap.proj i : Module.Dual real (Vector n)) =
    (LinearMap.proj i.succ : Module.Dual real (Vector (n+1))).
Proof: LinearMap.ext, intro x, rfl from dualTailMap/vectorTail. Explicit ext
avoids recursively invoking ExteriorAlgebra's alternating extensionality.

The substantive next theorem is ALL-LATER-STAGE GENERATOR READBACK, not another
colimit-action definition. For a fixed birth stage m and i:Fin m, use:
  eC := (Pi.basisFun real (Fin m) i, 0) : Neutral m
  eD := (0, LinearMap.proj i) : Neutral m
  aC := CliffordAlgebra.iota (TowerForm m) (neutralToSplit m eC)
  aD := CliffordAlgebra.iota (TowerForm m) (neutralToSplit m eD).
These are expressions in existing carriers, not a new Clifford/coordinate model.

A small index helper shift(m,n,h,i):Fin n may be recursively defined by the
same Nat.leRecOn pattern as fockStageMap: identity at m, Fin.succ each step.
It must satisfy shift(m,n+1,h.trans(le_succ n),i)=(shift(m,n,h,i)).succ.
Equivalently its coordinate value is i.val+(n-m); do NOT use fixed index zero
or castLE, which retains the wrong coordinate under zero-head insertion.

Required separate exact statements, for every h:m<=n and psi:FockStage n:
  towerSpinorRep n (splitCliffordMap m n h aC) psi =
    fockExtActionCLM n (shift m n h i) psi;
  towerSpinorRep n (splitCliffordMap m n h aD) psi =
    fockIntActionCLM n (shift m n h i) psi.
Proof route: first identify transported algebra GENERATORS by induction on h,
using splitCliffordMap_succ, splitCliffordStep_eq_splitStageCliffordMap,
its native generator action, neutralToSplit_tail, existing vectorHeadZero_basisFun
and the dualTailMap projection lemma. Then use towerSpinorRep_generator and
neutralToSplit.symm_apply_apply, reducing spinorAction at (basis,0)/(0,proj).
This is stronger than intertwining on the image of FockStage m and is necessary:
an arbitrary later-stage psi need not lie in that earlier image.
The finite norm bounds immediately give <=norm psi on ALL later-stage inputs.

## Extend the existing action, in small downstream steps

1. A general mixed-stage action readback follows from existing of/readback plus
   Algebra.of_f and Module.of_f, moving to max(m,n). It can be a reusable lemma
   for arbitrary a:SplitClNNAlg m, psi:FockStage n; it is not a new action.
2. For the actual fixed colimit elements Algebra.of m aC/aD, represent arbitrary
   psiInf at stage n, move to max(m,n), apply all-later-stage readback and the
   finite bound, then fockToInfinity_norm and fockStageMap_norm. Conclude
     norm(splitCliffordFockAction (Algebra.of m aC/aD) psiInf) <= norm psiInf.
   No assumed compatible-family or uniform-bound field is permitted.
3. Bundle splitCliffordFockAction aInf using the ALREADY PROVED add_right and
   smul_right. For these fixed coordinate elements use LinearMap.mkContinuous 1
   with the derived bound. Its application must definitionally be the existing
   splitCliffordFockAction; no alternate direct-limit lift/map₂.
4. Apply ContinuousLinearMap.completion to that actual CLM, obtaining an operator
   RealFockCompletion ->L[real] RealFockCompletion. Mathlib
   Topology/Algebra/LinearMapCompletion.lean:45 and completion_apply_coe:60 give
   the exact readback on algebraic vectors. Compose with completed stage readback
   for every later stage and the shifted mode.
5. Extend the pointwise <=norm estimate to the completion using density and the
   closed inequality set (continuity of the completed CLM and norm), then use
   ContinuousLinearMap.opNorm_le_bound with zero_le_one. Do not assume the bound.

## Scope boundary

This contract targets actual completed fixed-mode creation/contraction with
norm<=1 and exact native-action/stage readbacks. The finite bound applies to a
fixed birth mode shifted through the tower, not an unrelated family of fresh
head modes. There is no uniform norm<=1 claim for arbitrary Clifford elements.
Completed CAR and adjoint laws can subsequently extend from finite common-stage
identities by density; they are not supplied by compatibility or norm bounds
alone and are not part of the smallest prerequisite implementation.
