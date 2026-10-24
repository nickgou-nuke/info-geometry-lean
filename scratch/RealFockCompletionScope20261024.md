# Existing real Fock completion: next implementation contract

Read-only source audit; contract only. No Lean implementation, builds, or live
owner edits. FiniteFockChordalNorm v2 is independently queued and untouched.
This updates the earlier stage-isometry outline using the now-live native owner.

## Exact existing signatures

Canonical/FilteredIsometricInnerProductColimit.lean:25-38:
  E : I -> Type u, [forall i, NormedAddCommGroup (E i)],
  [forall i, InnerProductSpace complex (E i)].
  structure IsometricDirectSystem where
    map : forall {i j}, i <= j -> E i ->ₗᵢ[complex] E j
    map_id : forall i, map (le_refl i) = LinearIsometry.id
    map_comp : (map hjk).comp (map hij) = map (le_trans hij hjk).
At52, realTransition : E i ->ₗ[real] E j restricts the complex map.
At65, RealDirectLimit := Module.DirectLimit E (fun _ _ h => realTransition E sys h).
At83, commonStageInner (i j) (x:E i) (y:E j) : complex is the inner product
at a chosen common upper stage; commonStageInner_eq_at:90 proves independence
of that choice from isometry and map composition.

Canonical/FilteredIsometricInnerProductDirectLimit.lean:
realDirectLimitInner:215 : Dinf ->ₗ[real] Dinf ->ₗ[real] complex,
built by two Module.DirectLimit.lift applications (stage functionals at117-215).
complexScalarDirectLimit:295 and instances at322-371 install complex scalar
multiplication on that REAL module quotient, with real/complex tower coherence.
directLimitInner:444 : Dinf ->ₛₗ[starRingEnd complex] Dinf ->ₗ[complex] complex.
Conjugate symmetry:470, positivity:490, definite self-pairing:501.

Canonical/FilteredIsometricHilbertCompletion.lean:
directLimitInnerProductCore:41 and instances:59-74 install the actual positive
metric; stageToDirectLimitLinearIsometry:129 preserves the original metric.
HilbertDirectLimit:162 := UniformSpace.Completion (RealDirectLimit E sys).
stageToHilbertDirectLimit:213 : E i ->ₗᵢ[complex] HilbertDirectLimit E sys.
Transition equality:236 and dense_iUnion_range_stageToHilbertDirectLimit:248.

Canonical/FilteredCompatibleOperatorColimit.lean:43:
  CompatibleOperatorFamily E sys has
    op : forall i, E i ->L[complex] E i
    intertwines : sys.map hij (op i x) = op j (sys.map hij x)
    bound : real
    norm_le : forall i x, norm(op i x) <= bound * norm x.
The bound is not implicitly nonnegative.
algebraicOperatorReal:120 uses the real direct-limit lift; algebraicOperator:148
adds complex linearity. algebraicOperator_norm_le:169 derives the descended
bound. algebraicOperatorCLM:192 uses mkContinuous; completedOperator:206 is
its native ContinuousLinearMap.completion. completedOperator_stage:223 gives
exact finite-stage readback. FilteredCompatibleOperatorNorm subsequently proves
completedOperator_norm_le with explicit 0 <= T.bound.

## Existing Fock carrier and comparison map

Clifford/ClNNFockDirectLimitRepresentation.lean:
FockStage:29 := Clifford.SpinorSpace (ClNNNeutralChevalleyBridge.Vector n).
fockStageMap:51 : FockStage m ->ₗ[real] FockStage n, via Nat.leRecOn of the
actual zero-head fockTailMap. Identity:57, successor:65, composition:113,
fockDirectedSystem:126.
FockInfinity:137 := _root_.DirectLimit FockStage (fun m n h => fockStageMap m n h).
fockToInfinity:141 is DirectLimit.Module.of on that EXISTING quotient.

Clifford/FiniteRealFockStageIsometry.lean (now native):
fockStageMap_inner:24 proves every all-index map preserves inner real;
fockStageLinearIsometry:35 bundles that exact map;
fockStageMap_norm:44, identity:49, composition:56.
FiniteRealFockMetric supplies the locally activated metric, not a complex space.

Mathlib/Algebra/Colimit/Module.lean:242:
  Module.DirectLimit.linearEquiv G f :
    Module.DirectLimit G f ≃ₗ[R] _root_.DirectLimit G f
under the directed-system assumptions.
linearEquiv_of:250 maps the module-colimit stage representative to the root
quotient representative; linearEquiv_symm_mk:254 gives the reverse readback.
The two carriers are NOT definitionally equal. This equivalence is reusable
and removes any justification for a new Fock quotient or guessed identification.
Also Mathlib/Algebra/Colimit/DirectLimit.lean:681 already provides the root
DirectLimit.Module.lift for compatible stage linear maps.

## Smallest immediate route: real specialization on existing FockInfinity

Recommended first completion task, leaving all complex owners untouched:
1. Define the real common-stage bilinear pairing using actual fockStageMap at
   max(m,n). Prove independence under further extension using
   fockStageMap_inner and fockStageMap_apply_trans. No isometry premise is added.
2. Descend the real bilinear form onto FockInfinity using the EXISTING root
   DirectLimit.Module.lift twice. Alternatively use Module.DirectLimit.lift
   and pull the form back along Module.DirectLimit.linearEquiv.symm; prove the
   representative comparison explicitly. Choose one route, not two quotients.
3. Prove symmetry, additivity, real homogeneity and nonnegative self-pairing
   on representatives. Prove definiteness from finite norm definiteness and
   direct-limit representation, not by assuming the norm is nondegenerate.
4. Install a named native InnerProductSpace.Core real FockInfinity and its
   induced norm/inner structures, preferably locally until consumers are aligned.
   Verify its stage readback EXACTLY equals the accepted finite metric.
5. Define the completion only as UniformSpace.Completion FockInfinity with
   that proved metric. Construct stage linear isometries by composing the
   native algebraic injections with the completion map. Prove transition
   compatibility and density of the union of stage ranges.

This is a metric/analytic extension of the existing algebraic carrier, not an
alternate Hilbert-space model. A focused reusable real bilinear descent helper
may take a directed system of linear isometries as genuine primitive input,
but the concrete Fock instantiation must discharge every property from the
accepted maps. Do not copy the entire complex system under a new Fock hierarchy.
No assumed completed carrier, isometry, compatibility, or boundedness fields.

## Subsequent operator obligations (not part of mere metric completion)

FiniteRealFockNormBounds.fockExtActionCLM/fockIntActionCLM have norm <=1.
For a mode born at a fixed stage, transport its index by Fin.succ under each
zero-head inclusion. Prove successor intertwining from fockTailMap_generator,
multiplicativity, and fockTailMap_contractLeft; then derive all-index transport.
A newly selected head coordinate zero at every stage is NOT that same mode.
Use the proved stage bounds to descend a real CLM on FockInfinity and its native
completion; prove exact stage readback and norm <=1. No arbitrary stage-varying
family may be assumed compatible. CAR/reflexivity/inner-adjoint laws then extend
by density from actual finite identities. These are later claims, not established
by the current six isometry declarations alone.

## Reusable scalar-generalization alternative and preservation requirements

A long-term RCLike k generalization must address ALL four layers above, not just
replace complex in IsometricDirectSystem. Two coherent designs:
- Keep the underlying real quotient: generalize commonStageInner to k-valued,
  retain realTransition, generalize the reconstructed complex action to a
  k-action and prove scalar-tower coherence. At k=real this must agree with
  the existing real action, avoiding duplicate nondefinitional instances.
- Use Module.DirectLimit directly over k and descend a sesquilinear pairing;
  then supply an explicit comparison to the existing complex-on-real quotient.
  A plain linear equivalence between module/root quotients does not by itself
  prove that comparison's complex scalar or norm compatibility.

For preservation, retain current complex theorem names/types, carrier maps,
scalar actions, stage readbacks, and instance behavior, or supply checked
isometric comparisons before migrating consumers. This is a coordinated owner
change and is NOT authorized by the present scratch-contract task.

## Concrete direct dependents inspected

Import search of the four complex owners finds FilteredGNSHilbertColimit,
FilteredGNSTailRepresentation, CuntzGNSFilteredHilbertBridge,
FilteredHilbertColimitInnerClosure, NoncommutativeStarDirectLimit,
FilteredCompatibleOperatorSelfAdjoint, FilteredCompatibleOperatorCompositionClosure,
FilteredCompatibleOperatorNorm, and the intermediate owners/All umbrellas.
FilteredGNSHilbertColimit constructs its system from complex state GNS spaces;
these must not be forced to adopt the new real Fock metric or carrier.
GrowingOnsiteTraceGNSFamily and its fresh-tail consumer depend transitively on
this complex operator/completion pipeline. Preserving their checked instances
and exact stage readbacks is a concrete compatibility requirement.

The bounded Fock/carrier/metric/colimit searches found no existing metric
completion of FockInfinity that fills this gap. This is a scoped source finding,
not a global nonexistence assertion. No compilation or axiom receipt is claimed.
