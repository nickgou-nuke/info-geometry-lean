# Actual represented tilt motion: continuation contract after probe failure

Read-only owner research plus this NEW contract only. No Lean implementation,
compiler/test invocation, owner edit, transparency attribute, or budget change.
Parent is preparing the native readback API; do not duplicate that work.

## Unchanged final consumer

Namespace InfoGeometry.Canonical.FiniteSeedRepresentedRealTime. For ALL real
h and beta, with only hh : h ≠ 0, retain precisely this target:

```lean
theorem tiltSeed_exists_realTime_move (h β : ℝ) (hh : h ≠ 0) :
    let J := seedStageHom (k := 1) (h • tilt2)
      (tiltHamiltonian_isHermitian h) β
    ∃ t : ℝ, seedRealTimeAut (k := 1) (h • tilt2)
      (tiltHamiltonian_isHermitian h) β t (J switch2) ≠ J switch2
```

This is the actual finiteSeedCompatibleStageStates H hH beta, its completed
GNS represented C-star closure, and the actual native seedRealTimeAut. No chosen
abstract substitute state, no raw matrix action replacing the represented flow,
no beta≠0 condition. Time is existential, not every nonzero time. Invariance of
the state does not mean pointwise invariance of every represented observable.

## Exact current native dependencies

FiniteSeedRepresentedRealTime.lean:198 representedMatrixStageMap is the composite
of algebraicColimitToRepresentedClosure, algebraicStarDirectLimitOf and the
matrix stage map. :253 seedStageHom specializes it to the actual Gibbs family.
:268 seedRealTimeAut specializes matrixRealTimeAut on that same family/map.
:167 matrixRealTimeAut is Unitary.conjStarAlgAut of matrixUnitary; :124 the
self-adjoint generator is f H. The sign is positive exp(i*t*f H) conjugation.
Native local CStar/order/star-order instance families are at :229–235.

FilteredGNSMatrixFaithfulness.globalStageRepresentation_injective (:39)
already proves stage injectivity from simplicity and a normalized nonzero vacuum,
without faithful-state assumptions. The private matrixStageSimple instance is
registered and usable; do not duplicate it. The same owner supplies
matrix_algebraicColimitGNSRepresentation_injective and matrix_rangeAlgHom_injective.
FilteredGNSRepresentedCStarClosure.algebraicColimitToRepresentedClosure_coe (:75)
reads the subtype back to the actual bounded operator. The stage evaluation law
is FilteredGNSAlgebraicColimitRepresentation.algebraicColimitGNSRepresentation_of.

## Diagnostics and current handoff boundary

V9 /tmp/qa-a-motion-v9-bjildmql/compile.log: concrete seed specialization timed
out at whnf/isDefEq after abstract-state helpers. V10
/tmp/qa-a-motion-v10-pr6kq2gv/compile.log: local reducible changes were rejected,
then concrete injectivity timed out. Those are failures, not acceptance receipts.

Latest /tmp/qa-a-seed-injectivity-probe-bbn63g8g/compile.log fails FIRST
seedStageHom_coe_apply_probe at the simp/isDefEq step (1M limit). Thus the
second injectivity probe is NOT yet verified. This does not identify a proved
instance diamond or a mathematical counterexample.

Parent now owns a full owner candidate with:
1. generic representedMatrixStageMap_coe BEFORE seed specialization;
2. explicit seedStageHom result type under the native instance telescope;
3. native seedStageHom_coe_apply consuming the generic law.
No new budgets or transparency policy. Freeze motion authoring until that exact
owner candidate has AA and serial QA plus usable application readback.

## Smallest subsequent steps, contingent on that repair

A. Derive actual seedStageHom injectivity using congrArg Subtype.val on equality,
rewrite the accepted seedStageHom_coe_apply twice, apply existing
 globalStageRepresentation_injective and CStarMatrix.ofMatrixStarAlgEquiv.injective.
Do not unfold the Gibbs state or reconstruct its Hilbert/operator instances.
If this fails, isolate its first diagnostic; no full motion wrapper iteration.

B. Reuse the finite witness from scratch/TiltSeedRealTimeNontrivial20261024v10.lean:
`tilt_switch_commutator_ne_zero`: (h•tilt2)*switch2-switch2*(h•tilt2) ≠ 0.
Its actual proof evaluates entry01, obtaining 2*(h:Complex)≠0. Transfer this
single raw commutator through the actual J using injectivity and map_zero.
Keep the intermediate statement J(rawcommutator)≠0, avoiding premature
elaboration of products of concrete dependent closure elements.

C. Reuse the small generic motion chain in that same scratch file:
- ModularFlowExponentialGenerator.exists_complexExponentialConjugationPath_ne;
- OperatorAlgebra.expUnitary_conjugation_eq_complexPath;
- OperatorAlgebra.exists_complexPath_move_of_mapped_commutator;
- FilteredGNSMatrixRealTime.matrixRealTimeAut_eq_complexExponentialConjugationPath;
- FilteredGNSMatrixRealTime.matrixRealTimeAut_exists_move.
The last lemma accepts f(rawcommutator)≠0 and concludes existence of motion for
THE EXISTING matrixRealTimeAut. This is the exact consumer to specialize after A/B.
These are draft reuse sources whose earlier files failed later; do not describe
the entire v10 file or these extracted declarations as independently certified.
A bounded exact-name search of native owners found no promoted versions of these
motion helpers at inspection. Native mathematical foundation remains
Canonical.ModularFlowExponentialGenerator.hasDerivAt_complexExponentialConjugationPath_zero
(:52): derivative at zero is I•[G,x]. A constant orbit would have derivative zero.
No new exponential analysis is needed.

D. Align matrixRealTimeAut with native seedRealTimeAut by a small named application
law under the SAME owner instance telescope if direct specialization still costs
too much. Request a parent-reviewed native application API rather than unfolding
the whole state/closure or changing its transparency. The final statement above
must still name seedRealTimeAut and seedStageHom on the original Gibbs seed.

## Acceptance boundaries

First readback QA, then injectivity QA, then mapped finite witness and motion
specialization. Preserve all older candidates. No claims that probe success
alone proves full motion, and no inference of kernel pass from source review.

## Source SHA256 at this read

- `lean/InfoGeometry/Canonical/FiniteSeedRepresentedRealTime.lean`: `de19e22b0619c2d9a743dac42355971c4223c27bffeb41033b7ff1135862232e`

- `lean/InfoGeometry/Canonical/FilteredGNSMatrixFaithfulness.lean`: `3c4671269246b2e46b263d5f629eac0e900f823e778e9e807043b79d68f3c48b`

- `lean/InfoGeometry/Canonical/ModularFlowExponentialGenerator.lean`: `f603fd412894ae06ca05acec14df33bac756b4dac8f6c5f1b9dfb0aa94a2a145`

- `scratch/SeedStageInjectivityProbe20261024.lean`: `e9f5da9eb98f8db3c1ed09c95299ca8638d27564963a3727763d88be81dfec87`

- `scratch/TiltSeedRealTimeNontrivial20261024v10.lean`: `ee62f07e73fa8373657147f6569a793e2b0b563b3ab682e692a61e5baedae8c6`
