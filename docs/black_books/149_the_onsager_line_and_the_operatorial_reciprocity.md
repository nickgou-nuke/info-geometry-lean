# Chapter 149: The Onsager-Casimir Operatorial Lift

**Verdict: Volume-First Defect Dynamics Is Now Welded to the Onsager Trunk.**

This chapter records the canonical operatorial lift on the maintained Onsager line:

- trunk reciprocity owner: `lean/InfoGeometry/Canonical/OnsagerReciprocity.lean`,
- `J`-Casimir parity owner: `lean/InfoGeometry/Canonical/OnsagerCasimirJ.lean`,
- Sinkhorn-to-Onsager operator lift: `lean/InfoGeometry/Canonical/OnsagerSinkhornOperatorLift.lean`.

## I. No Spacetime Coordinates: Variations Live on State/Operator Manifolds

All derivatives in this lane are variational:

- first variation: perturbation of state/operator data,
- second variation: Hessian bilinear form on perturbation channels,
- flow parameter: Sinkhorn iteration/descent index, not physical spacetime time.

So the relevant objects are channel perturbations and operator readouts, not coordinate gradients in $(x,t)$.

## II. Onsager Line in the Trunk

The reciprocal operator response is already owned by:

- `responseCoefficient` and `responseCoefficient_swap` in `OnsagerReciprocity`,
- `J`-conjugation parity and Casimir sign-flip in `OnsagerCasimirJ`.

This gives the symmetric (dissipative) vs skew (phase/curvature) split directly in operator language.

## III. New Lift: Sinkhorn Relative-Volume Defect -> Operatorial Onsager Response

The new lift module introduces:

1. `onsagerResponseAbs`: absolute Onsager response readout from `responseCoefficient`.
2. `onsagerResponseAbs_swap`: reciprocity invariance under channel swap.
3. `SinkhornOnsagerResponseBridge`: one-step bridge assumptions from `trajectoryRNBarrier*` to operator response.
4. `onsagerResponseAbs_next_le_now`: monotone one-step response bound forced by RN-barrier monotonicity.
5. `onsagerResponseAbs_next_le_now_swap`: the same bound on the swapped Onsager pair.

This is the precise closure statement: the volume-first defect corridor controls operatorial Onsager response without introducing extra physics surface.

## IV. Architectural Position

This lift does **not** claim a global Fredholm/zeta determinant theory.
It enforces a rigorous local program already owned in-repo:

- count/projective/relative-potential spine provides the defect source,
- Sinkhorn RN barrier provides the monotone scalar control,
- Onsager line provides reciprocal operator readout,
- bridge theorems transport monotonicity from RN barrier to operator response.

The result is a strict canonical step: no metaphor layer, no coordinate drift, no new ontology.
