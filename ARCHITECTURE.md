# InfoGeometry Architecture

This file is the root routing map for agents. It is navigation, not proof
evidence. Lean source files are the authority.

Before adding categorical, representation-theoretic, Clifford, or matrix-level
content, read:

- `AGENTS.md`
- `docs/CATEGORICAL_INFRASTRUCTURE_MAP.md`
- `docs/REPOSITORY_PROOF_POLICY.md`
- `docs/ARCHITECTURE_AUDIT.md`

Core rule:

```text
Graph tools identify candidate wires.
Lean owner files decide truth.
Matrix-level code is an instance layer, not a replacement for categorical
or algebraic owner layers.
```

## Status Labels

Use these labels when documenting or extending a corridor:

- `proved`: kernel-checked theorem or definition in an owner file.
- `conditional`: theorem from explicit hypotheses or a proof-carrying packet.
- `socket`: structure/interface awaiting a concrete model.
- `debt`: missing theorem surface; must be explicit, not hidden behind `True`
  or a wrapper.
- `external`: searchable context only, never proof authority.

## Connection Tower

The current exceptional/tower architecture should be read as this owner-routed
chain:

```text
Cuntz/Cantor KMS boundary
  -> Cl(1,1) modular atom and Cl(1,1) tensor tower
  -> split Cl(4,4) recursive/triality proxy corridor
  -> Zorn/split-octonion local geometry
  -> Freudenthal charge space and quartic invariant
  -> abstract invariant action / TKK socket
  -> open exceptional realization targets: E7(7), E8(8)
```

Do not invert this chain by starting from an asserted `E8(8)` realization and
backfilling lower layers. The repo currently supports lower-layer kernels,
proxies, sockets, and invariant interfaces. Full split exceptional group
realizations remain explicit future targets unless a concrete owner file proves
them.

## Owner Surface Inventory

| Layer | Status | Owner files |
| --- | --- | --- |
| Cuntz/Cantor binary boundary | proved/conditional | `lean/InfoGeometry/Canonical/CantorCuntzBasis.lean`, `lean/InfoGeometry/Canonical/CantorCuntzCliffordBridge.lean`, `lean/InfoGeometry/Topology/CuntzCantorSpectralTriple.lean`, `lean/InfoGeometry/Canonical/HilbertCuntz.lean`, `lean/InfoGeometry/Analysis/L2CantorCommutation.lean` |
| KMS and boundary flow | proved/conditional | `lean/InfoGeometry/Canonical/KMSBoundaryTrajectory.lean`, `lean/InfoGeometry/Canonical/InfiniteKMSCondition.lean`, `lean/InfoGeometry/Canonical/KMSInteriorPoint.lean`, `lean/InfoGeometry/Analysis/BregmanAnalyticBound.lean`, `lean/InfoGeometry/Canonical/BregmanDeformation.lean` |
| Cl(1,1) modular atom | proved/conditional | `lean/InfoGeometry/Canonical/Cl11ModularAtom.lean`, `lean/InfoGeometry/Canonical/PrimeCl11ModularAtomCore.lean`, `lean/InfoGeometry/Clifford/Cl11Matrix.lean`, `lean/InfoGeometry/Clifford/Cl11Quaternion.lean` |
| Tensor tower / colimit | proved/conditional | `lean/InfoGeometry/Clifford/Cl11TensorTower.lean`, `lean/InfoGeometry/Clifford/Cl11TensorTowerIteration.lean`, `lean/InfoGeometry/Clifford/Cl11TensorTowerLimit.lean`, `lean/InfoGeometry/Canonical/Cl11TensorTowerBridge.lean`, `lean/InfoGeometry/Canonical/TensorTowerColimit.lean` |
| Split Cl(4,4) / triality proxy | proved proxy, not full classification | `lean/InfoGeometry/Canonical/SplitCl44TKKJordanLieBridge.lean`, `lean/InfoGeometry/Canonical/Spin44CharacterShadow.lean`, `lean/InfoGeometry/Clifford/Cl44SignatureResidue.lean`, `lean/InfoGeometry/Quantum/SplitTrialityKernel.lean`, `lean/InfoGeometry/Canonical/TrialitySpin8Permutations.lean` |
| Split octonion / Zorn geometry | proved local Zorn facts; no associative matrix API | `lean/InfoGeometry/Canonical/SplitOctonionClassificationCore.lean`, `lean/InfoGeometry/Canonical/SplitOctonionAssociator.lean`, `lean/InfoGeometry/Canonical/SplitOctonionRigidity.lean`, `lean/InfoGeometry/Canonical/ZornComposition.lean`, `lean/InfoGeometry/Projective/SplitOctonions.lean` |
| Fermionic/CAR bridge | proved/conditional | `lean/InfoGeometry/Quantum/FermionicOperators.lean`, `lean/InfoGeometry/Canonical/CantorCuntzCliffordBridge.lean`, `lean/InfoGeometry/Canonical/CantorTiltSwitchCliffordBridge.lean` |
| Freudenthal charge space | proved abstract invariant formulas; socket for concrete split Albert model | `lean/InfoGeometry/Exceptional/Freudenthal.lean`, `lean/InfoGeometry/Exceptional/FreudenthalAction.lean`, `lean/InfoGeometry/Application/OperatorFreudenthalBoundary.lean`, `lean/InfoGeometry/Canonical/GeometricCalculusFreudenthalBridge.lean` |
| E7/E8 exceptional realization | debt/socket | No owner file currently proves a concrete `E7(7)` or `E8(8)` Lie group/algebra realization from the lower tower. Treat any such prose as a target, not a theorem. |

## Hard Boundaries

These are project-level constraints, repeated here because they prevent most
agent mistakes:

- Zorn split octonions are nonassociative. Do not replace them with ordinary
  associative matrix multiplication.
- `SplitCl44TKKJordanLieBridge.lean` explicitly states that it does not prove
  full `Spin(4,4)` triality, split-octonion classification, `F4`, or `E8`.
- `Freudenthal.lean` defines abstract cubic Jordan and Freudenthal charge data.
  It does not construct `E7(7)`.
- `FreudenthalAction.lean` packages invariant actions preserving symplectic and
  quartic forms. It is not a concrete exceptional group construction.
- Categorical owner layers (`Algebra/Grothendieck.lean`,
  `Canonical/TensorTowerColimit.lean`, `Categorical/FibonacciBraiding.lean`)
  must be reused before writing matrix-level replacement code.
- External refs and generated artifacts are retrieval context only.

## Immediate Formalization Targets

The next buildable targets are not a prose `E8` claim. They are narrow owner
theorems:

1. Connect `modularDelta epsilon` with
   `NormedSpace.exp (epsilon • phaseAxis)` in
   `lean/InfoGeometry/Canonical/BregmanDeformation.lean`.
2. Lift the entrywise Bregman bound in
   `lean/InfoGeometry/Analysis/BregmanAnalyticBound.lean` to the chosen
   operator norm, or keep it explicitly entrywise.
3. Instantiate a concrete cubic Jordan datum for a split-Albert or STU model
   and feed it into `lean/InfoGeometry/Exceptional/Freudenthal.lean`.
4. Prove a concrete invariant action on the Freudenthal charge space through
   `lean/InfoGeometry/Exceptional/FreudenthalAction.lean`.
5. Only after 3 and 4, add a theorem surface stating exactly which split
   exceptional group or Lie algebra has been constructed.

## Agent Operating Rule

When a prompt says the tower is complete, translate that into a checklist:

1. Identify the owner file.
2. Check whether the claim is `proved`, `conditional`, `socket`, or `debt`.
3. Edit only owner source, not generated artifacts or external refs.
4. Run the narrow Lean gate for the owner file.
5. If touching import surfaces, run the smallest aggregate build that reaches
   the changed file.
6. Report remaining debt explicitly.
