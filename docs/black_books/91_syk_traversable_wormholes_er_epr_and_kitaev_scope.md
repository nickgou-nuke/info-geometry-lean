# SYK Traversable Wormholes, ER=EPR, and Kitaev-Chain Scope Discipline

## Executive Correction

The repository must keep the following distinction strict:

1. `Kitaev chain` language in this repo means finite topological-Majorana and
   boundary zero-mode structure on the owned doubled-real/Krein corridor.
2. `Traversable wormhole teleportation` language in modern holography is a
   two-copy coupled many-body protocol (SYK/SYK-like), with a sign-sensitive
   left-right coupling in a TFD-like setup.

These are connected conceptually, but they are not the same object class.

## I. What the Repository Owns Today

Current compiled owner surfaces cover:

- finite Kitaev-chain topological index and phase fusion (`topologicalIndexZ2`,
  append law),
- boundary-localized zero-mode extraction under simplified boundary hypotheses,
- Majorana/Weyl boundary pairing and nontrivial generalized-inverse
  regularization packages,
- modular and Connes cocycle chain-rule owners on finite and Type-III lanes.

Representative owner anchors:

- [topologicalIndexZ2](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Quantum/KitaevChain.lean:199)
- [topologicalIndexZ2_append_of_macroscopicVolume_ne_zero](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Quantum/KitaevChain.lean:206)
- [boundaryLocalizedZeroModeWitness_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Quantum/BulkBoundary.lean:491)
- [bulk_boundary_correspondence_concrete_of_simplifiedBoundaryModel](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Quantum/BulkBoundary.lean:914)
- [weylBoundarySpinorPair_of_simplifiedBoundaryModel](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/MajoranaKitaevSpinorBridge.lean:199)
- [exists_nontrivial_regularization_pair_of_simplifiedBoundaryModel](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/MajoranaKitaevSpinorBridge.lean:230)
- [relativeModularOperator_state_chain](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RNDeterminantConnesChainBridge.lean:46)
- [connesCocycle_state_chain](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RNDeterminantConnesChainBridge.lean:120)
- [typeIII_connes_chain_package](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RNDeterminantConnesChainBridge.lean:167)

## II. What Is Not Yet an Owner Theorem Surface

The repo does not currently own a compiled two-copy SYK traversable-protocol
stack with:

- explicit left/right copy Hamiltonians,
- TFD-preparation lane,
- sign-sensitive left-right interaction witness (`mu < 0` style traversability
  window),
- teleportation-window diagnostics linked to that coupled dynamics.

Therefore statements of the form:

- "this theorem is a traversable wormhole realization,"
- "this lane reproduces ER-bridge traversability in hardware,"

are not owner-level claims in current repo state.

## III. Methodological Law for This Topic

For SYK/ER=EPR language, use three bands:

1. `REPO_THEOREM`: declarations compiled in owned Lean surfaces.
2. `FORMALIZABLE_NEXT_OWNER_TARGET`: precise local theorem surfaces we can
   formalize next.
3. `EXTERNAL_INTERPRETATION`: dual/holographic or experimental framing not yet
   translated into owned declarations.

No claim may cross from (3) to (1) without an explicit theorem-target map and
owner implementation.

## IV. Canonical Headline Sentence (Scope-Safe)

Kitaev chains here provide the topological-Majorana boundary toolkit, while a
traversable-wormhole teleportation protocol requires a distinct two-copy
coupled many-body SYK-like lane; modular/cocycle owners in this repo support
the chain-rule substrate but do not by themselves assert a literal spacetime
wormhole realization.

