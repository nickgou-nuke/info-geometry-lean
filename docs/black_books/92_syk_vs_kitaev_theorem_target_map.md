# SYK vs Kitaev Theorem Target Map

This map separates current owner theorems from external interpretation claims.

## Status Bands

- `REPO_THEOREM`: compiled theorem/definition in current repo owner surfaces.
- `FORMALIZABLE_NEXT_OWNER_TARGET`: well-scoped theorem surfaces to implement next.
- `EXTERNAL_INTERPRETATION`: physics/experiment framing not yet translated to owned Lean declarations.

## I. Kitaev / Majorana Finite-Lane Owners

- `REPO_THEOREM`
  [topologicalIndexZ2](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Quantum/KitaevChain.lean:199)
- `REPO_THEOREM`
  [topologicalIndexZ2_append_of_macroscopicVolume_ne_zero](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Quantum/KitaevChain.lean:206)
- `REPO_THEOREM`
  [boundaryLocalizedZeroModeWitness_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Quantum/BulkBoundary.lean:491)
- `REPO_THEOREM`
  [bulk_boundary_correspondence_concrete_of_simplifiedBoundaryModel](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Quantum/BulkBoundary.lean:914)
- `REPO_THEOREM`
  [zero_mode_is_information_sink_concrete_of_simplifiedBoundaryModel](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Quantum/BulkBoundary.lean:939)
- `REPO_THEOREM`
  [weylBoundarySpinorPair_of_simplifiedBoundaryModel](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/MajoranaKitaevSpinorBridge.lean:199)
- `REPO_THEOREM`
  [exists_nontrivial_regularization_pair_of_simplifiedBoundaryModel](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/MajoranaKitaevSpinorBridge.lean:230)

## II. Modular / Cocycle Chain Owners (Bridge Substrate)

- `REPO_THEOREM`
  [relativeModularOperator_state_chain](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RNDeterminantConnesChainBridge.lean:46)
- `REPO_THEOREM`
  [connesCocycle_state_chain](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RNDeterminantConnesChainBridge.lean:120)
- `REPO_THEOREM`
  [connesCocycle_state_chain_three](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RNDeterminantConnesChainBridge.lean:133)
- `REPO_THEOREM`
  [typeIII_connes_chain_package](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RNDeterminantConnesChainBridge.lean:167)

## III. Next Owner Targets for a True SYK-Style Lane

- `FORMALIZABLE_NEXT_OWNER_TARGET`:
  finite two-copy coupled-system structure with explicit left/right Hamiltonians
  and a typed cross-coupling operator.
- `FORMALIZABLE_NEXT_OWNER_TARGET`:
  TFD-like preparation interface and admissibility axioms suitable for finite
  simulation lanes.
- `FORMALIZABLE_NEXT_OWNER_TARGET`:
  sign-sensitive coupling witness (`mu` lane) with theorem-level channel-open
  vs channel-closed diagnostics.
- `FORMALIZABLE_NEXT_OWNER_TARGET`:
  teleportation-window-style observable package stated without geometric
  overclaim.

## IV. Explicitly External Interpretation Claims (Not Owner-Compiled)

- `EXTERNAL_INTERPRETATION`: "ER=EPR semiclassical bridge realized for this
  system."
- `EXTERNAL_INTERPRETATION`: "negative null energy shock generated in dual AdS
  geometry."
- `EXTERNAL_INTERPRETATION`: "hardware experiment X proves literal spacetime
  wormhole."

These remain interpretation layer until translated into repo-owned definitions
and theorem surfaces.

