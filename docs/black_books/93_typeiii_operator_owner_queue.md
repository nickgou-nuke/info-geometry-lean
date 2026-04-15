# Type III Operator Owner Queue (Build-Ordered)

This chapter turns the current Type III/operator frontier into a strict queue
with build-gated targets.

## Status Bands

- `REPO_THEOREM`: owner theorem already present.
- `INTERFACE_READY`: compiled scaffold exists; full theorem stack not yet done.
- `NEXT_OWNER_TARGET`: next owner theorem surface to construct.

## 1) First Lane (now compiled)

- `INTERFACE_READY`
  [PedersenTakesakiRNInterface.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/PedersenTakesakiRNInterface.lean)
  - `AffiliatedOperatorRNInterface`
  - `AffiliatedOperatorRNInterface.cocycle_chain`
  - `AffiliatedOperatorRNInterface.typeIII_affiliatedRN_interface_package`
  - `finiteAffiliatedDensity`
  - `finite_affiliatedRN_shadow_package`

Interpretation: this is a conservative operator-RN interface lane, not the full
Pedersen-Takesaki/Vaes affiliated-operator theorem stack.

## 2) Next Owner Targets

1. `NEXT_OWNER_TARGET`: full Pedersen-Takesaki/Vaes affiliated-operator RN owner
   theorems (existence/uniqueness/covariance) over the Type III lane.
2. `NEXT_OWNER_TARGET`: GNS owner construction lane (`state -> representation`,
   cyclic/separating package).
3. `NEXT_OWNER_TARGET`: spectral multiplication-model owner lane (cyclic-subspace
   to multiplication representation).
4. `NEXT_OWNER_TARGET`: internal continuous-core crossed-product owner
   realization, then determinant/relative-Hamiltonian bridge on that core.

## 3) Existing Anchors Used by This Queue

- `REPO_THEOREM`
  [TypeIIIContinuousCoreReal.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/TypeIIIContinuousCoreReal.lean)
- `REPO_THEOREM`
  [RNDeterminantConnesChainBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RNDeterminantConnesChainBridge.lean)
- `REPO_THEOREM`
  [RelativeModularOperator.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularOperator.lean)

## 4) Build Gate

```bash
lake env lean lean/InfoGeometry/Canonical/PedersenTakesakiRNInterface.lean
lake env lean lean/InfoGeometry/Canonical/All.lean
```

If these remain green, the first missing Type III operator lane is now
interface-compiled and attached to the canonical umbrella.
