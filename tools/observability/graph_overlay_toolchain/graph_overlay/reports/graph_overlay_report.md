# Lean Graph Overlay / Dedup Report

## Scope

Root: `/mnt/data/lean`

## Static scan summary

- `files`: **5**
- `decls`: **99**
- `imports`: **10**
- `edges`: **337**
- `duplicate_alpha_classes`: **5**
- `duplicate_wl_classes`: **1**
- `sccs`: **1**
- `sorry_decl_count`: **0**
- `axiom_like_decl_count`: **0**

## Files

- `InfoGeometry/Arithmetic/SplitMajoranaPrimeGas.lean` — 12 declarations
- `InfoGeometry/Arithmetic/SupergradedLiouvilleanWittenIndex.lean` — 16 declarations
- `InfoGeometry/Canonical/CantorCliffordFockGate.lean` — 15 declarations
- `InfoGeometry/Canonical/KANIwasawaObstructionBridge.lean` — 29 declarations
- `InfoGeometry/Canonical/SL2R_KAN_Model.lean` — 27 declarations

## Alpha-normalized duplicate declaration silhouettes

### `62b789d19a6bf019` (3 declarations)
- `InfoGeometry.Canonical.CantorCliffordFockGate.CantorCliffordFockBridgeData.car_relations_hold` (theorem) in `InfoGeometry/Canonical/CantorCliffordFockGate.lean:171-177`
- `InfoGeometry.Canonical.CantorCliffordFockGate.CantorCliffordFockBridgeData.fock_left_inverse` (theorem) in `InfoGeometry/Canonical/CantorCliffordFockGate.lean:178-184`
- `InfoGeometry.Canonical.CantorCliffordFockGate.CantorCliffordFockBridgeData.cuntz_isometry_relations` (theorem) in `InfoGeometry/Canonical/CantorCliffordFockGate.lean:185-191`

### `b5bee5659dd21689` (3 declarations)
- `InfoGeometry.Arithmetic.SupergradedLiouvilleanWittenIndex.finiteBosonicPrimonPartition` (def) in `InfoGeometry/Arithmetic/SupergradedLiouvilleanWittenIndex.lean:79-82`
- `InfoGeometry.Arithmetic.SupergradedLiouvilleanWittenIndex.finiteMobiusFermionicSignedTrace` (def) in `InfoGeometry/Arithmetic/SupergradedLiouvilleanWittenIndex.lean:83-86`
- `InfoGeometry.Arithmetic.SupergradedLiouvilleanWittenIndex.finiteSupergradedLiouvilleanWittenIndex` (def) in `InfoGeometry/Arithmetic/SupergradedLiouvilleanWittenIndex.lean:87-90`

### `d3df0c3f244d32c1` (2 declarations)
- `InfoGeometry.Canonical.SL2R_KAN_Model.KSectorDetOne_true` (theorem) in `InfoGeometry/Canonical/SL2R_KAN_Model.lean:169-172`
- `InfoGeometry.Canonical.SL2R_KAN_Model.ASectorDetOne_true` (theorem) in `InfoGeometry/Canonical/SL2R_KAN_Model.lean:173-176`

### `ef88c8bd0163ef7e` (2 declarations)
- `InfoGeometry.Canonical.SL2R_KAN_Model.KSectorDetOne` (def) in `InfoGeometry/Canonical/SL2R_KAN_Model.lean:157-160`
- `InfoGeometry.Canonical.SL2R_KAN_Model.ASectorDetOne` (def) in `InfoGeometry/Canonical/SL2R_KAN_Model.lean:161-164`

### `f0ee89a50b9d263b` (2 declarations)
- `InfoGeometry.Arithmetic.SplitMajoranaPrimeGas.SplitPrimeCAR.N` (def) in `InfoGeometry/Arithmetic/SplitMajoranaPrimeGas.lean:69-72`
- `InfoGeometry.Arithmetic.SplitMajoranaPrimeGas.SplitPrimeCAR.Pi` (def) in `InfoGeometry/Arithmetic/SplitMajoranaPrimeGas.lean:73-76`

## WL duplicate graph neighborhoods

### `265db99c8f4f8379` (2 declarations)
- `InfoGeometry.Canonical.CantorCliffordFockGate.CantorCliffordFockBridgeData.fock_left_inverse` (theorem) in `InfoGeometry/Canonical/CantorCliffordFockGate.lean:178-184`
- `InfoGeometry.Canonical.CantorCliffordFockGate.CantorCliffordFockBridgeData.cuntz_isometry_relations` (theorem) in `InfoGeometry/Canonical/CantorCliffordFockGate.lean:185-191`

## Strongly connected components in lexical declaration graph

- InfoGeometry.Canonical.CantorCliffordFockGate.CantorCliffordFockBridgeData.self_duality_law, InfoGeometry.Canonical.CantorCliffordFockGate.InductiveLimitSelfDualityGate, InfoGeometry.Canonical.CantorCliffordFockGate.CantorCliffordFockBridgeData, InfoGeometry.Canonical.CantorCliffordFockGate.CantorCliffordFockBridgeData.car_relations_hold, InfoGeometry.Canonical.CantorCliffordFockGate.CantorCliffordRepresentationGate

## Interpretation

This report is a static observability overlay. It is not a Lean proof check and not a kernel-accurate expression hash. The next precision step is a Lean-native exporter over elaborated `Expr`, using de-Bruijn indices and universe normalization, feeding this same JSON schema.