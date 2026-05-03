# Krein Compatibility Vacuity Audit (2026-03-09)

> Status: `generated/historical report`
> Audited: 2026-05-02
> Note: Treat this as a snapshot. Regenerate before relying on it.
> See: [README.md](../README.md), [docs/README.md](../docs/README.md), [docs/CODEBASE_STATUS.md](../docs/CODEBASE_STATUS.md)

This audit flags declarations that are currently vacuous compatibility shims or explicit proof holes in the Krein compatibility path.

## 1) Explicit missing proofs

- `lean/InfoGeometry/Krein/Metric.lean:41`
  - `hessianIndefiniteFormCoord_eq_hessianDoubled` is still `sorry`.
  - This is a real proof hole in the bridge theorem.

## 2) Vacuous structure-level compatibility shims

- `lean/InfoGeometry/Krein/HilbertBridge.lean:17`
  - `HilbertDoubled` is an alias to `DoubledSpace`.
- `lean/InfoGeometry/Krein/HilbertBridge.lean:21`
  - `NeutralSpace` is an alias to `DoubledSpace`.
- `lean/InfoGeometry/Krein/HilbertBridge.lean:49-66`
  - `rotation45` is now non-vacuous, but its core obligations are explicit `sorry` placeholders
    (`left_inv`, `right_inv`, linearity, and norm preservation).
- `lean/InfoGeometry/Krein/HilbertBridge.lean:74-78`
  - `rotation45KreinEquiv.isometric` is still `sorry`.

## 3) Vacuous statement-level compatibility aliases

- `lean/InfoGeometry/Clifford/Cl11.lean`
  - Global API is mostly forwarded aliases into `InfoGeometry.Krein.*`.
  - Intended as shim, but these statements are definitional wrappers (no new proof content).

- `lean/InfoGeometry/Clifford/Lift.lean`
  - Entire layer is forwarded to `InfoGeometry.Krein.Representation`.
  - This restores API, but contributes little independent mathematical content.

- `lean/InfoGeometry/Geometry/KreinAsHessian.lean:22, 40, 44`
  - `kreinHessian := spectralEpsilon`, `kreinGrad_eq_hessian_apply := rfl`,
    and `kreinHessian_eq_spectralEpsilon := rfl` are direct compatibility identifications.
  - These are not wrong, but they are compatibility equalities rather than fresh proofs.

## 4) Where this currently surfaces as breakage

- `InfoGeometry.Krein.Clifford` currently fails to build in its Hilbert/neutral transport section.
  Current blockers are concentrated around:
  - unresolved heavy proofs/timeouts in `cl11RepLinHilbert`/`cl11RepLinHilbert_sq`,
  - transport/conjugation lemmas that depend on the still-unproven bridge obligations in `HilbertBridge`.

## 5) Next patch targets (ordered)

1. Reconstruct non-vacuous `rotation45` and `neutralLift` in `Krein/HilbertBridge.lean`.
2. Discharge `Metric.hessianIndefiniteFormCoord_eq_hessianDoubled` without `sorry`.
3. Reconcile `Krein/Clifford` transport lemmas against the restored bridge.
