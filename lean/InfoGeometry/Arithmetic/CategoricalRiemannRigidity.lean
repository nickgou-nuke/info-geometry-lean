import InfoGeometry.Canonical.CategoricalRiemannRigidity

/-!
Compatibility shim for `CategoricalRiemannRigidity`.

All live symbols are re-exported from the canonical owner lane.  The stale
`is_colimit_kernel_object` / `riemann_hypothesis_colimit_rigidity` interface
is intentionally omitted because it does not construct a ModuleCat colimit or
prove `RH ↔ colimit_rigidity`.
-/

open InfoGeometry.Canonical.CategoricalRiemannRigidity
