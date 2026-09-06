/- 
InfoGeometry/Topological/RealCuspLimitT.lean

Boundary cusp theorem for the real modular readout.

The theorem is intentionally small:
- the algebraic lane provides the `T`-identity property;
- the topological lane reduces the cusp limit to `tendsto_const_nhds`.
-/

import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Basic
import InfoGeometry.Algebraic.RealModularReadout

open scoped Topology

namespace InfoGeometry.Topological

open Filter
open InfoGeometry.Algebraic
open InfoGeometry.Geometry

/--
If the real modular readout is identically `1` on the `T` side-pairing,
then the cusp limit along the positive real vertical ray is `1`.
-/
theorem cusp_limit_T_eq_one
    {R : Type*} [Monoid R] [TopologicalSpace R]
    (D : RealModularReadoutData R) :
    Tendsto
      (fun Y : PosReal => D.readout D.T (verticalRay Y))
      atTop
      (𝓝 (1 : R)) := by
  have hconst : ∀ Y : PosReal, D.readout D.T (verticalRay Y) = (1 : R) := by
    intro Y
    exact D.T_identity (verticalRay Y)
  simpa [hconst] using
    (tendsto_const_nhds : Tendsto (fun _ : PosReal => (1 : R)) atTop (𝓝 (1 : R)))

/--
Pullback version of the boundary cusp theorem.

This packages the algebraic lift from `SL(2, ℝ)` to `SL(2, ℤ)` and then
pushes the cusp limit through the real vertical ray.
-/
theorem pullback_cusp_limit_T_eq_one
    {R : Type*} [Monoid R] [TopologicalSpace R]
    (J : SL2R → RealUpperHalfPlane → R)
    (T : SL2Z)
    (hT : ∀ τ : RealUpperHalfPlane, J (sl2zToSL2R T) τ = 1) :
    Tendsto
      (fun Y : PosReal => pullbackReadout J T (verticalRay Y))
      atTop
      (𝓝 (1 : R)) := by
  have hconst : ∀ Y : PosReal, pullbackReadout J T (verticalRay Y) = (1 : R) := by
    intro Y
    simpa [pullbackReadout] using hT (verticalRay Y)
  change Tendsto (fun Y : PosReal => J (sl2zToSL2R T) (verticalRay Y))
    atTop (𝓝 (1 : R))
  have hfun : (fun Y : PosReal => J (sl2zToSL2R T) (verticalRay Y)) =
      fun _ : PosReal => (1 : R) := by
    funext Y
    exact hconst Y
  rw [hfun]
  exact tendsto_const_nhds

end InfoGeometry.Topological
