/-
InfoGeometry/OperatorAlgebra/TKKFluxBalance.lean

Decomposition of TKK Ricci flux into curvature transport plus hidden/material/
topological defect ledgers.

This file does not prove the Einstein field equations. It records the exact
accounting identity needed by a later Einstein-readout theorem.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.TKKConformalClosure

noncomputable section

namespace InfoGeometry.OperatorAlgebra.TKKConformalClosure

/-! ## Defect decomposition ledger -/

/--
A decomposition of the TKK closure defect into named physical/operatorial
ledger components.

The intended interpretation is:

* `hiddenFlux`      : Stinespring/Tomita leakage into the commutant;
* `materialFlux`    : susceptibility/Hessian/Jones-Fresnel material response;
* `topologicalFlux` : snap/anomaly/chiral residue contribution.

All three live in the same `Geometry` readout type as the Ricci flux.
-/
structure TKKDefectDecomposition
    {L State Geometry : Type*}
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry]
    (R : TKKRicciFluxDatum L State Geometry) where
  /-- Hidden/environment/commutant ledger contribution. -/
  hiddenFlux : L → State → Geometry
  /-- Material/susceptibility/interface response contribution. -/
  materialFlux : L → State → Geometry
  /-- Topological snap/chiral residue contribution. -/
  topologicalFlux : L → State → Geometry
  /-- The closure defect decomposes into the three ledger components. -/
  closureDefect_eq :
    ∀ X : L, ∀ s : State,
      R.closureDefect.defect X s =
        hiddenFlux X s + materialFlux X s + topologicalFlux X s

namespace TKKDefectDecomposition

variable
    {L State Geometry : Type*}
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry]

variable
    {R : TKKRicciFluxDatum L State Geometry}
    (D : TKKDefectDecomposition R)

/--
Ricci flux expands as curvature variation plus the three decomposed defect
ledgers.
-/
theorem ricciFlux_eq_curvature_plus_decomposed_defects
    (X : L)
    (s : State) :
    R.ricciFlux X s =
      R.derivativeAlong.deriv R.curvatureReadout.curvature X s +
        (D.hiddenFlux X s + D.materialFlux X s + D.topologicalFlux X s) := by
  rw [R.ricciFlux_def X s]
  rw [D.closureDefect_eq X s]

/--
If the hidden, material, and topological fluxes all vanish, Ricci flux is pure
curvature transport.
-/
theorem ricciFlux_eq_curvature_of_all_defects_zero
    (X : L)
    (s : State)
    (hHidden : D.hiddenFlux X s = 0)
    (hMaterial : D.materialFlux X s = 0)
    (hTopological : D.topologicalFlux X s = 0) :
    R.ricciFlux X s =
      R.derivativeAlong.deriv R.curvatureReadout.curvature X s := by
  rw [D.ricciFlux_eq_curvature_plus_decomposed_defects X s]
  rw [hHidden, hMaterial, hTopological]
  simp

/--
If curvature variation is stationary, Ricci flux is exactly the decomposed
defect ledger.
-/
theorem ricciFlux_eq_decomposed_defects_of_curvature_stationary
    (X : L)
    (s : State)
    (hCurv :
      R.derivativeAlong.deriv R.curvatureReadout.curvature X s = 0) :
    R.ricciFlux X s =
      D.hiddenFlux X s + D.materialFlux X s + D.topologicalFlux X s := by
  rw [D.ricciFlux_eq_curvature_plus_decomposed_defects X s]
  rw [hCurv]
  simp

/--
If curvature variation and all decomposed defects vanish, Ricci flux vanishes.
-/
theorem ricciFlux_eq_zero_of_stationary_and_all_defects_zero
    (X : L)
    (s : State)
    (hCurv :
      R.derivativeAlong.deriv R.curvatureReadout.curvature X s = 0)
    (hHidden : D.hiddenFlux X s = 0)
    (hMaterial : D.materialFlux X s = 0)
    (hTopological : D.topologicalFlux X s = 0) :
    R.ricciFlux X s = 0 := by
  rw [D.ricciFlux_eq_curvature_plus_decomposed_defects X s]
  rw [hCurv, hHidden, hMaterial, hTopological]
  simp

end TKKDefectDecomposition

end InfoGeometry.OperatorAlgebra.TKKConformalClosure

