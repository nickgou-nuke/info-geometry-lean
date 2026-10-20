/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.Cl11TensorInductiveLimit
import InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalTrace
import InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalComparison

/-!
# Wave 4: global trace comparison for the Cl(1,1) colimit lanes

The algebraic tensor-inductive-limit owner permits a supplied global linear
functional extending the normalized finite traces.  The TopCat owner has a
canonical continuous trace descent.  This theorem proves that, after the
existing algebraic-to-topological map, those two readouts agree on the whole
algebraic carrier, not merely on individual stage representatives.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalTrace

open InfoGeometry.Canonical.Cl11TensorInductiveLimit
open InfoGeometry.Canonical.CliffordCARAlgebraicTopologicalComparison
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11TensorTower
open FilteredColimit.Native.Topological

/-- A global functional extending the finite normalized traces agrees with the
canonical normalized-trace map on the topological colimit after the native
algebraic-to-topological comparison. -/
theorem normalizedTraceTopologicalColimitMap_algebraicToTopological_eq_limitFunctional
    (Ω : cl11TensorInductiveLimit.LimitFunctional)
    (hΩ : cl11TensorInductiveLimit.ExtendsFamily
      InfoGeometry.Canonical.Cl11MarkovJonesCompatibleFunctionalFamily.cl11CompatibleFunctionalFamily Ω)
    (x : cl11TensorInductiveLimit.AInf) :
    normalizedTraceTopologicalColimitMap
        (algebraicToTopological x) = Ω x := by
  let Ω' : InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit →ₗ[ℝ] ℝ := Ω
  have hΩ' : ∀ n (A : InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage n),
      Ω' (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n A) = InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace n A := by
    intro n A
    exact cl11_limit_functional_recovers_normalized_trace Ω hΩ n A
  change normalizedTraceTopologicalColimitMap (algebraicToTopological x) = Ω' x
  induction x using DirectLimit.induction with
  | _ n A =>
      change normalizedTraceTopologicalColimitMap
          (algebraicToTopological
            (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n A)) =
        Ω' (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n A)
      rw [algebraicToTopological_ofStage,
        normalizedTraceTopologicalColimitMap_inclusion,
        hΩ' n A]

end InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalTrace
