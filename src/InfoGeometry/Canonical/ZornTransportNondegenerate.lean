/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornPolarFormTransport

/-! Symmetry, nondegeneracy, and adjoint uniqueness for the transported
split-polar form. Invertibility is explicit; no positivity is required. -/
noncomputable section
namespace InfoGeometry.Canonical.ZornTransportNondegenerate
open _root_.InfoGeometry.Canonical.ZornVectorMatrixExplicit
open ZornPolarizationMetricBridge ZornPolarOperatorAdjoint ZornPolarFormTransport

theorem transportedPolar_symm (T : Module.End ℝ ZornCoord) (X Y : ZornCoord) :
    transportedPolar T X Y = transportedPolar T Y X :=
  polarPair_symm (T X) (T Y)

theorem transportedPolar_nondegenerate (S T : Module.End ℝ ZornCoord)
    (hST : S*T=1) (hTS : T*S=1) : (transportedPolar T).Nondegenerate := by
  have hleft : (transportedPolar T).SeparatingLeft := by
    intro X hX
    have hz : T X = 0 := by
      apply polarForm_nondegenerate.1
      intro Y
      have hv := hX (S Y)
      change polarForm (T X) ((T*S) Y) = 0 at hv
      rw [hTS] at hv
      exact hv
    have hv := congrArg (fun U => S U) hz
    change (S*T) X = S 0 at hv
    rw [hST] at hv
    change X = S 0 at hv
    simpa only [map_zero] using hv
  exact ⟨hleft, fun X hX => hleft X (fun Y => by
    rw [transportedPolar_symm]; exact hX Y)⟩

theorem transportedPolar_adjoint_unique (S T f g k : Module.End ℝ ZornCoord)
    (hST : S*T=1) (hTS : T*S=1)
    (hg : LinearMap.IsAdjointPair (transportedPolar T) (transportedPolar T) f g)
    (hk : LinearMap.IsAdjointPair (transportedPolar T) (transportedPolar T) f k) : g=k := by
  apply LinearMap.ext
  intro Y
  apply sub_eq_zero.mp
  apply (transportedPolar_nondegenerate S T hST hTS).2
  intro X
  rw [map_sub, ← hg X Y, ← hk X Y, sub_self]

end InfoGeometry.Canonical.ZornTransportNondegenerate
