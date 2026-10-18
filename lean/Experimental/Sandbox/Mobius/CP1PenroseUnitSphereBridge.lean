/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Experimental.Sandbox.Mobius.CP1RiemannSphereEquiv
import InfoGeometry.Physics.PenroseQuantizedTwistorSplitOctonion

/-!
# Projective CP¹ classes and the Penrose unit-sphere chart

The projective coordinate relation descends through `toRiemannSphere`, and
the Penrose stereographic chart sends each finite value to a unit-sphere
point. This file combines those finite results into a sphere-valued map on
the quotient of homogeneous coordinates. Infinity is sent to the omitted
south pole of the chosen chart. No topological equivalence is asserted.
-/

set_option autoImplicit false

namespace Experimental.Sandbox.Mobius

open InfoGeometry.Physics.PenroseTwistor

/-- The subtype of `SpherePoint` satisfying the Euclidean unit-sphere equation. -/
abbrev UnitSphereCarrier :=
  { p : SpherePoint // p.X ^ 2 + p.Y ^ 2 + p.Z ^ 2 = 1 }

/-- Extend the Penrose finite stereographic chart to the Riemann sphere by
sending infinity to the chart's omitted south pole. -/
noncomputable def riemannSphereToUnitSphere
    (z : InfoGeometry.RiemannSphere) : UnitSphereCarrier :=
  match z with
  | none =>
      ⟨⟨0, 0, -1⟩, by norm_num⟩
  | some ζ =>
      ⟨stereographicSphere ζ, by
        simpa using stereographic_unit_sphere ζ⟩

/-- No finite stereographic coordinate maps to the south pole; this is why
the `none` branch supplies the missing point of the chart. -/
theorem stereographicSphere_ne_southPole (ζ : ℂ) :
    stereographicSphere ζ ≠ ⟨0, 0, -1⟩ := by
  intro h
  have hZ := congrArg SpherePoint.Z h
  have hratio :
      (1 - (ζ.re ^ 2 + ζ.im ^ 2)) /
          (1 + (ζ.re ^ 2 + ζ.im ^ 2)) = -1 := by
    simpa [stereographicSphere] using hZ
  have hnum := (div_eq_iff (denom_ne_zero ζ)).mp hratio
  linarith

/-- The sphere-valued readout is invariant under rescaling homogeneous
coordinates, since it factors through the Riemann-sphere readout. -/
theorem cp1_unitSphere_invariant_under_projective_equivalence
    {p q : InfoGeometry.CP1}
    (h : InfoGeometry.CP1.equiv p q) :
    riemannSphereToUnitSphere p.toRiemannSphere =
      riemannSphereToUnitSphere q.toRiemannSphere := by
  exact congrArg riemannSphereToUnitSphere (cp1_equiv_toRiemannSphere h)

/-- The projective relation on homogeneous representatives. -/
def cp1ProjectiveSetoid : Setoid InfoGeometry.CP1 where
  r := InfoGeometry.CP1.equiv
  iseqv := ⟨cp1_equiv_refl, @cp1_equiv_symm, @cp1_equiv_trans⟩

/-- The Penrose chart, extended at infinity, descends to projective CP¹
classes. -/
noncomputable def projectiveCP1ToUnitSphere
    (p : Quotient cp1ProjectiveSetoid) : UnitSphereCarrier :=
  Quotient.lift
    (fun q : InfoGeometry.CP1 =>
      riemannSphereToUnitSphere q.toRiemannSphere)
    (by
      intro q r hqr
      exact cp1_unitSphere_invariant_under_projective_equivalence hqr)
    p

@[simp]
theorem projectiveCP1ToUnitSphere_mk (p : InfoGeometry.CP1) :
    projectiveCP1ToUnitSphere (Quotient.mk cp1ProjectiveSetoid p) =
      riemannSphereToUnitSphere p.toRiemannSphere := by
  rfl

end Experimental.Sandbox.Mobius
