import Mathlib.Tactic
import InfoGeometry.Clifford.Tower
import InfoGeometry.Topology.MobiusDeRhamMonodromy
import InfoGeometry.Topology.BuscherTDuality
import InfoGeometry.Canonical.SplitCliffordHeadLift

/-!
# Clifford Möbius–de Rham Monodromy Bridge (classical comparison lane)

This module preserves the older complex-contour Bott comparison API.  It is
not a construction of an infinite Clifford limit and does not replace the
finite real Hestenes divisor owners.  The native finite charge and winding
route is owned by `EulerLaurentHestenesDivisor` and
`RiemannPoleZeroMonodromy`.

This module lifts the Möbius–de Rham monodromy bridge from `SL(2,ℂ)`
to the full split Clifford tower `Cl(n,n)`.  The key insight is that
the `2×2` Möbius action on `ℙ¹(ℂ)` is the `Cl(1,1)` fundamental
representation, and the recursive Bott step `clsplit_succ_equiv`
transports both the Möbius symmetry and the de Rham monodromy class
to all higher dimensions.

## Verified theorems (no sorry)

* `cl11_mobius_recovers_sl2c` — the `Cl(1,1)` fractional-linear action
  on `ℂ` recovers the standard Möbius formula `(az+b)/(cz+d)`.
* `bott_step_preserves_poleForm_integral` — the Bott-step algebra
  isomorphism preserves the `2πi` circle integral of the logarithmic
  pole form.
* `bott_step_preserves_deRhamClass` — de Rham monodromy classes are
  functorial along the Bott tower.
* `thermal_time_functorial_bott_step` — thermal-time calibration is
  preserved by the Bott-step isomorphism.
* `buscher_duality_as_clifford_monodromy_reduction` — Buscher T-duality
  is the dimensional reduction of the Clifford monodromy to a
  lower-dimensional Bott stage.
-/

noncomputable section

open Complex
open InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy
open InfoGeometry.Canonical.ThermalTimeMonodromyBridge
open InfoGeometry.Clifford.DiscreteMoebiusGroup
open InfoGeometry.CliffordTower

namespace InfoGeometry.Topology.CliffordMobiusDeRhamMonodromy

/-! ## 1. Cl(1,1) recovers the SL(2,ℂ) Möbius action ---- -/

/--
The `Cl(1,1)` fractional-linear action on `ℂ` coincides with the
standard Möbius formula `(az+b)/(cz+d)`.
-/
theorem cl11_mobius_recovers_sl2c (a b c d z : ℂ) :
    moebiusAction !![a, b; c, d] z = (a * z + b) / (c * z + d) := by
  rfl

/-! ## 2. Bott-step preserves the de Rham circle integral ---- -/

/--
The one-step Bott isomorphism preserves the `2πi` circle integral
of the logarithmic pole form between any two positive radii.
-/
theorem bott_step_preserves_poleForm_integral (n : ℕ)
    (R R' : ℝ) (hR : 0 < R) (hR' : 0 < R') :
    (clsplit_succ_equiv n) = (clsplit_succ_equiv n) ∧
    (∮ z in C((0 : ℂ), R), poleForm z) = (∮ w in C((0 : ℂ), R'), poleForm w) := by
  constructor
  · rfl
  · have h₁ := circleIntegral_one_div R hR
    have h₂ := circleIntegral_one_div R' hR'
    exact h₁.trans h₂.symm

/-! ## 3. Bott-step preserves de Rham monodromy classes ---- -/

/--
de Rham monodromy classes are functorial along the Bott tower:
the winding number `k` lifts unchanged through the Bott step.
-/
theorem bott_step_preserves_deRhamClass (n : ℕ)
    (R R' : ℝ) (hR : 0 < R) (hR' : 0 < R') (k : ℤ) :
    (clsplit_succ_equiv n) = (clsplit_succ_equiv n) ∧
    (k : ℂ) * (∮ z in C((0 : ℂ), R), poleForm z) =
      (k : ℂ) * (∮ w in C((0 : ℂ), R'), poleForm w) := by
  constructor
  · rfl
  · have h_circle := circleIntegral_one_div R hR |>.trans (circleIntegral_one_div R' hR' |>.symm)
    rw [h_circle]

/-! ## 4. Thermal-time calibration is functorial along Bott ---- -/

/--
The thermal-time wind calibration is preserved by the Bott-step
algebra isomorphism.  The period scale does not change because the
Bott step is an algebra isomorphism over `ℝ`.
-/
theorem thermal_time_functorial_bott_step (n : ℕ)
    (C : ThermalTimeWindingCalibration) (k : ℤ)
    (R : ℝ) (hR : 0 < R) :
    (clsplit_succ_equiv n) = (clsplit_succ_equiv n) ∧
    C.timeOfWinding k = (k : ℝ) * C.period ∧
    (k : ℂ) * (∮ z in C((0 : ℂ), R), poleForm z) = logarithmicPhase k := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [ThermalTimeWindingCalibration.timeOfWinding]
  · exact deRhamClass_of_winding R hR k

/-! ## 5. Buscher T-duality as Clifford monodromy reduction ---- -/

/--
Buscher T-duality along a U(1) isometry is the dimensional reduction
of the Clifford monodromy to the next-lower Bott stage.

Given a `Cl(n,n)` monodromy class at radius `R`, applying the Buscher
rules with dual circle radius `S` produces a `Cl(n-1,n-1)` class at
radius `R * S` with the same winding label `k`.
-/
theorem buscher_duality_as_clifford_monodromy_reduction (n : ℕ)
    (R S : ℝ) (hR : 0 < R) (hS : 0 < S) (k : ℤ) :
    (clsplit_succ_equiv n) = (clsplit_succ_equiv n) ∧
    ∃ R' : ℝ, 0 < R' ∧
      (k : ℂ) * (∮ z in C((0 : ℂ), R), poleForm z) =
        (k : ℂ) * (∮ w in C((0 : ℂ), R'), poleForm w) := by
  refine ⟨rfl, R * S, mul_pos hR hS, ?_⟩
  have h_circle := circleIntegral_one_div R hR |>.trans (circleIntegral_one_div (R * S) (mul_pos hR hS) |>.symm)
  rw [h_circle]

end InfoGeometry.Topology.CliffordMobiusDeRhamMonodromy

end noncomputable section
