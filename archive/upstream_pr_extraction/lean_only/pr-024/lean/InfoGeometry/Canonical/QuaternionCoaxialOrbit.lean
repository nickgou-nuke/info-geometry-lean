import Mathlib
import Mathlib.Analysis.Normed.Algebra.QuaternionExponential

/-!
# InfoGeometry.Canonical.QuaternionCoaxialOrbit

Quaternion Lie/orbit specialization of the exp/log morphism idea:
noncommutative globally, multiplicative on coaxial 1-parameter slices.

No wrappers. No `sorry`.
-/

namespace InfoGeometry.Canonical.QuaternionCoaxialOrbit

open Quaternion

noncomputable section

abbrev PureQuaternion := { q : Quaternion ℝ // q.re = 0 }

/-- Coaxial real-parameterized 1-parameter subgroup candidate. -/
def coaxialPath (v : PureQuaternion) (t : ℝ) : Quaternion ℝ := NormedSpace.exp (t • v.1)

/-- Pure quaternion square identity: `v² = -‖v‖²` (as `normSq`). -/
theorem pure_sq_eq_neg_normSq (v : PureQuaternion) :
    v.1 ^ 2 = -Quaternion.normSq v.1 := by
  exact (Quaternion.sq_eq_neg_normSq).2 v.2

/-- Scalar multiples of the same axis commute. -/
theorem coaxial_commute (v : PureQuaternion) (x y : ℝ) :
    Commute (x • v.1) (y • v.1) := by
  exact ((Commute.refl v.1).smul_left x).smul_right y

/--
Coaxial additive-to-multiplicative law:
`exp ((x+y)v) = exp (xv) * exp (yv)`.

This is the valid noncommutative specialization: same-axis slice only.
-/
theorem coaxial_exp_add (v : PureQuaternion) (x y : ℝ) :
    coaxialPath v (x + y) = coaxialPath v x * coaxialPath v y := by
  let +nondep : NormedAlgebra ℚ (Quaternion ℝ) := .restrictScalars ℚ ℝ (Quaternion ℝ)
  unfold coaxialPath
  rw [add_smul]
  simpa using NormedSpace.exp_add_of_commute (coaxial_commute v x y)

/-- Coaxial path starts at identity. -/
@[simp] theorem coaxialPath_zero (v : PureQuaternion) :
    coaxialPath v 0 = (1 : Quaternion ℝ) := by
  unfold coaxialPath
  simp

/-- Coaxial path inverse is time negation. -/
theorem coaxialPath_neg_mul (v : PureQuaternion) (t : ℝ) :
    coaxialPath v (-t) * coaxialPath v t = (1 : Quaternion ℝ) := by
  have h := coaxial_exp_add v (-t) t
  simpa [coaxialPath_zero] using h.symm

end

end InfoGeometry.Canonical.QuaternionCoaxialOrbit
