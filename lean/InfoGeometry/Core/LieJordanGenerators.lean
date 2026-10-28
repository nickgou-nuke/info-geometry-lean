/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.LieJordanBoundaryOperators
import InfoGeometry.Core.PeirceQuadraticFrame
import InfoGeometry.Core.PeirceSandwichDuality
import Mathlib.Basic.Real.Basic

/-!
# Three native Lie--Jordan generators

The generators are sums and differences of compositions of the existing
adjoint and Jordan actions. Their two-sided expansions retain the two different
skew signs. Opposite-corner support determines their exact values on the
projection and quadratic frame. Stationarity of the quadratic complement for
the skew-plus generator requires precisely an idempotence condition when
multiplication by four is injective; this cancellation holds over real algebras.
-/

namespace InfoGeometry.Core.LieJordanGenerators

attribute [local instance 100] LieRing.ofAssociativeRing

open JordanMultiplicationClosure LieJordanBoundaryOperators
open PeirceDecomposition PeirceGrading PeirceCoupledCorners
open PeirceQuadraticFrame PeirceSandwichDuality

section Operators

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

def symmetricGenerator (a b : A) : Module.End R A :=
  -(LieAlgebra.ad R A a * LieAlgebra.ad R A b +
    LieAlgebra.ad R A b * LieAlgebra.ad R A a)

def skewPlusGenerator (a b : A) : Module.End R A :=
  LieAlgebra.ad R A a * jordanLeft (R := R) b -
    LieAlgebra.ad R A b * jordanLeft (R := R) a

def skewMinusGenerator (a b : A) : Module.End R A :=
  -(jordanLeft (R := R) a * LieAlgebra.ad R A b -
    jordanLeft (R := R) b * LieAlgebra.ad R A a)

@[simp] theorem symmetricGenerator_apply (a b x : A) :
    symmetricGenerator (R := R) a b x =
      -(LieAlgebra.ad R A a (LieAlgebra.ad R A b x) +
        LieAlgebra.ad R A b (LieAlgebra.ad R A a x)) := rfl

@[simp] theorem skewPlusGenerator_apply (a b x : A) :
    skewPlusGenerator (R := R) a b x =
      LieAlgebra.ad R A a (jordanLeft (R := R) b x) -
        LieAlgebra.ad R A b (jordanLeft (R := R) a x) := rfl

@[simp] theorem skewMinusGenerator_apply (a b x : A) :
    skewMinusGenerator (R := R) a b x =
      -(jordanLeft (R := R) a (LieAlgebra.ad R A b x) -
        jordanLeft (R := R) b (LieAlgebra.ad R A a x)) := rfl

theorem symmetricGenerator_eq_sandwich (a b : A) :
    symmetricGenerator (R := R) a b =
      2 • (LinearMap.mulLeftRight R (a, b) + LinearMap.mulLeftRight R (b, a)) -
        jordanLeft (R := R) (a * b + b * a) := by
  rw [symmetricGenerator, ad_mul_ad_add, neg_sub]

theorem skewPlusGenerator_eq_sandwich (a b : A) :
    skewPlusGenerator (R := R) a b =
      2 • (LinearMap.mulLeftRight R (a, b) - LinearMap.mulLeftRight R (b, a)) +
        jordanLeft (R := R) ⁅a, b⁆ := by
  rw [skewPlusGenerator, ad_mul_jordan_sub, add_comm]

theorem skewMinusGenerator_eq_sandwich (a b : A) :
    skewMinusGenerator (R := R) a b =
      2 • (LinearMap.mulLeftRight R (a, b) - LinearMap.mulLeftRight R (b, a)) -
        jordanLeft (R := R) ⁅a, b⁆ := by
  rw [skewMinusGenerator, jordan_mul_ad_sub, neg_sub]

theorem symmetricGenerator_sandwich_apply (a b x : A) :
    symmetricGenerator (R := R) a b x =
      2 • (a * x * b + b * x * a) -
        ((a * b + b * a) * x + x * (a * b + b * a)) := by
  rw [symmetricGenerator_eq_sandwich]
  rfl

theorem skewPlusGenerator_sandwich_apply (a b x : A) :
    skewPlusGenerator (R := R) a b x =
      2 • (a * x * b - b * x * a) + (⁅a, b⁆ * x + x * ⁅a, b⁆) := by
  rw [skewPlusGenerator_eq_sandwich]
  rfl

theorem skewMinusGenerator_sandwich_apply (a b x : A) :
    skewMinusGenerator (R := R) a b x =
      2 • (a * x * b - b * x * a) - (⁅a, b⁆ * x + x * ⁅a, b⁆) := by
  rw [skewMinusGenerator_eq_sandwich]
  rfl

@[simp] theorem symmetricGenerator_one (a b : A) :
    symmetricGenerator (R := R) a b 1 = 0 := by
  rw [symmetricGenerator_sandwich_apply]
  simp only [mul_one, one_mul, two_nsmul, sub_self]

@[simp] theorem skewPlusGenerator_one (a b : A) :
    skewPlusGenerator (R := R) a b 1 = 4 • ⁅a, b⁆ := by
  rw [skewPlusGenerator_sandwich_apply]
  simp only [mul_one, one_mul, Ring.lie_def]
  rw [show (4 : ℕ) = 2 + 2 by decide, add_nsmul]
  simp only [two_nsmul]

@[simp] theorem skewMinusGenerator_one (a b : A) :
    skewMinusGenerator (R := R) a b 1 = 0 := by
  rw [skewMinusGenerator_sandwich_apply]
  simp only [mul_one, one_mul, Ring.lie_def, two_nsmul, sub_self]

end Operators

section RingFrame

variable {A : Type*} [Ring A] {p u v : A}

/-- The quadratic frame centralizers factor both ordered sandwiches. -/
theorem sandwich_sum_quadratic (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    u * (u * v + v * u) * v + v * (u * v + v * u) * u =
      (u * v + v * u) ^ 2 := by
  rw [← (quadratic_commute_left (v := v) hp hu).eq,
    ← (quadratic_commute_right (u := u) hp hv).eq]
  noncomm_ring

theorem sandwich_sub_quadratic (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    u * (u * v + v * u) * v - v * (u * v + v * u) * u =
      (u * v + v * u) * ⁅u, v⁆ := by
  rw [← (quadratic_commute_left (v := v) hp hu).eq,
    ← (quadratic_commute_right (u := u) hp hv).eq]
  change (u * v + v * u) * u * v - (u * v + v * u) * v * u =
    (u * v + v * u) * (u * v - v * u)
  noncomm_ring

/-- Input reflection transports the quadratic sandwich to the bracket. -/
theorem sandwich_sum_bracket (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    u * ⁅u, v⁆ * v + v * ⁅u, v⁆ * u = -((u * v + v * u) * ⁅u, v⁆) := by
  calc
    _ = u * (reflection p * (u * v + v * u)) * v +
        v * (reflection p * (u * v + v * u)) * u := by
      rw [reflection_mul_jordan hp hu hv]
    _ = -(u * (u * v + v * u) * v - v * (u * v + v * u) * u) :=
      sandwich_sum_reflection hp hu hv _
    _ = _ := by rw [sandwich_sub_quadratic hp hu hv]

theorem sandwich_sub_bracket (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    u * ⁅u, v⁆ * v - v * ⁅u, v⁆ * u = -((u * v + v * u) ^ 2) := by
  calc
    _ = u * (reflection p * (u * v + v * u)) * v -
        v * (reflection p * (u * v + v * u)) * u := by
      rw [reflection_mul_jordan hp hu hv]
    _ = -(u * (u * v + v * u) * v + v * (u * v + v * u) * u) :=
      sandwich_sub_reflection hp hu hv _
    _ = _ := by rw [sandwich_sum_quadratic hp hu hv]

/-- The defect formula holds for every element of every associative ring. -/
theorem one_sub_idempotence_defect (k : A) :
    (1 - k) ^ 2 - (1 - k) = k ^ 2 - k := by
  noncomm_ring

/-- Reflection is invertible, so the bracket defect detects quadratic idempotence. -/
theorem bracket_mul_one_sub_quadratic_eq_zero_iff (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    ⁅u, v⁆ * (1 - (u * v + v * u)) = 0 ↔
      IsIdempotentElem (u * v + v * u) := by
  constructor
  · intro h
    have hk : (u * v + v * u) * (1 - (u * v + v * u)) = 0 := by
      calc
        _ = reflection p * (⁅u, v⁆ * (1 - (u * v + v * u))) := by
          rw [← mul_assoc, reflection_mul_bracket hp hu hv]
        _ = 0 := by rw [h, mul_zero]
    exact isIdempotentElem_iff_mul_one_sub_self.mpr hk
  · intro hk
    rw [← reflection_mul_jordan hp hu hv, mul_assoc, hk.mul_one_sub_self, mul_zero]

end RingFrame

section SupportedGenerators

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {p u v : A}

theorem symmetricGenerator_projection (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    symmetricGenerator (R := R) u v p = -(2 • ⁅u, v⁆) := by
  rw [symmetricGenerator_sandwich_apply, right_support10 hp hu,
    right_support01 hp hv, zero_mul, zero_add, right_jordan hp hu hv,
    left_jordan hp hu hv]
  simp only [two_nsmul, Ring.lie_def]
  abel

theorem skewPlusGenerator_projection (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    skewPlusGenerator (R := R) u v p = 2 • ⁅u, v⁆ := by
  rw [skewPlusGenerator_sandwich_apply, right_support10 hp hu,
    right_support01 hp hv, zero_mul, zero_sub, right_bracket hp hu hv,
    left_bracket hp hu hv]
  simp only [two_nsmul, Ring.lie_def]
  abel

theorem skewMinusGenerator_projection (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    skewMinusGenerator (R := R) u v p = -(2 • (u * v + v * u)) := by
  rw [skewMinusGenerator_sandwich_apply, right_support10 hp hu,
    right_support01 hp hv, zero_mul, zero_sub, right_bracket hp hu hv,
    left_bracket hp hu hv]
  simp only [two_nsmul]
  abel

theorem symmetricGenerator_quadratic (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    symmetricGenerator (R := R) u v (u * v + v * u) = 0 := by
  rw [symmetricGenerator_sandwich_apply, sandwich_sum_quadratic hp hu hv]
  simp only [pow_two, two_nsmul, sub_self]

theorem skewPlusGenerator_quadratic (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    skewPlusGenerator (R := R) u v (u * v + v * u) =
      4 • (⁅u, v⁆ * (u * v + v * u)) := by
  rw [skewPlusGenerator_sandwich_apply, sandwich_sub_quadratic hp hu hv,
    (quadratic_commute_bracket hp hu hv).eq]
  rw [show (4 : ℕ) = 2 + 2 by decide, add_nsmul]
  simp only [two_nsmul]

theorem skewMinusGenerator_quadratic (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    skewMinusGenerator (R := R) u v (u * v + v * u) = 0 := by
  rw [skewMinusGenerator_sandwich_apply, sandwich_sub_quadratic hp hu hv,
    (quadratic_commute_bracket hp hu hv).eq]
  simp only [two_nsmul, sub_self]

theorem symmetricGenerator_bracket (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    symmetricGenerator (R := R) u v ⁅u, v⁆ =
      -(4 • ((u * v + v * u) * ⁅u, v⁆)) := by
  rw [symmetricGenerator_sandwich_apply, sandwich_sum_bracket hp hu hv,
    (quadratic_commute_bracket hp hu hv).eq]
  rw [show (4 : ℕ) = 2 + 2 by decide, add_nsmul]
  simp only [two_nsmul]
  abel

theorem skewPlusGenerator_bracket (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    skewPlusGenerator (R := R) u v ⁅u, v⁆ = 0 := by
  rw [skewPlusGenerator_sandwich_apply, sandwich_sub_bracket hp hu hv,
    ← pow_two ⁅u, v⁆, bracket_square hp hu hv]
  simp only [two_nsmul]
  abel

theorem skewMinusGenerator_bracket (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    skewMinusGenerator (R := R) u v ⁅u, v⁆ = -(4 • ((u * v + v * u) ^ 2)) := by
  rw [skewMinusGenerator_sandwich_apply, sandwich_sub_bracket hp hu hv,
    ← pow_two ⁅u, v⁆, bracket_square hp hu hv]
  rw [show (4 : ℕ) = 2 + 2 by decide, add_nsmul]
  simp only [two_nsmul]
  abel

theorem symmetricGenerator_one_sub_quadratic (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    symmetricGenerator (R := R) u v (1 - (u * v + v * u)) = 0 := by
  rw [map_sub, symmetricGenerator_one, symmetricGenerator_quadratic hp hu hv, sub_zero]

theorem skewPlusGenerator_one_sub_quadratic (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    skewPlusGenerator (R := R) u v (1 - (u * v + v * u)) =
      4 • (⁅u, v⁆ * (1 - (u * v + v * u))) := by
  rw [map_sub, skewPlusGenerator_one, skewPlusGenerator_quadratic hp hu hv,
    ← smul_sub, mul_sub, mul_one]

theorem skewMinusGenerator_one_sub_quadratic (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    skewMinusGenerator (R := R) u v (1 - (u * v + v * u)) = 0 := by
  rw [map_sub, skewMinusGenerator_one, skewMinusGenerator_quadratic hp hu hv, sub_zero]

theorem skewPlusGenerator_one_sub_eq_zero_iff (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p)
    (h4 : Function.Injective (fun x : A => (4 : ℕ) • x)) :
    skewPlusGenerator (R := R) u v (1 - (u * v + v * u)) = 0 ↔
      IsIdempotentElem (u * v + v * u) := by
  rw [skewPlusGenerator_one_sub_quadratic hp hu hv]
  have hz (x : A) : 4 • x = 0 ↔ x = 0 := by
    constructor
    · intro h
      apply h4
      simpa only [smul_zero] using h
    · rintro rfl
      exact smul_zero 4
  rw [hz, bracket_mul_one_sub_quadratic_eq_zero_iff hp hu hv]

end SupportedGenerators

section Real

variable {A : Type*} [Ring A] [Algebra ℝ A] {p u v : A}

/-- Four is cancelled through the real module structure, not through ring division. -/
theorem skewPlusGenerator_one_sub_eq_zero_iff_real (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    skewPlusGenerator (R := ℝ) u v (1 - (u * v + v * u)) = 0 ↔
      IsIdempotentElem (u * v + v * u) := by
  apply skewPlusGenerator_one_sub_eq_zero_iff hp hu hv
  intro x y h
  have hreal : (4 : ℝ) • x = (4 : ℝ) • y := by
    simpa only [← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_ofNat] using h
  have hquarter := congrArg (fun z : A => (1 / 4 : ℝ) • z) hreal
  simpa only [smul_smul, show (1 / 4 : ℝ) * 4 = 1 by norm_num, one_smul] using hquarter

theorem skewPlusGenerator_one_sub_eq_zero_iff_complement_real (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    skewPlusGenerator (R := ℝ) u v (1 - (u * v + v * u)) = 0 ↔
      IsIdempotentElem (1 - (u * v + v * u)) :=
  (skewPlusGenerator_one_sub_eq_zero_iff_real hp hu hv).trans
    IsIdempotentElem.one_sub_iff.symm

end Real

end InfoGeometry.Core.LieJordanGenerators
