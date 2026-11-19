/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.SplitOctonionRegularMultiplicationHestenesBridge

/-!
# Bounds and periodicity for real quadratic exponential flows

The scalar-square exponential formulas are owned by
`SplitOctonionRegularMultiplicationHestenesBridge`. This file adds their analytic
consequences in an arbitrary complete real normed algebra. No commutativity of
the algebra is assumed.

The time parameter ranges over all of `ℝ`. A nonzero square-zero generator has
linear norm growth, and a positive scalar-square generator has an unbounded
two-sided flow. Thus, in a nontrivial algebra, `G ^ 2 = q • 1` gives a globally
bounded exponential flow exactly when `q < 0` or `G = 0`.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.QuadraticExponentialBounds

open InfoGeometry.Lie.SplitOctonionRegularMultiplicationHestenesBridge
open InfoGeometry.Physics.HestenesKreinOperatorCalculus

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

local instance : NormedAlgebra ℚ A :=
  NormedAlgebra.restrictScalars ℚ ℝ A

/-- A negative scalar-square generator has a time-independent norm bound.
The bound retains `‖1‖`, so no normalized-unit-norm assumption is needed. -/
theorem norm_exp_le_of_sq_eq_neg_scalar
    (G : A) (r : ℝ) (hr : 0 < r)
    (hG : G ^ 2 = -(r ^ 2) • (1 : A)) (t : ℝ) :
    ‖NormedSpace.exp (t • G)‖ ≤ ‖(1 : A)‖ + ‖G‖ / r := by
  have hcos : |Real.cos (r * t)| * ‖(1 : A)‖ ≤ ‖(1 : A)‖ := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (Real.abs_cos_le_one (r * t)) (norm_nonneg (1 : A))
  have hsin : (|Real.sin (r * t)| / r) * ‖G‖ ≤ ‖G‖ / r := by
    calc
      (|Real.sin (r * t)| / r) * ‖G‖ ≤ (1 / r) * ‖G‖ :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (Real.abs_sin_le_one (r * t)) (le_of_lt hr))
          (norm_nonneg G)
      _ = ‖G‖ / r := by ring
  rw [exp_of_sq_eq_neg_scalar G r t (ne_of_gt hr) hG]
  calc
    ‖Real.cos (r * t) • (1 : A) + (Real.sin (r * t) / r) • G‖ ≤
        ‖Real.cos (r * t) • (1 : A)‖ + ‖(Real.sin (r * t) / r) • G‖ :=
      norm_add_le _ _
    _ = |Real.cos (r * t)| * ‖(1 : A)‖ + (|Real.sin (r * t)| / r) * ‖G‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hr]
    _ ≤ ‖(1 : A)‖ + ‖G‖ / r := add_le_add hcos hsin

/-- The whole exponential, rather than just a scalar coefficient, is periodic
when the generator has negative scalar square. -/
theorem periodic_exp_of_sq_eq_neg_scalar
    (G : A) (r : ℝ) (hr : r ≠ 0)
    (hG : G ^ 2 = -(r ^ 2) • (1 : A)) :
    Function.Periodic (fun t : ℝ => NormedSpace.exp (t • G)) (2 * Real.pi / r) := by
  intro t
  change NormedSpace.exp ((t + 2 * Real.pi / r) • G) = NormedSpace.exp (t • G)
  rw [exp_of_sq_eq_neg_scalar G r (t + 2 * Real.pi / r) hr hG,
    exp_of_sq_eq_neg_scalar G r t hr hG]
  have harg : r * (t + 2 * Real.pi / r) = r * t + 2 * Real.pi := by
    rw [mul_add, mul_div_cancel₀ (2 * Real.pi) hr]
  rw [harg, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- A square-zero generator has the explicit linear lower norm bound obtained
from `exp (t • G) = 1 + t • G` and the reverse triangle inequality. -/
theorem norm_exp_ge_of_sq_eq_zero
    (G : A) (hG : G ^ 2 = (0 : A)) (t : ℝ) :
    |t| * ‖G‖ - ‖(1 : A)‖ ≤ ‖NormedSpace.exp (t • G)‖ := by
  have hnorm : ‖t • G‖ ≤ ‖(1 : A) + t • G‖ + ‖(1 : A)‖ := by
    simpa only [add_sub_cancel_left] using norm_sub_le ((1 : A) + t • G) (1 : A)
  rw [norm_smul, Real.norm_eq_abs] at hnorm
  rw [exp_of_sq_eq_zero G t hG]
  linarith

/-- Among square-zero generators, the zero generator is exactly the one with
a globally bounded exponential norm. This includes the degenerate algebra. -/
theorem bddAbove_norm_exp_of_sq_eq_zero_iff
    (G : A) (hG : G ^ 2 = (0 : A)) :
    BddAbove (Set.range fun t : ℝ => ‖NormedSpace.exp (t • G)‖) ↔ G = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra hne
    have hnorm : 0 < ‖G‖ := norm_pos_iff.mpr hne
    let t : ℝ := (|C| + ‖(1 : A)‖ + 1) / ‖G‖
    have ht : 0 < t := by
      dsimp [t]
      positivity
    have hmul : t * ‖G‖ = |C| + ‖(1 : A)‖ + 1 := by
      dsimp [t]
      exact div_mul_cancel₀ _ (ne_of_gt hnorm)
    have hlower := norm_exp_ge_of_sq_eq_zero G hG t
    rw [abs_of_pos ht, hmul] at hlower
    have hupper : ‖NormedSpace.exp (t • G)‖ ≤ C := hC (Set.mem_range_self t)
    have habs : C ≤ |C| := le_abs_self C
    linarith
  · rintro rfl
    refine ⟨‖(1 : A)‖, ?_⟩
    rintro y ⟨t, rfl⟩
    simp

/-- For a positive scalar-square generator, adding the forward and backward
exponentials removes the odd term. The triangle inequality gives this lower
bound without selecting an eigenspace or a preferred time direction. -/
theorem norm_exp_add_norm_exp_neg_ge_of_sq_eq_pos_scalar
    (G : A) (r : ℝ) (hr : r ≠ 0)
    (hG : G ^ 2 = (r ^ 2) • (1 : A)) (t : ℝ) :
    2 * (Real.cosh (r * t) * ‖(1 : A)‖) ≤
      ‖NormedSpace.exp (t • G)‖ + ‖NormedSpace.exp ((-t) • G)‖ := by
  have hsum : NormedSpace.exp (t • G) + NormedSpace.exp ((-t) • G) =
      (2 * Real.cosh (r * t)) • (1 : A) := by
    rw [exp_of_sq_eq_pos_scalar G r t hr hG,
      exp_of_sq_eq_pos_scalar G r (-t) hr hG]
    simp only [mul_neg, Real.cosh_neg, Real.sinh_neg, neg_div, neg_smul]
    module
  have hnorm := norm_add_le (NormedSpace.exp (t • G))
    (NormedSpace.exp ((-t) • G))
  rw [hsum, norm_smul, Real.norm_eq_abs,
    abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) (Real.cosh_pos (r * t)))] at hnorm
  simpa only [mul_assoc] using hnorm

/-- A positive scalar-square generator in a nontrivial algebra has no bound
valid for every real time. The proof uses both time directions. -/
theorem not_bddAbove_norm_exp_of_sq_eq_pos_scalar
    [Nontrivial A] (G : A) (r : ℝ) (hr : r ≠ 0)
    (hG : G ^ 2 = (r ^ 2) • (1 : A)) :
    ¬ BddAbove (Set.range fun t : ℝ => ‖NormedSpace.exp (t • G)‖) := by
  rintro ⟨C, hC⟩
  have hnorm : 0 < ‖(1 : A)‖ := norm_pos_iff.mpr one_ne_zero
  let x : ℝ := 2 * (C / ‖(1 : A)‖ + 1)
  have hx : x = 2 * (C / ‖(1 : A)‖ + 1) := rfl
  have hcosh : C / ‖(1 : A)‖ < Real.cosh x := by
    have hexp := Real.add_one_le_exp x
    have hpos := Real.exp_pos (-x)
    rw [Real.cosh_eq]
    linarith
  have hlarge : C < Real.cosh x * ‖(1 : A)‖ := (div_lt_iff₀ hnorm).mp hcosh
  let t : ℝ := x / r
  have harg : r * t = x := by
    dsimp [t]
    exact mul_div_cancel₀ x hr
  have hlower := norm_exp_add_norm_exp_neg_ge_of_sq_eq_pos_scalar G r hr hG t
  rw [harg] at hlower
  have hforward : ‖NormedSpace.exp (t • G)‖ ≤ C := hC (Set.mem_range_self t)
  have hbackward : ‖NormedSpace.exp ((-t) • G)‖ ≤ C := hC (Set.mem_range_self (-t))
  linarith

/-- Complete boundedness classification for a real scalar-square generator.
The zero generator is the exceptional bounded flow at scalar square zero. -/
theorem bddAbove_norm_exp_iff_of_sq_eq_scalar
    [Nontrivial A] (G : A) (q : ℝ) (hG : G ^ 2 = q • (1 : A)) :
    BddAbove (Set.range fun t : ℝ => ‖NormedSpace.exp (t • G)‖) ↔ q < 0 ∨ G = 0 := by
  constructor
  · intro hbounded
    rcases lt_trichotomy q 0 with hq | hq | hq
    · exact Or.inl hq
    · right
      have hzero : G ^ 2 = (0 : A) := by simpa only [hq, zero_smul] using hG
      exact (bddAbove_norm_exp_of_sq_eq_zero_iff G hzero).mp hbounded
    · have hsquare : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt (le_of_lt hq)
      have hpositive : G ^ 2 = (Real.sqrt q ^ 2) • (1 : A) := by
        simpa only [hsquare] using hG
      exact False.elim (not_bddAbove_norm_exp_of_sq_eq_pos_scalar G (Real.sqrt q)
        (ne_of_gt (Real.sqrt_pos.mpr hq)) hpositive hbounded)
  · rintro (hq | hzero)
    · let r : ℝ := Real.sqrt (-q)
      have hr : 0 < r := Real.sqrt_pos.mpr (neg_pos.mpr hq)
      have hsquare : r ^ 2 = -q := Real.sq_sqrt (le_of_lt (neg_pos.mpr hq))
      have hnegative : G ^ 2 = -(r ^ 2) • (1 : A) := by
        rw [hsquare, neg_neg]
        exact hG
      refine ⟨‖(1 : A)‖ + ‖G‖ / r, ?_⟩
      rintro y ⟨t, rfl⟩
      exact norm_exp_le_of_sq_eq_neg_scalar G r hr hnegative t
    · subst G
      refine ⟨‖(1 : A)‖, ?_⟩
      rintro y ⟨t, rfl⟩
      simp

/-- The noncommutative anticommuting complex-structure/involution pair inherits
the full classification from its proved mixed-square identity. -/
theorem bddAbove_norm_exp_mixed_iff
    [Nontrivial A] (I K : A) (hI : I ^ 2 = -1) (hK : K ^ 2 = 1)
    (hanti : I * K = -(K * I)) (θ η : ℝ) :
    BddAbove (Set.range fun t : ℝ => ‖NormedSpace.exp (t • (θ • I + η • K))‖) ↔
      η ^ 2 < θ ^ 2 ∨ θ • I + η • K = 0 := by
  simpa only [sub_neg] using
    bddAbove_norm_exp_iff_of_sq_eq_scalar (θ • I + η • K) (η ^ 2 - θ ^ 2)
      (anticommuting_mixed_square I K hI hK hanti θ η)

end InfoGeometry.OperatorAlgebra.QuadraticExponentialBounds
