/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealTwistorPolynomialCCR
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# Positive algebraic Fock pairing for real polynomial twistors

The factorial pairing is constructed on the actual polynomial carrier.  It is
positive definite, has unit vacuum norm, and makes polynomial creation and
annihilation algebraic adjoints.  All sums are finite coefficient sums; this
file asserts no Hilbert completion or self-adjointness of unbounded operators.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealPolynomialCCR

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Multi-index factorial, as a strictly positive real coefficient. -/
def factorialWeight (m : ι →₀ ℕ) : ℝ := ∏ i, (Nat.factorial (m i) : ℝ)

omit [DecidableEq ι] in
theorem factorialWeight_pos (m : ι →₀ ℕ) : 0 < factorialWeight m := by
  apply Finset.prod_pos
  intro i _
  exact_mod_cast Nat.factorial_pos (m i)

omit [DecidableEq ι] in
@[simp] theorem factorialWeight_zero : factorialWeight (0 : ι →₀ ℕ) = 1 := by
  simp [factorialWeight]

theorem factorialWeight_add_single (m : ι →₀ ℕ) (i : ι) :
    factorialWeight (m + Finsupp.single i 1) = (m i + 1 : ℝ) * factorialWeight m := by
  have h (j : ι) :
      (Nat.factorial ((m + Finsupp.single i (1 : ℕ) : ι →₀ ℕ) j) : ℝ) =
        (if j = i then (m i + 1 : ℝ) else 1) * (Nat.factorial (m j) : ℝ) := by
    by_cases hji : j = i
    · subst j
      simp [Nat.factorial_succ]
    · simp [hji]
  unfold factorialWeight
  simp_rw [h]
  rw [Finset.prod_mul_distrib]
  simp

/-- `⟨x^m, x^n⟩ = δₘₙ m!`, extended by finite coefficient sums. -/
def fockPairing (p q : WavePolynomial ι) : ℝ :=
  p.coeff.sum fun m a => a * q.coeff m * factorialWeight m

omit [DecidableEq ι] in
theorem fockPairing_eq_sum (p q : WavePolynomial ι) :
    fockPairing p q = ∑ m ∈ p.support, p.coeff m * q.coeff m * factorialWeight m := by
  exact MvPolynomial.sum_def

omit [DecidableEq ι] in
@[simp] theorem fockPairing_monomial_left (m : ι →₀ ℕ) (a : ℝ)
    (q : WavePolynomial ι) :
    fockPairing (MvPolynomial.monomial m a) q = a * q.coeff m * factorialWeight m := by
  exact MvPolynomial.sum_monomial_eq (by simp)

omit [DecidableEq ι] in
@[simp] theorem fockPairing_add_left (p q r : WavePolynomial ι) :
    fockPairing (p + q) r = fockPairing p r + fockPairing q r := by
  change (p.coeff + q.coeff).sum _ = _
  exact Finsupp.sum_add_index' (by intros; simp) (by intros; ring)

omit [DecidableEq ι] in
@[simp] theorem fockPairing_add_right (p q r : WavePolynomial ι) :
    fockPairing p (q + r) = fockPairing p q + fockPairing p r := by
  simp [fockPairing, mul_add, add_mul, Finsupp.sum_add]

omit [DecidableEq ι] in
@[simp] theorem fockPairing_zero_left (p : WavePolynomial ι) : fockPairing 0 p = 0 := by
  simp [fockPairing]

omit [DecidableEq ι] in
@[simp] theorem fockPairing_zero_right (p : WavePolynomial ι) : fockPairing p 0 = 0 := by
  simp [fockPairing]

omit [DecidableEq ι] in
theorem fockPairing_symmetric (p q : WavePolynomial ι) :
    fockPairing p q = fockPairing q p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p₁ p₂ hp₁ hp₂ => simp [hp₁, hp₂]
  | monomial m a =>
    induction q using MvPolynomial.induction_on' with
    | add q₁ q₂ hq₁ hq₂ => simp [hq₁, hq₂]
    | monomial n b =>
      by_cases h : m = n
      · subst n
        simp [mul_comm a b]
      · simp [MvPolynomial.coeff_monomial, h, Ne.symm h]

omit [DecidableEq ι] in
@[simp] theorem fockPairing_smul_left (c : ℝ) (p q : WavePolynomial ι) :
    fockPairing (c • p) q = c * fockPairing p q := by
  induction p using MvPolynomial.induction_on' with
  | add p₁ p₂ hp₁ hp₂ => simp [smul_add, hp₁, hp₂, mul_add]
  | monomial m a =>
    rw [MvPolynomial.smul_monomial]
    simp [mul_assoc]

omit [DecidableEq ι] in
@[simp] theorem fockPairing_smul_right (c : ℝ) (p q : WavePolynomial ι) :
    fockPairing p (c • q) = c * fockPairing p q := by
  rw [fockPairing_symmetric, fockPairing_smul_left, fockPairing_symmetric q p]

/-- The pairing is a native bilinear form, with linearity proved above. -/
def fockForm : LinearMap.BilinForm ℝ (WavePolynomial ι) where
  toFun p :=
    { toFun := fockPairing p
      map_add' := fockPairing_add_right p
      map_smul' := by intros; simp }
  map_add' p q := by
    apply LinearMap.ext
    intro r
    exact fockPairing_add_left p q r
  map_smul' c p := by
    apply LinearMap.ext
    intro q
    exact fockPairing_smul_left c p q

omit [DecidableEq ι] in
theorem fockPairing_self_nonneg (p : WavePolynomial ι) : 0 ≤ fockPairing p p := by
  rw [fockPairing_eq_sum]
  exact Finset.sum_nonneg fun m _ =>
    mul_nonneg (mul_self_nonneg _) (le_of_lt (factorialWeight_pos m))

omit [DecidableEq ι] in
theorem fockPairing_self_pos {p : WavePolynomial ι} (hp : p ≠ 0) :
    0 < fockPairing p p := by
  obtain ⟨m, hm⟩ : ∃ m, p.coeff m ≠ 0 := by
    by_contra h
    apply hp
    apply MvPolynomial.ext
    intro m
    simpa using (not_exists.mp h m)
  rw [fockPairing_eq_sum]
  apply Finset.sum_pos'
  · intro n _
    exact mul_nonneg (mul_self_nonneg _) (le_of_lt (factorialWeight_pos n))
  · exact ⟨m, MvPolynomial.mem_support_iff.mpr hm,
      mul_pos (mul_self_pos.mpr hm) (factorialWeight_pos m)⟩

omit [DecidableEq ι] in
theorem fockPairing_self_eq_zero_iff (p : WavePolynomial ι) :
    fockPairing p p = 0 ↔ p = 0 := by
  constructor
  · intro h
    by_contra hp
    exact (ne_of_gt (fockPairing_self_pos hp)) h
  · intro h
    subst p
    simp

/-- A positive pairing gives a native map into the algebraic dual. -/
def fockToDual : WavePolynomial ι →ₗ[ℝ] Module.Dual ℝ (WavePolynomial ι) := fockForm

omit [DecidableEq ι] in
/-- This algebraic dual map is injective; surjectivity is not asserted. -/
theorem fockToDual_injective : Function.Injective (fockToDual (ι := ι)) := by
  intro p q h
  apply sub_eq_zero.mp
  apply (fockPairing_self_eq_zero_iff (p - q)).mp
  have hz : fockToDual (p - q) = 0 := by
    rw [map_sub, h, sub_self]
  change fockToDual (p - q) (p - q) = 0
  rw [hz]
  rfl

omit [DecidableEq ι] in
@[simp] theorem fockPairing_vacuum :
    fockPairing (1 : WavePolynomial ι) 1 = 1 := by
  change fockPairing (MvPolynomial.monomial (0 : ι →₀ ℕ) (1 : ℝ))
    (MvPolynomial.monomial (0 : ι →₀ ℕ) (1 : ℝ)) = 1
  rw [fockPairing_monomial_left]
  classical
  simp

/-- Creation and annihilation are genuine algebraic adjoints on all polynomials. -/
theorem create_annihilate_adjoint (i : ι) (p q : WavePolynomial ι) :
    fockPairing (create i p) q = fockPairing p (annihilate i q) := by
  induction p using MvPolynomial.induction_on' with
  | add p₁ p₂ hp₁ hp₂ =>
    simp only [map_add, fockPairing_add_left, hp₁, hp₂]
  | monomial m a =>
    rw [create_apply, MvPolynomial.X, MvPolynomial.monomial_mul_monomial]
    simp only [one_mul, fockPairing_monomial_left, annihilate_apply,
      MvPolynomial.coeff_pderiv]
    rw [add_comm (Finsupp.single i 1) m, factorialWeight_add_single]
    ring

theorem annihilate_create_adjoint (i : ι) (p q : WavePolynomial ι) :
    fockPairing (annihilate i p) q = fockPairing p (create i q) := by
  rw [fockPairing_symmetric, ← create_annihilate_adjoint,
    fockPairing_symmetric (create i q) p]

/-- Occupation is symmetric for the positive algebraic pairing. -/
theorem number_symmetric (i : ι) (p q : WavePolynomial ι) :
    fockPairing (number i p) q = fockPairing p (number i q) := by
  change fockPairing (create i (annihilate i p)) q =
    fockPairing p (create i (annihilate i q))
  rw [create_annihilate_adjoint, annihilate_create_adjoint]

end InfoGeometry.Twistor.RealPolynomialCCR
