import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite scalar Rényi order readback

This owner records the finite scalar moment kernel behind Rényi readouts.  It
does not identify a scalar kernel with an operator trace or assert any
differentiability in the order parameter.
-/

namespace InfoGeometry.Canonical.RenyiFiniteOrderReadback

open scoped BigOperators

/-- Finite scalar power-moment kernel. -/
noncomputable def momentKernel {n : ℕ} (p : Fin n → ℝ) (β : ℝ) : ℝ :=
  ∑ i, Real.rpow (p i) β

theorem momentKernel_pos {n : ℕ} (p : Fin n → ℝ) (hn : 0 < n)
    (hp : ∀ i, 0 < p i) (β : ℝ) :
    0 < momentKernel p β := by
  unfold momentKernel
  apply Finset.sum_pos'
  · intro i hi
    exact (Real.rpow_pos_of_pos (hp i) β).le
  · refine ⟨⟨0, hn⟩, Finset.mem_univ _, ?_⟩
    exact Real.rpow_pos_of_pos (hp ⟨0, hn⟩) β

theorem deriv_rpow_in_order (p : ℝ) (hp : 0 < p) :
    deriv (fun β : ℝ => Real.rpow p β) 1 = Real.log p * p := by
  have h := deriv_const_rpow hp
    (differentiableAt_id : DifferentiableAt ℝ id (1 : ℝ))
  simpa [id_eq, Real.rpow_one] using h

theorem second_deriv_rpow_in_order (p : ℝ) (hp : 0 < p) :
    deriv (deriv (fun β : ℝ => Real.rpow p β)) 1 = Real.log p * p * Real.log p := by
  have hderiv : deriv (fun β : ℝ => Real.rpow p β) =
      fun β => Real.rpow p β * Real.log p := by
    funext β
    simpa [id_eq, mul_comm] using
      (deriv_const_rpow hp (differentiableAt_id : DifferentiableAt ℝ id β))
  rw [hderiv]
  simpa [Real.rpow_one, mul_assoc, mul_comm, mul_left_comm] using
    ((Real.hasStrictDerivAt_const_rpow hp 1).hasDerivAt.mul_const (Real.log p)).deriv

theorem second_deriv_momentKernel_at_one {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) :
    deriv (deriv (fun β : ℝ => momentKernel p β)) 1 =
      ∑ i, p i * (Real.log (p i)) ^ 2 := by
  have hderiv : deriv (fun β : ℝ => momentKernel p β) =
      fun β => ∑ i, Real.rpow (p i) β * Real.log (p i) := by
    funext β
    unfold momentKernel
    rw [deriv_fun_sum]
    · apply Finset.sum_congr rfl
      intro i hi
      simpa [mul_comm] using
        (deriv_const_rpow (hp i)
          (differentiableAt_id : DifferentiableAt ℝ id β))
    · intro i hi
      exact (Real.hasStrictDerivAt_const_rpow (hp i) β).differentiableAt
  rw [hderiv]
  rw [deriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    simpa [Real.rpow_one, mul_assoc, mul_comm, mul_left_comm, pow_two] using
      ((Real.hasStrictDerivAt_const_rpow (hp i) 1).hasDerivAt.mul_const
        (Real.log (p i))).deriv
  · intro i hi
    exact ((Real.hasStrictDerivAt_const_rpow (hp i) 1).hasDerivAt.mul_const
      (Real.log (p i))).differentiableAt

theorem deriv_momentKernel_at_one {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) :
    deriv (fun β : ℝ => momentKernel p β) 1 =
      ∑ i, Real.log (p i) * p i := by
  unfold momentKernel
  rw [deriv_fun_sum]
  · simp [deriv_rpow_in_order, hp]
  · intro i hi
    exact (Real.hasStrictDerivAt_const_rpow (hp i) 1).differentiableAt

/-- At order one, the moment kernel is the coordinate sum. -/
theorem momentKernel_one {n : ℕ} (p : Fin n → ℝ) :
    momentKernel p 1 = ∑ i, p i := by
  unfold momentKernel
  simp [Real.rpow_one]

/-- At order two, the moment kernel is the collision/purity sum. -/
theorem momentKernel_two {n : ℕ} (p : Fin n → ℝ) :
    momentKernel p 2 = ∑ i, (p i) ^ 2 := by
  unfold momentKernel
  simp

/-- A normalized nonnegative vector has unit order-one moment. -/
theorem momentKernel_one_eq_one {n : ℕ} (p : Fin n → ℝ)
    (hp : ∑ i, p i = 1) :
    momentKernel p 1 = 1 := by
  rw [momentKernel_one, hp]

theorem deriv_log_momentKernel_at_one {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    deriv (fun β => Real.log (momentKernel p β)) 1 =
      ∑ i, Real.log (p i) * p i := by
  have hderiv : HasDerivAt (fun β : ℝ => momentKernel p β)
      (∑ i, Real.log (p i) * p i) 1 := by
    unfold momentKernel
    apply HasDerivAt.fun_sum
    intro i hi
    simpa [Real.rpow_one, mul_comm] using
      (Real.hasStrictDerivAt_const_rpow (hp i) 1).hasDerivAt
  have hlog := hderiv.log (by
    rw [momentKernel_one_eq_one p hsum]
    norm_num)
  simpa [momentKernel_one_eq_one p hsum] using hlog.deriv

theorem deriv_log_momentKernel {n : ℕ} (p : Fin n → ℝ) (hn : 0 < n)
    (hp : ∀ i, 0 < p i) (β : ℝ) :
    deriv (fun γ => Real.log (momentKernel p γ)) β =
      (∑ i, Real.rpow (p i) β * Real.log (p i)) / momentKernel p β := by
  have hderiv : HasDerivAt (fun γ : ℝ => momentKernel p γ)
      (∑ i, Real.rpow (p i) β * Real.log (p i)) β := by
    unfold momentKernel
    apply HasDerivAt.fun_sum
    intro i hi
    simpa [mul_comm] using
      (Real.hasStrictDerivAt_const_rpow (hp i) β).hasDerivAt
  have hlog := hderiv.log (momentKernel_pos p hn hp β).ne'
  exact hlog.deriv

theorem second_deriv_log_momentKernel_at_one_raw {n : ℕ} (p : Fin n → ℝ)
    (hn : 0 < n) (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    deriv (deriv (fun β => Real.log (momentKernel p β))) 1 =
      (∑ i, p i * (Real.log (p i)) ^ 2) -
        (∑ i, p i * Real.log (p i)) ^ 2 := by
  have hM : HasDerivAt (fun β : ℝ => momentKernel p β)
      (∑ i, p i * Real.log (p i)) 1 := by
    unfold momentKernel
    apply HasDerivAt.fun_sum
    intro i hi
    simpa [Real.rpow_one, mul_comm] using
      (Real.hasStrictDerivAt_const_rpow (hp i) 1).hasDerivAt
  have hN : HasDerivAt
      (fun β : ℝ => ∑ i, Real.rpow (p i) β * Real.log (p i))
      (∑ i, p i * (Real.log (p i)) ^ 2) 1 := by
    apply HasDerivAt.fun_sum
    intro i hi
    simpa [Real.rpow_one, mul_assoc, mul_comm, mul_left_comm, pow_two] using
      ((Real.hasStrictDerivAt_const_rpow (hp i) 1).hasDerivAt.mul_const
        (Real.log (p i)))
  have hquot := hN.div hM (momentKernel_pos p hn hp 1).ne'
  have heq : deriv (fun β : ℝ => Real.log (momentKernel p β)) =
      fun β => (∑ i, Real.rpow (p i) β * Real.log (p i)) /
        momentKernel p β := by
    funext γ
    exact deriv_log_momentKernel p hn hp γ
  rw [heq]
  convert hquot.deriv using 1
  · simp [momentKernel_one_eq_one p hsum, Real.rpow_one]
    ring

theorem neg_deriv_log_momentKernel_at_one {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    -deriv (fun β => Real.log (momentKernel p β)) 1 =
      ∑ i, p i * (-Real.log (p i)) := by
  rw [deriv_log_momentKernel_at_one p hp hsum]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

noncomputable def varentropy {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  (∑ i, p i * (Real.log (p i)) ^ 2) -
    (∑ i, p i * (-Real.log (p i))) ^ 2

theorem second_deriv_log_momentKernel_at_one_eq_varentropy
    {n : ℕ} (p : Fin n → ℝ) (hn : 0 < n)
    (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    deriv (deriv (fun β => Real.log (momentKernel p β))) 1 =
      varentropy p := by
  rw [second_deriv_log_momentKernel_at_one_raw p hn hp hsum]
  unfold varentropy
  have hneg : (∑ i, p i * -Real.log (p i)) =
      -(∑ i, p i * Real.log (p i)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hneg]
  ring

theorem varentropy_eq_centered_surprisal_moments {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    varentropy p =
      (∑ i, p i * (Real.log (p i)) ^ 2) -
        (-deriv (fun β => Real.log (momentKernel p β)) 1) ^ 2 := by
  rw [neg_deriv_log_momentKernel_at_one p hp hsum]
  rfl

theorem varentropy_eq_raw_derivative_gap {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) :
    varentropy p =
      deriv (deriv (fun β => momentKernel p β)) 1 -
        (deriv (fun β => momentKernel p β) 1) ^ 2 := by
  rw [second_deriv_momentKernel_at_one p hp]
  rw [deriv_momentKernel_at_one p hp]
  unfold varentropy
  rw [show (∑ i, Real.log (p i) * p i) =
      ∑ i, p i * Real.log (p i) by
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  have hneg : (∑ i, p i * -Real.log (p i)) =
      -(∑ i, p i * Real.log (p i)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hneg]
  ring

/-- Scalar Rényi-2 readout (collision entropy) for a finite vector. -/
noncomputable def renyiTwo {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  -Real.log (momentKernel p 2)

/-- The Rényi-2 readout is the negative logarithm of the purity sum. -/
theorem renyiTwo_eq_neg_log_collision {n : ℕ} (p : Fin n → ℝ) :
    renyiTwo p = -Real.log (∑ i, (p i) ^ 2) := by
  unfold renyiTwo
  rw [momentKernel_two]

/-! ## Normalized collision bounds

These lemmas are the finite probability-simplex boundary of the order-two
readout.  They deliberately stop at the collision moment; no logarithmic
positivity claim is needed to establish the underlying algebraic bound.
-/

theorem collisionMoment_nonneg {n : ℕ} (p : Fin n → ℝ) :
    0 ≤ ∑ i, (p i) ^ 2 := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (p i))

theorem collisionMoment_le_one {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    ∑ i, (p i) ^ 2 ≤ 1 := by
  have hle : ∀ i, p i ≤ 1 := by
    intro i
    have hi : p i ≤ ∑ j, p j := by
      exact Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
    simpa [hsum] using hi
  have hterm : ∀ i, (p i) ^ 2 ≤ p i := by
    intro i
    nlinarith [hp i, hle i]
  calc
    ∑ i, (p i) ^ 2 ≤ ∑ i, p i := Finset.sum_le_sum (fun i _ => hterm i)
    _ = 1 := hsum

theorem collisionMoment_bounds {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    0 ≤ ∑ i, (p i) ^ 2 ∧ ∑ i, (p i) ^ 2 ≤ 1 := by
  exact ⟨collisionMoment_nonneg p, collisionMoment_le_one p hp hsum⟩

theorem collisionMoment_pos {n : ℕ} (p : Fin n → ℝ)
    (hsum : ∑ i, p i = 1) :
    0 < ∑ i, (p i) ^ 2 := by
  have hzero : ∑ i, (p i) ^ 2 ≠ 0 := by
    intro h
    have hall : ∀ i, (p i) ^ 2 = 0 := by
      intro i
      have hiff := Finset.sum_eq_zero_iff_of_nonneg
        (s := Finset.univ) (f := fun j => (p j) ^ 2)
        (fun j _ => sq_nonneg (p j))
      exact (hiff.mp (by simpa using h)) i (Finset.mem_univ i)
    have hpzero : ∀ i, p i = 0 := fun i => (sq_eq_zero_iff.mp (hall i))
    have : ∑ i, p i = 0 := Finset.sum_eq_zero (fun i _ => hpzero i)
    linarith
  exact lt_of_le_of_ne (collisionMoment_nonneg p) (Ne.symm hzero)

theorem momentKernel_two_pos {n : ℕ} (p : Fin n → ℝ)
    (hsum : ∑ i, p i = 1) :
    0 < momentKernel p 2 := by
  rw [momentKernel_two]
  exact collisionMoment_pos p hsum

theorem renyiTwo_nonneg {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    0 ≤ renyiTwo p := by
  rw [renyiTwo_eq_neg_log_collision]
  exact neg_nonneg.mpr (Real.log_nonpos
    (collisionMoment_nonneg p) (collisionMoment_le_one p hp hsum))

end InfoGeometry.Canonical.RenyiFiniteOrderReadback
