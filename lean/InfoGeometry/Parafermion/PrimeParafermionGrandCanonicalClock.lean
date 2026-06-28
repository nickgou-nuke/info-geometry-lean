import Mathlib

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Parafermion

def localParafermionFactor (κ : ℕ) (x : ℝ) : ℝ :=
  Finset.sum (Finset.range κ) (fun j => x ^ j)

def stateProbability (κ : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  x ^ n / localParafermionFactor κ x

def stateSurprisal (κ : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  -Real.log (stateProbability κ x n)

def parafermionMassieu (κ : ℕ) (x : ℝ) : ℝ :=
  Real.log (localParafermionFactor κ x)

def parafermionGrandPotential (κ : ℕ) (x β : ℝ) : ℝ :=
  -β⁻¹ * parafermionMassieu κ x

def Q_kappa (κ : ℕ) (x : ℝ) : ℝ :=
  localParafermionFactor κ x

@[simp]
theorem localParafermionFactor_zero (x : ℝ) :
    localParafermionFactor 0 x = 0 := by
  simp [localParafermionFactor]

@[simp]
theorem localParafermionFactor_one (x : ℝ) :
    localParafermionFactor 1 x = 1 := by
  simp [localParafermionFactor]

theorem localParafermionFactor_succ (κ : ℕ) (x : ℝ) :
    localParafermionFactor (κ + 1) x = localParafermionFactor κ x + x ^ κ := by
  simp [localParafermionFactor, Finset.sum_range_succ]

theorem localParafermionFactor_eq_quotient {κ : ℕ} {x : ℝ} (hx : x ≠ 1) :
    localParafermionFactor κ x = (1 - x ^ κ) / (1 - x) := by
  have hmul : localParafermionFactor κ x * (1 - x) = 1 - x ^ κ := by
    simpa [localParafermionFactor, mul_comm, mul_left_comm, mul_assoc] using
      geom_sum_mul_neg x κ
  have hden : (1 - x) ≠ 0 := sub_ne_zero.mpr (by intro h; exact hx h.symm)
  exact (eq_div_iff hden).2 hmul

@[simp]
theorem localParafermionFactor_two (x : ℝ) :
    localParafermionFactor 2 x = 1 + x := by
  simp [localParafermionFactor, Finset.sum_range_succ]

@[simp]
theorem localParafermionFactor_three (x : ℝ) :
    localParafermionFactor 3 x = 1 + x + x ^ 2 := by
  simp [localParafermionFactor, Finset.sum_range_succ, pow_two]

@[simp]
theorem stateProbability_two (x : ℝ) (n : ℕ) :
    stateProbability 2 x n = x ^ n / (1 + x) := by
  simp [stateProbability]

@[simp]
theorem stateProbability_three (x : ℝ) (n : ℕ) :
    stateProbability 3 x n = x ^ n / (1 + x + x ^ 2) := by
  simp [stateProbability]

theorem stateSurprisal_eq_massieu_sub_log_weight
    {κ : ℕ} {x : ℝ} (n : ℕ)
    (hx : 0 < x) (hQ : 0 < localParafermionFactor κ x) :
    stateSurprisal κ x n =
      parafermionMassieu κ x - n * Real.log x := by
  unfold stateSurprisal stateProbability parafermionMassieu
  rw [Real.log_div (pow_pos hx n).ne' hQ.ne', Real.log_pow x n]
  ring

@[simp]
theorem parafermionGrandPotential_eq (κ : ℕ) (x β : ℝ) :
    parafermionGrandPotential κ x β = -β⁻¹ * parafermionMassieu κ x := by
  rfl

@[simp]
theorem ln_Q_is_massieu (κ : ℕ) (x : ℝ) :
    Real.log (Q_kappa κ x) = parafermionMassieu κ x := by
  rfl

@[simp]
theorem Q_kappa_eq_localParafermionFactor (κ : ℕ) (x : ℝ) :
    Q_kappa κ x = localParafermionFactor κ x := by
  rfl

end InfoGeometry.Parafermion
