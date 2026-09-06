import Mathlib

open Matrix

/-!
# Modular Monodromy and Parabolic Time Ticks

Lean mirror of `proofs/modular_monodromy_sympy.py`.

The modular time parameter is explicitly sheeted:

`t_n = t + n * beta`.

This keeps KMS winding/monodromy visible instead of hiding it in a single real
parameter.
-/

noncomputable section

set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false

def sheetTime (β t : ℝ) (n : ℤ) : ℝ := t + (n : ℝ) * β

theorem sheetTime_add (β t : ℝ) (n m : ℤ) :
    sheetTime β (sheetTime β t n) m = sheetTime β t (n + m) := by
  simp [sheetTime]
  ring

noncomputable def modularFactor (K β t : ℝ) (n : ℤ) : ℝ :=
  Real.exp (-K * sheetTime β t n)

noncomputable def windingMultiplier (K β : ℝ) (n : ℤ) : ℝ :=
  Real.exp (-K * ((n : ℝ) * β))

theorem modularFactor_splits (K β t : ℝ) (n : ℤ) :
    modularFactor K β t n =
      Real.exp (-K * t) * windingMultiplier K β n := by
  rw [modularFactor, windingMultiplier, sheetTime]
  rw [← Real.exp_add]
  congr 1
  ring

theorem kms_one_winding (K β t : ℝ) (n : ℤ) :
    modularFactor K β t (n + 1) =
      Real.exp (-K * β) * modularFactor K β t n := by
  rw [modularFactor, modularFactor, sheetTime, sheetTime]
  rw [← Real.exp_add]
  congr 1
  norm_num
  ring

def nilpotentN : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

noncomputable def parabolicTick (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 : Matrix (Fin 2) (Fin 2) ℝ) + t • nilpotentN

theorem nilpotentN_sq : nilpotentN * nilpotentN = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nilpotentN]

theorem parabolicTick_eq (t : ℝ) :
    parabolicTick t = !![1, t; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [parabolicTick, nilpotentN]

theorem parabolic_ticks_add (t s : ℝ) :
    parabolicTick t * parabolicTick s = parabolicTick (t + s) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parabolicTick_eq, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem parabolic_tick_inverse (t : ℝ) :
    parabolicTick t * parabolicTick (-t) = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [parabolic_ticks_add]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [parabolicTick_eq]

def boostJ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
def parityJ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

noncomputable def bogoliubovBoost (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cosh t, Real.sinh t; Real.sinh t, Real.cosh t]

theorem parity_flips_boost :
    parityJ * boostJ * parityJ = -boostJ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [parityJ, boostJ]

theorem det_bogoliubovBoost (t : ℝ) : (bogoliubovBoost t).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [bogoliubovBoost]
  simpa [pow_two] using Real.cosh_sq_sub_sinh_sq t

def quadraticPotential (θ : ℝ) : ℝ := θ ^ 2 / 2

theorem modularQuadraticPotential_gradient (θ : ℝ) :
    deriv quadraticPotential θ = θ := by
  unfold quadraticPotential
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * θ) θ := by
    simpa using hasDerivAt_pow 2 θ
  have hhalf : HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * x ^ 2)
      ((1 / 2 : ℝ) * (2 * θ)) θ :=
    hsq.const_mul (1 / 2 : ℝ)
  simpa [mul_comm, mul_left_comm, mul_assoc] using hhalf.deriv

theorem quadratic_legendre_value (p : ℝ) :
    p * p - p ^ 2 / 2 = p ^ 2 / 2 := by
  ring

noncomputable def quadraticGradientFlow (θ₀ τ : ℝ) : ℝ :=
  θ₀ * Real.exp (-τ)

theorem quadraticGradientFlow_equation (θ₀ τ : ℝ) :
    deriv (fun u => quadraticGradientFlow θ₀ u) τ +
      quadraticGradientFlow θ₀ τ = 0 := by
  unfold quadraticGradientFlow
  have h :
      deriv (fun u : ℝ => θ₀ * Real.exp (-u)) τ =
        θ₀ * (-Real.exp (-τ)) := by
    have hexp : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-τ)) τ := by
      simpa using (Real.hasDerivAt_exp (-τ)).comp τ (hasDerivAt_id τ).neg
    simpa using hexp.const_mul θ₀ |>.deriv
  rw [h]
  ring

/-- Modular monodromy theorem: sheeted KMS winding, parabolic ticks,
    Bogoliubov boost determinant, CPT boost flip, and quadratic Legendre law. -/
theorem modular_monodromy_theorem :
    (∀ β t n m, sheetTime β (sheetTime β t n) m = sheetTime β t (n + m)) ∧
    (∀ K β t n,
      modularFactor K β t n = Real.exp (-K * t) * windingMultiplier K β n) ∧
    (∀ K β t n,
      modularFactor K β t (n + 1) = Real.exp (-K * β) * modularFactor K β t n) ∧
    (∀ t s, parabolicTick t * parabolicTick s = parabolicTick (t + s)) ∧
    (∀ t, parabolicTick t * parabolicTick (-t) = 1) ∧
    parityJ * boostJ * parityJ = -boostJ ∧
    (∀ t, (bogoliubovBoost t).det = 1) ∧
    (∀ p : ℝ, p * p - p ^ 2 / 2 = p ^ 2 / 2) := by
  exact ⟨sheetTime_add, modularFactor_splits, kms_one_winding,
    parabolic_ticks_add, parabolic_tick_inverse, parity_flips_boost,
    det_bogoliubovBoost, quadratic_legendre_value⟩
