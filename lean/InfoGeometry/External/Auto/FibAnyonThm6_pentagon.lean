import Mathlib

/-══════════════════════════════════════════════════════════════════════
  FIBONACCI ANYON THEOREM 6 — FINITE F-MATRIX IDENTITIES

  This file proves finite matrix identities for the Fibonacci `F` matrix:
  `F² = I`, a padded `F₁₂³ = F₁₂` consequence, and symmetry of `F`.
  It does not formalize a full monoidal category or prove Mac Lane coherence.
-/

set_option maxHeartbeats 400000

noncomputable def tau_gr : ℝ := (Real.sqrt 5 - 1) / 2
noncomputable def s_gr : ℝ := Real.sqrt tau_gr

lemma tau_nonneg : 0 ≤ tau_gr := by
  dsimp [tau_gr]
  have h : (1 : ℝ) ≤ Real.sqrt 5 := by
    calc
      (1 : ℝ) = Real.sqrt ((1 : ℝ) ^ 2) := by norm_num
      _ ≤ Real.sqrt 5 := Real.sqrt_le_sqrt (by norm_num)
  nlinarith

lemma s_sq_eq_tau : s_gr ^ 2 = tau_gr :=
  Real.sq_sqrt tau_nonneg

lemma pentagon_condition : tau_gr ^ 2 + s_gr ^ 2 = 1 := by
  rw [s_sq_eq_tau]
  dsimp [tau_gr]
  have h5sq : Real.sqrt 5 ^ 2 = (5 : ℝ) := Real.sq_sqrt (show 0 ≤ (5 : ℝ) from by norm_num)
  nlinarith

/-- Fibonacci F-matrix = [[τ, s], [s, -τ]] -/
noncomputable def F_mat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![tau_gr, s_gr; s_gr, -tau_gr]

/-- Theorem 6a: the finite Fibonacci `F` matrix is involutive. -/
theorem fib_anyons_pentagon_eq : F_mat * F_mat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [F_mat]
  · calc
      tau_gr * tau_gr + s_gr * s_gr = tau_gr ^ 2 + s_gr ^ 2 := by ring
      _ = 1 := pentagon_condition
  · ring
  · ring
  · calc
      s_gr * s_gr + tau_gr * tau_gr = tau_gr ^ 2 + s_gr ^ 2 := by ring
      _ = 1 := pentagon_condition

/-- F₁₂ = diag(1, F) on the 3-dim fusion space -/
noncomputable def F12_mat : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1,        0,       0;
     0,    tau_gr,   s_gr;
     0,     s_gr, -tau_gr]

/-- Theorem 6b: F₁₂³ = F₁₂ (since F₁₂² = I₃). -/
theorem fib_anyons_pentagon_full : F12_mat * F12_mat * F12_mat = F12_mat := by
  have hF12sq : F12_mat * F12_mat = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [F12_mat]
    · calc
        tau_gr * tau_gr + s_gr * s_gr = tau_gr ^ 2 + s_gr ^ 2 := by ring
        _ = 1 := pentagon_condition
    · ring
    · ring
    · calc
        s_gr * s_gr + tau_gr * tau_gr = tau_gr ^ 2 + s_gr ^ 2 := by ring
        _ = 1 := pentagon_condition
  calc
    F12_mat * F12_mat * F12_mat = (F12_mat * F12_mat) * F12_mat := by rfl
    _ = (1 : Matrix (Fin 3) (Fin 3) ℝ) * F12_mat := by rw [hF12sq]
    _ = F12_mat := by simp

/-- Theorem 6c: F is symmetric. -/
theorem fib_anyons_pentagon_symmetric : F_mat.transpose = F_mat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [F_mat]
