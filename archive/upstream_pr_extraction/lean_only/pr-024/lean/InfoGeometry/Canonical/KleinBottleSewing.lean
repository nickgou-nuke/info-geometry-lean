import Mathlib
open Matrix Complex

noncomputable section

/-- Concrete Pauli-`Z` sewing tilt. -/
def tilt : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-- Concrete Pauli-`X` sewing switch. -/
def switch : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

lemma tilt_sq : tilt ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tilt, pow_two, Matrix.mul_apply]

lemma switch_sq : switch ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [switch, pow_two, Matrix.mul_apply]

lemma tilt_switch_anticomm : tilt * switch = -(switch * tilt) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tilt, switch, Matrix.mul_apply]

structure BoundaryState where
  rho : Matrix (Fin 2) (Fin 2) ℂ
  is_hermitian : rho.conjTranspose = rho
  trace_one : Matrix.trace rho = 1

def isSewn (s : BoundaryState) : Prop :=
  switch * s.rho * switch = s.rho

lemma trace_rot (A B C : Matrix (Fin 2) (Fin 2) ℂ) : (A * B * C).trace = (B * C * A).trace := by
  calc
    (A * B * C).trace = ((A * B) * C).trace := by simp [mul_assoc]
    _ = (C * (A * B)).trace := Matrix.trace_mul_comm (A * B) C
    _ = (C * A * B).trace := by simp [mul_assoc]
    _ = (B * (C * A)).trace := (Matrix.trace_mul_comm B (C * A)).symm
    _ = (B * C * A).trace := by simp [mul_assoc]

noncomputable def chiralIndex (s : BoundaryState) : ℂ :=
  Matrix.trace (tilt * s.rho)

theorem klein_throat_anomaly_vanishes (s : BoundaryState) (h_sewn : isSewn s) :
    chiralIndex s = 0 := by
  unfold chiralIndex
  unfold isSewn at h_sewn
  -- h_sewn: switch * s.rho * switch = s.rho
  have h_anticomm_sw_tilt : switch * tilt = -(tilt * switch) := by
    calc
      switch * tilt = -(-(switch * tilt)) := by simp
      _ = -(tilt * switch) := by rw [← tilt_switch_anticomm]
  have hτ_neg : Matrix.trace (tilt * s.rho) = -Matrix.trace (tilt * s.rho) := by
    have step1 : Matrix.trace (tilt * s.rho) = Matrix.trace (tilt * s.rho * switch * switch) := by
      calc
        Matrix.trace (tilt * s.rho) = Matrix.trace ((tilt * s.rho) * 1) := by simp
        _ = Matrix.trace ((tilt * s.rho) * (switch ^ 2)) := by rw [switch_sq]
        _ = Matrix.trace ((tilt * s.rho) * (switch * switch)) := by simp [sq]
        _ = Matrix.trace (tilt * s.rho * switch * switch) := by simp [mul_assoc]
    have step2 : Matrix.trace (tilt * s.rho * switch * switch) = Matrix.trace (switch * tilt * s.rho * switch) := by
      calc
        Matrix.trace (tilt * s.rho * switch * switch) = Matrix.trace (switch * (tilt * s.rho * switch)) := by
          simpa [mul_assoc] using (trace_rot switch (tilt * s.rho) switch).symm
        _ = Matrix.trace (switch * tilt * s.rho * switch) := by simp [mul_assoc]
    have step3 : Matrix.trace (switch * tilt * s.rho * switch) = -Matrix.trace (tilt * switch * s.rho * switch) := by
      calc
        Matrix.trace (switch * tilt * s.rho * switch) = Matrix.trace ((-(tilt * switch)) * s.rho * switch) := by
          rw [h_anticomm_sw_tilt]
        _ = -Matrix.trace (tilt * switch * s.rho * switch) := by simp
    have step4 : -Matrix.trace (tilt * switch * s.rho * switch) = -Matrix.trace (tilt * s.rho) := by
      calc
        -Matrix.trace (tilt * switch * s.rho * switch) = -Matrix.trace (tilt * (switch * s.rho * switch)) := by
          simp [mul_assoc]
        _ = -Matrix.trace (tilt * s.rho) := by rw [h_sewn]
    calc
      Matrix.trace (tilt * s.rho) = Matrix.trace (tilt * s.rho * switch * switch) := step1
      _ = Matrix.trace (switch * tilt * s.rho * switch) := step2
      _ = -Matrix.trace (tilt * switch * s.rho * switch) := step3
      _ = -Matrix.trace (tilt * s.rho) := step4
  have h_sum : Matrix.trace (tilt * s.rho) + Matrix.trace (tilt * s.rho) = 0 := by
    calc
      Matrix.trace (tilt * s.rho) + Matrix.trace (tilt * s.rho) =
        Matrix.trace (tilt * s.rho) + (-Matrix.trace (tilt * s.rho)) := by nth_rw 2 [hτ_neg]
      _ = 0 := by simp
  have h2 : (2 : ℂ) * Matrix.trace (tilt * s.rho) = 0 := by
    calc
      (2 : ℂ) * Matrix.trace (tilt * s.rho) = Matrix.trace (tilt * s.rho) + Matrix.trace (tilt * s.rho) := by ring
      _ = 0 := by rw [h_sum]
  have h2_nz : (2 : ℂ) ≠ 0 := by norm_num
  rcases mul_eq_zero.mp h2 with (h2z | hz)
  · exact absurd h2z h2_nz
  · exact hz
