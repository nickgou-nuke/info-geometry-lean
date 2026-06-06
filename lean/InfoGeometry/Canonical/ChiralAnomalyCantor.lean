import Mathlib
open Matrix Complex

noncomputable section

axiom tilt : Matrix (Fin 2) (Fin 2) ℂ
axiom tilt_sq : tilt ^ 2 = 1
axiom D : Matrix (Fin 2) (Fin 2) ℂ
axiom D_anticomm_tilt : D * tilt + tilt * D = 0

structure KTheoryProjection (n : ℕ) where
  e : Matrix (Fin n) (Fin n) ℂ
  is_idempotent : e * e = e

def cyclic_0_cocycle (A : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  Matrix.trace (tilt * A)

noncomputable def index_pairing (proj : KTheoryProjection 2) : ℂ :=
  cyclic_0_cocycle proj.e

lemma trace_rot (A B C : Matrix (Fin 2) (Fin 2) ℂ) : (A * B * C).trace = (B * C * A).trace := by
  calc
    (A * B * C).trace = ((A * B) * C).trace := by simp [mul_assoc]
    _ = (C * (A * B)).trace := Matrix.trace_mul_comm (A * B) C
    _ = (C * A * B).trace := by simp [mul_assoc]
    _ = (B * (C * A)).trace := (Matrix.trace_mul_comm B (C * A)).symm
    _ = (B * C * A).trace := by simp [mul_assoc]

theorem chiral_anomaly_vanishes_at_flat_boundary (proj : KTheoryProjection 2)
    (h_comm : D * proj.e = proj.e * D)
    (h_Dinv : ∃ D_inv, D * D_inv = 1 ∧ D_inv * D = 1) :
    index_pairing proj = 0 := by
  rcases h_Dinv with ⟨D_inv, hD_Dinv, hDinv_D⟩
  unfold index_pairing cyclic_0_cocycle
  have h_anticomm : D * tilt = -(tilt * D) := by
    calc
      D * tilt = (D * tilt + tilt * D) - (tilt * D) := by simp
      _ = 0 - (tilt * D) := by rw [D_anticomm_tilt]
      _ = -(tilt * D) := by simp
  have h_tilt_D : tilt * D = -(D * tilt) := by
    calc
      tilt * D = (tilt * D + D * tilt) - (D * tilt) := by simp
      _ = (D * tilt + tilt * D) - (D * tilt) := by abel
      _ = 0 - (D * tilt) := by rw [D_anticomm_tilt]
      _ = -(D * tilt) := by simp
  have h_comm_tilt_e_D : tilt * proj.e * D = -(D * tilt * proj.e) := by
    calc
      tilt * proj.e * D = tilt * (proj.e * D) := by simp [mul_assoc]
      _ = tilt * (D * proj.e) := by rw [h_comm]
      _ = (tilt * D) * proj.e := by simp [mul_assoc]
      _ = (-(D * tilt)) * proj.e := by rw [h_tilt_D]
      _ = -(D * tilt * proj.e) := by simp [mul_assoc]
  have hτ_neg : Matrix.trace (tilt * proj.e) = -Matrix.trace (tilt * proj.e) := by
    calc
      Matrix.trace (tilt * proj.e) = Matrix.trace ((tilt * proj.e) * (D * D_inv)) := by
        simp [hD_Dinv]
      _ = Matrix.trace ((tilt * proj.e * D) * D_inv) := by simp [mul_assoc]
      _ = Matrix.trace ((-(D * tilt * proj.e)) * D_inv) := by rw [h_comm_tilt_e_D]
      _ = -Matrix.trace (D * tilt * proj.e * D_inv) := by simp
      _ = -Matrix.trace ((D * (tilt * proj.e)) * D_inv) := by simp [mul_assoc]
      _ = -Matrix.trace ((tilt * proj.e) * D_inv * D) := by
        rw [trace_rot D (tilt * proj.e) D_inv]
      _ = -Matrix.trace (tilt * proj.e * (D_inv * D)) := by simp [mul_assoc]
      _ = -Matrix.trace (tilt * proj.e * 1) := by rw [hDinv_D]
      _ = -Matrix.trace (tilt * proj.e) := by simp
  have h_sum : Matrix.trace (tilt * proj.e) + Matrix.trace (tilt * proj.e) = 0 := by
    calc
      Matrix.trace (tilt * proj.e) + Matrix.trace (tilt * proj.e) =
        Matrix.trace (tilt * proj.e) + (-Matrix.trace (tilt * proj.e)) := by
          nth_rw 2 [hτ_neg]
      _ = 0 := by simp
  have h2 : (2 : ℂ) * Matrix.trace (tilt * proj.e) = 0 := by
    calc
      (2 : ℂ) * Matrix.trace (tilt * proj.e) = Matrix.trace (tilt * proj.e) + Matrix.trace (tilt * proj.e) := by ring
      _ = 0 := by rw [h_sum]
  have h2_nz : (2 : ℂ) ≠ 0 := by norm_num
  rcases mul_eq_zero.mp h2 with (h2z | hz)
  · exact absurd h2z h2_nz
  · exact hz
