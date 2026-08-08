import proofs.Clifford55

open Clifford55

@[simp] theorem e_pos_ortho_e_pos (i j : Fin 5) (h : i ≠ j) : Q55.IsOrtho (e_pos i) (e_pos j) := by
  simp [QuadraticMap.isOrtho_def, Q55, e_pos]
  intro k
  split
  · split
    · subst_vars; contradiction
    · rfl
  · rfl

theorem e_pos_anticomm (i j : Fin 5) (h : i ≠ j) :
    ι55 (e_pos i) * ι55 (e_pos j) = - ι55 (e_pos j) * ι55 (e_pos i) := by
  have := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho (Q := Q55) (e_pos_ortho_e_pos i j h)
  linarith

-- I can write the explicit sequence of swaps for R_P_sq.
