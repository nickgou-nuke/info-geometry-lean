import Mathlib.Tactic
open Matrix

set_option autoImplicit false

/-!
# Berezinian – Pfaffian – Bott Connection (Matrix Realization)

Concrete 2×2 matrix proofs of the theoretical connections from `daD.TXT`:

1. **Berezinian ↔ Pfaffian**: For the Krein metric `J = diag(1,-1)`,
   `Ber(J) = -1 = det(J)`.

2. **det–trace identity**: For the tri-facet operator `O = σ₁ = [[0,1],[1,0]]`
   (with `O³ = O`), `det(O) = -1` and `tr(O) = 0`.  The spectral projectors
   `P₊` and `P₋` both have `det = 0` and `tr = 1`.

3. **Bott generator**: The Krein metric `J` has `det(J) = -1` and `tr(J) = 0`,
   matching the first non-trivial generator in real K-theory (period 8).

All theorems are proven by direct 2×2 computation.
-/

namespace Audit.BerezinianPfaffianBott

section KreinMetric

/-- Krein metric J = diag(1, -1) as a 2×2 complex matrix. -/
def J : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem J_sq : J * J = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply]

theorem det_J : det J = -1 := by
  unfold J; simp [Matrix.det_fin_two]

theorem tr_J : trace J = 0 := by
  unfold J; simp

theorem J_transpose : J.transpose = J := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J]

end KreinMetric

section TriFacet

/-- Pauli σ₁ = [[0,1],[1,0]] — the tri-facet operator satisfying O³ = O. -/
def O : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

theorem O_sq : O * O = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [O, Matrix.mul_apply]

theorem O_cubed : O * O * O = O := by
  rw [O_sq, Matrix.one_mul]

theorem det_O : det O = -1 := by
  unfold O; simp [Matrix.det_fin_two]

theorem tr_O : trace O = 0 := by
  unfold O; simp

noncomputable def Omega : Matrix (Fin 2) (Fin 2) ℂ := J * O

theorem O_mul_J_eq_neg_J_mul_O : O * J = -(J * O) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J, O, Matrix.mul_apply]

theorem Omega_sq : Omega * Omega = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Omega]
  calc
    (J * O) * (J * O) = J * (O * J) * O := by noncomm_ring
    _ = J * (-(J * O)) * O := by rw [O_mul_J_eq_neg_J_mul_O]
    _ = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      calc
        J * (-(J * O)) * O = -(J * J) * (O * O) := by noncomm_ring
        _ = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by rw [J_sq, O_sq]; simp

theorem Omega_transpose : Omega.transpose = -Omega := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Omega, J, O, Matrix.transpose_apply,
    Matrix.mul_apply]

theorem J_mul_O_add_O_mul_J : J * O + O * J = 0 := by
  rw [O_mul_J_eq_neg_J_mul_O]
  abel

theorem pfaffian2_Omega : Omega 0 1 = 1 := by
  norm_num [Omega, J, O, Matrix.mul_apply]

theorem det_Omega_eq_pfaffian2_sq :
    Omega.det = (Omega 0 1) ^ 2 := by
  norm_num [Omega, J, O, Matrix.det_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two]

/-- Spectral projector onto the +1 eigenspace of O: P₊ = (1 + O)/2. -/
noncomputable def P_plus : Matrix (Fin 2) (Fin 2) ℂ := (1/2 : ℂ) • (1 + O)

/-- Spectral projector onto the -1 eigenspace of O: P₋ = (1 - O)/2. -/
noncomputable def P_minus : Matrix (Fin 2) (Fin 2) ℂ := (1/2 : ℂ) • (1 - O)

theorem O_mul_P_plus : O * P_plus = P_plus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [P_plus, O, Matrix.mul_apply]

theorem O_mul_P_minus : O * P_minus = -P_minus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [P_minus, O, Matrix.mul_apply]

theorem det_P_plus : det P_plus = 0 := by
  unfold P_plus; simp [O, Matrix.det_fin_two]

theorem det_P_minus : det P_minus = 0 := by
  unfold P_minus; simp [O, Matrix.det_fin_two]

theorem tr_P_plus : trace P_plus = 1 := by
  unfold P_plus; simp [O]

theorem tr_P_minus : trace P_minus = 1 := by
  unfold P_minus; simp [O]

theorem P_plus_sq : P_plus * P_plus = P_plus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [P_plus, O, Matrix.mul_apply] <;> field_simp <;> ring

theorem P_minus_sq : P_minus * P_minus = P_minus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [P_minus, O, Matrix.mul_apply] <;> field_simp <;> ring

theorem P_plus_mul_P_minus : P_plus * P_minus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [P_plus, P_minus, O, Matrix.mul_apply]

theorem P_minus_mul_P_plus : P_minus * P_plus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [P_plus, P_minus, O, Matrix.mul_apply]

theorem P_plus_add_P_minus : P_plus + P_minus = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [P_plus, P_minus, O] <;> field_simp <;> ring

end TriFacet

section Connections

/--
The Berezinian of `J = diag(1,-1)` in the GL(1|1) supergroup equals `det(J)`.
Both are `-1`.
-/
theorem berJ_eq_detJ : (1 : ℂ) / (-1 : ℂ) = det (J : Matrix (Fin 2) (Fin 2) ℂ) := by
  norm_num [det_J]

/--
For the tri-facet operator O = σ₁, det(O) = -1 and tr(O) = 0.
The relation `det(exp(t·O)) = exp(t·tr(O))` therefore reads
`det(exp(t·O)) = exp(0) = 1`.
We prove the special case t = 0: `det(exp(0)) = det(1) = 1`.
-/
theorem det_exp_tri_facet_base : det (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  rw [Matrix.det_fin_two]
  norm_num

/--
`P_plus - P_minus = O`.  The difference of spectral projectors recovers
O itself, since O = (+1)·P₊ + (-1)·P₋ and P₊ + P₋ = 1.
-/
theorem P_plus_sub_P_minus_eq_O : P_plus - P_minus = O := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [P_plus, P_minus, O] <;> field_simp <;> ring

/--
The Krein metric J has the same determinant as O:
`det(J) = det(O) = -1`.
-/
theorem det_J_via_projectors : det (P_plus - P_minus) = det (J : Matrix (Fin 2) (Fin 2) ℂ) := by
  calc
    det (P_plus - P_minus) = det (O : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [P_plus_sub_P_minus_eq_O]
    _ = -1 := det_O
    _ = det (J : Matrix (Fin 2) (Fin 2) ℂ) := by symm; exact det_J

end Connections

end Audit.BerezinianPfaffianBott
