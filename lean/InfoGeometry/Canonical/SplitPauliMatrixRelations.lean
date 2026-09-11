import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

/-- 1. Матрично Представяне на 4D Сплит-Кватернионната Алгебра Cl(1,1) ≅ M₂(ℝ) -/
def I_2 : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 0], ![0, 1]]
def L_2 : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 0], ![0, -1]]   -- l  (σ_z)
def I_comp : Matrix (Fin 2) (Fin 2) ℝ := ![![0, -1], ![1, 0]]-- i  (-iσ_y)
def IL_comp : Matrix (Fin 2) (Fin 2) ℝ := ![![0, 1], ![1, 0]] -- il (σ_x)

/-- Теорема 1: Компактното въртене i² = -1 в M₂(ℝ) -/
theorem I_comp_sq : I_comp * I_comp = -I_2 := by
  ext i j; fin_cases i <;> fin_cases j <;> 
  simp [I_2, I_comp, Matrix.mul_apply, Fin.sum_univ_two]

/-- Теорема 2: Хиперболичният буст (il)² = +1 в M₂(ℝ) -/
theorem IL_comp_sq : IL_comp * IL_comp = I_2 := by
  ext i j; fin_cases i <;> fin_cases j <;> 
  simp [I_2, IL_comp, Matrix.mul_apply, Fin.sum_univ_two]

/-- Теорема 3: Часовниковата ос l² = +1 в M₂(ℝ) -/
theorem L_2_sq : L_2 * L_2 = I_2 := by
  ext i j; fin_cases i <;> fin_cases j <;> 
  simp [I_2, L_2, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Теорема 4 (Комутаторното Затваряне)**: [i, il] = -2l в M₂(ℝ). -/
theorem split_pauli_matrix_commutator :
    I_comp * IL_comp - IL_comp * I_comp = (-2 : ℝ) • L_2 := by
  ext i j; fin_cases i <;> fin_cases j <;> 
  simp [L_2, I_comp, IL_comp, Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Fin.sum_univ_two] <;> ring

/-- **Master Synthesis**: Cl(1,1) ≅ M₂(ℝ) Сплит-Паули Затваряне Synthesis. -/
theorem master_split_pauli_matrix_relations :
    (I_comp * I_comp = -I_2) ∧
    (IL_comp * IL_comp = I_2) ∧
    (I_comp * IL_comp - IL_comp * I_comp = (-2 : ℝ) • L_2) := ⟨
  I_comp_sq,
  IL_comp_sq,
  split_pauli_matrix_commutator
⟩

end InfoGeometry.Canonical
