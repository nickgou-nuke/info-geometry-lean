import Mathlib
import InfoGeometry.Canonical.MoebiusCore
import InfoGeometry.Canonical.FormalizationExtension

noncomputable section

namespace InfoGeometry.Canonical.MoebiusClosure

open InfoGeometry.Canonical.MoebiusCore
open InfoGeometry.Canonical.FormalizationExtension

/-- **Theorem**: SL(2, ℝ) Möbius Inversion Matrix J = [[0, -1], [1, 0]] satisfies J^2 = -I.
    This proves that the Möbius inversion action is an involution in PGL(2, ℝ). -/
theorem sl2_moebius_inversion_matrix_square :
    (Matrix.of ![![0, -1], ![1, 0]]) * (Matrix.of ![![0, -1], ![1, 0]]) = - (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **Theorem**: Discrete Multidimensional Fisher Information Metric Identity.
    ∑_{i} (∇ρ_i)^2 / ρ_i = 4 * ∑_{i} (∇ u_i)^2 where ∇ρ_i = 2 u_i ∇u_i. -/
theorem discrete_multidimensional_fisher_rao_identity
    {n : ℕ} (u du dρ : Fin n → ℝ) (hu : ∀ i, 0 < u i) (hdρ : ∀ i, dρ i = 2 * u i * du i) :
    (Finset.univ : Finset (Fin n)).sum (fun i => (dρ i)^2 / (u i)^2) =
      4 * (Finset.univ : Finset (Fin n)).sum (fun i => (du i)^2) := by
  have h_elem : ∀ i, (dρ i)^2 / (u i)^2 = 4 * (du i)^2 := by
    intro i
    have h0 := fisher_information_metric_equivalence (u i) (du i) (dρ i) (hu i) (hdρ i)
    linear_combination h0
  calc (Finset.univ : Finset (Fin n)).sum (fun i => (dρ i)^2 / (u i)^2)
    _ = (Finset.univ : Finset (Fin n)).sum (fun i => 4 * (du i)^2) := by
      congr 1
      ext i
      exact h_elem i
    _ = 4 * (Finset.univ : Finset (Fin n)).sum (fun i => (du i)^2) := by
      rw [← Finset.mul_sum]

/-- Master Möbius & Fisher-Rao Closure Synthesis Theorem.
    Unifies:
    1. SL(2, ℝ) Möbius matrix square identity J^2 = -I.
    2. Multidimensional Fisher-Rao metric identity ∑ (dρ_i)^2 / u_i^2 = 4 ∑ (du_i)^2. -/
theorem master_moebius_fisher_rao_closure_synthesis
    {n : ℕ} (u du dρ : Fin n → ℝ) (hu : ∀ i, 0 < u i) (hdρ : ∀ i, dρ i = 2 * u i * du i) :
    ((Matrix.of ![![0, -1], ![1, 0]]) * (Matrix.of ![![0, -1], ![1, 0]]) = - (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    ((Finset.univ : Finset (Fin n)).sum (fun i => (dρ i)^2 / (u i)^2) =
      4 * (Finset.univ : Finset (Fin n)).sum (fun i => (du i)^2)) := ⟨
  sl2_moebius_inversion_matrix_square,
  discrete_multidimensional_fisher_rao_identity u du dρ hu hdρ
⟩

end InfoGeometry.Canonical.MoebiusClosure
