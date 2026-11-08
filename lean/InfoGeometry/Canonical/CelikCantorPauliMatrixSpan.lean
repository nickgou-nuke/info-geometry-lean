import InfoGeometry.Canonical.CelikCantorPauliJ
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Matrix closure of the rank-one Pauli packet

This owner proves the explicit coordinate decomposition of every complex
`2 × 2` matrix in the Pauli basis `{1, U, V, U * V}`.  It is a concrete
linear-spanning theorem, not yet a universal Clifford-algebra equivalence.
-/

noncomputable section

namespace InfoGeometry.Canonical.CelikCantorPauliMatrixSpan

open InfoGeometry.Canonical.CelikCantorClifford

theorem pauli_coordinate_decomposition
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A =
      ((A 0 0 + A 1 1) / 2) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      ((A 0 0 - A 1 1) / 2) • U +
      ((A 0 1 + A 1 0) / 2) • V +
      ((A 0 1 - A 1 0) / 2) • (U * V) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [U, V, Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply,
      Fin.sum_univ_two]
    <;> ring

theorem pauli_coordinate_decomposition_unique
    (a b c d : ℂ)
    (h : a • (1 : Matrix (Fin 2) (Fin 2) ℂ) + b • U + c • V + d • (U * V) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have h00 := congr_fun (congr_fun h 0) 0
  have h01 := congr_fun (congr_fun h 0) 1
  have h10 := congr_fun (congr_fun h 1) 0
  have h11 := congr_fun (congr_fun h 1) 1
  simp [U, V, Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply,
    Fin.sum_univ_two] at h00 h01 h10 h11
  constructor
  · linear_combination (1 / 2 : ℂ) * h00 + (1 / 2 : ℂ) * h11
  constructor
  · linear_combination (1 / 2 : ℂ) * h00 - (1 / 2 : ℂ) * h11
  constructor
  · linear_combination (1 / 2 : ℂ) * h01 + (1 / 2 : ℂ) * h10
  · linear_combination (1 / 2 : ℂ) * h01 - (1 / 2 : ℂ) * h10

theorem pauli_packet_linearly_independent :
    LinearIndependent ℂ ![(1 : Matrix (Fin 2) (Fin 2) ℂ), U, V, U * V] := by
  apply Fintype.linearIndependent_iff.mpr
  intro l hsum i
  fin_cases i
  · apply (pauli_coordinate_decomposition_unique (l 0) (l 1) (l 2) (l 3) ?_).1
    simpa [Fin.sum_univ_four] using hsum
  · apply (pauli_coordinate_decomposition_unique (l 0) (l 1) (l 2) (l 3) ?_).2.1
    simpa [Fin.sum_univ_four] using hsum
  · apply (pauli_coordinate_decomposition_unique (l 0) (l 1) (l 2) (l 3) ?_).2.2.1
    simpa [Fin.sum_univ_four] using hsum
  · apply (pauli_coordinate_decomposition_unique (l 0) (l 1) (l 2) (l 3) ?_).2.2.2
    simpa [Fin.sum_univ_four] using hsum

/-- The two Pauli generators generate the full matrix algebra. -/
theorem algebra_adjoin_U_V_eq_top :
    Algebra.adjoin ℂ
        ({U, V} : Set (Matrix (Fin 2) (Fin 2) ℂ)) = ⊤ := by
  apply top_unique
  intro A hA
  rw [pauli_coordinate_decomposition A]
  let S := Algebra.adjoin ℂ
      ({U, V} : Set (Matrix (Fin 2) (Fin 2) ℂ))
  have hU : U ∈ S := Algebra.subset_adjoin (by simp [S])
  have hV : V ∈ S := Algebra.subset_adjoin (by simp [S])
  have hUV : U * V ∈ S := S.mul_mem hU hV
  have h1 : (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ S := S.one_mem
  exact S.add_mem
    (S.add_mem
      (S.add_mem (S.smul_mem h1 _) (S.smul_mem hU _))
      (S.smul_mem hV _))
    (S.smul_mem hUV _)

end InfoGeometry.Canonical.CelikCantorPauliMatrixSpan
