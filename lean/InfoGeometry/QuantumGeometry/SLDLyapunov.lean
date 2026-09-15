import InfoGeometry.QuantumGeometry.NoncommutativeSLDFisherMetric
import Mathlib.Analysis.Matrix.PosDef

noncomputable section

namespace InfoGeometry.QuantumGeometry.SLD

open scoped ComplexOrder

variable {Index : Type*} [Fintype Index] [DecidableEq Index]

def diagonalSLD (weights : Index → ℝ) (variation : Matrix Index Index ℂ) :
    Matrix Index Index ℂ :=
  fun row column => 2 * variation row column / (weights row + weights column : ℂ)

theorem isSLD_diagonal_iff (weights : Index → ℝ)
    (positive : ∀ index, 0 < weights index) (variation score : Matrix Index Index ℂ) :
    IsSLD (Matrix.diagonal (fun index => (weights index : ℂ))) variation score ↔
      score = diagonalSLD weights variation := by
  have denominator (row column : Index) : (weights row + weights column : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (add_pos (positive row) (positive column)))
  constructor
  · intro equation
    ext row column
    have entry := congrArg (fun matrix : Matrix Index Index ℂ => matrix row column) equation
    simp only [jordanProd, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
      Matrix.diagonal_mul, Matrix.mul_diagonal] at entry
    change score row column = 2 * variation row column / (weights row + weights column : ℂ)
    apply (eq_div_iff (denominator row column)).mpr
    linear_combination -2 * entry
  · rintro rfl
    unfold IsSLD jordanProd
    ext row column
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
      Matrix.diagonal_mul, Matrix.mul_diagonal, diagonalSLD]
    field_simp [denominator row column]

omit [DecidableEq Index] in
theorem isSLD_equiv_iff (equivalence : Matrix Index Index ℂ ≃⋆ₐ[ℂ] Matrix Index Index ℂ)
    (density variation score : Matrix Index Index ℂ) :
    IsSLD (equivalence density) (equivalence variation) (equivalence score) ↔
      IsSLD density variation score := by
  unfold IsSLD jordanProd
  rw [← map_mul, ← map_mul, ← map_add, ← map_smul]
  exact equivalence.injective.eq_iff

theorem existsUnique_sld_of_posDef (density variation : Matrix Index Index ℂ)
    (positive : density.PosDef) :
    ∃! score, IsSLD density variation score := by
  let equivalence := Unitary.conjStarAlgAut ℂ _ (star positive.isHermitian.eigenvectorUnitary)
  have diagonalized : equivalence density =
      Matrix.diagonal (fun index => (positive.isHermitian.eigenvalues index : ℂ)) :=
    positive.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  let score := diagonalSLD positive.isHermitian.eigenvalues (equivalence variation)
  have solves : IsSLD (equivalence density) (equivalence variation) score := by
    rw [diagonalized]
    exact (isSLD_diagonal_iff _ positive.eigenvalues_pos _ _).mpr rfl
  refine ⟨equivalence.symm score, ?_, ?_⟩
  · apply (isSLD_equiv_iff equivalence density variation _).mp
    simpa using solves
  · intro candidate candidate_solves
    apply equivalence.injective
    change equivalence candidate = equivalence (equivalence.symm score)
    rw [equivalence.apply_symm_apply]
    have transported := (isSLD_equiv_iff equivalence density variation candidate).mpr
      candidate_solves
    rw [diagonalized] at transported
    exact (isSLD_diagonal_iff _ positive.eigenvalues_pos _ _).mp transported

omit [DecidableEq Index] in
theorem isSLD_star (density variation score : Matrix Index Index ℂ)
    (density_self : star density = density) (variation_self : star variation = variation)
    (solves : IsSLD density variation score) :
    IsSLD density variation (star score) := by
  have conjugated := congrArg star solves
  simpa [IsSLD, jordanProd, star_smul, density_self, variation_self, add_comm] using conjugated

theorem existsUnique_selfAdjoint_sld (density variation : Matrix Index Index ℂ)
    (positive : density.PosDef) (variation_self : star variation = variation) :
    ∃! score, IsSLD density variation score ∧ star score = score := by
  obtain ⟨score, solves, unique⟩ := existsUnique_sld_of_posDef density variation positive
  refine ⟨score, ⟨solves, ?_⟩, fun candidate candidate_solves => unique candidate candidate_solves.1⟩
  exact unique (star score) (isSLD_star density variation score
    positive.isHermitian.eq variation_self solves)

end InfoGeometry.QuantumGeometry.SLD
