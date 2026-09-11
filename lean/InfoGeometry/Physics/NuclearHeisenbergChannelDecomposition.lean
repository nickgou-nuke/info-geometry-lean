import InfoGeometry.Physics.NuclearGradedBathCommutant
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Physics.NuclearGradedBathCommutant

variable {A : Type*} [Ring A] [Algebra ℝ A]

def heisenbergGradeZeroChannel
    {grade : ℤ → Submodule ℝ A}
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) : A :=
  M.coupling • ⁅M.H_int_minus, q.op⁆

def heisenbergGradeOneChannel
    {grade : ℤ → Submodule ℝ A}
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) : A :=
  ⁅M.H_qp, q.op⁆ + ⁅M.H_bath, q.op⁆

def heisenbergGradeTwoChannel
    {grade : ℤ → Submodule ℝ A}
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) : A :=
  M.coupling • ⁅M.H_int_plus, q.op⁆

theorem heisenbergGradeZeroChannel_mem
    {grade : ℤ → Submodule ℝ A}
    (hgrade : LieGrading grade)
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    heisenbergGradeZeroChannel M q ∈ grade 0 := by
  exact (grade 0).smul_mem M.coupling
    (interaction_minus_grade_zero hgrade M q)

theorem heisenbergGradeOneChannel_mem
    {grade : ℤ → Submodule ℝ A}
    (hgrade : LieGrading grade)
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    heisenbergGradeOneChannel M q ∈ grade 1 := by
  exact (grade 1).add_mem
    (free_quasiparticle_grade_one hgrade M q)
    (hgrade.bracket_mem M.h_bath_grade q.grade_one)

theorem heisenbergGradeTwoChannel_mem
    {grade : ℤ → Submodule ℝ A}
    (hgrade : LieGrading grade)
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    heisenbergGradeTwoChannel M q ∈ grade 2 := by
  exact (grade 2).smul_mem M.coupling
    (interaction_plus_grade_two hgrade M q)

@[simp] theorem heisenbergGradeOneChannel_eq_qp
    {grade : ℤ → Submodule ℝ A}
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    heisenbergGradeOneChannel M q = ⁅M.H_qp, q.op⁆ := by
  simp [heisenbergGradeOneChannel, bath_bracket_quasiparticle_eq_zero M q]

theorem heisenberg_evolution_eq_channels
    {grade : ℤ → Submodule ℝ A}
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    ⁅M.totalHamiltonian, q.op⁆ =
      heisenbergGradeZeroChannel M q +
        heisenbergGradeOneChannel M q +
          heisenbergGradeTwoChannel M q := by
  dsimp [ThermalQuasiparticleModel.totalHamiltonian,
    ThermalQuasiparticleModel.interactionHamiltonian,
    heisenbergGradeZeroChannel, heisenbergGradeOneChannel,
    heisenbergGradeTwoChannel]
  rw [add_lie, add_lie, smul_lie, add_lie, smul_add]
  abel

theorem heisenberg_evolution_eq_shielded_channels
    {grade : ℤ → Submodule ℝ A}
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    ⁅M.totalHamiltonian, q.op⁆ =
      heisenbergGradeZeroChannel M q +
        ⁅M.H_qp, q.op⁆ +
          heisenbergGradeTwoChannel M q := by
  rw [heisenberg_evolution_eq_channels M q,
    heisenbergGradeOneChannel_eq_qp M q]

theorem heisenberg_evolution_decomposition
    {grade : ℤ → Submodule ℝ A}
    (hgrade : LieGrading grade)
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    ∃ c₀ c₁ c₂ : A,
      c₀ ∈ grade 0 ∧ c₁ ∈ grade 1 ∧ c₂ ∈ grade 2 ∧
        ⁅M.totalHamiltonian, q.op⁆ = c₀ + c₁ + c₂ := by
  refine ⟨heisenbergGradeZeroChannel M q,
    heisenbergGradeOneChannel M q,
    heisenbergGradeTwoChannel M q,
    heisenbergGradeZeroChannel_mem hgrade M q,
    heisenbergGradeOneChannel_mem hgrade M q,
    heisenbergGradeTwoChannel_mem hgrade M q, ?_⟩
  exact heisenberg_evolution_eq_channels M q

end InfoGeometry.Physics.NuclearGradedBathCommutant
