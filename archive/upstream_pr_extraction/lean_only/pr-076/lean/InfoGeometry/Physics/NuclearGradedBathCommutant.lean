import Mathlib

noncomputable section

namespace InfoGeometry.Physics.NuclearGradedBathCommutant

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The associative commutant of an intrinsic nuclear/bath subalgebra. -/
noncomputable def bathCommutant
    (bath : Subalgebra ℝ A) : Subalgebra ℝ A :=
  Subalgebra.centralizer ℝ (bath : Set A)

@[simp] theorem mem_bathCommutant_iff
    (bath : Subalgebra ℝ A) (x : A) :
    x ∈ bathCommutant bath ↔
      ∀ b : A, b ∈ bath → b * x = x * b := by
  exact Subalgebra.mem_centralizer_iff ℝ

theorem bath_element_lie_eq_zero
    (bath : Subalgebra ℝ A) {b x : A}
    (hb : b ∈ bath)
    (hx : x ∈ bathCommutant bath) :
    ⁅b, x⁆ = 0 := by
  change b * x - x * b = 0
  rw [(mem_bathCommutant_iff bath x).mp hx b hb, sub_self]

theorem commutant_element_lie_bath_eq_zero
    (bath : Subalgebra ℝ A) {b x : A}
    (hb : b ∈ bath)
    (hx : x ∈ bathCommutant bath) :
    ⁅x, b⁆ = 0 := by
  change x * b - b * x = 0
  rw [(mem_bathCommutant_iff bath x).mp hx b hb, sub_self]

theorem commutator_mem_bathCommutant
    (bath : Subalgebra ℝ A) {x y : A}
    (hx : x ∈ bathCommutant bath)
    (hy : y ∈ bathCommutant bath) :
    x * y - y * x ∈ bathCommutant bath := by
  exact (bathCommutant bath).sub_mem
    ((bathCommutant bath).mul_mem hx hy)
    ((bathCommutant bath).mul_mem hy hx)

theorem lie_mem_bathCommutant
    (bath : Subalgebra ℝ A) {x y : A}
    (hx : x ∈ bathCommutant bath)
    (hy : y ∈ bathCommutant bath) :
    ⁅x, y⁆ ∈ bathCommutant bath := by
  change x * y - y * x ∈ bathCommutant bath
  exact commutator_mem_bathCommutant bath hx hy

/-- The version-independent grading law needed by the pinned Mathlib API. -/
structure LieGrading (grade : ℤ → Submodule ℝ A) : Prop where
  bracket_mem :
    ∀ {i j : ℤ} {x y : A},
      x ∈ grade i → y ∈ grade j → ⁅x, y⁆ ∈ grade (i + j)

def gradedBathCommutant
    (grade : ℤ → Submodule ℝ A)
    (bath : Subalgebra ℝ A)
    (i : ℤ) : Submodule ℝ A :=
  grade i ⊓ (bathCommutant bath).toSubmodule

theorem gradedBathCommutant_bracket
    (grade : ℤ → Submodule ℝ A)
    (hgrade : LieGrading grade)
    (bath : Subalgebra ℝ A)
    {i j : ℤ} {x y : A}
    (hx : x ∈ gradedBathCommutant grade bath i)
    (hy : y ∈ gradedBathCommutant grade bath j) :
    ⁅x, y⁆ ∈ gradedBathCommutant grade bath (i + j) := by
  constructor
  · exact hgrade.bracket_mem hx.1 hy.1
  · exact lie_mem_bathCommutant bath hx.2 hy.2

structure ThermalQuasiparticleModel
    (grade : ℤ → Submodule ℝ A) where
  bath : Subalgebra ℝ A
  H_bath : A
  H_qp : A
  H_int_minus : A
  H_int_plus : A
  coupling : ℝ
  h_bath_mem : H_bath ∈ bath
  h_bath_grade : H_bath ∈ grade 0
  h_qp_mem : H_qp ∈ bathCommutant bath
  h_qp_grade : H_qp ∈ grade 0
  h_int_minus_grade : H_int_minus ∈ grade (-1)
  h_int_plus_grade : H_int_plus ∈ grade 1

namespace ThermalQuasiparticleModel

variable {grade : ℤ → Submodule ℝ A}

def interactionHamiltonian
    (M : ThermalQuasiparticleModel grade) : A :=
  M.H_int_minus + M.H_int_plus

def totalHamiltonian
    (M : ThermalQuasiparticleModel grade) : A :=
  M.H_qp + M.H_bath + M.coupling • M.interactionHamiltonian

theorem interactionHamiltonian_mem
    (M : ThermalQuasiparticleModel grade) :
    M.interactionHamiltonian ∈ grade (-1) ⊔ grade 1 := by
  exact Submodule.add_mem_sup M.h_int_minus_grade M.h_int_plus_grade

end ThermalQuasiparticleModel

structure QuasiparticleCreation
    (grade : ℤ → Submodule ℝ A)
    (M : ThermalQuasiparticleModel grade) where
  op : A
  mem_commutant : op ∈ bathCommutant M.bath
  grade_one : op ∈ grade 1

theorem QuasiparticleCreation.mem_gradedBathCommutant
    {grade : ℤ → Submodule ℝ A}
    {M : ThermalQuasiparticleModel grade}
    (q : QuasiparticleCreation grade M) :
    q.op ∈ gradedBathCommutant grade M.bath 1 :=
  ⟨q.grade_one, q.mem_commutant⟩

theorem bath_bracket_quasiparticle_eq_zero
    {grade : ℤ → Submodule ℝ A}
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    ⁅M.H_bath, q.op⁆ = 0 :=
  bath_element_lie_eq_zero M.bath M.h_bath_mem q.mem_commutant

theorem quasiparticle_eom
    {grade : ℤ → Submodule ℝ A}
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    ⁅M.totalHamiltonian, q.op⁆ =
      ⁅M.H_qp, q.op⁆ +
        M.coupling • ⁅M.interactionHamiltonian, q.op⁆ := by
  unfold ThermalQuasiparticleModel.totalHamiltonian
  rw [add_lie, add_lie, bath_bracket_quasiparticle_eq_zero M q,
    add_zero, smul_lie]

theorem free_quasiparticle_grade_one
    {grade : ℤ → Submodule ℝ A}
    (hgrade : LieGrading grade)
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    ⁅M.H_qp, q.op⁆ ∈ grade 1 := by
  have h := hgrade.bracket_mem M.h_qp_grade q.grade_one
  simpa using h

theorem interaction_minus_grade_zero
    {grade : ℤ → Submodule ℝ A}
    (hgrade : LieGrading grade)
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    ⁅M.H_int_minus, q.op⁆ ∈ grade 0 := by
  have h := hgrade.bracket_mem M.h_int_minus_grade q.grade_one
  simpa using h

theorem interaction_plus_grade_two
    {grade : ℤ → Submodule ℝ A}
    (hgrade : LieGrading grade)
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    ⁅M.H_int_plus, q.op⁆ ∈ grade 2 := by
  have h := hgrade.bracket_mem M.h_int_plus_grade q.grade_one
  simpa using h

theorem interaction_bracket_grade_zero_sup_two
    {grade : ℤ → Submodule ℝ A}
    (hgrade : LieGrading grade)
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    ⁅M.interactionHamiltonian, q.op⁆ ∈ grade 0 ⊔ grade 2 := by
  rw [ThermalQuasiparticleModel.interactionHamiltonian, add_lie]
  exact Submodule.add_mem_sup
    (interaction_minus_grade_zero hgrade M q)
    (interaction_plus_grade_two hgrade M q)

theorem total_eom_grade_support
    {grade : ℤ → Submodule ℝ A}
    (hgrade : LieGrading grade)
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    ⁅M.totalHamiltonian, q.op⁆ ∈ grade 1 ⊔ (grade 0 ⊔ grade 2) := by
  rw [quasiparticle_eom M q]
  exact Submodule.add_mem_sup
    (free_quasiparticle_grade_one hgrade M q)
    ((grade 0 ⊔ grade 2).smul_mem M.coupling
      (interaction_bracket_grade_zero_sup_two hgrade M q))

end InfoGeometry.Physics.NuclearGradedBathCommutant
