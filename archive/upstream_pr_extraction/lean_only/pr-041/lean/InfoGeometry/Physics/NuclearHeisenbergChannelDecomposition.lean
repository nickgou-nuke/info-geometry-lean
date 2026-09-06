import InfoGeometry.Physics.NuclearGradedBathCommutant

/-!
# Graded Heisenberg channels for the nuclear quasiparticle model

This file refines the equation of motion from
`NuclearGradedBathCommutant` into explicit degree-zero, degree-one, and
degree-two channels.

For

`H = H_qp + H_bath + λ (H_int,-1 + H_int,+1)`

and a degree-one quasiparticle creation observable `q`, the commutator is
written exactly as

`[H,q] = c₀ + c₁ + c₂`,

where

* `c₀ = λ [H_int,-1,q]` has degree zero;
* `c₁ = [H_qp,q] + [H_bath,q]` has degree one;
* `c₂ = λ [H_int,+1,q]` has degree two.

Because `q` belongs to the associative bath commutant, the bath summand in
`c₁` is subsequently proved to vanish.  The degree-two result is an algebraic
channel-selection theorem only: identifying a concrete degree-two subspace
with a QPNM phonon or pairing representation requires a separate bridge.
-/

set_option autoImplicit false

namespace InfoGeometry.Physics.NuclearGradedBathCommutant

variable {R A : Type*}
variable [CommRing R] [Ring A] [Algebra R A]

/-- The degree-zero interaction channel in the Heisenberg derivative. -/
def heisenbergGradeZeroChannel
    (grade : ℤ → Submodule R A)
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) : A :=
  M.coupling • ⁅M.H_int_minus, q.op⁆

/-- The degree-one free channel before applying bath shielding. -/
def heisenbergGradeOneChannel
    (grade : ℤ → Submodule R A)
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) : A :=
  ⁅M.H_qp, q.op⁆ + ⁅M.H_bath, q.op⁆

/-- The degree-two interaction channel in the Heisenberg derivative. -/
def heisenbergGradeTwoChannel
    (grade : ℤ → Submodule R A)
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) : A :=
  M.coupling • ⁅M.H_int_plus, q.op⁆

/-- The bath bracket is homogeneous of degree one before its stronger
commutant-vanishing property is used. -/
theorem bath_term_grade_one
    (grade : ℤ → Submodule R A)
    (hgrade : LieGrading grade)
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    ⁅M.H_bath, q.op⁆ ∈ grade 1 := by
  simpa using hgrade.bracket_mem M.h_bath_grade q.grade_one

/-- The `-1` interaction component and a degree-one quasiparticle produce a
degree-zero channel. -/
theorem heisenbergGradeZeroChannel_mem
    (grade : ℤ → Submodule R A)
    (hgrade : LieGrading grade)
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    heisenbergGradeZeroChannel grade M q ∈ grade 0 := by
  exact (grade 0).smul_mem M.coupling
    (interaction_minus_grade_zero grade hgrade M q)

/-- The quasiparticle and bath free terms both occupy degree one. -/
theorem heisenbergGradeOneChannel_mem
    (grade : ℤ → Submodule R A)
    (hgrade : LieGrading grade)
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    heisenbergGradeOneChannel grade M q ∈ grade 1 := by
  exact (grade 1).add_mem
    (free_quasiparticle_grade_one grade hgrade M q)
    (bath_term_grade_one grade hgrade M q)

/-- The `+1` interaction component and a degree-one quasiparticle produce a
degree-two channel. -/
theorem heisenbergGradeTwoChannel_mem
    (grade : ℤ → Submodule R A)
    (hgrade : LieGrading grade)
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    heisenbergGradeTwoChannel grade M q ∈ grade 2 := by
  exact (grade 2).smul_mem M.coupling
    (interaction_plus_grade_two grade hgrade M q)

/-- Exact algebraic expansion of the Heisenberg derivative into its three
homogeneous channels.  No direct-sum decomposition or projection operator is
assumed. -/
theorem heisenberg_evolution_eq_channels
    (grade : ℤ → Submodule R A)
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    ⁅M.totalHamiltonian, q.op⁆ =
      heisenbergGradeZeroChannel grade M q +
        heisenbergGradeOneChannel grade M q +
          heisenbergGradeTwoChannel grade M q := by
  dsimp [ThermalQuasiparticleModel.totalHamiltonian,
    ThermalQuasiparticleModel.interactionHamiltonian,
    heisenbergGradeZeroChannel, heisenbergGradeOneChannel,
    heisenbergGradeTwoChannel]
  rw [add_lie, add_lie, smul_lie, add_lie, smul_add]
  abel

/-- The degree-one channel reduces to the free quasiparticle term because the
quasiparticle observable belongs to the bath commutant. -/
@[simp]
theorem heisenbergGradeOneChannel_eq_qp
    (grade : ℤ → Submodule R A)
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    heisenbergGradeOneChannel grade M q = ⁅M.H_qp, q.op⁆ := by
  rw [heisenbergGradeOneChannel,
    bath_bracket_quasiparticle_eq_zero grade M q, add_zero]

/-- Shielded form of the three-channel Heisenberg expansion. -/
theorem heisenberg_evolution_eq_shielded_channels
    (grade : ℤ → Submodule R A)
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    ⁅M.totalHamiltonian, q.op⁆ =
      heisenbergGradeZeroChannel grade M q +
        ⁅M.H_qp, q.op⁆ +
          heisenbergGradeTwoChannel grade M q := by
  rw [heisenberg_evolution_eq_channels grade M q,
    heisenbergGradeOneChannel_eq_qp grade M q]

/-- The Heisenberg derivative admits explicit components in degrees zero, one,
and two.  This is the existential presentation useful to downstream spectral
or representation-theoretic owners. -/
theorem heisenberg_evolution_decomposition
    (grade : ℤ → Submodule R A)
    (hgrade : LieGrading grade)
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    ∃ c₀ c₁ c₂ : A,
      c₀ ∈ grade 0 ∧
      c₁ ∈ grade 1 ∧
      c₂ ∈ grade 2 ∧
      ⁅M.totalHamiltonian, q.op⁆ = c₀ + c₁ + c₂ := by
  refine ⟨heisenbergGradeZeroChannel grade M q,
    heisenbergGradeOneChannel grade M q,
    heisenbergGradeTwoChannel grade M q, ?_, ?_, ?_, ?_⟩
  · exact heisenbergGradeZeroChannel_mem grade hgrade M q
  · exact heisenbergGradeOneChannel_mem grade hgrade M q
  · exact heisenbergGradeTwoChannel_mem grade hgrade M q
  · exact heisenberg_evolution_eq_channels grade M q

end InfoGeometry.Physics.NuclearGradedBathCommutant
