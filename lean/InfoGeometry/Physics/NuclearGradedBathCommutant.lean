import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Tactic

/-!
# Nuclear graded bath commutants

This file gives a theorem-safe algebraic interface for a Soloviev-type
quasiparticle/bath separation inside an associative operator algebra.

The bath is a unital `Subalgebra`. Its commutant is Mathlib's native
`Subalgebra.centralizer`; the corresponding commutator-closed Lie subalgebra is
obtained by forgetting multiplication and retaining closure under
`⁅x, y⁆ = x * y - y * x`.

For an integer-indexed homogeneous decomposition, the degree-`i` bath
commutant is the intersection of the degree-`i` submodule with the associative
centralizer. Mathlib `v4.28.1` predates the later generic graded-bracket
interface, so this owner stores only the required bracket-compatibility law in
`LieGrading`. Brackets then satisfy

`[C_bath,i, C_bath,j] ⊆ C_bath,i+j`.

The interaction Hamiltonian is stored by its separate degree `-1` and `+1`
components. This avoids extracting a decomposition from membership in a
submodule supremum. The resulting Heisenberg equation proves bath shielding
and the exact grade support of the free and interaction terms.

No KMS state, Tomita standard form, thermo-field tilde identification, RPA
closure, or physical identification of every degree-two element with a phonon
is asserted here.
-/

set_option autoImplicit false

namespace InfoGeometry.Physics.NuclearGradedBathCommutant

variable {R A : Type*}
variable [CommRing R] [Ring A] [Algebra R A]

/-- The associative commutant of a unital bath subalgebra. -/
def bathCommutant (bath : Subalgebra R A) : Subalgebra R A :=
  Subalgebra.centralizer R (bath : Set A)

/-- Membership in the bath commutant is pointwise commutation with every bath
operator. -/
@[simp]
theorem mem_bathCommutant_iff
    (bath : Subalgebra R A) (x : A) :
    x ∈ bathCommutant bath ↔
      ∀ b : A, b ∈ bath → b * x = x * b := by
  change x ∈ Subalgebra.centralizer R (bath : Set A) ↔ _
  exact Subalgebra.mem_centralizer_iff

/-- The associative centralizer, regarded as a Lie subalgebra under the
commutator bracket. -/
def bathLieCommutant (bath : Subalgebra R A) : LieSubalgebra R A where
  toSubmodule := (bathCommutant bath).toSubmodule
  lie_mem' := by
    intro x y hx hy
    change x * y - y * x ∈ bathCommutant bath
    exact (bathCommutant bath).sub_mem
      ((bathCommutant bath).mul_mem hx hy)
      ((bathCommutant bath).mul_mem hy hx)

/-- A bath element has zero Lie bracket with every element of the bath
commutant. -/
@[simp]
theorem bath_element_lie_eq_zero
    (bath : Subalgebra R A)
    {b x : A}
    (hb : b ∈ bath)
    (hx : x ∈ bathCommutant bath) :
    ⁅b, x⁆ = 0 := by
  have hcomm : b * x = x * b :=
    (mem_bathCommutant_iff bath x).1 hx b hb
  rw [LieRing.of_associative_ring_bracket, hcomm, sub_self]

/-- The same shielding identity with the commutant element in the first slot. -/
@[simp]
theorem commutant_element_lie_bath_eq_zero
    (bath : Subalgebra R A)
    {b x : A}
    (hb : b ∈ bath)
    (hx : x ∈ bathCommutant bath) :
    ⁅x, b⁆ = 0 := by
  have hcomm : b * x = x * b :=
    (mem_bathCommutant_iff bath x).1 hx b hb
  rw [LieRing.of_associative_ring_bracket, hcomm, sub_self]

/-- Version-compatible bracket law for an integer-indexed family of homogeneous
submodules. This is the only grading property used by the present owner. -/
structure LieGrading (grade : ℤ → Submodule R A) : Prop where
  bracket_mem :
    ∀ {i j : ℤ} {x y : A},
      x ∈ grade i → y ∈ grade j → ⁅x, y⁆ ∈ grade (i + j)

/-- The homogeneous degree-`i` part of the bath commutant. -/
def gradedBathCommutant
    (grade : ℤ → Submodule R A)
    (bath : Subalgebra R A)
    (i : ℤ) : Submodule R A :=
  grade i ⊓ (bathCommutant bath).toSubmodule

@[simp]
theorem mem_gradedBathCommutant_iff
    (grade : ℤ → Submodule R A)
    (bath : Subalgebra R A)
    (i : ℤ)
    (x : A) :
    x ∈ gradedBathCommutant grade bath i ↔
      x ∈ grade i ∧ x ∈ bathCommutant bath := by
  simp [gradedBathCommutant]

/-- The bath commutant inherits the ambient homogeneous Lie-bracket law. -/
theorem gradedBathCommutant_bracket
    (grade : ℤ → Submodule R A)
    (hgrade : LieGrading grade)
    (bath : Subalgebra R A)
    {i j : ℤ}
    {x y : A}
    (hx : x ∈ gradedBathCommutant grade bath i)
    (hy : y ∈ gradedBathCommutant grade bath j) :
    ⁅x, y⁆ ∈ gradedBathCommutant grade bath (i + j) := by
  have hx' := (mem_gradedBathCommutant_iff grade bath i x).1 hx
  have hy' := (mem_gradedBathCommutant_iff grade bath j y).1 hy
  exact (mem_gradedBathCommutant_iff grade bath (i + j) ⁅x, y⁆).2
    ⟨hgrade.bracket_mem hx'.1 hy'.1,
      (bathLieCommutant bath).lie_mem hx'.2 hy'.2⟩

/-- Algebraic data for a bath-coupled quasiparticle Hamiltonian.

The interaction is represented by explicit degree `-1` and degree `+1`
components, so no noncanonical decomposition from a supremum membership is
required. -/
structure ThermalQuasiparticleModel
    (grade : ℤ → Submodule R A) where
  bath : Subalgebra R A
  H_bath : A
  H_qp : A
  H_int_minus : A
  H_int_plus : A
  coupling : R
  h_bath_mem : H_bath ∈ bath
  h_bath_grade : H_bath ∈ grade 0
  h_qp_mem : H_qp ∈ bathCommutant bath
  h_qp_grade : H_qp ∈ grade 0
  h_int_minus_grade : H_int_minus ∈ grade (-1)
  h_int_plus_grade : H_int_plus ∈ grade 1

namespace ThermalQuasiparticleModel

variable {grade : ℤ → Submodule R A}

/-- The exchange interaction, assembled from its degree `-1` and `+1`
components. -/
def interactionHamiltonian
    (M : ThermalQuasiparticleModel grade) : A :=
  M.H_int_minus + M.H_int_plus

/-- Total Hamiltonian of the algebraic quasiparticle/bath model. -/
def totalHamiltonian
    (M : ThermalQuasiparticleModel grade) : A :=
  M.H_qp + M.H_bath + M.coupling • M.interactionHamiltonian

end ThermalQuasiparticleModel

/-- A degree-one quasiparticle creation observable that commutes with the free
bath algebra. -/
structure QuasiparticleCreation
    (grade : ℤ → Submodule R A)
    (M : ThermalQuasiparticleModel grade) where
  op : A
  mem_commutant : op ∈ bathCommutant M.bath
  grade_one : op ∈ grade 1

namespace QuasiparticleCreation

variable {grade : ℤ → Submodule R A}
variable {M : ThermalQuasiparticleModel grade}

/-- A quasiparticle creation observable lies in the degree-one bath
commutant. -/
theorem mem_gradedBathCommutant
    (q : QuasiparticleCreation grade M) :
    q.op ∈ gradedBathCommutant grade M.bath 1 :=
  (mem_gradedBathCommutant_iff grade M.bath 1 q.op).2
    ⟨q.grade_one, q.mem_commutant⟩

end QuasiparticleCreation

section EquationsOfMotion

variable (grade : ℤ → Submodule R A)
variable (hgrade : LieGrading grade)

/-- The free bath Hamiltonian is shielded from a quasiparticle observable in
its commutant. -/
@[simp]
theorem bath_bracket_quasiparticle_eq_zero
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    ⁅M.H_bath, q.op⁆ = 0 :=
  bath_element_lie_eq_zero M.bath M.h_bath_mem q.mem_commutant

/-- Exact Heisenberg equation after the free bath term is removed by
commutant shielding. -/
theorem quasiparticle_eom
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    ⁅M.totalHamiltonian, q.op⁆ =
      ⁅M.H_qp, q.op⁆ +
        M.coupling • ⁅M.interactionHamiltonian, q.op⁆ := by
  simp [ThermalQuasiparticleModel.totalHamiltonian,
    bath_bracket_quasiparticle_eq_zero]

/-- The free quasiparticle term remains in degree `+1`. -/
theorem free_quasiparticle_grade_one
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    ⁅M.H_qp, q.op⁆ ∈ grade 1 := by
  simpa using hgrade.bracket_mem M.h_qp_grade q.grade_one

/-- The degree `-1` interaction component bracketed with a degree `+1`
quasiparticle lies in degree zero. -/
theorem interaction_minus_grade_zero
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    ⁅M.H_int_minus, q.op⁆ ∈ grade 0 := by
  simpa using hgrade.bracket_mem M.h_int_minus_grade q.grade_one

/-- The degree `+1` interaction component bracketed with a degree `+1`
quasiparticle lies in degree `+2`. -/
theorem interaction_plus_grade_two
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    ⁅M.H_int_plus, q.op⁆ ∈ grade 2 := by
  simpa using hgrade.bracket_mem M.h_int_plus_grade q.grade_one

/-- The complete interaction contribution has support only in degrees zero and
`+2`. -/
theorem interaction_bracket_grade_zero_sup_two
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    ⁅M.interactionHamiltonian, q.op⁆ ∈ grade 0 ⊔ grade 2 := by
  change ⁅M.H_int_minus + M.H_int_plus, q.op⁆ ∈ grade 0 ⊔ grade 2
  rw [add_lie]
  exact Submodule.add_mem_sup
    (interaction_minus_grade_zero grade hgrade M q)
    (interaction_plus_grade_two grade hgrade M q)

/-- The full Heisenberg derivative is supported in the free degree-one sector
and the interaction-generated degree-zero/degree-two sector. -/
theorem total_eom_grade_support
    (M : ThermalQuasiparticleModel grade)
    (q : QuasiparticleCreation grade M) :
    ⁅M.totalHamiltonian, q.op⁆ ∈
      grade 1 ⊔ (grade 0 ⊔ grade 2) := by
  rw [quasiparticle_eom grade M q]
  exact Submodule.add_mem_sup
    (free_quasiparticle_grade_one grade hgrade M q)
    ((grade 0 ⊔ grade 2).smul_mem M.coupling
      (interaction_bracket_grade_zero_sup_two grade hgrade M q))

end EquationsOfMotion

end InfoGeometry.Physics.NuclearGradedBathCommutant
