import Mathlib

/-!
# Graded bath commutants for nuclear operator models

This file gives a theorem-safe algebraic interface for separating a selected
quasiparticle sector from an intrinsic/collective nuclear background.

The bath is represented by a `Subalgebra ℝ A`.  Its commutant is Mathlib's
native `Subalgebra.centralizer`.  The five-grading is kept as an independent
property layer on the associative commutator `X * Y - Y * X`.

The formal results deliberately distinguish two statements:

* grading alone places the interaction commutator in the appropriate grade;
* membership in the bath commutant requires an additional commutation
  hypothesis on the interaction operator itself.

Thus a grade `+2` result may be interpreted as a collective/pair channel in a
chosen nuclear realization, but that physical interpretation is not built into
the algebraic theorem.
-/

noncomputable section

namespace InfoGeometry.Nuclear.GradedBathCommutant

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Associative-algebra commutator. -/
def opCommutator (X Y : A) : A := X * Y - Y * X

@[simp] theorem opCommutator_add_left (X Y Z : A) :
    opCommutator (X + Y) Z = opCommutator X Z + opCommutator Y Z := by
  simp [opCommutator, add_mul, mul_add]
  noncomm_ring

@[simp] theorem opCommutator_smul_left (r : ℝ) (X Y : A) :
    opCommutator (r • X) Y = r • opCommutator X Y := by
  simp [opCommutator, smul_mul_assoc, mul_smul_comm, smul_sub]

/-- The intrinsic/collective bath commutant, using Mathlib's native
`Subalgebra.centralizer`. -/
def bathCommutant (bath : Subalgebra ℝ A) : Subalgebra ℝ A :=
  Subalgebra.centralizer ℝ (bath : Set A)

/-- Membership readback for the bath commutant. -/
theorem mem_bathCommutant_iff
    (bath : Subalgebra ℝ A) (X : A) :
    X ∈ bathCommutant bath ↔
      ∀ B : A, B ∈ bath → B * X = X * B := by
  rw [bathCommutant, Subalgebra.mem_centralizer_iff]

/-- Two observables commuting with the bath have a commutator that also
commutes with the bath. -/
theorem opCommutator_mem_bathCommutant
    (bath : Subalgebra ℝ A) {X Y : A}
    (hX : X ∈ bathCommutant bath)
    (hY : Y ∈ bathCommutant bath) :
    opCommutator X Y ∈ bathCommutant bath := by
  exact (bathCommutant bath).sub_mem
    ((bathCommutant bath).mul_mem hX hY)
    ((bathCommutant bath).mul_mem hY hX)

/-- Five homogeneous operator sectors with the bracket laws needed by the
quasiparticle/bath application.  This uses the associative commutator
explicitly, so no compatibility assumption with an unrelated `LieRing`
instance is hidden. -/
structure OperatorFiveGrading (A : Type*) [Ring A] [Algebra ℝ A] where
  gNegTwo : Submodule ℝ A
  gNegOne : Submodule ℝ A
  gZero : Submodule ℝ A
  gPosOne : Submodule ℝ A
  gPosTwo : Submodule ℝ A
  negOne_posOne_mem_zero :
    ∀ {X Y : A}, X ∈ gNegOne → Y ∈ gPosOne →
      opCommutator X Y ∈ gZero
  posOne_posOne_mem_posTwo :
    ∀ {X Y : A}, X ∈ gPosOne → Y ∈ gPosOne →
      opCommutator X Y ∈ gPosTwo
  negOne_negOne_mem_negTwo :
    ∀ {X Y : A}, X ∈ gNegOne → Y ∈ gNegOne →
      opCommutator X Y ∈ gNegTwo
  zero_posOne_mem_posOne :
    ∀ {X Y : A}, X ∈ gZero → Y ∈ gPosOne →
      opCommutator X Y ∈ gPosOne
  zero_negOne_mem_negOne :
    ∀ {X Y : A}, X ∈ gZero → Y ∈ gNegOne →
      opCommutator X Y ∈ gNegOne

namespace OperatorFiveGrading

variable (G : OperatorFiveGrading A)

/-- Homogeneous negative-two component of the bath commutant. -/
def commutantNegTwo (bath : Subalgebra ℝ A) : Submodule ℝ A :=
  G.gNegTwo ⊓ (bathCommutant bath).toSubmodule

/-- Homogeneous negative-one component of the bath commutant. -/
def commutantNegOne (bath : Subalgebra ℝ A) : Submodule ℝ A :=
  G.gNegOne ⊓ (bathCommutant bath).toSubmodule

/-- Homogeneous zero component of the bath commutant. -/
def commutantZero (bath : Subalgebra ℝ A) : Submodule ℝ A :=
  G.gZero ⊓ (bathCommutant bath).toSubmodule

/-- Homogeneous positive-one component of the bath commutant. -/
def commutantPosOne (bath : Subalgebra ℝ A) : Submodule ℝ A :=
  G.gPosOne ⊓ (bathCommutant bath).toSubmodule

/-- Homogeneous positive-two component of the bath commutant. -/
def commutantPosTwo (bath : Subalgebra ℝ A) : Submodule ℝ A :=
  G.gPosTwo ⊓ (bathCommutant bath).toSubmodule

/-- The graded bath commutant inherits the `(+1,+1) → +2` bracket law. -/
theorem commutant_posOne_posOne_mem_posTwo
    (bath : Subalgebra ℝ A) {X Y : A}
    (hX : X ∈ G.commutantPosOne bath)
    (hY : Y ∈ G.commutantPosOne bath) :
    opCommutator X Y ∈ G.commutantPosTwo bath := by
  constructor
  · exact G.posOne_posOne_mem_posTwo hX.1 hY.1
  · exact opCommutator_mem_bathCommutant bath hX.2 hY.2

/-- The graded bath commutant inherits the `(-1,+1) → 0` bracket law. -/
theorem commutant_negOne_posOne_mem_zero
    (bath : Subalgebra ℝ A) {X Y : A}
    (hX : X ∈ G.commutantNegOne bath)
    (hY : Y ∈ G.commutantPosOne bath) :
    opCommutator X Y ∈ G.commutantZero bath := by
  constructor
  · exact G.negOne_posOne_mem_zero hX.1 hY.1
  · exact opCommutator_mem_bathCommutant bath hX.2 hY.2

end OperatorFiveGrading

/-- A Soloviev-type quasiparticle/intrinsic-background placement packet.
The interaction is split into its grade `-1` and `+1` pieces explicitly. -/
structure ThermalQuasiparticleModel (G : OperatorFiveGrading A) where
  bath : Subalgebra ℝ A
  H_bath : A
  H_qp : A
  H_int_minus : A
  H_int_plus : A
  coupling : ℝ
  h_bath_mem : H_bath ∈ bath
  h_bath_grade : H_bath ∈ G.gZero
  h_qp_mem : H_qp ∈ bathCommutant bath
  h_qp_grade : H_qp ∈ G.gZero
  h_int_minus_grade : H_int_minus ∈ G.gNegOne
  h_int_plus_grade : H_int_plus ∈ G.gPosOne

/-- A quasiparticle creation observable is bath-independent and belongs to the
positive-one homogeneous sector. -/
structure QuasiparticleCreation
    {G : OperatorFiveGrading A}
    (M : ThermalQuasiparticleModel G) where
  Q : A
  commutes_with_bath : Q ∈ bathCommutant M.bath
  grade_posOne : Q ∈ G.gPosOne

/-- Total Hamiltonian with the interaction decomposed into exchange grades. -/
def totalHamiltonian
    {G : OperatorFiveGrading A}
    (M : ThermalQuasiparticleModel G) : A :=
  M.H_qp + M.H_bath + M.coupling • (M.H_int_minus + M.H_int_plus)

/-- Bath shielding: a quasiparticle observable in the bath commutant has zero
commutator with the free bath Hamiltonian. -/
theorem bath_commutator_eq_zero
    {G : OperatorFiveGrading A}
    (M : ThermalQuasiparticleModel G)
    (qp : QuasiparticleCreation M) :
    opCommutator M.H_bath qp.Q = 0 := by
  have hcomm : M.H_bath * qp.Q = qp.Q * M.H_bath :=
    (mem_bathCommutant_iff M.bath qp.Q).mp qp.commutes_with_bath
      M.H_bath M.h_bath_mem
  exact sub_eq_zero.mpr hcomm

/-- Heisenberg-style equation-of-motion decomposition.  The free bath term
vanishes exactly because the selected quasiparticle observable lies in the
bath commutant. -/
theorem quasiparticle_eom
    {G : OperatorFiveGrading A}
    (M : ThermalQuasiparticleModel G)
    (qp : QuasiparticleCreation M) :
    opCommutator (totalHamiltonian M) qp.Q =
      opCommutator M.H_qp qp.Q +
        M.coupling • opCommutator (M.H_int_minus + M.H_int_plus) qp.Q := by
  rw [totalHamiltonian, opCommutator_add_left, opCommutator_add_left,
    bath_commutator_eq_zero M qp, add_zero, opCommutator_smul_left]

/-- Grade-only interaction theorem.  The `-1` interaction component gives a
zero-grade scattering term, while the `+1` component gives a grade `+2` term. -/
theorem interaction_commutator_grade
    {G : OperatorFiveGrading A}
    (M : ThermalQuasiparticleModel G)
    (qp : QuasiparticleCreation M) :
    opCommutator (M.H_int_minus + M.H_int_plus) qp.Q ∈
      G.gZero ⊔ G.gPosTwo := by
  rw [opCommutator_add_left]
  exact Submodule.add_mem_sup
    (G.negOne_posOne_mem_zero M.h_int_minus_grade qp.grade_posOne)
    (G.posOne_posOne_mem_posTwo M.h_int_plus_grade qp.grade_posOne)

/-- Stronger positive-two commutant theorem.  This requires the additional
hypothesis that the positive-one interaction component itself commutes with the
bath; grading alone is not enough to infer this. -/
theorem interaction_plus_commutator_mem_commutantPosTwo
    {G : OperatorFiveGrading A}
    (M : ThermalQuasiparticleModel G)
    (qp : QuasiparticleCreation M)
    (hInt : M.H_int_plus ∈ bathCommutant M.bath) :
    opCommutator M.H_int_plus qp.Q ∈ G.commutantPosTwo M.bath := by
  constructor
  · exact G.posOne_posOne_mem_posTwo M.h_int_plus_grade qp.grade_posOne
  · exact opCommutator_mem_bathCommutant M.bath hInt qp.commutes_with_bath

/-- The free quasiparticle Hamiltonian preserves the positive-one grade. -/
theorem free_qp_commutator_grade_posOne
    {G : OperatorFiveGrading A}
    (M : ThermalQuasiparticleModel G)
    (qp : QuasiparticleCreation M) :
    opCommutator M.H_qp qp.Q ∈ G.gPosOne :=
  G.zero_posOne_mem_posOne M.h_qp_grade qp.grade_posOne

end InfoGeometry.Nuclear.GradedBathCommutant
