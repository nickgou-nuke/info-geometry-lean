import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Lie.Basic
import InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger

/-!
# Graded bath commutants for nuclear operator models

This file gives a theorem-safe bridge between the repository's existing
five-graded Lie-algebra interface and an associative operator-algebra
commutant.  The bath is represented by an `ℝ`-subalgebra of the ambient
operator algebra.  Its commutant is Mathlib's native
`Subalgebra.centralizer`.

No KMS state, modular operator, quasiparticle-phonon Hamiltonian, or thermal
approximation is asserted here.  Those are later representation-level data.
-/

noncomputable section

namespace InfoGeometry.Physics.GradedBathCommutant

open InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The associative commutant of the collective/bath operator subalgebra. -/
noncomputable def bathCommutant (bath : Subalgebra ℝ A) : Subalgebra ℝ A :=
  Subalgebra.centralizer ℝ (bath : Set A)

/-- Membership in the bath commutant is ordinary operator commutation with
all bath elements. -/
theorem mem_bathCommutant_iff
    (bath : Subalgebra ℝ A) {x : A} :
    x ∈ bathCommutant bath ↔ ∀ b ∈ bath, b * x = x * b := by
  exact Subalgebra.mem_centralizer_iff ℝ

/-- The commutator of two bath-commuting operators again commutes with the
bath.  This is inherited from the associative subalgebra structure. -/
theorem commutator_mem_bathCommutant
    (bath : Subalgebra ℝ A) {x y : A}
    (hx : x ∈ bathCommutant bath)
    (hy : y ∈ bathCommutant bath) :
    x * y - y * x ∈ bathCommutant bath := by
  exact (bathCommutant bath).sub_mem
    ((bathCommutant bath).mul_mem hx hy)
    ((bathCommutant bath).mul_mem hy hx)

/-- Native Lie form of `commutator_mem_bathCommutant`. -/
theorem lie_mem_bathCommutant
    (bath : Subalgebra ℝ A) {x y : A}
    (hx : x ∈ bathCommutant bath)
    (hy : y ∈ bathCommutant bath) :
    ⁅x, y⁆ ∈ bathCommutant bath := by
  change x * y - y * x ∈ bathCommutant bath
  exact commutator_mem_bathCommutant bath hx hy

/-! ## Intersection with the existing five grading -/

/-- Grade `-2` part of the bath commutant. -/
noncomputable def commutantNegTwo
    (G : FiveGrading A) (bath : Subalgebra ℝ A) : Submodule ℝ A :=
  G.gNegTwo ⊓ (bathCommutant bath).toSubmodule

/-- Grade `-1` part of the bath commutant. -/
noncomputable def commutantNegOne
    (G : FiveGrading A) (bath : Subalgebra ℝ A) : Submodule ℝ A :=
  G.gNegOne ⊓ (bathCommutant bath).toSubmodule

/-- Grade `0` part of the bath commutant. -/
noncomputable def commutantZero
    (G : FiveGrading A) (bath : Subalgebra ℝ A) : Submodule ℝ A :=
  G.gZero ⊓ (bathCommutant bath).toSubmodule

/-- Grade `+1` part of the bath commutant. -/
noncomputable def commutantPosOne
    (G : FiveGrading A) (bath : Subalgebra ℝ A) : Submodule ℝ A :=
  G.gPosOne ⊓ (bathCommutant bath).toSubmodule

/-- Grade `+2` part of the bath commutant. -/
noncomputable def commutantPosTwo
    (G : FiveGrading A) (bath : Subalgebra ℝ A) : Submodule ℝ A :=
  G.gPosTwo ⊓ (bathCommutant bath).toSubmodule

/-- The inherited `[-1,+1] -> 0` bracket law on the bath commutant. -/
theorem commutant_negOne_posOne_mem_zero
    (G : FiveGrading A) (bath : Subalgebra ℝ A)
    {x y : A}
    (hx : x ∈ commutantNegOne G bath)
    (hy : y ∈ commutantPosOne G bath) :
    ⁅x, y⁆ ∈ commutantZero G bath := by
  constructor
  · exact G.negOne_posOne_mem_zero hx.1 hy.1
  · exact lie_mem_bathCommutant bath hx.2 hy.2

/-- The inherited `[+1,+1] -> +2` bracket law on the bath commutant. -/
theorem commutant_posOne_posOne_mem_posTwo
    (G : FiveGrading A) (bath : Subalgebra ℝ A)
    {x y : A}
    (hx : x ∈ commutantPosOne G bath)
    (hy : y ∈ commutantPosOne G bath) :
    ⁅x, y⁆ ∈ commutantPosTwo G bath := by
  constructor
  · exact G.posOne_posOne_mem_posTwo hx.1 hy.1
  · exact lie_mem_bathCommutant bath hx.2 hy.2

/-- The inherited `[-1,-1] -> -2` bracket law on the bath commutant. -/
theorem commutant_negOne_negOne_mem_negTwo
    (G : FiveGrading A) (bath : Subalgebra ℝ A)
    {x y : A}
    (hx : x ∈ commutantNegOne G bath)
    (hy : y ∈ commutantNegOne G bath) :
    ⁅x, y⁆ ∈ commutantNegTwo G bath := by
  constructor
  · exact G.negOne_negOne_mem_negTwo hx.1 hy.1
  · exact lie_mem_bathCommutant bath hx.2 hy.2

/-- The inherited `[-2,+2] -> 0` bracket law on the bath commutant. -/
theorem commutant_negTwo_posTwo_mem_zero
    (G : FiveGrading A) (bath : Subalgebra ℝ A)
    {x y : A}
    (hx : x ∈ commutantNegTwo G bath)
    (hy : y ∈ commutantPosTwo G bath) :
    ⁅x, y⁆ ∈ commutantZero G bath := by
  constructor
  · exact G.bracket_negTwo_posTwo x y hx.1 hy.1
  · exact lie_mem_bathCommutant bath hx.2 hy.2

/-- The bath commutant inherits exactly the bracket laws carried by the
repository's `FiveGrading` owner, without introducing a second grading
carrier. -/
noncomputable def commutantFiveGrading
    (G : FiveGrading A) (bath : Subalgebra ℝ A) : FiveGrading A where
  gNegTwo := commutantNegTwo G bath
  gNegOne := commutantNegOne G bath
  gZero := commutantZero G bath
  gPosOne := commutantPosOne G bath
  gPosTwo := commutantPosTwo G bath
  negOne_posOne_mem_zero := commutant_negOne_posOne_mem_zero G bath
  bracket_negTwo_posTwo := by
    intro x y hx hy
    exact commutant_negTwo_posTwo_mem_zero G bath hx hy
  posOne_posOne_mem_posTwo := commutant_posOne_posOne_mem_posTwo G bath
  negOne_negOne_mem_negTwo := commutant_negOne_negOne_mem_negTwo G bath

end InfoGeometry.Physics.GradedBathCommutant
