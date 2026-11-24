/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Canonical.GradedBRSTCochainComplexBridge

variable {R H : Type*} [Ring R] [AddCommGroup H] [Module R H]

/-- **Structure**: Graded BRST Cochain Package. -/
structure GradedBRSTCochainPackage (R H : Type*) [Ring R] [AddCommGroup H] [Module R H] where
  q : Module.End R H
  g_op : Module.End R H
  hq2 : q.comp q = 0
  h_comm : g_op.comp q - q.comp g_op = q

/-- **Theorem**: BRST Operator Composition Nilpotency q ∘ q = 0. -/
theorem brst_operator_sq_zero (P : GradedBRSTCochainPackage R H) :
    P.q.comp P.q = 0 := P.hq2

end InfoGeometry.Canonical.GradedBRSTCochainComplexBridge

/-! ## Concrete noncommutative matrix BRST operators

This finite operator model constructs the differential, reverse homotopy, and
ghost grading as left actions on the actual matrix ring over an arbitrary
coefficient ring. It does not identify this contractible model with physical
BRST cohomology. -/

namespace InfoGeometry.Canonical.NoncommMatrixBRST

variable {A : Type*} [Ring A]

abbrev OperatorCarrier (A : Type*) := Matrix (Fin 2) (Fin 2) A

/-- The creation matrix unit, with multiplication in the actual coefficient
matrix algebra. -/
def create : OperatorCarrier A := !![0, 1; 0, 0]

/-- The annihilation matrix unit opposite to `create`. -/
def annihilate : OperatorCarrier A := !![0, 0; 1, 0]

/-- A ghost-number grading operator on the two matrix rows. -/
def ghostGrade : OperatorCarrier A := !![1, 0; 0, 0]

/-- Left multiplication acts as an integer-linear operator on the additive
group underlying the matrix ring. The matrix coefficients themselves remain
in the arbitrary, possibly noncommutative ring `A`. -/
def leftAction (T : OperatorCarrier A) : Module.End ℤ (OperatorCarrier A) :=
  ({ toFun := fun X => T * X
     map_zero' := by simp
     map_add' := by intro X Y; simp [Matrix.mul_add] } :
      OperatorCarrier A →+ OperatorCarrier A).toIntLinearMap

/-- Left multiplication is a representation of the matrix ring on its additive
group, with composition ordered as matrix multiplication. -/
theorem leftAction_mul (S T : OperatorCarrier A) :
    leftAction S * leftAction T = leftAction (S * T) := by
  ext X
  simp [leftAction, Matrix.mul_assoc]

theorem create_sq : create (A := A) * create = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [create, Matrix.mul_apply, Fin.sum_univ_two]

theorem annihilate_sq : annihilate (A := A) * annihilate = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [annihilate, Matrix.mul_apply, Fin.sum_univ_two]

theorem create_annihilate_anticommutator :
    create (A := A) * annihilate + annihilate * create = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [create, annihilate]

/-- Non-commutativity witness on the concrete `2 × 2` BRST matrix carrier:
`create * annihilate ≠ annihilate * create`. -/
theorem create_annihilate_noncommute :
    (create : OperatorCarrier ℝ) * annihilate ≠ annihilate * create := by
  intro h
  have h00 := congrArg (fun M : OperatorCarrier ℝ => M 0 0) h
  norm_num [create, annihilate, Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem ghostGrade_create_commutator :
    ghostGrade (A := A) * create - create * ghostGrade = create := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ghostGrade, create]

theorem ghostGrade_annihilate_commutator :
    ghostGrade (A := A) * annihilate - annihilate * ghostGrade = -annihilate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ghostGrade, annihilate]

/-- Concrete BRST differential given by left action of the nilpotent
creation operator. -/
def differential : Module.End ℤ (OperatorCarrier A) := leftAction create

/-- Concrete degree-lowering operator given by left action of the opposite
matrix unit. -/
def homotopy : Module.End ℤ (OperatorCarrier A) := leftAction annihilate

/-- The ghost grading acts on the same noncommutative operator carrier. -/
def ghostNumber : Module.End ℤ (OperatorCarrier A) := leftAction ghostGrade

theorem differential_sq_zero :
    differential (A := A) * differential (A := A) = 0 := by
  change leftAction create * leftAction create = 0
  ext X : 1
  change create * (create * X) = 0
  ext i j
  rw [← Matrix.mul_assoc, create_sq]
  simp

theorem homotopy_sq_zero :
    homotopy (A := A) * homotopy (A := A) = 0 := by
  change leftAction annihilate * leftAction annihilate = 0
  ext X : 1
  change annihilate * (annihilate * X) = 0
  ext i j
  rw [← Matrix.mul_assoc, annihilate_sq]
  simp

theorem contracting_anticommutator :
    differential (A := A) * homotopy (A := A) +
      homotopy (A := A) * differential (A := A) = 1 := by
  change leftAction create * leftAction annihilate +
    leftAction annihilate * leftAction create = 1
  ext X : 1
  change create * (annihilate * X) + annihilate * (create * X) = X
  ext i j
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.add_mul,
    create_annihilate_anticommutator]
  simp

/-- The ghost-number operator raises the differential by one in its
commutator relation. -/
theorem ghostNumber_differential_commutator :
    ghostNumber (A := A) * differential (A := A) -
      differential (A := A) * ghostNumber (A := A) = differential (A := A) := by
  change leftAction ghostGrade * leftAction create -
    leftAction create * leftAction ghostGrade = leftAction create
  ext X : 1
  change ghostGrade * (create * X) - create * (ghostGrade * X) = create * X
  ext i j
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.sub_mul,
    ghostGrade_create_commutator]

/-- Concrete instantiation of `GradedBRSTCochainPackage` on the matrix carrier. -/
def package (A : Type*) [Ring A] :
    InfoGeometry.Canonical.GradedBRSTCochainComplexBridge.GradedBRSTCochainPackage
      ℤ (OperatorCarrier A) where
  q := differential
  g_op := ghostNumber
  hq2 := differential_sq_zero
  h_comm := ghostNumber_differential_commutator

/-- Ghost-number eigenspaces in the actual operator-matrix module. -/
def ghostEigenspace (n : ℤ) : Submodule ℤ (OperatorCarrier A) :=
  LinearMap.ker (ghostNumber (A := A) -
    n • (LinearMap.id : Module.End ℤ (OperatorCarrier A)))

/-- Membership in a ghost-number eigenspace is its explicit eigenvector law. -/
theorem mem_ghostEigenspace_iff (n : ℤ) (X : OperatorCarrier A) :
    X ∈ ghostEigenspace (A := A) n ↔ ghostNumber X = n • X := by
  rw [ghostEigenspace, LinearMap.mem_ker]
  change ghostNumber X - n • X = 0 ↔ _
  rw [sub_eq_zero]

/-- The concrete matrix differential raises ghost number by one. -/
theorem differential_raises_ghostNumber (n : ℤ)
    (X : OperatorCarrier A)
    (hX : ghostNumber X = n • X) :
    ghostNumber (differential X) = (n + 1) • differential X := by
  have hcomm := LinearMap.congr_fun
    (ghostNumber_differential_commutator (A := A)) X
  change ghostNumber (differential X) -
    differential (ghostNumber X) = differential X at hcomm
  rw [hX, differential.map_smul] at hcomm
  rw [sub_eq_iff_eq_add] at hcomm
  rw [hcomm, add_smul, one_smul, add_comm]

/-- The homotopy endomorphism has the required adjoint ghost-number
commutator on the full operator-matrix module. -/
theorem ghostNumber_homotopy_commutator :
    ghostNumber (A := A) * homotopy (A := A) -
        homotopy (A := A) * ghostNumber (A := A) =
      -homotopy (A := A) := by
  change leftAction ghostGrade * leftAction annihilate -
      leftAction annihilate * leftAction ghostGrade =
    -leftAction annihilate
  rw [leftAction_mul, leftAction_mul]
  ext X i j
  dsimp [leftAction]
  have hmat : (ghostGrade * annihilate - annihilate * ghostGrade) * X =
      -(annihilate * X) := by
    rw [ghostGrade_annihilate_commutator, neg_mul]
  simpa [Matrix.sub_mul, Matrix.mul_assoc] using
    congrFun (congrFun hmat i) j

/-- The contracting homotopy lowers ghost number by one. -/
theorem homotopy_lowers_ghostNumber (n : ℤ)
    (X : OperatorCarrier A)
    (hX : ghostNumber X = n • X) :
    ghostNumber (homotopy X) = (n - 1) • homotopy X := by
  have hcomm := congrArg (fun T : Module.End ℤ (OperatorCarrier A) => T X)
    (ghostNumber_homotopy_commutator (A := A))
  change ghostNumber (homotopy X) - homotopy (ghostNumber X) =
    -homotopy X at hcomm
  rw [hX, homotopy.map_smul] at hcomm
  rw [sub_eq_iff_eq_add] at hcomm
  calc
    ghostNumber (homotopy X) = -(homotopy X) + n • homotopy X := hcomm
    _ = n • homotopy X - homotopy X := by abel
    _ = (n - 1) • homotopy X := by rw [sub_smul, one_smul]

/-- The differential sends each ghost-number eigenspace to the next one. -/
theorem differential_maps_ghostEigenspace_succ (n : ℤ) :
    Submodule.map (differential (A := A)) (ghostEigenspace (A := A) n) ≤
      ghostEigenspace (A := A) (n + 1) := by
  intro X hX
  rw [Submodule.mem_map] at hX
  rcases hX with ⟨Y, hY, rfl⟩
  rw [ghostEigenspace, LinearMap.mem_ker] at hY ⊢
  rw [LinearMap.sub_apply] at hY ⊢
  rw [sub_eq_zero] at hY ⊢
  rw [LinearMap.smul_apply, LinearMap.id_apply] at hY ⊢
  exact differential_raises_ghostNumber n Y hY

/-- The degree-one differential obtained by restricting the operator
differential to consecutive ghost-number eigenspaces. -/
def gradedDifferential (n : ℤ) :
    ghostEigenspace (A := A) n →ₗ[ℤ]
      ghostEigenspace (A := A) (n + 1) where
  toFun X := ⟨differential X,
    (mem_ghostEigenspace_iff (A := A) (n + 1) (differential X)).2
      (differential_raises_ghostNumber n X.1
        ((mem_ghostEigenspace_iff (A := A) n X.1).mp X.2))⟩
  map_add' X Y := by
    apply Subtype.ext
    exact differential.map_add X.1 Y.1
  map_smul' k X := by
    apply Subtype.ext
    exact differential.map_smul k X.1

/-- Consecutive restricted maps compose to zero, so these eigenspaces form
an actual integer-graded cochain complex. -/
theorem gradedDifferential_comp_eq_zero (n : ℤ) :
    (gradedDifferential (A := A) (n + 1)).comp
        (gradedDifferential (A := A) n) = 0 := by
  apply LinearMap.ext
  intro X
  apply Subtype.ext
  exact LinearMap.congr_fun (differential_sq_zero (A := A)) X.1

/-- The contracting homotopy restricted to ghost eigenspaces, in the degree
opposite to the differential. -/
def gradedHomotopy (n : ℤ) :
    ghostEigenspace (A := A) n →ₗ[ℤ]
      ghostEigenspace (A := A) (n - 1) where
  toFun X := ⟨homotopy X,
    (mem_ghostEigenspace_iff (A := A) (n - 1) (homotopy X)).2
      (homotopy_lowers_ghostNumber n X.1
        ((mem_ghostEigenspace_iff (A := A) n X.1).mp X.2))⟩
  map_add' X Y := by
    apply Subtype.ext
    exact homotopy.map_add X.1 Y.1
  map_smul' k X := by
    apply Subtype.ext
    exact homotopy.map_smul k X.1

/-- Every closed element in a ghost-number eigenspace is the differential of
an element in the preceding eigenspace. This is degreewise exactness of the
constructed matrix complex. -/
theorem graded_cycles_are_boundaries (n : ℤ)
    (X : ghostEigenspace (A := A) n)
    (hX : gradedDifferential (A := A) n X = 0) :
    ∃ Y : ghostEigenspace (A := A) (n - 1),
      (gradedDifferential (A := A) (n - 1) Y : OperatorCarrier A) = X.1 := by
  have hclosed : differential X.1 = 0 := by
    exact congrArg Subtype.val hX
  have hcontract := congrArg
    (fun T : Module.End ℤ (OperatorCarrier A) => T X.1)
    (contracting_anticommutator (A := A))
  change differential (homotopy X.1) +
      homotopy (differential X.1) = X.1 at hcontract
  rw [hclosed] at hcontract
  simp only [homotopy.map_zero, add_zero] at hcontract
  refine ⟨gradedHomotopy (A := A) n X, ?_⟩
  change differential (homotopy X.1) = X.1
  exact hcontract

/-- Every cycle in this concrete two-state complex is a boundary. -/
theorem cycles_are_boundaries (X : OperatorCarrier A)
    (hX : differential X = 0) :
    ∃ Y : OperatorCarrier A, differential Y = X := by
  have h := congrArg (fun T : Module.End ℤ (OperatorCarrier A) => T X)
    contracting_anticommutator
  change differential (homotopy X) + homotopy (differential X) = X at h
  refine ⟨homotopy X, ?_⟩
  rw [hX] at h
  simpa using h

/-- This concrete two-state BRST complex is exact: its cycles are precisely
the image of its differential. -/
theorem differential_ker_eq_range :
    LinearMap.ker (differential (A := A)) =
      LinearMap.range (differential (A := A)) := by
  apply Submodule.ext
  intro X
  constructor
  · intro hX
    exact cycles_are_boundaries X hX
  · rintro ⟨Y, rfl⟩
    have h := congrArg (fun T : Module.End ℤ (OperatorCarrier A) => T Y)
      differential_sq_zero
    change differential (differential Y) = 0 at h
    exact h

/-- The cycle submodule of the concrete two-state cochain complex. -/
def cycleSubmodule : Submodule ℤ (OperatorCarrier A) :=
  LinearMap.ker (differential (A := A))

/-- Boundaries viewed inside cycles, by pulling back the differential's range
along the cycle-submodule inclusion. -/
def boundaryInCycles : Submodule ℤ (cycleSubmodule (A := A)) :=
  (LinearMap.range (differential (A := A))).comap
    (cycleSubmodule (A := A)).subtype

/-- The cohomology of this explicit cochain complex is the quotient of cycles
by boundaries, with both submodules constructed from the differential. -/
abbrev Cohomology :=
  cycleSubmodule (A := A) ⧸ boundaryInCycles (A := A)

/-- Exactness identifies every cycle with a boundary inside the cycle module. -/
theorem boundaryInCycles_eq_top :
    boundaryInCycles (A := A) = ⊤ := by
  apply Submodule.eq_top_iff'.2
  intro X
  change (X : OperatorCarrier A) ∈ LinearMap.range (differential (A := A))
  exact cycles_are_boundaries (X : OperatorCarrier A) X.property

/-- The actual quotient cohomology is subsingleton (hence zero) for this
contractible matrix complex. -/
theorem cohomology_subsingleton : Subsingleton (Cohomology (A := A)) := by
  rw [Submodule.Quotient.subsingleton_iff, boundaryInCycles_eq_top]

end InfoGeometry.Canonical.NoncommMatrixBRST
