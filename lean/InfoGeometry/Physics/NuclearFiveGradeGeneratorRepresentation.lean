/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import InfoGeometry.Physics.NuclearTwoModeCARFiveGrade
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel
import InfoGeometry.Physics.NuclearTwoModeFiveGradeSubmodules
import InfoGeometry.Canonical.SL2SpinorLadder
import InfoGeometry.Exceptional.FreudenthalSymplecticContactLieAlgebra
import InfoGeometry.Exceptional.FreudenthalSymplecticContactGrading

/-!
# A concrete grade-preserving nuclear generator representation

This finite generator set records the nonzero degrees of the two-mode CAR
five-grading. Its representation lands in the associative endomorphism Lie
algebra, and brackets add degrees by the adjoint-weight theorem.

It is not definitionally identified with the generic Freudenthal/TKK carrier;
that comparison requires an explicit intertwining Lie homomorphism.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation

open InfoGeometry.Physics.NuclearTwoModeCARFiveGrade

inductive Generator : Type
  | pairAnnihilation
  | annihilationOne
  | annihilationTwo
  | cartan
  | creationOne
  | creationTwo
  | pairCreation
  deriving DecidableEq, Repr

instance : Fintype Generator where
  elems := { .pairAnnihilation, .annihilationOne, .annihilationTwo, .cartan,
             .creationOne, .creationTwo, .pairCreation }
  complete := by
    intro x
    cases x <;> simp

/-- Integer grade of each named generator. -/
def degree : Generator → ℤ
  | .pairAnnihilation => -2
  | .annihilationOne => -1
  | .annihilationTwo => -1
  | .cartan => 0
  | .creationOne => 1
  | .creationTwo => 1
  | .pairCreation => 2

/-- Concrete representation in the four-state operator algebra. -/
def represent : Generator → Op
  | .pairAnnihilation => NuclearTwoModeCARFiveGrade.pairAnnihilation
  | .annihilationOne => NuclearTwoModeCARFiveGrade.annihilationOne
  | .annihilationTwo => NuclearTwoModeCARFiveGrade.annihilationTwo
  | .cartan => gradeCartan
  | .creationOne => NuclearTwoModeCARFiveGrade.creationOne
  | .creationTwo => NuclearTwoModeCARFiveGrade.creationTwo
  | .pairCreation => NuclearTwoModeCARFiveGrade.pairCreation

/-- Every named generator lies in its declared Cartan grade. -/
theorem represent_hasGrade (g : Generator) :
    HasGrade (degree g) (represent g) := by
  cases g <;> simp [degree, represent]

/-- The commutator of represented generators lies in the sum grade. -/
theorem represented_commutator_hasGrade (g h : Generator) :
    HasGrade (degree g + degree h)
      (commutator (represent g) (represent h)) :=
  (represent_hasGrade g).commutator (represent_hasGrade h)

/-- Degree reversal exchanging creation and annihilation. -/
def opposite : Generator → Generator
  | .pairAnnihilation => .pairCreation
  | .annihilationOne => .creationOne
  | .annihilationTwo => .creationTwo
  | .cartan => .cartan
  | .creationOne => .annihilationOne
  | .creationTwo => .annihilationTwo
  | .pairCreation => .pairAnnihilation

@[simp] theorem opposite_involutive (g : Generator) :
    opposite (opposite g) = g := by
  cases g <;> rfl

@[simp] theorem degree_opposite (g : Generator) :
    degree (opposite g) = -degree g := by
  cases g <;> rfl

/-- Every one of the five grades has an explicit generator. -/
theorem five_grades_are_occupied :
    (∃ g, degree g = -2) ∧
      (∃ g, degree g = -1) ∧
      (∃ g, degree g = 0) ∧
      (∃ g, degree g = 1) ∧
      (∃ g, degree g = 2) := by
  exact ⟨⟨.pairAnnihilation, rfl⟩,
    ⟨.annihilationOne, rfl⟩,
    ⟨.cartan, rfl⟩,
    ⟨.creationOne, rfl⟩,
    ⟨.pairCreation, rfl⟩⟩

/-- Compact representation packet. -/
theorem nuclear_five_grade_representation_packet :
    (∀ g, HasGrade (degree g) (represent g)) ∧
      (∀ g h, HasGrade (degree g + degree h)
        (commutator (represent g) (represent h))) ∧
      (∀ g, opposite (opposite g) = g) ∧
      (∀ g, degree (opposite g) = -degree g) := by
  exact ⟨represent_hasGrade, represented_commutator_hasGrade,
    opposite_involutive, degree_opposite⟩

section ConcreteFiveGradedLieBridge

open InfoGeometry.Canonical.SplitCliffordTwoModeCAR
open InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel
open InfoGeometry.Exceptional.Freudenthal
open InfoGeometry.Canonical.SL2SpinorLadder
open scoped Matrix

private def degreeZeroRaise : NuclearTwoModeFiveGradeLieModel.M4R :=
  a1Dag * a2

private def degreeZeroLower : NuclearTwoModeFiveGradeLieModel.M4R :=
  a2Dag * a1

private def degreeZeroCartan : NuclearTwoModeFiveGradeLieModel.M4R :=
  NuclearTwoModeFiveGradeLieModel.number1 - NuclearTwoModeFiveGradeLieModel.number2

private theorem gradingOperator_grade :
    NuclearTwoModeFiveGradeLieModel.HasGrade 0 gradingOperator := by
  unfold NuclearTwoModeFiveGradeLieModel.HasGrade
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [NuclearTwoModeFiveGradeLieModel.comm, gradingOperator,
      NuclearTwoModeFiveGradeLieModel.number1, NuclearTwoModeFiveGradeLieModel.number2,
      a1, a2, a1Dag, a2Dag, Matrix.mul_apply, Fin.sum_univ_four]

private theorem degreeZero_raise_comm_lower :
    NuclearTwoModeFiveGradeLieModel.comm degreeZeroRaise degreeZeroLower = degreeZeroCartan := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [NuclearTwoModeFiveGradeLieModel.comm, degreeZeroRaise, degreeZeroLower,
      degreeZeroCartan, NuclearTwoModeFiveGradeLieModel.number1,
      NuclearTwoModeFiveGradeLieModel.number2, a1, a2, a1Dag, a2Dag,
      Matrix.mul_apply, Fin.sum_univ_four]

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- Real basis-swap involution exchanging mode 1 and mode 2 (`Fock4` index `1 ↔ 2`). -/
def swap12 : NuclearTwoModeFiveGradeLieModel.M4R :=
  !![1, 0, 0, 0;
     0, 0, 1, 0;
     0, 1, 0, 0;
     0, 0, 0, 1]

theorem swap12_sq : swap12 * swap12 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [swap12, Matrix.mul_apply, Fin.sum_univ_four]

/-- Real `4 × 4` two-mode CAR representation of the 7 nuclear five-grade generators. -/
def representM4R : Generator → NuclearTwoModeFiveGradeLieModel.M4R
  | .pairAnnihilation => NuclearTwoModeFiveGradeLieModel.pairAnnihilation
  | .annihilationOne => a1
  | .annihilationTwo => a2
  | .cartan => gradingOperator
  | .creationOne => a1Dag
  | .creationTwo => a2Dag
  | .pairCreation => NuclearTwoModeFiveGradeLieModel.pairCreation

theorem representM4R_hasGrade (g : Generator) :
    NuclearTwoModeFiveGradeLieModel.HasGrade (degree g) (representM4R g) := by
  cases g
  · exact pairAnnihilation_grade
  · exact a1_grade
  · exact a2_grade
  · exact gradingOperator_grade
  · exact a1Dag_grade
  · exact a2Dag_grade
  · exact pairCreation_grade

/-- Faithful real Lie-algebra embedding `M₄(ℝ) →ₗ⁅ℝ⁆ End_ℂ(ℂ⁴)` intertwining
`SplitCliffordTwoModeCAR` with `NuclearTwoModeCARFiveGrade.Op` via `swap12`. -/
def m4rToOp : NuclearTwoModeFiveGradeLieModel.M4R →ₗ⁅ℝ⁆ Op where
  toFun X := Matrix.mulVecLin ((swap12 * X * swap12).map Complex.ofReal)
  map_add' X Y := by
    apply LinearMap.ext
    intro ψ
    ext i
    simp [Matrix.mulVec, dotProduct, mul_add, add_mul, Fin.sum_univ_four]
    ring
  map_smul' r X := by
    apply LinearMap.ext
    intro ψ
    ext i
    simp [Matrix.mulVec, dotProduct, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm, Fin.sum_univ_four]
    ring
  map_lie' {X Y} := by
    have hswap : (swap12 * (X * Y - Y * X) * swap12) =
        (swap12 * X * swap12) * (swap12 * Y * swap12) -
          (swap12 * Y * swap12) * (swap12 * X * swap12) := by
      calc
        swap12 * (X * Y - Y * X) * swap12
          = swap12 * X * 1 * Y * swap12 - swap12 * Y * 1 * X * swap12 := by
              noncomm_ring
        _ = swap12 * X * (swap12 * swap12) * Y * swap12 -
              swap12 * Y * (swap12 * swap12) * X * swap12 := by
              rw [swap12_sq]
        _ = (swap12 * X * swap12) * (swap12 * Y * swap12) -
              (swap12 * Y * swap12) * (swap12 * X * swap12) := by
              noncomm_ring
    have hmap_sub : ∀ P Q : NuclearTwoModeFiveGradeLieModel.M4R,
        (P - Q).map Complex.ofReal = P.map Complex.ofReal - Q.map Complex.ofReal := by
      intro P Q; ext a b; simp
    have hmap_mul : ∀ P Q : NuclearTwoModeFiveGradeLieModel.M4R,
        (P * Q).map Complex.ofReal = P.map Complex.ofReal * Q.map Complex.ofReal := by
      intro P Q; ext a b; simp [Matrix.mul_apply]
    apply LinearMap.ext
    intro ψ
    change ((swap12 * (X * Y - Y * X) * swap12).map Complex.ofReal).mulVecLin ψ =
      (((swap12 * X * swap12).map Complex.ofReal).mulVecLin *
          ((swap12 * Y * swap12).map Complex.ofReal).mulVecLin -
        ((swap12 * Y * swap12).map Complex.ofReal).mulVecLin *
          ((swap12 * X * swap12).map Complex.ofReal).mulVecLin) ψ
    rw [hswap, hmap_sub]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Matrix.mulVecLin_apply,
      Matrix.sub_mulVec, Matrix.mulVec_mulVec, hmap_mul]

theorem m4rToOp_injective : Function.Injective m4rToOp := by
  intro X Y hXY
  have hmat : swap12 * X * swap12 = swap12 * Y * swap12 := by
    ext i j
    let ej : Fock4 := fun k => if k = j then 1 else 0
    have he := congr_fun (LinearMap.congr_fun hXY ej) i
    simp only [m4rToOp, LieHom.coe_mk,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
      ej, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at he
    exact Complex.ofReal_injective he
  calc
    X = (swap12 * swap12) * X * (swap12 * swap12) := by rw [swap12_sq, one_mul, mul_one]
    _ = swap12 * (swap12 * X * swap12) * swap12 := by noncomm_ring
    _ = swap12 * (swap12 * Y * swap12) * swap12 := by rw [hmat]
    _ = (swap12 * swap12) * Y * (swap12 * swap12) := by noncomm_ring
    _ = Y := by rw [swap12_sq, one_mul, mul_one]

theorem m4rToOp_representM4R (g : Generator) :
    m4rToOp (representM4R g) = represent g := by
  apply LinearMap.ext
  intro ψ
  ext i
  dsimp [m4rToOp]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_four]
  cases g <;> fin_cases i <;>
    norm_num [representM4R, represent, swap12,
      NuclearTwoModeFiveGradeLieModel.pairAnnihilation,
      NuclearTwoModeFiveGradeLieModel.pairCreation,
      NuclearTwoModeFiveGradeLieModel.gradingOperator,
      NuclearTwoModeFiveGradeLieModel.number1,
      NuclearTwoModeFiveGradeLieModel.number2,
      a1, a2, a1Dag, a2Dag,
      NuclearTwoModeCARFiveGrade.pairAnnihilation,
      NuclearTwoModeCARFiveGrade.pairCreation,
      NuclearTwoModeCARFiveGrade.gradeCartan,
      NuclearTwoModeCARFiveGrade.numberOne,
      NuclearTwoModeCARFiveGrade.numberTwo,
      NuclearTwoModeCARFiveGrade.annihilationOne_apply,
      NuclearTwoModeCARFiveGrade.creationOne_apply,
      NuclearTwoModeCARFiveGrade.annihilationTwo_apply,
      NuclearTwoModeCARFiveGrade.creationTwo_apply,
      Matrix.mul_apply, Fin.sum_univ_four, Module.End.mul_apply]

/-- Canonical `4 × 4` skew-symmetric symplectic form preserved by the 10D 2-mode CAR
Lie algebra `sp(4, ℝ)`: `Ω * X + Xᵀ * Ω = 0`. -/
def symplecticOmega4 : NuclearTwoModeFiveGradeLieModel.M4R :=
  !![0, 0, 0, 1;
     0, 0, 1, 0;
     0, -1, 0, 0;
     -1, 0, 0, 0]

/-- The 10-dimensional symplectic Lie subalgebra `sp(4, ℝ) ≤ M₄(ℝ)` generated by
the two-mode CAR operators `{a1, a2, a1Dag, a2Dag}`. -/
def carLieSubalgebra : LieSubalgebra ℝ NuclearTwoModeFiveGradeLieModel.M4R where
  carrier := {X | symplecticOmega4 * X + Xᵀ * symplecticOmega4 = 0}
  zero_mem' := by simp
  add_mem' {X Y} hX hY := by
    change symplecticOmega4 * (X + Y) + (X + Y)ᵀ * symplecticOmega4 = 0
    rw [Matrix.transpose_add, mul_add, add_mul]
    rw [show symplecticOmega4 * X + symplecticOmega4 * Y +
        (Xᵀ * symplecticOmega4 + Yᵀ * symplecticOmega4) =
      (symplecticOmega4 * X + Xᵀ * symplecticOmega4) +
        (symplecticOmega4 * Y + Yᵀ * symplecticOmega4) by abel]
    rw [hX, hY, add_zero]
  smul_mem' r {X} hX := by
    change symplecticOmega4 * (r • X) + (r • X)ᵀ * symplecticOmega4 = 0
    rw [Matrix.transpose_smul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← smul_add,
      hX, smul_zero]
  lie_mem' {X Y} hX hY := by
    change symplecticOmega4 * (X * Y - Y * X) + (X * Y - Y * X)ᵀ * symplecticOmega4 = 0
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul]
    have hX' : symplecticOmega4 * X = -(Xᵀ * symplecticOmega4) := eq_neg_of_add_eq_zero_left hX
    have hY' : symplecticOmega4 * Y = -(Yᵀ * symplecticOmega4) := eq_neg_of_add_eq_zero_left hY
    calc
      symplecticOmega4 * (X * Y - Y * X) + (Yᵀ * Xᵀ - Xᵀ * Yᵀ) * symplecticOmega4
        = (symplecticOmega4 * X) * Y - (symplecticOmega4 * Y) * X +
            Yᵀ * Xᵀ * symplecticOmega4 - Xᵀ * Yᵀ * symplecticOmega4 := by noncomm_ring
      _ = -(Xᵀ * symplecticOmega4) * Y - -(Yᵀ * symplecticOmega4) * X +
            Yᵀ * Xᵀ * symplecticOmega4 - Xᵀ * Yᵀ * symplecticOmega4 := by rw [hX', hY']
      _ = -(Xᵀ * (symplecticOmega4 * Y)) + Yᵀ * (symplecticOmega4 * X) +
            Yᵀ * Xᵀ * symplecticOmega4 - Xᵀ * Yᵀ * symplecticOmega4 := by noncomm_ring
      _ = -(Xᵀ * -(Yᵀ * symplecticOmega4)) + Yᵀ * -(Xᵀ * symplecticOmega4) +
            Yᵀ * Xᵀ * symplecticOmega4 - Xᵀ * Yᵀ * symplecticOmega4 := by rw [hX', hY']
      _ = 0 := by noncomm_ring

theorem representM4R_mem_carLieSubalgebra (g : Generator) :
    representM4R g ∈ carLieSubalgebra := by
  change symplecticOmega4 * representM4R g + (representM4R g)ᵀ * symplecticOmega4 = 0
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply,
    Fin.sum_univ_four]
  cases g <;> fin_cases i <;> fin_cases j <;>
    norm_num [symplecticOmega4, representM4R,
      NuclearTwoModeFiveGradeLieModel.pairAnnihilation,
      NuclearTwoModeFiveGradeLieModel.pairCreation,
      NuclearTwoModeFiveGradeLieModel.gradingOperator,
      NuclearTwoModeFiveGradeLieModel.number1,
      NuclearTwoModeFiveGradeLieModel.number2,
      a1, a2, a1Dag, a2Dag, Matrix.mul_apply, Fin.sum_univ_four]

theorem degreeZeroSL2_mem_carLieSubalgebra :
    degreeZeroRaise ∈ carLieSubalgebra ∧
    degreeZeroLower ∈ carLieSubalgebra ∧
    degreeZeroCartan ∈ carLieSubalgebra := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · change symplecticOmega4 * _ + _ᵀ * symplecticOmega4 = 0
    ext i j
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply,
      Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;>
      norm_num [symplecticOmega4, degreeZeroRaise, degreeZeroLower, degreeZeroCartan,
        NuclearTwoModeFiveGradeLieModel.number1,
        NuclearTwoModeFiveGradeLieModel.number2,
        a1, a2, a1Dag, a2Dag, Matrix.mul_apply, Fin.sum_univ_four]

private theorem carLieSubalgebra_entry_laws {X : NuclearTwoModeFiveGradeLieModel.M4R}
    (hX : X ∈ carLieSubalgebra) :
    X 0 0 = -X 3 3 ∧ X 1 1 = -X 2 2 ∧
    X 3 1 = X 2 0 ∧ X 3 2 = -X 1 0 ∧
    X 1 3 = X 0 2 ∧ X 2 3 = -X 0 1 := by
  change symplecticOmega4 * X + Xᵀ * symplecticOmega4 = 0 at hX
  have h00 := congr_fun (congr_fun hX 0) 3
  have h11 := congr_fun (congr_fun hX 1) 2
  have h31 := congr_fun (congr_fun hX 0) 1
  have h32 := congr_fun (congr_fun hX 0) 2
  have h13 := congr_fun (congr_fun hX 2) 3
  have h23 := congr_fun (congr_fun hX 1) 3
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply,
    Fin.sum_univ_four] at h00 h11 h31 h32 h13 h23
  norm_num [symplecticOmega4] at h00 h11 h31 h32 h13 h23
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- `carLieSubalgebra` (`sp(4, ℝ)`) is generated as a Lie subalgebra by `{a1, a2, a1Dag, a2Dag}`. -/
theorem carLieSubalgebra_eq_lieSpan :
    carLieSubalgebra =
      LieSubalgebra.lieSpan ℝ NuclearTwoModeFiveGradeLieModel.M4R
        {a1, a2, a1Dag, a2Dag} := by
  apply le_antisymm
  · intro X hX
    let S := LieSubalgebra.lieSpan ℝ NuclearTwoModeFiveGradeLieModel.M4R {a1, a2, a1Dag, a2Dag}
    have ha1 : a1 ∈ S := LieSubalgebra.subset_lieSpan (by simp)
    have ha2 : a2 ∈ S := LieSubalgebra.subset_lieSpan (by simp)
    have ha1d : a1Dag ∈ S := LieSubalgebra.subset_lieSpan (by simp)
    have ha2d : a2Dag ∈ S := LieSubalgebra.subset_lieSpan (by simp)
    have hEp : NuclearTwoModeFiveGradeLieModel.pairCreation ∈ S := by
      have hbr : ⁅a1Dag, a2Dag⁆ = (2 : ℝ) • NuclearTwoModeFiveGradeLieModel.pairCreation :=
        creation_bracket_generates_pair
      have hmem : (1 / 2 : ℝ) • ⁅a1Dag, a2Dag⁆ ∈ S := S.smul_mem _ (S.lie_mem ha1d ha2d)
      rw [hbr, smul_smul] at hmem
      simpa using hmem
    have hEm : NuclearTwoModeFiveGradeLieModel.pairAnnihilation ∈ S := by
      have hbr : ⁅a1, a2⁆ = (-2 : ℝ) • NuclearTwoModeFiveGradeLieModel.pairAnnihilation :=
        annihilation_bracket_generates_pair
      have hmem : (-1 / 2 : ℝ) • ⁅a1, a2⁆ ∈ S := S.smul_mem _ (S.lie_mem ha1 ha2)
      rw [hbr, smul_smul] at hmem
      simpa using hmem
    have hH : gradingOperator ∈ S := by
      rw [← pair_extreme_bracket]
      exact S.lie_mem hEp hEm
    have hE0 : degreeZeroRaise ∈ S := by
      have hbr : ⁅a2, a1Dag⁆ = (-2 : ℝ) • degreeZeroRaise := by
        ext i j; fin_cases i <;> fin_cases j <;>
          norm_num [Ring.lie_def, degreeZeroRaise, a2, a1Dag, Matrix.mul_apply, Fin.sum_univ_four]
      have hmem : (-1 / 2 : ℝ) • ⁅a2, a1Dag⁆ ∈ S := S.smul_mem _ (S.lie_mem ha2 ha1d)
      rw [hbr, smul_smul] at hmem
      simpa using hmem
    have hF0 : degreeZeroLower ∈ S := by
      have hbr : ⁅a1, a2Dag⁆ = (-2 : ℝ) • degreeZeroLower := by
        ext i j; fin_cases i <;> fin_cases j <;>
          norm_num [Ring.lie_def, degreeZeroLower, a1, a2Dag, Matrix.mul_apply, Fin.sum_univ_four]
      have hmem : (-1 / 2 : ℝ) • ⁅a1, a2Dag⁆ ∈ S := S.smul_mem _ (S.lie_mem ha1 ha2d)
      rw [hbr, smul_smul] at hmem
      simpa using hmem
    have hH0 : degreeZeroCartan ∈ S := by
      rw [← degreeZero_raise_comm_lower]
      exact S.lie_mem hE0 hF0
    have ⟨h00, h11, h31, h32, h13, h23⟩ := carLieSubalgebra_entry_laws hX
    have hX_eq :
        X = X 3 0 • NuclearTwoModeFiveGradeLieModel.pairCreation +
            X 2 0 • a1Dag + X 1 0 • a2Dag + X 3 3 • gradingOperator +
            X 2 1 • degreeZeroRaise + X 1 2 • degreeZeroLower + X 2 2 • degreeZeroCartan +
            X 0 2 • a1 + X 0 1 • a2 + X 0 3 • NuclearTwoModeFiveGradeLieModel.pairAnnihilation := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [NuclearTwoModeFiveGradeLieModel.pairCreation,
          NuclearTwoModeFiveGradeLieModel.pairAnnihilation,
          gradingOperator, NuclearTwoModeFiveGradeLieModel.number1,
          NuclearTwoModeFiveGradeLieModel.number2,
          degreeZeroRaise, degreeZeroLower, degreeZeroCartan,
          a1, a2, a1Dag, a2Dag, h00, h11, h31, h32, h13, h23]
    rw [hX_eq]
    repeat apply S.add_mem
    all_goals exact S.smul_mem _ (by assumption)
  · rw [LieSubalgebra.lieSpan_le]
    intro X hX
    rcases hX with rfl | rfl | rfl | rfl
    · exact representM4R_mem_carLieSubalgebra .annihilationOne
    · exact representM4R_mem_carLieSubalgebra .annihilationTwo
    · exact representM4R_mem_carLieSubalgebra .creationOne
    · exact representM4R_mem_carLieSubalgebra .creationTwo

/-- Basis charge `Q₁ = (1, 0, 0, 0)` in `FreudenthalCharge J`. -/
def q1Charge {J : Type*} [AddCommGroup J] [Module ℝ J] : FreudenthalCharge J :=
  ⟨1, 0, 0, 0⟩

/-- Basis charge `Q₂ = (0, 1, 0, 0)` in `FreudenthalCharge J`. -/
def q2Charge {J : Type*} [AddCommGroup J] [Module ℝ J] : FreudenthalCharge J :=
  ⟨0, 1, 0, 0⟩

/-- Canonical `sp(2, ℝ)` zero-grade symplectic operator in `SymplecticZero D` corresponding
to `(E₀, F₀, H₀)` of the two-mode CAR algebra. -/
def sympOfM4R {J : Type*} [AddCommGroup J] [Module ℝ J] (D : CubicJordanDatum J)
    (e0 f0 h0 : ℝ) : SymplecticZero D :=
  (e0 / 2) • mixedSymplecticBracket D q1Charge q1Charge +
    (-f0 / 2) • mixedSymplecticBracket D q2Charge q2Charge +
    (-h0) • mixedSymplecticBracket D q1Charge q2Charge

private theorem sympOfM4R_apply {J : Type*} [AddCommGroup J] [Module ℝ J]
    (D : CubicJordanDatum J) (e0 f0 h0 : ℝ) (Z : FreudenthalCharge J) :
    ((sympOfM4R D e0 f0 h0 : Module.End ℝ (FreudenthalCharge J)) Z) =
      ⟨h0 * Z.alpha + e0 * Z.beta, f0 * Z.alpha - h0 * Z.beta, 0, 0⟩ := by
  have neg_alpha : ∀ Q : FreudenthalCharge J, (-Q).alpha = -Q.alpha := fun _ => rfl
  have neg_beta : ∀ Q : FreudenthalCharge J, (-Q).beta = -Q.beta := fun _ => rfl
  have neg_x : ∀ Q : FreudenthalCharge J, (-Q).x = -Q.x := fun _ => rfl
  have neg_y : ∀ Q : FreudenthalCharge J, (-Q).y = -Q.y := fun _ => rfl
  dsimp [sympOfM4R]
  simp only [symplecticRankTwo_apply, FreudenthalCharge.symplecticForm, q1Charge, q2Charge,
    map_zero, LinearMap.zero_apply]
  apply FreudenthalCharge.ext <;>
    simp [alpha_add, alpha_smul, neg_alpha, beta_add, beta_smul, neg_beta,
      x_add, x_smul, neg_x, y_add, y_smul, neg_y] <;> ring

private theorem carToFiveGraded_lie_m2 {J : Type*} [AddCommGroup J] [Module ℝ J]
    (D : CubicJordanDatum J) {X Y : carLieSubalgebra} :
    (NuclearTwoModeFiveGradeLieModel.comm X.1 Y.1) 0 3 =
      (-2 * X.1 3 3 * Y.1 0 3 + 2 * Y.1 3 3 * X.1 0 3) -
        2 * FreudenthalCharge.symplecticForm D
          ((-X.1 0 1) • q1Charge + X.1 0 2 • q2Charge)
          ((-Y.1 0 1) • q1Charge + Y.1 0 2 • q2Charge) := by
  have ⟨hx00, _, _, _, hx13, hx23⟩ := carLieSubalgebra_entry_laws X.2
  have ⟨hy00, _, _, _, hy13, hy23⟩ := carLieSubalgebra_entry_laws Y.2
  dsimp [NuclearTwoModeFiveGradeLieModel.comm]
  simp only [Matrix.mul_apply, Fin.sum_univ_four,
    FreudenthalCharge.symplecticForm, q1Charge, q2Charge,
    alpha_add, alpha_smul, beta_add, beta_smul, x_add, x_smul, y_add, y_smul,
    smul_zero, add_zero, map_zero,
    hx00, hx13, hx23, hy00, hy13, hy23]
  ring

private theorem carToFiveGraded_lie_m1 {J : Type*} [AddCommGroup J] [Module ℝ J]
    (D : CubicJordanDatum J) {X Y : carLieSubalgebra} :
    (-(NuclearTwoModeFiveGradeLieModel.comm X.1 Y.1) 0 1) • q1Charge +
        (NuclearTwoModeFiveGradeLieModel.comm X.1 Y.1) 0 2 • q2Charge =
      (-X.1 3 3 • ((-Y.1 0 1) • q1Charge + Y.1 0 2 • q2Charge) +
        Y.1 3 3 • ((-X.1 0 1) • q1Charge + X.1 0 2 • q2Charge)) +
        ((sympOfM4R D (X.1 2 1) (X.1 1 2) (X.1 2 2) : Module.End ℝ (FreudenthalCharge J))
          ((-Y.1 0 1) • q1Charge + Y.1 0 2 • q2Charge) -
         (sympOfM4R D (Y.1 2 1) (Y.1 1 2) (Y.1 2 2) : Module.End ℝ (FreudenthalCharge J))
          ((-X.1 0 1) • q1Charge + X.1 0 2 • q2Charge)) +
        ((-X.1 0 3) • (Y.1 2 0 • q1Charge + Y.1 1 0 • q2Charge) +
         Y.1 0 3 • (X.1 2 0 • q1Charge + X.1 1 0 • q2Charge)) := by
  have ⟨hx00, hx11, hx31, hx32, _, _⟩ := carLieSubalgebra_entry_laws X.2
  have ⟨hy00, hy11, hy31, hy32, _, _⟩ := carLieSubalgebra_entry_laws Y.2
  have neg_x : ∀ Q : FreudenthalCharge J, (-Q).x = -Q.x := fun _ => rfl
  have neg_y : ∀ Q : FreudenthalCharge J, (-Q).y = -Q.y := fun _ => rfl
  have sub_alpha : ∀ P Q : FreudenthalCharge J, (P - Q).alpha = P.alpha - Q.alpha := fun _ _ => rfl
  have sub_beta : ∀ P Q : FreudenthalCharge J, (P - Q).beta = P.beta - Q.beta := fun _ _ => rfl
  have sub_x : ∀ P Q : FreudenthalCharge J, (P - Q).x = P.x - Q.x := fun _ _ => rfl
  have sub_y : ∀ P Q : FreudenthalCharge J, (P - Q).y = P.y - Q.y := fun _ _ => rfl
  dsimp [NuclearTwoModeFiveGradeLieModel.comm]
  apply FreudenthalCharge.ext
  · simp only [Matrix.mul_apply, Fin.sum_univ_four,
      alpha_add, alpha_smul, beta_add, beta_smul, sub_alpha,
      sympOfM4R_apply, q1Charge, q2Charge,
      hx00, hx11, hx31, hy00, hy11, hy31]
    ring
  · simp only [Matrix.mul_apply, Fin.sum_univ_four,
      alpha_add, alpha_smul, beta_add, beta_smul, sub_beta,
      sympOfM4R_apply, q1Charge, q2Charge,
      hx00, hx11, hx32, hy00, hy11, hy32]
    ring
  · simp [x_add, x_smul, neg_x, sub_x, sympOfM4R_apply, q1Charge, q2Charge]
  · simp [y_add, y_smul, neg_y, sub_y, sympOfM4R_apply, q1Charge, q2Charge]

private theorem carToFiveGraded_lie_0symp {J : Type*} [AddCommGroup J] [Module ℝ J]
    (D : CubicJordanDatum J) {X Y : carLieSubalgebra} :
    sympOfM4R D ((NuclearTwoModeFiveGradeLieModel.comm X.1 Y.1) 2 1)
        ((NuclearTwoModeFiveGradeLieModel.comm X.1 Y.1) 1 2)
        ((NuclearTwoModeFiveGradeLieModel.comm X.1 Y.1) 2 2) =
      ⁅sympOfM4R D (X.1 2 1) (X.1 1 2) (X.1 2 2),
        sympOfM4R D (Y.1 2 1) (Y.1 1 2) (Y.1 2 2)⁆ +
      mixedSymplecticBracket D
        ((-X.1 0 1) • q1Charge + X.1 0 2 • q2Charge)
        (Y.1 2 0 • q1Charge + Y.1 1 0 • q2Charge) -
      mixedSymplecticBracket D
        ((-Y.1 0 1) • q1Charge + Y.1 0 2 • q2Charge)
        (X.1 2 0 • q1Charge + X.1 1 0 • q2Charge) := by
  have ⟨_, hx11, hx31, hx32, hx13, hx23⟩ := carLieSubalgebra_entry_laws X.2
  have ⟨_, hy11, hy31, hy32, hy13, hy23⟩ := carLieSubalgebra_entry_laws Y.2
  have sub_alpha : ∀ P Q : FreudenthalCharge J, (P - Q).alpha = P.alpha - Q.alpha := fun _ _ => rfl
  have sub_beta : ∀ P Q : FreudenthalCharge J, (P - Q).beta = P.beta - Q.beta := fun _ _ => rfl
  have sub_x : ∀ P Q : FreudenthalCharge J, (P - Q).x = P.x - Q.x := fun _ _ => rfl
  have sub_y : ∀ P Q : FreudenthalCharge J, (P - Q).y = P.y - Q.y := fun _ _ => rfl
  have neg_x : ∀ Q : FreudenthalCharge J, (-Q).x = -Q.x := fun _ => rfl
  have neg_y : ∀ Q : FreudenthalCharge J, (-Q).y = -Q.y := fun _ => rfl
  apply Subtype.ext
  apply LinearMap.ext
  intro Z
  dsimp [NuclearTwoModeFiveGradeLieModel.comm]
  simp only [symplecticRankTwo_apply, sympOfM4R_apply,
    FreudenthalCharge.symplecticForm, q1Charge, q2Charge,
    alpha_add, alpha_smul, beta_add, beta_smul, x_add, x_smul, y_add, y_smul,
    smul_zero, Matrix.mul_apply, Fin.sum_univ_four]
  apply FreudenthalCharge.ext
  · simp only [sub_alpha, alpha_add, alpha_smul, add_zero, map_zero, LinearMap.zero_apply,
      hx11, hx31, hx32, hx23, hy11, hy31, hy32, hy23]
    ring
  · simp only [sub_beta, beta_add, beta_smul, add_zero, map_zero, LinearMap.zero_apply,
      hx11, hx32, hx13, hx23, hy11, hy32, hy13, hy23]
    ring
  · simp [sub_x, x_add, x_smul, neg_x]
  · simp [sub_y, y_add, y_smul, neg_y]

private theorem carToFiveGraded_lie_0s {J : Type*} [AddCommGroup J] [Module ℝ J]
    (D : CubicJordanDatum J) {X Y : carLieSubalgebra} :
    (NuclearTwoModeFiveGradeLieModel.comm X.1 Y.1) 3 3 =
      (X.1 3 0 * Y.1 0 3 - Y.1 3 0 * X.1 0 3) +
        (FreudenthalCharge.symplecticForm D
          ((-X.1 0 1) • q1Charge + X.1 0 2 • q2Charge)
          (Y.1 2 0 • q1Charge + Y.1 1 0 • q2Charge) -
         FreudenthalCharge.symplecticForm D
          ((-Y.1 0 1) • q1Charge + Y.1 0 2 • q2Charge)
          (X.1 2 0 • q1Charge + X.1 1 0 • q2Charge)) := by
  have ⟨_, _, hx31, hx32, hx13, hx23⟩ := carLieSubalgebra_entry_laws X.2
  have ⟨_, _, hy31, hy32, hy13, hy23⟩ := carLieSubalgebra_entry_laws Y.2
  dsimp [NuclearTwoModeFiveGradeLieModel.comm]
  simp only [Matrix.mul_apply, Fin.sum_univ_four,
    FreudenthalCharge.symplecticForm, q1Charge, q2Charge,
    alpha_add, alpha_smul, beta_add, beta_smul, x_add, x_smul, y_add, y_smul,
    smul_zero, add_zero, map_zero,
    hx31, hx32, hx13, hx23, hy31, hy32, hy13, hy23]
  ring

private theorem carToFiveGraded_lie_p1 {J : Type*} [AddCommGroup J] [Module ℝ J]
    (D : CubicJordanDatum J) {X Y : carLieSubalgebra} :
    (NuclearTwoModeFiveGradeLieModel.comm X.1 Y.1) 2 0 • q1Charge +
        (NuclearTwoModeFiveGradeLieModel.comm X.1 Y.1) 1 0 • q2Charge =
      (X.1 3 3 • (Y.1 2 0 • q1Charge + Y.1 1 0 • q2Charge) -
        Y.1 3 3 • (X.1 2 0 • q1Charge + X.1 1 0 • q2Charge)) +
        ((sympOfM4R D (X.1 2 1) (X.1 1 2) (X.1 2 2) : Module.End ℝ (FreudenthalCharge J))
          (Y.1 2 0 • q1Charge + Y.1 1 0 • q2Charge) -
         (sympOfM4R D (Y.1 2 1) (Y.1 1 2) (Y.1 2 2) : Module.End ℝ (FreudenthalCharge J))
          (X.1 2 0 • q1Charge + X.1 1 0 • q2Charge)) +
        ((-X.1 3 0) • ((-Y.1 0 1) • q1Charge + Y.1 0 2 • q2Charge) +
         Y.1 3 0 • ((-X.1 0 1) • q1Charge + X.1 0 2 • q2Charge)) := by
  have ⟨hx00, hx11, _, _, hx13, hx23⟩ := carLieSubalgebra_entry_laws X.2
  have ⟨hy00, hy11, _, _, hy13, hy23⟩ := carLieSubalgebra_entry_laws Y.2
  have neg_x : ∀ Q : FreudenthalCharge J, (-Q).x = -Q.x := fun _ => rfl
  have neg_y : ∀ Q : FreudenthalCharge J, (-Q).y = -Q.y := fun _ => rfl
  have sub_alpha : ∀ P Q : FreudenthalCharge J, (P - Q).alpha = P.alpha - Q.alpha := fun _ _ => rfl
  have sub_beta : ∀ P Q : FreudenthalCharge J, (P - Q).beta = P.beta - Q.beta := fun _ _ => rfl
  have sub_x : ∀ P Q : FreudenthalCharge J, (P - Q).x = P.x - Q.x := fun _ _ => rfl
  have sub_y : ∀ P Q : FreudenthalCharge J, (P - Q).y = P.y - Q.y := fun _ _ => rfl
  dsimp [NuclearTwoModeFiveGradeLieModel.comm]
  apply FreudenthalCharge.ext
  · simp only [Matrix.mul_apply, Fin.sum_univ_four,
      alpha_add, alpha_smul, beta_add, beta_smul, sub_alpha,
      sympOfM4R_apply, q1Charge, q2Charge,
      hx00, hx23, hy00, hy23]
    ring
  · simp only [Matrix.mul_apply, Fin.sum_univ_four,
      alpha_add, alpha_smul, beta_add, beta_smul, sub_beta,
      sympOfM4R_apply, q1Charge, q2Charge,
      hx00, hx11, hx13, hy00, hy11, hy13]
    ring
  · simp [x_add, x_smul, neg_x, sub_x, sympOfM4R_apply, q1Charge, q2Charge]
  · simp [y_add, y_smul, neg_y, sub_y, sympOfM4R_apply, q1Charge, q2Charge]

private theorem carToFiveGraded_lie_p2 {J : Type*} [AddCommGroup J] [Module ℝ J]
    (D : CubicJordanDatum J) {X Y : carLieSubalgebra} :
    (NuclearTwoModeFiveGradeLieModel.comm X.1 Y.1) 3 0 =
      (2 * X.1 3 3 * Y.1 3 0 - 2 * Y.1 3 3 * X.1 3 0) +
        2 * FreudenthalCharge.symplecticForm D
          (X.1 2 0 • q1Charge + X.1 1 0 • q2Charge)
          (Y.1 2 0 • q1Charge + Y.1 1 0 • q2Charge) := by
  have ⟨hx00, _, hx31, hx32, _, _⟩ := carLieSubalgebra_entry_laws X.2
  have ⟨hy00, _, hy31, hy32, _, _⟩ := carLieSubalgebra_entry_laws Y.2
  dsimp [NuclearTwoModeFiveGradeLieModel.comm]
  simp only [Matrix.mul_apply, Fin.sum_univ_four,
    FreudenthalCharge.symplecticForm, q1Charge, q2Charge,
    alpha_add, alpha_smul, beta_add, beta_smul, x_add, x_smul, y_add, y_smul,
    smul_zero, add_zero, map_zero,
    hx00, hx31, hx32, hy00, hy31, hy32]
  ring

private theorem carToFiveGraded_map_smul_minus1 {J : Type*} [AddCommGroup J] [Module ℝ J]
    (r : ℝ) (X : carLieSubalgebra) :
    (-(r • X).1 0 1) • q1Charge + (r • X).1 0 2 • q2Charge =
      r • ((-X.1 0 1) • (q1Charge : FreudenthalCharge J) + X.1 0 2 • q2Charge) := by
  have hcar_smul : (r • X).1 = r • X.1 := rfl
  have neg_alpha : ∀ Q : FreudenthalCharge J, (-Q).alpha = -Q.alpha := fun _ => rfl
  have neg_beta : ∀ Q : FreudenthalCharge J, (-Q).beta = -Q.beta := fun _ => rfl
  have neg_x : ∀ Q : FreudenthalCharge J, (-Q).x = -Q.x := fun _ => rfl
  have neg_y : ∀ Q : FreudenthalCharge J, (-Q).y = -Q.y := fun _ => rfl
  apply FreudenthalCharge.ext
  · simp [hcar_smul, alpha_add, alpha_smul, neg_alpha, q1Charge, q2Charge, smul_eq_mul]
  · simp [hcar_smul, beta_add, beta_smul, neg_beta, q1Charge, q2Charge, smul_eq_mul]
  · simp [hcar_smul, x_add, x_smul, neg_x, q1Charge, q2Charge]
  · simp [hcar_smul, y_add, y_smul, neg_y, q1Charge, q2Charge]

private theorem carToFiveGraded_map_smul_plus1 {J : Type*} [AddCommGroup J] [Module ℝ J]
    (r : ℝ) (X : carLieSubalgebra) :
    (r • X).1 2 0 • q1Charge + (r • X).1 1 0 • q2Charge =
      r • (X.1 2 0 • (q1Charge : FreudenthalCharge J) + X.1 1 0 • q2Charge) := by
  have hcar_smul : (r • X).1 = r • X.1 := rfl
  apply FreudenthalCharge.ext
  · simp [hcar_smul, alpha_add, alpha_smul, q1Charge, q2Charge, smul_eq_mul]
  · simp [hcar_smul, beta_add, beta_smul, q1Charge, q2Charge, smul_eq_mul]
  · simp [hcar_smul, x_add, x_smul, q1Charge, q2Charge]
  · simp [hcar_smul, y_add, y_smul, q1Charge, q2Charge]

private theorem carToFiveGraded_map_lie_aux {J : Type*} [AddCommGroup J] [Module ℝ J]
    (D : CubicJordanDatum J) (X Y : carLieSubalgebra) :
    ({ minus2 := (⁅X, Y⁆ : carLieSubalgebra).1 0 3
       minus1 := (-(⁅X, Y⁆ : carLieSubalgebra).1 0 1) • q1Charge + (⁅X, Y⁆ : carLieSubalgebra).1 0 2 • q2Charge
       zero_symp := sympOfM4R D ((⁅X, Y⁆ : carLieSubalgebra).1 2 1)
         ((⁅X, Y⁆ : carLieSubalgebra).1 1 2) ((⁅X, Y⁆ : carLieSubalgebra).1 2 2)
       zero_scale := (⁅X, Y⁆ : carLieSubalgebra).1 3 3
       plus1 := (⁅X, Y⁆ : carLieSubalgebra).1 2 0 • q1Charge + (⁅X, Y⁆ : carLieSubalgebra).1 1 0 • q2Charge
       plus2 := (⁅X, Y⁆ : carLieSubalgebra).1 3 0 } : FiveGradedCarrier D) =
      ⁅({ minus2 := X.1 0 3
          minus1 := (-X.1 0 1) • q1Charge + X.1 0 2 • q2Charge
          zero_symp := sympOfM4R D (X.1 2 1) (X.1 1 2) (X.1 2 2)
          zero_scale := X.1 3 3
          plus1 := X.1 2 0 • q1Charge + X.1 1 0 • q2Charge
          plus2 := X.1 3 0 } : FiveGradedCarrier D),
       ({ minus2 := Y.1 0 3
          minus1 := (-Y.1 0 1) • q1Charge + Y.1 0 2 • q2Charge
          zero_symp := sympOfM4R D (Y.1 2 1) (Y.1 1 2) (Y.1 2 2)
          zero_scale := Y.1 3 3
          plus1 := Y.1 2 0 • q1Charge + Y.1 1 0 • q2Charge
          plus2 := Y.1 3 0 } : FiveGradedCarrier D)⁆ := by
  apply FiveGradedCarrier.ext
  · dsimp [symplecticContactBracket]; exact carToFiveGraded_lie_m2 D
  · dsimp [symplecticContactBracket]; exact carToFiveGraded_lie_m1 D
  · dsimp [symplecticContactBracket]; exact carToFiveGraded_lie_0symp D
  · dsimp [symplecticContactBracket]; exact carToFiveGraded_lie_0s D
  · dsimp [symplecticContactBracket]; exact carToFiveGraded_lie_p1 D
  · dsimp [symplecticContactBracket]; exact carToFiveGraded_lie_p2 D

private theorem carToFiveGraded_map_add_aux {J : Type*} [AddCommGroup J] [Module ℝ J]
    (D : CubicJordanDatum J) (X Y : carLieSubalgebra) :
    ({ minus2 := (X + Y).1 0 3
       minus1 := (-(X + Y).1 0 1) • q1Charge + (X + Y).1 0 2 • q2Charge
       zero_symp := sympOfM4R D ((X + Y).1 2 1) ((X + Y).1 1 2) ((X + Y).1 2 2)
       zero_scale := (X + Y).1 3 3
       plus1 := (X + Y).1 2 0 • q1Charge + (X + Y).1 1 0 • q2Charge
       plus2 := (X + Y).1 3 0 } : FiveGradedCarrier D) =
      ({ minus2 := X.1 0 3
         minus1 := (-X.1 0 1) • q1Charge + X.1 0 2 • q2Charge
         zero_symp := sympOfM4R D (X.1 2 1) (X.1 1 2) (X.1 2 2)
         zero_scale := X.1 3 3
         plus1 := X.1 2 0 • q1Charge + X.1 1 0 • q2Charge
         plus2 := X.1 3 0 } : FiveGradedCarrier D) +
        ({ minus2 := Y.1 0 3
           minus1 := (-Y.1 0 1) • q1Charge + Y.1 0 2 • q2Charge
           zero_symp := sympOfM4R D (Y.1 2 1) (Y.1 1 2) (Y.1 2 2)
           zero_scale := Y.1 3 3
           plus1 := Y.1 2 0 • q1Charge + Y.1 1 0 • q2Charge
           plus2 := Y.1 3 0 } : FiveGradedCarrier D) := by
  have hcar_add : (X + Y).1 = X.1 + Y.1 := rfl
  have h0_add : ∀ A B : SymplecticZero D,
      ((A + B : SymplecticZero D) : Module.End ℝ (FreudenthalCharge J)) = A.1 + B.1 := fun _ _ => rfl
  apply FiveGradedCarrier.ext
  · rw [hcar_add]; simp
  · simp only [FiveGradedCarrier.add_minus1, hcar_add, Matrix.add_apply]
    module
  · apply Subtype.ext; apply LinearMap.ext; intro Z
    simp only [FiveGradedCarrier.add_zero_symp, h0_add, LinearMap.add_apply,
      sympOfM4R_apply, hcar_add, Matrix.add_apply]
    apply FreudenthalCharge.ext <;>
      simp [alpha_add, beta_add, x_add, y_add] <;> ring
  · rw [hcar_add]; simp
  · simp only [FiveGradedCarrier.add_plus1, hcar_add, Matrix.add_apply]
    module
  · rw [hcar_add]; simp

private theorem carToFiveGraded_map_smul_aux {J : Type*} [AddCommGroup J] [Module ℝ J]
    (D : CubicJordanDatum J) (r : ℝ) (X : carLieSubalgebra) :
    ({ minus2 := (r • X).1 0 3
       minus1 := (-(r • X).1 0 1) • q1Charge + (r • X).1 0 2 • q2Charge
       zero_symp := sympOfM4R D ((r • X).1 2 1) ((r • X).1 1 2) ((r • X).1 2 2)
       zero_scale := (r • X).1 3 3
       plus1 := (r • X).1 2 0 • q1Charge + (r • X).1 1 0 • q2Charge
       plus2 := (r • X).1 3 0 } : FiveGradedCarrier D) =
      r • ({ minus2 := X.1 0 3
             minus1 := (-X.1 0 1) • q1Charge + X.1 0 2 • q2Charge
             zero_symp := sympOfM4R D (X.1 2 1) (X.1 1 2) (X.1 2 2)
             zero_scale := X.1 3 3
             plus1 := X.1 2 0 • q1Charge + X.1 1 0 • q2Charge
             plus2 := X.1 3 0 } : FiveGradedCarrier D) := by
  have hcar_smul : (r • X).1 = r • X.1 := rfl
  have h0_smul : ∀ (s : ℝ) (A : SymplecticZero D),
      ((s • A : SymplecticZero D) : Module.End ℝ (FreudenthalCharge J)) = s • A.1 := fun _ _ => rfl
  apply FiveGradedCarrier.ext
  · rw [hcar_smul]; simp [smul_eq_mul]
  · exact carToFiveGraded_map_smul_minus1 r X
  · apply Subtype.ext; apply LinearMap.ext; intro Z
    simp only [FiveGradedCarrier.smul_zero_symp, h0_smul, LinearMap.smul_apply,
      sympOfM4R_apply, hcar_smul, Matrix.smul_apply, smul_eq_mul]
    apply FreudenthalCharge.ext <;>
      simp [alpha_smul, beta_smul, x_smul, y_smul] <;> ring
  · rw [hcar_smul]; simp [smul_eq_mul]
  · exact carToFiveGraded_map_smul_plus1 r X
  · rw [hcar_smul]; simp [smul_eq_mul]

/-- **Concrete-to-Freudenthal Five-Grading Lie Algebra Homomorphism**:
For **any** `[AddCommGroup J] [Module ℝ J]` and **any** `CubicJordanDatum J`, maps the
10D concrete two-mode CAR Lie algebra `carLieSubalgebra` (`sp(4, ℝ)`) faithfully and
grade-preservingly into `Freudenthal.FiveGradedCarrier D`. -/
def carToFiveGraded {J : Type*} [AddCommGroup J] [Module ℝ J] (D : CubicJordanDatum J) :
    carLieSubalgebra →ₗ⁅ℝ⁆ FiveGradedCarrier D where
  toFun X :=
    { minus2 := X.1 0 3
      minus1 := (-X.1 0 1) • q1Charge + X.1 0 2 • q2Charge
      zero_symp := sympOfM4R D (X.1 2 1) (X.1 1 2) (X.1 2 2)
      zero_scale := X.1 3 3
      plus1 := X.1 2 0 • q1Charge + X.1 1 0 • q2Charge
      plus2 := X.1 3 0 }
  map_add' := carToFiveGraded_map_add_aux D
  map_smul' := carToFiveGraded_map_smul_aux D
  map_lie' {X Y} := carToFiveGraded_map_lie_aux D X Y

theorem carToFiveGraded_injective {J : Type*} [AddCommGroup J] [Module ℝ J]
    (D : CubicJordanDatum J) : Function.Injective (carToFiveGraded D) := by
  intro X Y hXY
  have hm2 : X.1 0 3 = Y.1 0 3 := congrArg FiveGradedCarrier.minus2 hXY
  have hp2 : X.1 3 0 = Y.1 3 0 := congrArg FiveGradedCarrier.plus2 hXY
  have hsc : X.1 3 3 = Y.1 3 3 := congrArg FiveGradedCarrier.zero_scale hXY
  have hm1 := congrArg FiveGradedCarrier.minus1 hXY
  have hm1a : X.1 0 1 = Y.1 0 1 := by
    have ha := congrArg FreudenthalCharge.alpha hm1
    dsimp [carToFiveGraded] at ha
    simpa [alpha_add, alpha_smul, q1Charge, q2Charge] using ha
  have hm1b : X.1 0 2 = Y.1 0 2 := by
    have hb := congrArg FreudenthalCharge.beta hm1
    dsimp [carToFiveGraded] at hb
    simpa [beta_add, beta_smul, q1Charge, q2Charge] using hb
  have hp1 := congrArg FiveGradedCarrier.plus1 hXY
  have hp1a : X.1 2 0 = Y.1 2 0 := by
    have ha := congrArg FreudenthalCharge.alpha hp1
    dsimp [carToFiveGraded] at ha
    simpa [alpha_add, alpha_smul, q1Charge, q2Charge] using ha
  have hp1b : X.1 1 0 = Y.1 1 0 := by
    have hb := congrArg FreudenthalCharge.beta hp1
    dsimp [carToFiveGraded] at hb
    simpa [beta_add, beta_smul, q1Charge, q2Charge] using hb
  have hsymp := congrArg (fun u => ((u.zero_symp : Module.End ℝ (FreudenthalCharge J)) q1Charge)) hXY
  have hsymp2 := congrArg (fun u => ((u.zero_symp : Module.End ℝ (FreudenthalCharge J)) q2Charge)) hXY
  have h22 : X.1 2 2 = Y.1 2 2 := by
    have ha := congrArg FreudenthalCharge.alpha hsymp
    simpa [carToFiveGraded, sympOfM4R_apply, q1Charge] using ha
  have h12 : X.1 1 2 = Y.1 1 2 := by
    have hb := congrArg FreudenthalCharge.beta hsymp
    simpa [carToFiveGraded, sympOfM4R_apply, q1Charge] using hb
  have h21 : X.1 2 1 = Y.1 2 1 := by
    have ha := congrArg FreudenthalCharge.alpha hsymp2
    simpa [carToFiveGraded, sympOfM4R_apply, q2Charge] using ha
  have ⟨hx00, hx11, hx31, hx32, hx13, hx23⟩ := carLieSubalgebra_entry_laws X.2
  have ⟨hy00, hy11, hy31, hy32, hy13, hy23⟩ := carLieSubalgebra_entry_laws Y.2
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · dsimp; rw [hx00, hy00, hsc]
  · exact hm1a
  · exact hm1b
  · exact hm2
  · exact hp1b
  · dsimp; rw [hx11, hy11, h22]
  · exact h12
  · dsimp; rw [hx13, hy13, hm1b]
  · exact hp1a
  · exact h21
  · exact h22
  · dsimp; rw [hx23, hy23, hm1a]
  · exact hp2
  · dsimp; rw [hx31, hy31, hp1a]
  · dsimp; rw [hx32, hy32, hp1b]
  · exact hsc

theorem carToFiveGraded_preserves_grade {J : Type*} [AddCommGroup J] [Module ℝ J]
    (D : CubicJordanDatum J) {k : ℤ} {X : carLieSubalgebra}
    (hX : NuclearTwoModeFiveGradeLieModel.HasGrade k X.1) :
    SymplecticContactHasGrade D k (carToFiveGraded D X) := by
  have hH : (⟨gradingOperator, representM4R_mem_carLieSubalgebra .cartan⟩ : carLieSubalgebra) =
      ⟨gradingOperator, representM4R_mem_carLieSubalgebra .cartan⟩ := rfl
  have heuler : carToFiveGraded D
      ⟨gradingOperator, representM4R_mem_carLieSubalgebra .cartan⟩ =
      symplecticContactEuler D := by
    apply FiveGradedCarrier.ext
    · norm_num [carToFiveGraded, gradingOperator, NuclearTwoModeFiveGradeLieModel.number1,
        NuclearTwoModeFiveGradeLieModel.number2, a1, a2, a1Dag, a2Dag,
        symplecticContactEuler, genHscale, Matrix.mul_apply, Fin.sum_univ_four]
    · apply FreudenthalCharge.ext <;>
        norm_num [carToFiveGraded, gradingOperator, NuclearTwoModeFiveGradeLieModel.number1,
          NuclearTwoModeFiveGradeLieModel.number2, a1, a2, a1Dag, a2Dag,
          symplecticContactEuler, genHscale, q1Charge, q2Charge,
          Matrix.mul_apply, Fin.sum_univ_four]
    · apply Subtype.ext; apply LinearMap.ext; intro Z
      simp [carToFiveGraded, sympOfM4R_apply, gradingOperator,
        NuclearTwoModeFiveGradeLieModel.number1, NuclearTwoModeFiveGradeLieModel.number2,
        a1, a2, a1Dag, a2Dag, symplecticContactEuler, genHscale]
      rfl
    · norm_num [carToFiveGraded, gradingOperator, NuclearTwoModeFiveGradeLieModel.number1,
        NuclearTwoModeFiveGradeLieModel.number2, a1, a2, a1Dag, a2Dag,
        symplecticContactEuler, genHscale, Matrix.mul_apply, Fin.sum_univ_four]
    · apply FreudenthalCharge.ext <;>
        norm_num [carToFiveGraded, gradingOperator, NuclearTwoModeFiveGradeLieModel.number1,
          NuclearTwoModeFiveGradeLieModel.number2, a1, a2, a1Dag, a2Dag,
          symplecticContactEuler, genHscale, q1Charge, q2Charge,
          Matrix.mul_apply, Fin.sum_univ_four]
    · norm_num [carToFiveGraded, gradingOperator, NuclearTwoModeFiveGradeLieModel.number1,
        NuclearTwoModeFiveGradeLieModel.number2, a1, a2, a1Dag, a2Dag,
        symplecticContactEuler, genHscale, Matrix.mul_apply, Fin.sum_univ_four]
  have hlie : ⁅(⟨gradingOperator, representM4R_mem_carLieSubalgebra .cartan⟩ : carLieSubalgebra), X⁆ =
      (k : ℝ) • X := by
    apply Subtype.ext
    exact hX
  calc
    ⁅symplecticContactEuler D, carToFiveGraded D X⁆
      = ⁅carToFiveGraded D ⟨gradingOperator, representM4R_mem_carLieSubalgebra .cartan⟩,
          carToFiveGraded D X⁆ := by rw [heuler]
    _ = carToFiveGraded D
          ⁅(⟨gradingOperator, representM4R_mem_carLieSubalgebra .cartan⟩ : carLieSubalgebra), X⁆ :=
        (carToFiveGraded D).map_lie _ _ |>.symm
    _ = (k : ℝ) • carToFiveGraded D X := by
        rw [hlie, map_smul]

/-- Trivial cubic Jordan datum on `PUnit`, where `FreudenthalCharge PUnit ≅ ℝ²` and
`carToFiveGraded` becomes a Lie algebra isomorphism `sp(4, ℝ) ≃ₗ⁅ℝ⁆ FiveGradedCarrier`. -/
def zeroCubicJordanDatum : CubicJordanDatum PUnit where
  traceBilin := 0
  trace_comm _ _ := rfl
  normCubic _ := 0
  adjointQuad _ := PUnit.unit
  normTrilin := 0
  normTrilin_swap₁₂ _ _ _ := rfl
  normTrilin_swap₂₃ _ _ _ := rfl
  normTrilin_self _ := rfl

noncomputable def carToFiveGradedEquiv :
    carLieSubalgebra ≃ₗ⁅ℝ⁆ FiveGradedCarrier zeroCubicJordanDatum :=
  LieEquiv.ofBijective (carToFiveGraded zeroCubicJordanDatum)
    ⟨carToFiveGraded_injective zeroCubicJordanDatum, by
      intro u
      let e0 := (u.zero_symp : Module.End ℝ (FreudenthalCharge PUnit)) q2Charge |>.alpha
      let f0 := (u.zero_symp : Module.End ℝ (FreudenthalCharge PUnit)) q1Charge |>.beta
      let h0 := (u.zero_symp : Module.End ℝ (FreudenthalCharge PUnit)) q1Charge |>.alpha
      let Xmat : NuclearTwoModeFiveGradeLieModel.M4R :=
        u.plus2 • NuclearTwoModeFiveGradeLieModel.pairCreation +
        u.plus1.alpha • a1Dag + u.plus1.beta • a2Dag +
        u.zero_scale • gradingOperator +
        e0 • degreeZeroRaise + f0 • degreeZeroLower + h0 • degreeZeroCartan +
        u.minus1.beta • a1 + (-u.minus1.alpha) • a2 +
        u.minus2 • NuclearTwoModeFiveGradeLieModel.pairAnnihilation
      have hXmem : Xmat ∈ carLieSubalgebra := by
        repeat apply carLieSubalgebra.add_mem
        all_goals apply carLieSubalgebra.smul_mem
        · exact representM4R_mem_carLieSubalgebra .pairCreation
        · exact representM4R_mem_carLieSubalgebra .creationOne
        · exact representM4R_mem_carLieSubalgebra .creationTwo
        · exact representM4R_mem_carLieSubalgebra .cartan
        · exact degreeZeroSL2_mem_carLieSubalgebra.1
        · exact degreeZeroSL2_mem_carLieSubalgebra.2.1
        · exact degreeZeroSL2_mem_carLieSubalgebra.2.2
        · exact representM4R_mem_carLieSubalgebra .annihilationOne
        · exact representM4R_mem_carLieSubalgebra .annihilationTwo
        · exact representM4R_mem_carLieSubalgebra .pairAnnihilation
      refine ⟨⟨Xmat, hXmem⟩, ?_⟩
      have hsymp_law : ∀ Z W : FreudenthalCharge PUnit,
          FreudenthalCharge.symplecticForm zeroCubicJordanDatum
            ((u.zero_symp : Module.End ℝ (FreudenthalCharge PUnit)) Z) W +
          FreudenthalCharge.symplecticForm zeroCubicJordanDatum Z
            ((u.zero_symp : Module.End ℝ (FreudenthalCharge PUnit)) W) = 0 :=
        u.zero_symp.property
      have hq1_a : (q1Charge : FreudenthalCharge PUnit).alpha = 1 := rfl
      have hq1_b : (q1Charge : FreudenthalCharge PUnit).beta = 0 := rfl
      have hq2_a : (q2Charge : FreudenthalCharge PUnit).alpha = 0 := rfl
      have hq2_b : (q2Charge : FreudenthalCharge PUnit).beta = 1 := rfl
      have h12 := hsymp_law q1Charge q2Charge
      simp only [FreudenthalCharge.symplecticForm,
        zeroCubicJordanDatum, LinearMap.zero_apply, sub_zero, add_zero] at h12
      rw [hq1_a, hq1_b, hq2_a, hq2_b] at h12
      have h22_diag :
          ((u.zero_symp : Module.End ℝ (FreudenthalCharge PUnit)) q2Charge).beta = -h0 := by
        dsimp [h0]
        linarith
      apply FiveGradedCarrier.ext
      · simp [carToFiveGraded, Xmat, NuclearTwoModeFiveGradeLieModel.pairCreation,
          NuclearTwoModeFiveGradeLieModel.pairAnnihilation, gradingOperator,
          NuclearTwoModeFiveGradeLieModel.number1, NuclearTwoModeFiveGradeLieModel.number2,
          degreeZeroRaise, degreeZeroLower, degreeZeroCartan, a1, a2, a1Dag, a2Dag]
      · apply FreudenthalCharge.ext
        · simp [carToFiveGraded, Xmat, q1Charge, q2Charge,
            NuclearTwoModeFiveGradeLieModel.pairCreation,
            NuclearTwoModeFiveGradeLieModel.pairAnnihilation, gradingOperator,
            NuclearTwoModeFiveGradeLieModel.number1, NuclearTwoModeFiveGradeLieModel.number2,
            degreeZeroRaise, degreeZeroLower, degreeZeroCartan, a1, a2, a1Dag, a2Dag]
        · simp [carToFiveGraded, Xmat, q1Charge, q2Charge,
            NuclearTwoModeFiveGradeLieModel.pairCreation,
            NuclearTwoModeFiveGradeLieModel.pairAnnihilation, gradingOperator,
            NuclearTwoModeFiveGradeLieModel.number1, NuclearTwoModeFiveGradeLieModel.number2,
            degreeZeroRaise, degreeZeroLower, degreeZeroCartan, a1, a2, a1Dag, a2Dag]
        · rfl
        · rfl
      · apply Subtype.ext
        apply LinearMap.ext
        intro Z
        have hZ : Z = Z.alpha • q1Charge + Z.beta • q2Charge := by
          apply FreudenthalCharge.ext <;> simp [q1Charge, q2Charge]
        have hX21 : Xmat 2 1 = e0 := by
          simp [Xmat, NuclearTwoModeFiveGradeLieModel.pairCreation,
            NuclearTwoModeFiveGradeLieModel.pairAnnihilation, gradingOperator,
            NuclearTwoModeFiveGradeLieModel.number1, NuclearTwoModeFiveGradeLieModel.number2,
            degreeZeroRaise, degreeZeroLower, degreeZeroCartan, a1, a2, a1Dag, a2Dag]
        have hX12 : Xmat 1 2 = f0 := by
          simp [Xmat, NuclearTwoModeFiveGradeLieModel.pairCreation,
            NuclearTwoModeFiveGradeLieModel.pairAnnihilation, gradingOperator,
            NuclearTwoModeFiveGradeLieModel.number1, NuclearTwoModeFiveGradeLieModel.number2,
            degreeZeroRaise, degreeZeroLower, degreeZeroCartan, a1, a2, a1Dag, a2Dag]
        have hX22 : Xmat 2 2 = h0 := by
          simp [Xmat, NuclearTwoModeFiveGradeLieModel.pairCreation,
            NuclearTwoModeFiveGradeLieModel.pairAnnihilation, gradingOperator,
            NuclearTwoModeFiveGradeLieModel.number1, NuclearTwoModeFiveGradeLieModel.number2,
            degreeZeroRaise, degreeZeroLower, degreeZeroCartan, a1, a2, a1Dag, a2Dag]
        dsimp [carToFiveGraded]
        rw [sympOfM4R_apply, hX21, hX12, hX22]
        conv_rhs => rw [hZ, map_add, map_smul, map_smul]
        apply FreudenthalCharge.ext
        · simp [e0, h0, alpha_add, alpha_smul]
          ring
        · simp [f0, h22_diag, beta_add, beta_smul]
          ring
        · rfl
        · rfl
      · simp [carToFiveGraded, Xmat, NuclearTwoModeFiveGradeLieModel.pairCreation,
          NuclearTwoModeFiveGradeLieModel.pairAnnihilation, gradingOperator,
          NuclearTwoModeFiveGradeLieModel.number1, NuclearTwoModeFiveGradeLieModel.number2,
          degreeZeroRaise, degreeZeroLower, degreeZeroCartan, a1, a2, a1Dag, a2Dag]
      · apply FreudenthalCharge.ext
        · simp [carToFiveGraded, Xmat, q1Charge, q2Charge,
            NuclearTwoModeFiveGradeLieModel.pairCreation,
            NuclearTwoModeFiveGradeLieModel.pairAnnihilation, gradingOperator,
            NuclearTwoModeFiveGradeLieModel.number1, NuclearTwoModeFiveGradeLieModel.number2,
            degreeZeroRaise, degreeZeroLower, degreeZeroCartan, a1, a2, a1Dag, a2Dag]
        · simp [carToFiveGraded, Xmat, q1Charge, q2Charge,
            NuclearTwoModeFiveGradeLieModel.pairCreation,
            NuclearTwoModeFiveGradeLieModel.pairAnnihilation, gradingOperator,
            NuclearTwoModeFiveGradeLieModel.number1, NuclearTwoModeFiveGradeLieModel.number2,
            degreeZeroRaise, degreeZeroLower, degreeZeroCartan, a1, a2, a1Dag, a2Dag]
        · rfl
        · rfl
      · simp [carToFiveGraded, Xmat, NuclearTwoModeFiveGradeLieModel.pairCreation,
          NuclearTwoModeFiveGradeLieModel.pairAnnihilation, gradingOperator,
          NuclearTwoModeFiveGradeLieModel.number1, NuclearTwoModeFiveGradeLieModel.number2,
          degreeZeroRaise, degreeZeroLower, degreeZeroCartan, a1, a2, a1Dag, a2Dag]⟩

/-- The `sl₂(ℝ)` pair subalgebra spanned by `{pairCreation, gradingOperator, pairAnnihilation}`
inside `M₄(ℝ)`. -/
def pairSL2Subalgebra : LieSubalgebra ℝ NuclearTwoModeFiveGradeLieModel.M4R :=
  LieSubalgebra.lieSpan ℝ NuclearTwoModeFiveGradeLieModel.M4R
    {NuclearTwoModeFiveGradeLieModel.pairCreation, gradingOperator,
      NuclearTwoModeFiveGradeLieModel.pairAnnihilation}

theorem pairSL2Subalgebra_le_car : pairSL2Subalgebra ≤ carLieSubalgebra := by
  rw [pairSL2Subalgebra, LieSubalgebra.lieSpan_le]
  intro X hX
  rcases hX with rfl | rfl | rfl
  · exact representM4R_mem_carLieSubalgebra .pairCreation
  · exact representM4R_mem_carLieSubalgebra .cartan
  · exact representM4R_mem_carLieSubalgebra .pairAnnihilation

/-- Faithful Lie embedding of `Alg` (`sl₂(ℝ) ⋉ ℝ²`) into `M₄(ℝ)` preserving
the five-grading under `gradingOperator`. -/
def ladderToM4R : Alg →ₗ⁅ℝ⁆ NuclearTwoModeFiveGradeLieModel.M4R where
  toFun x :=
    x.1 • NuclearTwoModeFiveGradeLieModel.pairCreation +
    x.2.1 • gradingOperator +
    x.2.2.1 • NuclearTwoModeFiveGradeLieModel.pairAnnihilation +
    x.2.2.2.1 • !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 1, 0, 0] +
    x.2.2.2.2 • !![0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' r x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  map_lie' {x y} := by
    have hbr : ⁅x, y⁆ = Alg.br x y := rfl
    rw [hbr]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Alg.br, Ring.lie_def,
        NuclearTwoModeFiveGradeLieModel.pairCreation,
        NuclearTwoModeFiveGradeLieModel.pairAnnihilation, gradingOperator,
        NuclearTwoModeFiveGradeLieModel.number1, NuclearTwoModeFiveGradeLieModel.number2,
        a1, a2, a1Dag, a2Dag, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem ladderToM4R_injective : Function.Injective ladderToM4R := by
  intro x y hxy
  have h1 : x.1 = y.1 := by simpa [ladderToM4R, NuclearTwoModeFiveGradeLieModel.pairCreation,
    NuclearTwoModeFiveGradeLieModel.pairAnnihilation, gradingOperator,
    NuclearTwoModeFiveGradeLieModel.number1, NuclearTwoModeFiveGradeLieModel.number2,
    a1, a2, a1Dag, a2Dag] using congr_fun (congr_fun hxy 3) 0
  have h2 : x.2.1 = y.2.1 := by simpa [ladderToM4R, NuclearTwoModeFiveGradeLieModel.pairCreation,
    NuclearTwoModeFiveGradeLieModel.pairAnnihilation, gradingOperator,
    NuclearTwoModeFiveGradeLieModel.number1, NuclearTwoModeFiveGradeLieModel.number2,
    a1, a2, a1Dag, a2Dag] using congr_fun (congr_fun hxy 3) 3
  have h3 : x.2.2.1 = y.2.2.1 := by simpa [ladderToM4R, NuclearTwoModeFiveGradeLieModel.pairCreation,
    NuclearTwoModeFiveGradeLieModel.pairAnnihilation, gradingOperator,
    NuclearTwoModeFiveGradeLieModel.number1, NuclearTwoModeFiveGradeLieModel.number2,
    a1, a2, a1Dag, a2Dag] using congr_fun (congr_fun hxy 0) 3
  have h4 : x.2.2.2.1 = y.2.2.2.1 := by simpa [ladderToM4R, NuclearTwoModeFiveGradeLieModel.pairCreation,
    NuclearTwoModeFiveGradeLieModel.pairAnnihilation, gradingOperator,
    NuclearTwoModeFiveGradeLieModel.number1, NuclearTwoModeFiveGradeLieModel.number2,
    a1, a2, a1Dag, a2Dag] using congr_fun (congr_fun hxy 3) 1
  have h5 : x.2.2.2.2 = y.2.2.2.2 := by simpa [ladderToM4R, NuclearTwoModeFiveGradeLieModel.pairCreation,
    NuclearTwoModeFiveGradeLieModel.pairAnnihilation, gradingOperator,
    NuclearTwoModeFiveGradeLieModel.number1, NuclearTwoModeFiveGradeLieModel.number2,
    a1, a2, a1Dag, a2Dag] using congr_fun (congr_fun hxy 0) 1
  ext <;> assumption

theorem ladderToM4R_preserves_grades :
    NuclearTwoModeFiveGradeLieModel.HasGrade 2 (ladderToM4R Alg.basisE) ∧
    NuclearTwoModeFiveGradeLieModel.HasGrade 1 (ladderToM4R Alg.basisU) ∧
    NuclearTwoModeFiveGradeLieModel.HasGrade 0 (ladderToM4R Alg.basisH) ∧
    NuclearTwoModeFiveGradeLieModel.HasGrade (-1) (ladderToM4R Alg.basisV) ∧
    NuclearTwoModeFiveGradeLieModel.HasGrade (-2) (ladderToM4R Alg.basisF) := by
  have hE : ladderToM4R Alg.basisE = NuclearTwoModeFiveGradeLieModel.pairCreation := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [ladderToM4R, Alg.basisE]
  have hU : ladderToM4R Alg.basisU = !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 1, 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [ladderToM4R, Alg.basisU]
  have hH : ladderToM4R Alg.basisH = gradingOperator := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [ladderToM4R, Alg.basisH]
  have hV : ladderToM4R Alg.basisV = !![0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [ladderToM4R, Alg.basisV]
  have hF : ladderToM4R Alg.basisF = NuclearTwoModeFiveGradeLieModel.pairAnnihilation := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [ladderToM4R, Alg.basisF]
  rw [hE, hU, hH, hV, hF]
  refine ⟨pairCreation_grade, ?_, gradingOperator_grade, ?_, pairAnnihilation_grade⟩ <;>
  · unfold NuclearTwoModeFiveGradeLieModel.HasGrade
    ext i j
    simp only [NuclearTwoModeFiveGradeLieModel.comm, Matrix.sub_apply, Matrix.mul_apply,
      Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;>
      norm_num [gradingOperator,
        NuclearTwoModeFiveGradeLieModel.number1, NuclearTwoModeFiveGradeLieModel.number2,
        a1, a2, a1Dag, a2Dag, Matrix.mul_apply, Fin.sum_univ_four]

/-- **Obstruction-Driven Grade Emergence Theorem**:
Because `[G₁', G₁'] = 0` in `Alg` (`sl₂(ℝ) ⋉ ℝ²`) whereas `[a1Dag, a2Dag] = 2 • pairCreation`
in the 2-mode CAR Lie algebra `carLieSubalgebra`, ANY grade-preserving `LieHom` from `carLieSubalgebra`
into `Alg` sending `a1Dag, a2Dag` into `G₁'` collapses `pairCreation`, `gradingOperator`,
`a1Dag`, and `a2Dag` to zero. In contrast, `carToFiveGraded D` realizes the noncommutative
`+2` pair-creation grade faithfully. -/
theorem car_to_ladder_obstruction (f : carLieSubalgebra →ₗ⁅ℝ⁆ Alg)
    (ha1 : f ⟨a1Dag, representM4R_mem_carLieSubalgebra .creationOne⟩ ∈ Alg.G₁')
    (ha2 : f ⟨a2Dag, representM4R_mem_carLieSubalgebra .creationTwo⟩ ∈ Alg.G₁') :
    f ⟨NuclearTwoModeFiveGradeLieModel.pairCreation, representM4R_mem_carLieSubalgebra .pairCreation⟩ = 0 ∧
    f ⟨gradingOperator, representM4R_mem_carLieSubalgebra .cartan⟩ = 0 ∧
    f ⟨a1Dag, representM4R_mem_carLieSubalgebra .creationOne⟩ = 0 ∧
    f ⟨a2Dag, representM4R_mem_carLieSubalgebra .creationTwo⟩ = 0 := by
  let x1 : carLieSubalgebra := ⟨a1Dag, representM4R_mem_carLieSubalgebra .creationOne⟩
  let x2 : carLieSubalgebra := ⟨a2Dag, representM4R_mem_carLieSubalgebra .creationTwo⟩
  let xEp : carLieSubalgebra :=
    ⟨NuclearTwoModeFiveGradeLieModel.pairCreation, representM4R_mem_carLieSubalgebra .pairCreation⟩
  let xEm : carLieSubalgebra :=
    ⟨NuclearTwoModeFiveGradeLieModel.pairAnnihilation, representM4R_mem_carLieSubalgebra .pairAnnihilation⟩
  let xH : carLieSubalgebra :=
    ⟨gradingOperator, representM4R_mem_carLieSubalgebra .cartan⟩
  have h12 : ⁅x1, x2⁆ = (2 : ℝ) • xEp := by
    apply Subtype.ext
    exact creation_bracket_generates_pair
  have hf_12 : ⁅f x1, f x2⁆ = 0 := by
    rcases Alg.span_singleton_eq ha1 with ⟨a, ha⟩
    rcases Alg.span_singleton_eq ha2 with ⟨b, hb⟩
    rw [ha, hb]
    have hbr : ∀ u v : Alg, ⁅u, v⁆ = Alg.br u v := fun _ _ => rfl
    rw [hbr]
    ext <;> simp [Alg.br, Alg.basisU]
  have hEp0 : f xEp = 0 := by
    have hsm : f ((2 : ℝ) • xEp) = (2 : ℝ) • f xEp := map_smul f 2 xEp
    have h2 : (2 : ℝ) • f xEp = 0 := by
      rw [← hsm, ← h12, LieHom.map_lie, hf_12]
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  have hEpEm : ⁅xEp, xEm⁆ = xH := by
    apply Subtype.ext
    exact pair_extreme_bracket
  have hH0 : f xH = 0 := by
    rw [← hEpEm, LieHom.map_lie, hEp0, zero_lie]
  have hHx1 : ⁅xH, x1⁆ = x1 := by
    apply Subtype.ext
    simpa [NuclearTwoModeFiveGradeLieModel.HasGrade] using a1Dag_grade
  have hHx2 : ⁅xH, x2⁆ = x2 := by
    apply Subtype.ext
    simpa [NuclearTwoModeFiveGradeLieModel.HasGrade] using a2Dag_grade
  have hx1_0 : f x1 = 0 := by
    rw [← hHx1, LieHom.map_lie, hH0, zero_lie]
  have hx2_0 : f x2 = 0 := by
    rw [← hHx2, LieHom.map_lie, hH0, zero_lie]
  exact ⟨hEp0, hH0, hx1_0, hx2_0⟩

end ConcreteFiveGradedLieBridge

end InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation

