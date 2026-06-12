import Mathlib
import InfoGeometry.Physics.MD003IsomorphicRepresentations

/-!
# Repaired MD 005: finite symmetry shadows

Source: `github-nick:nickgou-nuke/MD`, file `005.md`.

Chapter 5 discusses Lorentz symmetry from `SL(2,ℂ)`, the `SU(2)`/hyperkähler
interpretation, Poincaré algebra, Casimirs, and conformal symmetry.  The full
surjectivity theorem `SL(2,ℂ) → SO⁺(1,3)`, Lie-algebra representation theory,
Casimir classification, and conformal-spin-cover statements are standard or
continuum-level results outside this finite owner.

This file formalizes the finite algebraic content that the repository can check
kernel-safely:

* congruence action `X ↦ A X A†` on concrete `2 × 2` matrices;
* determinant transformation under congruence;
* determinant preservation under the explicit `det A = 1` gate;
* composition law for congruence actions;
* scalar unit-norm matrices act trivially by congruence, modeling the finite
  `{±I}` kernel shadow;
* finite translations of `ℝ⁴` compose and commute as an abelian subgroup.

No theorem here asserts the full Lorentz double-cover, surjectivity onto
`SO⁺(1,3)`, Poincaré Lie-algebra commutators, Pauli--Lubanski classification,
or conformal group/spin-cover identification.
-/

noncomputable section

namespace InfoGeometry.Physics.MD005Symmetries

open Matrix
open InfoGeometry.Physics.MD001MatrixQuantumGeometry

/-- Finite congruence action `X ↦ A X A†` on the concrete `2 × 2` carrier. -/
def congruenceAction (A X : MatrixQuantumCarrier) : MatrixQuantumCarrier :=
  A * X * A.conjTranspose

/-- Determinant transformation law under finite congruence. -/
theorem det_congruence (A X : MatrixQuantumCarrier) :
    Matrix.det (congruenceAction A X) =
      Matrix.det A * Matrix.det X * star (Matrix.det A) := by
  unfold congruenceAction
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]

/-- Determinant preservation for determinant-one congruence actions. -/
theorem det_congruence_of_det_one (A X : MatrixQuantumCarrier)
    (hA : Matrix.det A = 1) :
    Matrix.det (congruenceAction A X) = Matrix.det X := by
  rw [det_congruence, hA]
  simp

/-- Determinant preservation for the explicit special-linear unit-norm gate. -/
theorem det_congruence_of_special_linear_gate (A X : MatrixQuantumCarrier)
    (hA : Matrix.det A * star (Matrix.det A) = 1) :
    Matrix.det (congruenceAction A X) = Matrix.det X := by
  rw [det_congruence]
  calc
    Matrix.det A * Matrix.det X * star (Matrix.det A) =
        (Matrix.det A * star (Matrix.det A)) * Matrix.det X := by ring
    _ = Matrix.det X := by rw [hA]; simp

/-- Congruence actions compose as expected. -/
theorem congruenceAction_comp (A B X : MatrixQuantumCarrier) :
    congruenceAction A (congruenceAction B X) = congruenceAction (A * B) X := by
  unfold congruenceAction
  rw [Matrix.conjTranspose_mul]
  ext i j
  simp only [Matrix.mul_assoc]

/-- Scalar congruence by `cI`. -/
def scalarCongruenceAction (c : ℂ) (X : MatrixQuantumCarrier) : MatrixQuantumCarrier :=
  congruenceAction (c • (1 : MatrixQuantumCarrier)) X

/-- Scalar congruence rescales by `c * star c`. -/
theorem scalarCongruenceAction_eq_smul (c : ℂ) (X : MatrixQuantumCarrier) :
    scalarCongruenceAction c X = (c * star c) • X := by
  unfold scalarCongruenceAction congruenceAction
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf

/-- Unit-norm scalar matrices act trivially by congruence. -/
theorem scalarCongruenceAction_eq_self_of_unit_norm (c : ℂ)
    (X : MatrixQuantumCarrier) (hc : c * star c = 1) :
    scalarCongruenceAction c X = X := by
  rw [scalarCongruenceAction_eq_smul, hc]
  simp

/-- The `+I` scalar kernel shadow acts trivially. -/
theorem scalarCongruenceAction_one (X : MatrixQuantumCarrier) :
    scalarCongruenceAction 1 X = X := by
  exact scalarCongruenceAction_eq_self_of_unit_norm 1 X (by simp)

/-- The `-I` scalar kernel shadow acts trivially. -/
theorem scalarCongruenceAction_neg_one (X : MatrixQuantumCarrier) :
    scalarCongruenceAction (-1) X = X := by
  exact scalarCongruenceAction_eq_self_of_unit_norm (-1) X (by norm_num)

/-- Finite coordinate vector used for translation shadows. -/
abbrev Vec4 := Fin 4 → ℝ

/-- Translation of a finite four-coordinate vector. -/
def translate (ξ x : Vec4) : Vec4 :=
  fun i => x i + ξ i

/-- Zero translation is the identity. -/
theorem translate_zero (x : Vec4) : translate 0 x = x := by
  funext i
  simp [translate]

/-- Finite translations compose by addition of translation vectors. -/
theorem translate_comp (ξ η x : Vec4) :
    translate ξ (translate η x) = translate (fun i => η i + ξ i) x := by
  funext i
  simp [translate]
  ring

/-- Finite translations commute: the abelian translation subgroup shadow. -/
theorem translate_comm (ξ η x : Vec4) :
    translate ξ (translate η x) = translate η (translate ξ x) := by
  funext i
  simp [translate]
  ring

/-- Repaired theorem-safe Chapter 5 finite symmetry packet. -/
theorem repaired_MD005_symmetry_packet
    (A B X : MatrixQuantumCarrier) (hA : Matrix.det A = 1)
    (ξ η x : Vec4) :
    Matrix.det (congruenceAction A X) = Matrix.det X ∧
    congruenceAction A (congruenceAction B X) = congruenceAction (A * B) X ∧
    scalarCongruenceAction 1 X = X ∧
    scalarCongruenceAction (-1) X = X ∧
    translate ξ (translate η x) = translate η (translate ξ x) := by
  exact ⟨det_congruence_of_det_one A X hA,
    congruenceAction_comp A B X,
    scalarCongruenceAction_one X,
    scalarCongruenceAction_neg_one X,
    translate_comm ξ η x⟩

end InfoGeometry.Physics.MD005Symmetries

end noncomputable section
