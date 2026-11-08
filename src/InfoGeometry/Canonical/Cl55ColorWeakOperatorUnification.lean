/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl55ThreeColorWittChannels
import InfoGeometry.Physics.Cl55SpinorCartanFock

/-!
# Color and weak root operators on the same finite `Cl(5,5)` Fock carrier

The three color modes and the two weak-isospin modes are already represented by
CAR operators on `MatStage 5`. This module records their joint operator algebra:
color matrix units close under commutators, the selected weak pair closes as
`sl₂`, and the two actions commute because their mode sets are disjoint.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.Cl55ColorWeakOperatorUnification

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.Cl55ThreeColorWittChannels
open InfoGeometry.Canonical.Cl55WittLieRouting
open InfoGeometry.Physics.Cl55SpinorCartanFock

/-- The first three Witt modes, viewed as color matrix units on the full
32-dimensional spinor Fock carrier. -/
def colorUnit (i j : Fin 3) : MatStage 5 :=
  E (colorToCl55Index i) (colorToCl55Index j)

/-- A weak-isospin doublet carried by the remaining two selected Witt modes. -/
def weakPlus : MatStage 5 := isospinPlus 3 4

def weakMinus : MatStage 5 := isospinMinus 3 4

def weakCartan : MatStage 5 := isospinCartan 3 4

/-- The color root operators form the usual matrix-unit Lie algebra under the
commutator, represented on the actual five-mode Fock operator carrier. -/
theorem colorUnit_commutator (i j k l : Fin 3) :
    bracket (colorUnit i j) (colorUnit k l) =
      (if j = k then colorUnit i l else 0) -
        (if i = l then colorUnit k j else 0) := by
  have hmap : ∀ a b : Fin 3,
      (colorToCl55Index a = colorToCl55Index b) ↔ a = b := by
    intro a b
    constructor
    · intro h
      exact colorToCl55Index_injective h
    · rintro rfl
      rfl
  simp only [colorUnit, E_bracket]
  simp only [hmap]

/-- Color matrix units act on color creation modes by the defining
fundamental-representation rule. -/
theorem colorUnit_creation_action (i j k : Fin 3) :
    bracket (colorUnit i j) (GammaPlus k) =
      if j = k then GammaPlus i else 0 := by
  have hmap : ∀ a b : Fin 3,
      (colorToCl55Index a = colorToCl55Index b) ↔ a = b := by
    intro a b
    constructor
    · intro h
      exact colorToCl55Index_injective h
    · rintro rfl
      rfl
  simp only [colorUnit, GammaPlus, E_creation, hmap]

private theorem color_index_ne_weak (i : Fin 3) (p : Fin 5)
    (hp : 3 ≤ p.val) : colorToCl55Index i ≠ p := by
  intro h
  have hv := congrArg Fin.val h
  simp [colorToCl55Index] at hv
  have hi : i.val < 3 := i.isLt
  omega

/-- Every color matrix unit commutes with the selected weak raising operator. -/
theorem colorUnit_weakPlus_commute (i j : Fin 3) :
    bracket (colorUnit i j) weakPlus = 0 := by
  have hj : colorToCl55Index j ≠ (3 : Fin 5) :=
    color_index_ne_weak j 3 (by decide)
  have hi : colorToCl55Index i ≠ (4 : Fin 5) :=
    color_index_ne_weak i 4 (by decide)
  simp only [colorUnit, weakPlus, isospinPlus]
  rw [E_bracket]
  simp [hj, hi]

/-- Every color matrix unit commutes with the selected weak lowering operator. -/
theorem colorUnit_weakMinus_commute (i j : Fin 3) :
    bracket (colorUnit i j) weakMinus = 0 := by
  have hj : colorToCl55Index j ≠ (4 : Fin 5) :=
    color_index_ne_weak j 4 (by decide)
  have hi : colorToCl55Index i ≠ (3 : Fin 5) :=
    color_index_ne_weak i 3 (by decide)
  simp only [colorUnit, weakMinus, isospinMinus]
  rw [E_bracket]
  simp [hj, hi]

/-- Every color matrix unit commutes with the selected weak Cartan operator. -/
theorem colorUnit_weakCartan_commute (i j : Fin 3) :
    bracket (colorUnit i j) weakCartan = 0 := by
  have h3j : colorToCl55Index j ≠ (3 : Fin 5) :=
    color_index_ne_weak j 3 (by decide)
  have h4j : colorToCl55Index j ≠ (4 : Fin 5) :=
    color_index_ne_weak j 4 (by decide)
  have h3i : colorToCl55Index i ≠ (3 : Fin 5) :=
    color_index_ne_weak i 3 (by decide)
  have h4i : colorToCl55Index i ≠ (4 : Fin 5) :=
    color_index_ne_weak i 4 (by decide)
  have hsub (X Y Z : MatStage 5) : bracket X (Y - Z) = bracket X Y - bracket X Z := by
    unfold bracket
    noncomm_ring
  simp only [colorUnit, weakCartan, isospinCartan, H]
  rw [hsub, E_bracket, E_bracket]
  simp [h3j, h4j, h3i, h4i]

/-- The selected weak doublet satisfies all three `sl₂` commutator relations
inside the same matrix operator algebra as the color action. -/
theorem weak_doublet_sl2_relations :
    bracket weakPlus weakMinus = weakCartan ∧
    bracket weakCartan weakPlus = (2 : ℝ) • weakPlus ∧
    bracket weakCartan weakMinus = -(2 : ℝ) • weakMinus := by
  have h34 : (3 : Fin 5) ≠ 4 := by decide
  exact ⟨isospin_plus_minus_bracket 3 4,
    isospin_cartan_plus_bracket h34,
    isospin_cartan_minus_bracket h34⟩

/-- The five-mode number derivation vanishes on the color Cartan generators.
This records the existing color-charge operators in the same grade-zero
centralizer as the weak root operators; it does not identify this grading
operator with electroweak hypercharge. -/
theorem numberOperator_color_cartan_commute :
    bracket numberOperator colorGluonT3 = 0 ∧
    bracket numberOperator colorGluon3Y = 0 := by
  have hOcc (i : Fin 5) : bracket numberOperator (modeOccupied i) = 0 := by
    dsimp [modeOccupied, e, f]
    rw [bracket_mul_right, numberOperator_creation,
      numberOperator_annihilation]
    simp
  have hNeg (i : Fin 5) : bracket numberOperator (-modeOccupied i) = 0 := by
    rw [show -modeOccupied i = (-1 : ℝ) • modeOccupied i by simp,
      bracket_smul_right, hOcc]
    simp
  have hNegTwo (i : Fin 5) :
      bracket numberOperator (-((2 : ℝ) • modeOccupied i)) = 0 := by
    rw [show -((2 : ℝ) • modeOccupied i) = (-2 : ℝ) • modeOccupied i by
      rw [neg_smul], bracket_smul_right, hOcc]
    simp
  constructor
  · dsimp [colorGluonT3]
    rw [sub_eq_add_neg]
    rw [bracket_add_right, hOcc, hNeg]
    simp
  · dsimp [colorGluon3Y]
    rw [sub_eq_add_neg]
    rw [bracket_add_right, bracket_add_right, hOcc, hOcc]
    have hzero := hNegTwo 2
    convert hzero using 1 <;> simp [two_smul]

/-- The common number derivation grades the color and weak generators alike:
all color matrix units and the selected weak `sl₂` triple are degree zero. -/
theorem color_weak_are_number_grade_zero (i j : Fin 3) :
    bracket numberOperator (colorUnit i j) = 0 ∧
    bracket numberOperator weakPlus = 0 ∧
    bracket numberOperator weakMinus = 0 ∧
    bracket numberOperator weakCartan = 0 ∧
    bracket numberOperator colorGluonT3 = 0 ∧
    bracket numberOperator colorGluon3Y = 0 := by
  have hWeak := five_graded_isospin_and_pairing_grades 3 4
  have hColor := numberOperator_color_cartan_commute
  exact ⟨numberOperator_E (colorToCl55Index i) (colorToCl55Index j),
    hWeak.1, hWeak.2.1, hWeak.2.2.1, hColor.1, hColor.2⟩

/-- Joint finite color–weak operator representation: matrix-unit color
commutators and weak `sl₂` close on the 32-dimensional Fock carrier, and the
two generated sectors commute. The color Cartan charges and weak roots also
lie in the grade-zero centralizer of the existing number derivation. -/
theorem finite_color_weak_operator_algebra (i j k l : Fin 3) :
    bracket (colorUnit i j) (colorUnit k l) =
      (if j = k then colorUnit i l else 0) -
        (if i = l then colorUnit k j else 0) ∧
    bracket weakPlus weakMinus = weakCartan ∧
    bracket weakCartan weakPlus = (2 : ℝ) • weakPlus ∧
    bracket weakCartan weakMinus = -(2 : ℝ) • weakMinus ∧
    (∀ a b : Fin 3, bracket (colorUnit a b) weakPlus = 0) ∧
    (∀ a b : Fin 3, bracket (colorUnit a b) weakMinus = 0) ∧
    (∀ a b : Fin 3, bracket (colorUnit a b) weakCartan = 0) ∧
    (bracket numberOperator (colorUnit i j) = 0 ∧
      bracket numberOperator weakPlus = 0 ∧
      bracket numberOperator weakMinus = 0 ∧
      bracket numberOperator weakCartan = 0 ∧
      bracket numberOperator colorGluonT3 = 0 ∧
      bracket numberOperator colorGluon3Y = 0) := by
  refine ⟨colorUnit_commutator i j k l, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact weak_doublet_sl2_relations.1
  · exact weak_doublet_sl2_relations.2.1
  · exact weak_doublet_sl2_relations.2.2
  · intro a b
    exact colorUnit_weakPlus_commute a b
  · intro a b
    exact colorUnit_weakMinus_commute a b
  · intro a b
    exact colorUnit_weakCartan_commute a b
  · exact color_weak_are_number_grade_zero i j

end InfoGeometry.Canonical.Cl55ColorWeakOperatorUnification
