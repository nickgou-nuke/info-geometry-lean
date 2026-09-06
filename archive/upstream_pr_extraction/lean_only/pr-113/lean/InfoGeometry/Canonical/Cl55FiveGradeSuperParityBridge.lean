import Mathlib.Tactic
import InfoGeometry.Canonical.Cl55WittFiveGradeDecomposition
import InfoGeometry.Canonical.Cl55ChiralParityNormalOrderingBridge

/-!
# Cl(5,5) five-grading and chirality superparity

The Cartan adjoint grading and the chirality grading are compatible but not
identical.  On the native Witt generators:

* grades `-2, 0, +2` are chirality-even;
* grades `-1, +1` are chirality-odd.

This owner proves that statement directly on the existing generators.  It does
not install a second superalgebra carrier: the predicates below are only
readouts of multiplication by the repository-owned `gammaChiral` matrix.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.Cl55FiveGradeSuperParityBridge

open scoped Matrix Kronecker BigOperators
open Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.Cl55WittCAR
open InfoGeometry.Canonical.Cl55WittLieRouting
open InfoGeometry.Physics.Cl55SpinorCartanFock
open InfoGeometry.Canonical.Cl55ChiralOccupationFiveGradeBridge
open InfoGeometry.Canonical.Cl55ChiralParityNormalOrderingBridge

abbrev FockOp := InfoGeometry.Clifford.Cl11TensorTower.MatStage 5

/-- Chirality-even operator: it commutes with `gammaChiral`. -/
def IsGammaEven (X : FockOp) : Prop :=
  gammaChiral * X = X * gammaChiral

/-- Chirality-odd operator: it anticommutes with `gammaChiral`. -/
def IsGammaOdd (X : FockOp) : Prop :=
  gammaChiral * X = -(X * gammaChiral)

/-- Every creation generator is chirality-odd. -/
theorem creation_isGammaOdd (i : Fin 5) :
    IsGammaOdd (creation i) := by
  exact gammaChiral_e_anticomm i

/-- Every annihilation generator is chirality-odd. -/
theorem annihilation_isGammaOdd (i : Fin 5) :
    IsGammaOdd (annihilation i) := by
  exact gammaChiral_f_anticomm i

/-- A quadratic creation operator is chirality-even. -/
theorem creationQuadratic_isGammaEven (i j : Fin 5) :
    IsGammaEven (creation i * creation j) := by
  unfold IsGammaEven
  have hi := gammaChiral_e_anticomm i
  have hj := gammaChiral_e_anticomm j
  calc
    gammaChiral * (creation i * creation j) =
        (gammaChiral * creation i) * creation j := by rw [mul_assoc]
    _ = (-(creation i * gammaChiral)) * creation j := by rw [hi]
    _ = -(creation i * (gammaChiral * creation j)) := by noncomm_ring
    _ = -(creation i * (-(creation j * gammaChiral))) := by rw [hj]
    _ = (creation i * creation j) * gammaChiral := by noncomm_ring

/-- A quadratic annihilation operator is chirality-even. -/
theorem annihilationQuadratic_isGammaEven (i j : Fin 5) :
    IsGammaEven (annihilation i * annihilation j) := by
  unfold IsGammaEven
  have hi := gammaChiral_f_anticomm i
  have hj := gammaChiral_f_anticomm j
  calc
    gammaChiral * (annihilation i * annihilation j) =
        (gammaChiral * annihilation i) * annihilation j := by rw [mul_assoc]
    _ = (-(annihilation i * gammaChiral)) * annihilation j := by rw [hi]
    _ = -(annihilation i * (gammaChiral * annihilation j)) := by noncomm_ring
    _ = -(annihilation i * (-(annihilation j * gammaChiral))) := by rw [hj]
    _ = (annihilation i * annihilation j) * gammaChiral := by noncomm_ring

/-- A mixed CAR bilinear is chirality-even. -/
theorem mixedBilinear_isGammaEven (i j : Fin 5) :
    IsGammaEven (creation i * annihilation j) := by
  unfold IsGammaEven
  have hi := gammaChiral_e_anticomm i
  have hj := gammaChiral_f_anticomm j
  calc
    gammaChiral * (creation i * annihilation j) =
        (gammaChiral * creation i) * annihilation j := by rw [mul_assoc]
    _ = (-(creation i * gammaChiral)) * annihilation j := by rw [hi]
    _ = -(creation i * (gammaChiral * annihilation j)) := by noncomm_ring
    _ = -(creation i * (-(annihilation j * gammaChiral))) := by rw [hj]
    _ = (creation i * annihilation j) * gammaChiral := by noncomm_ring

/-- Every grade-zero matrix-unit generator is chirality-even. -/
theorem E_isGammaEven (i j : Fin 5) :
    IsGammaEven (E i j) := by
  unfold IsGammaEven E
  by_cases hij : i = j
  · subst j
    simp only [if_pos]
    have hm := mixedBilinear_isGammaEven i i
    unfold IsGammaEven at hm
    calc
      gammaChiral *
          (creation i * annihilation i -
            (1 / 2 : ℝ) • (1 : FockOp)) =
        gammaChiral * (creation i * annihilation i) -
          gammaChiral * ((1 / 2 : ℝ) • (1 : FockOp)) := by
            rw [mul_sub]
      _ = (creation i * annihilation i) * gammaChiral -
          ((1 / 2 : ℝ) • (1 : FockOp)) * gammaChiral := by
            rw [hm]
            simp
      _ = (creation i * annihilation i -
          (1 / 2 : ℝ) • (1 : FockOp)) * gammaChiral := by
            rw [sub_mul]
  · simp only [if_neg hij, sub_zero]
    exact mixedBilinear_isGammaEven i j

/-- The raw occupation is chirality-even. -/
theorem rawFockNumber_isGammaEven :
    IsGammaEven rawFockNumber := by
  unfold IsGammaEven
  exact gammaChiral_rawFockNumber_comm

/-- The centered five-grade Cartan generator is chirality-even. -/
theorem numberOperator_isGammaEven :
    IsGammaEven numberOperator := by
  rw [← centeredFockNumber_eq_numberOperator]
  unfold centeredFockNumber IsGammaEven
  have hraw := gammaChiral_rawFockNumber_comm
  noncomm_ring [hraw]

/-- The CAR odd-odd mixed anticommutator lands in the chirality-even sector. -/
theorem mixedCARAnticommutator_isGammaEven (i j : Fin 5) :
    IsGammaEven
      (creation i * annihilation j + annihilation j * creation i) := by
  unfold IsGammaEven
  have h₁ := mixedBilinear_isGammaEven i j
  have h₂ : IsGammaEven (annihilation j * creation i) := by
    unfold IsGammaEven
    have hj := gammaChiral_f_anticomm j
    have hi := gammaChiral_e_anticomm i
    calc
      gammaChiral * (annihilation j * creation i) =
          (gammaChiral * annihilation j) * creation i := by rw [mul_assoc]
      _ = (-(annihilation j * gammaChiral)) * creation i := by rw [hj]
      _ = -(annihilation j * (gammaChiral * creation i)) := by noncomm_ring
      _ = -(annihilation j * (-(creation i * gammaChiral))) := by rw [hi]
      _ = (annihilation j * creation i) * gammaChiral := by noncomm_ring
  unfold IsGammaEven at h₁ h₂
  rw [mul_add, add_mul, h₁, h₂]

/-- Generator-level compatibility of the five Cartan grades with chirality
superparity. -/
theorem fiveGrade_superParity_packet (i j : Fin 5) :
    (annihilation i * annihilation j ∈ gradeSubmodule (-2) ∧
      IsGammaEven (annihilation i * annihilation j)) ∧
    (annihilation i ∈ gradeSubmodule (-1) ∧
      IsGammaOdd (annihilation i)) ∧
    (E i j ∈ gradeSubmodule 0 ∧ IsGammaEven (E i j)) ∧
    (creation i ∈ gradeSubmodule 1 ∧ IsGammaOdd (creation i)) ∧
    (creation i * creation j ∈ gradeSubmodule 2 ∧
      IsGammaEven (creation i * creation j)) := by
  exact
    ⟨⟨annihilation_quadratic_mem_gradeSubmodule i j,
        annihilationQuadratic_isGammaEven i j⟩,
      ⟨annihilation_mem_gradeSubmodule i, annihilation_isGammaOdd i⟩,
      ⟨E_mem_gradeSubmodule i j, E_isGammaEven i j⟩,
      ⟨creation_mem_gradeSubmodule i, creation_isGammaOdd i⟩,
      ⟨creation_quadratic_mem_gradeSubmodule i j,
        creationQuadratic_isGammaEven i j⟩⟩

/-- The five-grade parity rule on the native generators:
even integer grade gives chirality-even, odd integer grade gives
chirality-odd. -/
theorem fiveGrade_modTwo_summary (i j : Fin 5) :
    IsGammaEven (annihilation i * annihilation j) ∧
    IsGammaOdd (annihilation i) ∧
    IsGammaEven (E i j) ∧
    IsGammaOdd (creation i) ∧
    IsGammaEven (creation i * creation j) := by
  exact ⟨annihilationQuadratic_isGammaEven i j,
    annihilation_isGammaOdd i,
    E_isGammaEven i j,
    creation_isGammaOdd i,
    creationQuadratic_isGammaEven i j⟩

end InfoGeometry.Canonical.Cl55FiveGradeSuperParityBridge
