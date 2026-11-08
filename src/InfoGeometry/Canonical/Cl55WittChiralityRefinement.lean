import InfoGeometry.Physics.Cl55SpinorCartanFock
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Cl55WittOrthogonalHierarchy

/-!
# Chirality conjugation on the stage-five matrix carrier

The chirality refinement is kept separate from the integer Witt grading.  This
file records only the canonical involutive algebra automorphism induced by the
existing stage-five chirality matrix.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.Cl55WittChiralityRefinement

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Physics.Cl55SpinorCartanFock
open InfoGeometry.Canonical.Cl55WittLieRouting
open InfoGeometry.Canonical.Cl55WittCAR
open InfoGeometry.Canonical.Cl55WittOrthogonalHierarchy

def chiralityConjugation : MatStage 5 →ₗ[ℝ] MatStage 5 where
  toFun X := gammaChiral * X * gammaChiral
  map_add' X Y := by simp [mul_add, add_mul]
  map_smul' c X := by
    change gammaChiral * (c • X) * gammaChiral =
      c • (gammaChiral * X * gammaChiral)
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

@[simp] theorem chiralityConjugation_apply (X : MatStage 5) :
    chiralityConjugation X = gammaChiral * X * gammaChiral := rfl

@[simp] theorem chiralityConjugation_one :
    chiralityConjugation (1 : MatStage 5) = 1 := by
  change gammaChiral * 1 * gammaChiral = 1
  simpa using gammaChiral_sq

theorem chiralityConjugation_mul (X Y : MatStage 5) :
    chiralityConjugation (X * Y) =
      chiralityConjugation X * chiralityConjugation Y := by
  change gammaChiral * (X * Y) * gammaChiral =
    (gammaChiral * X * gammaChiral) *
      (gammaChiral * Y * gammaChiral)
  calc
    gammaChiral * (X * Y) * gammaChiral =
        gammaChiral * X * (gammaChiral * gammaChiral) * Y * gammaChiral := by
          rw [gammaChiral_sq]
          noncomm_ring
    _ = (gammaChiral * X * gammaChiral) *
        (gammaChiral * Y * gammaChiral) := by noncomm_ring

theorem chiralityConjugation_involutive (X : MatStage 5) :
    chiralityConjugation (chiralityConjugation X) = X := by
  change gammaChiral * (gammaChiral * X * gammaChiral) * gammaChiral = X
  calc
    gammaChiral * (gammaChiral * X * gammaChiral) * gammaChiral =
        (gammaChiral * gammaChiral) * X *
          (gammaChiral * gammaChiral) := by noncomm_ring
    _ = X := by rw [gammaChiral_sq]; simp

def chiralityEven : Submodule ℝ (MatStage 5) :=
  LinearMap.ker (chiralityConjugation -
    (LinearMap.id : MatStage 5 →ₗ[ℝ] MatStage 5))

def chiralityOdd : Submodule ℝ (MatStage 5) :=
  LinearMap.ker (chiralityConjugation +
    (LinearMap.id : MatStage 5 →ₗ[ℝ] MatStage 5))

@[simp] theorem mem_chiralityEven_iff {X : MatStage 5} :
    X ∈ chiralityEven ↔ chiralityConjugation X = X := by
  rw [chiralityEven, LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

@[simp] theorem mem_chiralityOdd_iff {X : MatStage 5} :
    X ∈ chiralityOdd ↔ chiralityConjugation X = -X := by
  rw [chiralityOdd, LinearMap.mem_ker]
  simp only [LinearMap.add_apply, LinearMap.id_apply]
  exact add_eq_zero_iff_eq_neg

theorem chiralityConjugation_bracket (X Y : MatStage 5) :
    chiralityConjugation (bracket X Y) =
      bracket (chiralityConjugation X) (chiralityConjugation Y) := by
  unfold bracket
  rw [map_sub, chiralityConjugation_mul, chiralityConjugation_mul]

theorem creation_conjugation_neg (i : Fin 5) :
    chiralityConjugation (creation i) = -creation i := by
  change gammaChiral * creation i * gammaChiral = -creation i
  have hanti : gammaChiral * creation i = -(creation i * gammaChiral) := by
    simpa [e] using gammaChiral_e_anticomm i
  rw [hanti, neg_mul, mul_assoc, gammaChiral_sq, mul_one]

theorem annihilation_conjugation_neg (i : Fin 5) :
    chiralityConjugation (annihilation i) = -annihilation i := by
  change gammaChiral * annihilation i * gammaChiral = -annihilation i
  have hanti : gammaChiral * annihilation i =
      -(annihilation i * gammaChiral) := by
    simpa [f] using gammaChiral_f_anticomm i
  rw [hanti, neg_mul, mul_assoc, gammaChiral_sq, mul_one]

@[simp] theorem creation_mem_chiralityOdd (i : Fin 5) :
    creation i ∈ chiralityOdd := by
  rw [mem_chiralityOdd_iff]
  exact creation_conjugation_neg i

@[simp] theorem annihilation_mem_chiralityOdd (i : Fin 5) :
    annihilation i ∈ chiralityOdd := by
  rw [mem_chiralityOdd_iff]
  exact annihilation_conjugation_neg i

@[simp] theorem creationPair_mem_chiralityEven (i j : Fin 5) :
    creation i * creation j ∈ chiralityEven := by
  rw [mem_chiralityEven_iff, chiralityConjugation_mul,
    creation_conjugation_neg, creation_conjugation_neg]
  simp

@[simp] theorem annihilationPair_mem_chiralityEven (i j : Fin 5) :
    annihilation i * annihilation j ∈ chiralityEven := by
  rw [mem_chiralityEven_iff, chiralityConjugation_mul,
    annihilation_conjugation_neg, annihilation_conjugation_neg]
  simp

@[simp] theorem E_mem_chiralityEven (i j : Fin 5) :
    E i j ∈ chiralityEven := by
  rw [mem_chiralityEven_iff]
  unfold E
  rw [map_sub, chiralityConjugation_mul,
    creation_conjugation_neg, annihilation_conjugation_neg]
  by_cases h : i = j <;> simp [h, gammaChiral_sq]

theorem wittNegOne_le_chiralityOdd : wittNegOne ≤ chiralityOdd := by
  unfold wittNegOne
  apply Submodule.span_le.mpr
  rintro X ⟨i, rfl⟩
  exact annihilation_mem_chiralityOdd i

theorem wittPosOne_le_chiralityOdd : wittPosOne ≤ chiralityOdd := by
  unfold wittPosOne
  apply Submodule.span_le.mpr
  rintro X ⟨i, rfl⟩
  exact creation_mem_chiralityOdd i

theorem wittNegTwo_le_chiralityEven : wittNegTwo ≤ chiralityEven := by
  unfold wittNegTwo
  apply Submodule.span_le.mpr
  rintro X ⟨ij, rfl⟩
  exact annihilationPair_mem_chiralityEven ij.1 ij.2

theorem wittZero_le_chiralityEven : wittZero ≤ chiralityEven := by
  unfold wittZero
  apply Submodule.span_le.mpr
  rintro X ⟨ij, rfl⟩
  exact E_mem_chiralityEven ij.1 ij.2

theorem wittPosTwo_le_chiralityEven : wittPosTwo ≤ chiralityEven := by
  unfold wittPosTwo
  apply Submodule.span_le.mpr
  rintro X ⟨ij, rfl⟩
  exact creationPair_mem_chiralityEven ij.1 ij.2

theorem quadraticCoreSpan_le_chiralityEven :
    quadraticCoreSpan ≤ chiralityEven := by
  apply Submodule.span_le.mpr
  intro X hX
  rcases hX with ⟨lane, hLane⟩
  cases lane with
  | negTwo => exact wittNegTwo_le_chiralityEven hLane
  | zero => exact wittZero_le_chiralityEven hLane
  | posTwo => exact wittPosTwo_le_chiralityEven hLane

theorem chiralityEven_bracket_chiralityEven
    {X Y : MatStage 5} (hX : X ∈ chiralityEven)
    (hY : Y ∈ chiralityEven) : bracket X Y ∈ chiralityEven := by
  rw [mem_chiralityEven_iff] at hX hY ⊢
  rw [chiralityConjugation_bracket, hX, hY]

theorem chiralityEven_bracket_chiralityOdd
    {X Y : MatStage 5} (hX : X ∈ chiralityEven)
    (hY : Y ∈ chiralityOdd) : bracket X Y ∈ chiralityOdd := by
  rw [mem_chiralityEven_iff] at hX
  rw [mem_chiralityOdd_iff] at hY ⊢
  rw [chiralityConjugation_bracket, hX, hY]
  unfold bracket
  noncomm_ring

theorem chiralityOdd_bracket_chiralityEven
    {X Y : MatStage 5} (hX : X ∈ chiralityOdd)
    (hY : Y ∈ chiralityEven) : bracket X Y ∈ chiralityOdd := by
  rw [mem_chiralityOdd_iff] at hX ⊢
  rw [mem_chiralityEven_iff] at hY
  rw [chiralityConjugation_bracket, hX, hY]
  unfold bracket
  noncomm_ring

theorem chiralityOdd_bracket_chiralityOdd
    {X Y : MatStage 5} (hX : X ∈ chiralityOdd)
    (hY : Y ∈ chiralityOdd) : bracket X Y ∈ chiralityEven := by
  rw [mem_chiralityOdd_iff] at hX hY
  rw [mem_chiralityEven_iff]
  rw [chiralityConjugation_bracket, hX, hY]
  unfold bracket
  noncomm_ring

end InfoGeometry.Canonical.Cl55WittChiralityRefinement
