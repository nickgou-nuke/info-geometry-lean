import Mathlib
import InfoGeometry.Geometry.PauliParavectorBridge
import InfoGeometry.Canonical.MatrixStageLorentzKANSoldering

namespace InfoGeometry.Geometry.NullConeAlgebra

open Matrix
open InfoGeometry.Geometry.PauliParavectorBridge
open InfoGeometry.Canonical.MatrixStageLorentzKANSoldering

inductive Archetype
  | matrix
  | determinant
  | hermitian
  | lorentz
  | nilpotence
  | nullAddition
  deriving DecidableEq, Fintype

namespace Archetype

def prerequisites : Archetype → Finset Archetype
  | matrix => {matrix}
  | determinant => {matrix, determinant}
  | hermitian => {matrix, hermitian}
  | lorentz => {matrix, determinant, hermitian, lorentz}
  | nilpotence => {matrix, determinant, hermitian, nilpotence}
  | nullAddition => {matrix, determinant, hermitian, nullAddition}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

instance : DecidableLE Archetype := fun earlier later =>
  inferInstanceAs (Decidable (prerequisites earlier ⊆ prerequisites later))

theorem lorentz_nilpotence_independent :
    ¬ lorentz ≤ nilpotence ∧ ¬ nilpotence ≤ lorentz := by
  decide

theorem null_addition_requires_both :
    determinant ≤ nullAddition ∧ hermitian ≤ nullAddition := by
  decide

end Archetype

theorem det_eq_zero_of_square_zero
    (operator : Matrix (Fin 2) (Fin 2) ℂ)
    (squareZero : operator * operator = 0) :
    operator.det = 0 := by
  have productZero : operator.det * operator.det = 0 := by
    rw [← Matrix.det_mul, squareZero]
  rcases mul_eq_zero.mp productZero with vanished | vanished
  · exact vanished
  · exact vanished

theorem hermitian_square_zero_implies_zero
    (state : HermitianMat2)
    (squareZero : state.mat * state.mat = 0) :
    state.mat = 0 := by
  apply Matrix.conjTranspose_mul_self_eq_zero.mp
  rw [state.herm]
  exact squareZero

theorem unipotent_not_square_zero (parameter : ℂ) :
    unipotentN parameter * unipotentN parameter ≠ 0 := by
  intro squareZero
  have determinantZero :=
    det_eq_zero_of_square_zero (unipotentN parameter) squareZero
  have contradiction : (1 : ℂ) = 0 :=
    (unipotentN_det parameter).symm.trans determinantZero
  exact one_ne_zero contradiction

theorem tripotent_determinant
    (operator : Matrix (Fin 2) (Fin 2) ℂ)
    (tripotent : operator * operator * operator = operator) :
    operator.det = 0 ∨ operator.det = 1 ∨ operator.det = -1 := by
  have determinantEquation := congrArg Matrix.det tripotent
  rw [Matrix.det_mul, Matrix.det_mul] at determinantEquation
  have factorization :
      operator.det * (operator.det - 1) * (operator.det + 1) = 0 := by
    calc
      operator.det * (operator.det - 1) * (operator.det + 1) =
          operator.det * operator.det * operator.det - operator.det := by ring
      _ = 0 := sub_eq_zero.mpr determinantEquation
  rcases mul_eq_zero.mp factorization with firstFactors | lastFactor
  · rcases mul_eq_zero.mp firstFactors with zeroFactor | oneFactor
    · exact Or.inl zeroFactor
    · exact Or.inr (Or.inl (sub_eq_zero.mp oneFactor))
  · right
    right
    linear_combination lastFactor

theorem lorentz_null_iff
    (transformation : Matrix (Fin 2) (Fin 2) ℂ)
    (specialLinear : isSL2C transformation)
    (state : HermitianMat2) :
    (lorentzSoldering transformation state).mat.det = 0 ↔ state.mat.det = 0 := by
  rw [lorentzSoldering_isometry transformation specialLinear state]

theorem kan_null_iff
    {transformation : Matrix (Fin 2) (Fin 2) ℂ}
    (factorization : KANData transformation)
    (state : HermitianMat2) :
    (lorentzSoldering transformation state).mat.det = 0 ↔ state.mat.det = 0 :=
  lorentz_null_iff transformation (KANData_det_one factorization) state

def minkowskiPairing (first second : Minkowski4) : ℝ :=
  first.t * second.t - first.x * second.x -
    first.y * second.y - first.z * second.z

theorem minkowski_polarization (first second : Minkowski4) :
    (first + second).q = first.q + second.q + 2 * minkowskiPairing first second := by
  change
    (first.t + second.t) ^ 2 - (first.x + second.x) ^ 2 -
        (first.y + second.y) ^ 2 - (first.z + second.z) ^ 2 =
      first.q + second.q + 2 * minkowskiPairing first second
  unfold Minkowski4.q minkowskiPairing
  ring

theorem null_sum_iff_pairing_zero
    (first second : Minkowski4)
    (firstNull : first.IsNull) (secondNull : second.IsNull) :
    (first + second).IsNull ↔ minkowskiPairing first second = 0 := by
  have firstZero : first.q = 0 := firstNull
  have secondZero : second.q = 0 := secondNull
  change (first + second).q = 0 ↔ minkowskiPairing first second = 0
  rw [minkowski_polarization, firstZero, secondZero]
  constructor <;> intro equality <;> linarith

theorem null_sum_timelike_iff_positive_pairing
    (first second : Minkowski4)
    (firstNull : first.IsNull) (secondNull : second.IsNull) :
    0 < (first + second).q ↔ 0 < minkowskiPairing first second := by
  have firstZero : first.q = 0 := firstNull
  have secondZero : second.q = 0 := secondNull
  rw [minkowski_polarization, firstZero, secondZero]
  constructor <;> intro inequality <;> linarith

theorem null_vectors_can_have_timelike_sum :
    ∃ first second : Minkowski4,
      first.IsNull ∧ second.IsNull ∧ (first + second).q = 4 := by
  refine ⟨⟨1, 0, 0, 1⟩, ⟨1, 0, 0, -1⟩, ?_, ?_, ?_⟩
  · change (1 : ℝ) ^ 2 - 0 ^ 2 - 0 ^ 2 - 1 ^ 2 = 0
    norm_num
  · change (1 : ℝ) ^ 2 - 0 ^ 2 - 0 ^ 2 - (-1) ^ 2 = 0
    norm_num
  · rw [minkowski_polarization]
    norm_num [Minkowski4.q, minkowskiPairing]

end InfoGeometry.Geometry.NullConeAlgebra
