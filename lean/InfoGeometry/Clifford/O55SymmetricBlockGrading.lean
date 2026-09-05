import Mathlib
import proofs.O55GradedGeneratorBasis

/-!
# The symmetric `ℤ₂` block grading of `o(5,5)`

The existing `O55GradedGeneratorBasis` counts positive rotations, negative
rotations, and mixed boosts.  This file supplies the corresponding structural
Lie grading on the `10 × 10` split carrier.

Let `η = diag(I₅,-I₅)`.  Conjugation `X ↦ η X η` has eigenvalues `+1` on
block-diagonal matrices and `-1` on block-off-diagonal matrices.  Its
commutator table is

`[even,even] ⊆ even`, `[even,odd] ⊆ odd`, `[odd,odd] ⊆ even`.

Intersecting with the equation `Xᵀη + ηX = 0` gives the same genuine
`ℤ₂` grading on the matrix realization of `o(5,5)`.
-/

noncomputable section

namespace InfoGeometry.Clifford.O55SymmetricBlockGrading

open Matrix

abbrev SplitIndex := Fin 5 ⊕ Fin 5
abbrev Mat55 := Matrix SplitIndex SplitIndex ℝ

/-- Split metric and Cartan involution matrix. -/
def splitMetric : Mat55 :=
  Matrix.fromBlocks 1 0 0 (-1)

@[simp] theorem splitMetric_sq :
    splitMetric * splitMetric = (1 : Mat55) := by
  rw [splitMetric, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

/-- Cartan/symmetric-pair involution. -/
def cartanInvolution (X : Mat55) : Mat55 :=
  splitMetric * X * splitMetric

@[simp] theorem cartanInvolution_involutive (X : Mat55) :
    cartanInvolution (cartanInvolution X) = X := by
  unfold cartanInvolution
  noncomm_ring [splitMetric_sq]

/-- Multiplicativity of the involution. -/
theorem cartanInvolution_mul (X Y : Mat55) :
    cartanInvolution (X * Y) =
      cartanInvolution X * cartanInvolution Y := by
  unfold cartanInvolution
  noncomm_ring [splitMetric_sq]

/-- Matrix commutator. -/
def commutator (X Y : Mat55) : Mat55 :=
  X * Y - Y * X

/-- Even/block-diagonal predicate. -/
def IsEven (X : Mat55) : Prop :=
  cartanInvolution X = X

/-- Odd/block-off-diagonal predicate. -/
def IsOdd (X : Mat55) : Prop :=
  cartanInvolution X = -X

/-- The involution preserves commutators. -/
theorem cartanInvolution_commutator (X Y : Mat55) :
    cartanInvolution (commutator X Y) =
      commutator (cartanInvolution X) (cartanInvolution Y) := by
  simp only [commutator, cartanInvolution, mul_sub, sub_mul]
  rw [cartanInvolution_mul, cartanInvolution_mul]

/-- Even-even commutators are even. -/
theorem commutator_even_even {X Y : Mat55}
    (hX : IsEven X) (hY : IsEven Y) :
    IsEven (commutator X Y) := by
  unfold IsEven at hX hY ⊢
  rw [cartanInvolution_commutator, hX, hY]

/-- Even-odd commutators are odd. -/
theorem commutator_even_odd {X Y : Mat55}
    (hX : IsEven X) (hY : IsOdd Y) :
    IsOdd (commutator X Y) := by
  unfold IsEven at hX
  unfold IsOdd at hY ⊢
  rw [cartanInvolution_commutator, hX, hY]
  unfold commutator
  noncomm_ring

/-- Odd-even commutators are odd. -/
theorem commutator_odd_even {X Y : Mat55}
    (hX : IsOdd X) (hY : IsEven Y) :
    IsOdd (commutator X Y) := by
  unfold IsOdd at hX ⊢
  unfold IsEven at hY
  rw [cartanInvolution_commutator, hX, hY]
  unfold commutator
  noncomm_ring

/-- Odd-odd commutators are even. -/
theorem commutator_odd_odd {X Y : Mat55}
    (hX : IsOdd X) (hY : IsOdd Y) :
    IsEven (commutator X Y) := by
  unfold IsOdd at hX hY
  unfold IsEven
  rw [cartanInvolution_commutator, hX, hY]
  unfold commutator
  noncomm_ring

/-- Matrix equation defining the split orthogonal Lie algebra. -/
def IsO55Lie (X : Mat55) : Prop :=
  X.transpose * splitMetric + splitMetric * X = 0

/-- The matrix realization of `o(5,5)` is closed under commutators. -/
theorem commutator_mem_o55 {X Y : Mat55}
    (hX : IsO55Lie X) (hY : IsO55Lie Y) :
    IsO55Lie (commutator X Y) := by
  unfold IsO55Lie at hX hY ⊢
  unfold commutator
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul]
  noncomm_ring [hX, hY]

/-- Even part of the split orthogonal Lie algebra. -/
def IsO55Even (X : Mat55) : Prop :=
  IsO55Lie X ∧ IsEven X

/-- Odd part of the split orthogonal Lie algebra. -/
def IsO55Odd (X : Mat55) : Prop :=
  IsO55Lie X ∧ IsOdd X

/-- Native symmetric-pair bracket table inside `o(5,5)`. -/
theorem o55_even_even {X Y : Mat55}
    (hX : IsO55Even X) (hY : IsO55Even Y) :
    IsO55Even (commutator X Y) :=
  ⟨commutator_mem_o55 hX.1 hY.1,
    commutator_even_even hX.2 hY.2⟩

theorem o55_even_odd {X Y : Mat55}
    (hX : IsO55Even X) (hY : IsO55Odd Y) :
    IsO55Odd (commutator X Y) :=
  ⟨commutator_mem_o55 hX.1 hY.1,
    commutator_even_odd hX.2 hY.2⟩

theorem o55_odd_even {X Y : Mat55}
    (hX : IsO55Odd X) (hY : IsO55Even Y) :
    IsO55Odd (commutator X Y) :=
  ⟨commutator_mem_o55 hX.1 hY.1,
    commutator_odd_even hX.2 hY.2⟩

theorem o55_odd_odd {X Y : Mat55}
    (hX : IsO55Odd X) (hY : IsO55Odd Y) :
    IsO55Even (commutator X Y) :=
  ⟨commutator_mem_o55 hX.1 hY.1,
    commutator_odd_odd hX.2 hY.2⟩

/-- Parity associated with the previously named generator families. -/
def generatorParity :
    O55GradedGeneratorBasis.O55GeneratorGrade → ZMod 2
  | .positiveRotation => 0
  | .negativeRotation => 0
  | .mixedBoost => 1

@[simp] theorem positiveRotation_even :
    generatorParity
      O55GradedGeneratorBasis.O55GeneratorGrade.positiveRotation = 0 := rfl

@[simp] theorem negativeRotation_even :
    generatorParity
      O55GradedGeneratorBasis.O55GeneratorGrade.negativeRotation = 0 := rfl

@[simp] theorem mixedBoost_odd :
    generatorParity
      O55GradedGeneratorBasis.O55GeneratorGrade.mixedBoost = 1 := rfl

/-- Full compact/even generator count. -/
def fullEvenGeneratorCount : ℕ :=
  O55GradedGeneratorBasis.fullPositiveRotationCount +
    O55GradedGeneratorBasis.fullNegativeRotationCount

/-- Full noncompact/odd generator count. -/
def fullOddGeneratorCount : ℕ :=
  O55GradedGeneratorBasis.fullMixedBoostCount

@[simp] theorem full_even_generator_count_eq :
    fullEvenGeneratorCount = 20 := by
  norm_num [fullEvenGeneratorCount,
    O55GradedGeneratorBasis.fullPositiveRotationCount,
    O55GradedGeneratorBasis.fullNegativeRotationCount,
    O55GradedGeneratorBasis.chooseTwo]

@[simp] theorem full_odd_generator_count_eq :
    fullOddGeneratorCount = 25 := by
  exact O55GradedGeneratorBasis.full_mixed_boost_count_eq

@[simp] theorem full_even_add_odd_eq :
    fullEvenGeneratorCount + fullOddGeneratorCount = 45 := by
  norm_num

/-- Structural `o(5,5)` `ℤ₂`-grading packet. -/
theorem o55_symmetric_grading_packet :
    splitMetric * splitMetric = (1 : Mat55) ∧
      (∀ X, cartanInvolution (cartanInvolution X) = X) ∧
      (∀ X Y, IsO55Even X → IsO55Even Y →
        IsO55Even (commutator X Y)) ∧
      (∀ X Y, IsO55Even X → IsO55Odd Y →
        IsO55Odd (commutator X Y)) ∧
      (∀ X Y, IsO55Odd X → IsO55Odd Y →
        IsO55Even (commutator X Y)) ∧
      fullEvenGeneratorCount = 20 ∧
      fullOddGeneratorCount = 25 ∧
      fullEvenGeneratorCount + fullOddGeneratorCount = 45 := by
  exact ⟨splitMetric_sq,
    cartanInvolution_involutive,
    fun _ _ => o55_even_even,
    fun _ _ => o55_even_odd,
    fun _ _ => o55_odd_odd,
    full_even_generator_count_eq,
    full_odd_generator_count_eq,
    full_even_add_odd_eq⟩

end InfoGeometry.Clifford.O55SymmetricBlockGrading
