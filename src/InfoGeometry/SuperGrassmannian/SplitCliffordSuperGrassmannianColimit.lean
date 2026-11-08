import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

/-!
# Dimension Formulas and Equal-Shift Arithmetic

This module defines natural-number formulas for vector, Clifford, and spinor
dimensions and proves identities between those formulas. The stage-four result
is a dimension equality, and the stage-eight result is a finite dimension
calculation; these declarations do not construct spinor carriers, triality
maps, Clifford algebra equivalences, or Bott periodicity.

The other declarations prove parity of a power-of-two expression, scalar
normalization under an assumed factor-four scaling equation, and preservation
of a natural-number difference under assumed equal dimension shifts. They do
not construct a super-Grassmannian or Berezinian line bundle, an operator trace
on a Clifford algebra, an inductive colimit, or a Fredholm index. Concrete
operator and categorical results are formalized in separate owner modules.
-/

namespace InfoGeometry.SuperGrassmannian.SplitCliffordColimit

open Real

/-! ### 1. Natural-Number Formulae -/

/-- Natural-number formula `2 * n`, used here as a vector-dimension value. -/
def vectorDim (n : ℕ) : ℕ := 2 * n

/-- Formula `4 ^ n` used as a Clifford-dimension value. -/
def cliffordDim (n : ℕ) : ℕ := 4 ^ n

/-- Formula `2 ^ n` used as a spinor-dimension value. -/
def spinorDim (n : ℕ) : ℕ := 2 ^ n

/-- Formula `2 ^ (n - 1)` used for a chiral half-dimension. -/
def chiralHalfDim (n : ℕ) : ℕ := 2 ^ (n - 1)

/-- The formula `4 ^ n` equals `2 ^ (2 * n)`. -/
theorem clifford_dim_eq_two_pow_two_n (n : ℕ) :
    cliffordDim n = 2 ^ (2 * n) := by
  dsimp [cliffordDim]
  have h4 : (4 : ℕ) = 2 ^ 2 := by rfl
  rw [h4, ← Nat.pow_mul]

/-- The square of `2 ^ n` equals the formula `4 ^ n`. -/
theorem spinor_sq_eq_clifford (n : ℕ) :
    (spinorDim n) ^ 2 = cliffordDim n := by
  dsimp [spinorDim, cliffordDim]
  have h4 : (4 : ℕ) = 2 ^ 2 := by rfl
  rw [h4, ← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm n 2]

/-- The two half-dimension formulas sum to `2 ^ n` when `n` is positive. -/
theorem chiral_split_sum (n : ℕ) (hn : 1 ≤ n) :
    chiralHalfDim n + chiralHalfDim n = spinorDim n := by
  dsimp [chiralHalfDim, spinorDim]
  have h_two : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 * 2 ^ (n - 1) := by ring
  rw [h_two]
  have h_succ : 2 * 2 ^ (n - 1) = 2 ^ ((n - 1) + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  rw [h_succ]
  have h_pred : (n - 1) + 1 = n := Nat.sub_add_cancel hn
  rw [h_pred]

/-! ### 2. Formula Evaluations at Parameters Four and Eight -/

/-- The formula `vectorDim` evaluates to `8` at parameter `4`. -/
theorem vector_dim_four : vectorDim 4 = 8 := by rfl

/-- The formula `chiralHalfDim` evaluates to `8` at parameter `4`. -/
theorem chiral_plus_dim_four : chiralHalfDim 4 = 8 := by rfl

/-- A second readout of `chiralHalfDim` at parameter `4`. -/
theorem chiral_minus_dim_four : chiralHalfDim 4 = 8 := by rfl

/-- At parameter `4`, the vector and chiral half-dimension formulas both equal `8`. -/
theorem stage_four_dimension_formula_agreement :
    vectorDim 4 = chiralHalfDim 4 ∧ chiralHalfDim 4 = 8 := by
  exact ⟨rfl, rfl⟩

/-- The formula `vectorDim` evaluates to `16` at parameter `8`. -/
theorem vector_dim_eight : vectorDim 8 = 16 := by rfl

/-- The formula `spinorDim` evaluates to `256` at parameter `8`. -/
theorem spinor_dim_eight : spinorDim 8 = 256 := by rfl

/-- The formula `cliffordDim` evaluates to `65536` at parameter `8`. -/
theorem clifford_dim_eight : cliffordDim 8 = 65536 := by rfl

/--
At parameter `8`, the spinor-dimension formula is `256` and its square equals
the Clifford-dimension formula `65536`. This is an arithmetic identity.
-/
theorem stage_eight_dimension_formula_identity :
    spinorDim 8 = 256 ∧ (spinorDim 8) ^ 2 = cliffordDim 8 ∧ cliffordDim 8 = 65536 := by
  refine ⟨rfl, ?_, rfl⟩
  exact spinor_sq_eq_clifford 8

/-! ### 3. Bounded Natural-Number Pairs -/

/-- Natural-number parameters bounded by the two chiral half-dimension formulas. -/
structure BoundedChiralPair (n : ℕ) where
  p : ℕ
  q : ℕ
  le_chiral_plus : p ≤ chiralHalfDim n
  le_chiral_minus : q ≤ chiralHalfDim n

/-- The datum whose two parameters both equal `chiralHalfDim n`. -/
def balancedChiralPair (n : ℕ) (hn : 1 ≤ n) : BoundedChiralPair n :=
  { p := chiralHalfDim n
    q := chiralHalfDim n
    le_chiral_plus := le_rfl
    le_chiral_minus := le_rfl }

/-- The value of the chiral half-dimension formula is even for `n ≥ 2`. -/
theorem chiral_half_dim_even (n : ℕ) (hn : 2 ≤ n) :
    ∃ k : ℕ, chiralHalfDim n = 2 * k := by
  dsimp [chiralHalfDim]
  have h_decomp : n - 1 = (n - 2) + 1 := by omega
  rw [h_decomp, Nat.pow_succ]
  exact ⟨2 ^ (n - 2), by ring⟩

/-- 
For `n ≥ 2`, raising `-1` to the chiral half-dimension formula gives `1`.
This is a parity identity, not an orientation statement.
-/
theorem chiral_half_dimension_sign_even (n : ℕ) (hn : 2 ≤ n) :
    (-1 : ℤ) ^ (chiralHalfDim n) = 1 := by
  rcases chiral_half_dim_even n hn with ⟨k, hk⟩
  rw [hk]
  have h_sq : (-1 : ℤ) ^ (2 * k) = ((-1 : ℤ) ^ 2) ^ k := by rw [pow_mul]
  rw [h_sq]
  have h_neg_one_sq : (-1 : ℤ) ^ 2 = 1 := by rfl
  rw [h_neg_one_sq, one_pow]

/-! ### 4. Scalar Normalization Formulae -/

/-- 
Scalar normalization formula `(4 ^ n)⁻¹ * rawTr`; this is not a trace
map on a Clifford algebra.
-/
def normalizedScalarValue (n : ℕ) (rawTr : ℝ) : ℝ :=
  ((1 : ℝ) / (4 : ℝ) ^ n) * rawTr

/-- Scalar used as the raw identity-trace formula at stage `n`. -/
def rawStageScalarValue (n : ℕ) : ℝ :=
  (4 : ℝ) ^ n

/-- The scalar normalization formula sends its matching raw value to `1`. -/
theorem normalized_identity_trace_eq_one (n : ℕ) :
    normalizedScalarValue n (rawStageScalarValue n) = 1 := by
  dsimp [normalizedScalarValue, rawStageScalarValue]
  have hpos : (4 : ℝ) ^ n ≠ 0 := by positivity
  exact one_div_mul_cancel hpos

/-- Two real values satisfying a factor-four scaling equation. -/
structure FactorFourScalarData (n : ℕ) where
  tr_level_n : ℝ
  tr_level_succ : ℝ
  bonding_quadruples : tr_level_succ = 4 * tr_level_n

/-- The scalar normalized values agree under the supplied factor-four equation. -/
theorem normalized_scalar_factor_four_cancellation (n : ℕ) (data : FactorFourScalarData n) :
    normalizedScalarValue (n + 1) data.tr_level_succ = normalizedScalarValue n data.tr_level_n := by
  dsimp [normalizedScalarValue]
  rw [data.bonding_quadruples, pow_succ]
  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  have h_div : (1 : ℝ) / ((4 : ℝ) ^ n * 4) = ((1 : ℝ) / (4 : ℝ) ^ n) * (1 / 4) := by
    rw [← one_div_mul_one_div]
  rw [h_div]
  calc
    ((1 : ℝ) / (4 : ℝ) ^ n) * (1 / 4) * (4 * data.tr_level_n) =
        ((1 : ℝ) / (4 : ℝ) ^ n) * ((1 / 4) * 4 * data.tr_level_n) := by ring
    _ = ((1 : ℝ) / (4 : ℝ) ^ n) * (1 * data.tr_level_n) := by
      have h_one : (1 / (4 : ℝ)) * 4 = 1 := one_div_mul_cancel h4
      rw [h_one]
    _ = ((1 : ℝ) / (4 : ℝ) ^ n) * data.tr_level_n := by ring

/-! ### 5. Equal-Shift Integer-Difference Arithmetic -/

/-- A pair of natural numbers indexed by a stage parameter. -/
structure ChiralDimensionPair (n : ℕ) where
  dim_plus : ℕ
  dim_minus : ℕ

/-- The integer difference of the two natural-number fields. -/
def integerDimensionDifference {n : ℕ} (s : ChiralDimensionPair n) : ℤ :=
  (s.dim_plus : ℤ) - (s.dim_minus : ℤ)

/-- Successor-stage pairs whose two components have the same supplied increment. -/
structure EqualShiftDimensionData (n : ℕ) where
  state_n : ChiralDimensionPair n
  state_succ : ChiralDimensionPair (n + 1)
  shift : ℕ
  h_plus : state_succ.dim_plus = state_n.dim_plus + shift
  h_minus : state_succ.dim_minus = state_n.dim_minus + shift

/-- Equal increments preserve the integer difference of the two fields. -/
theorem equal_shift_preserves_dimension_difference (n : ℕ) (b : EqualShiftDimensionData n) :
    integerDimensionDifference b.state_succ = integerDimensionDifference b.state_n := by
  dsimp [integerDimensionDifference]
  rw [b.h_plus, b.h_minus]
  push_cast
  ring

/-! ### 6. Master Verification Certificate -/

/-- Bundle of the arithmetic and scalar equal-shift results proved in this module. -/
structure SplitCliffordDimensionArithmeticCertificate : Prop where
  clifford_dim_sq : ∀ n : ℕ, (spinorDim n) ^ 2 = cliffordDim n
  chiral_sum : ∀ n : ℕ, 1 ≤ n → chiralHalfDim n + chiralHalfDim n = spinorDim n
  stage_four_dimension_formula_agreement : vectorDim 4 = chiralHalfDim 4 ∧ chiralHalfDim 4 = 8
  stage_eight_dimension_formula_identity : spinorDim 8 = 256 ∧ (spinorDim 8) ^ 2 = cliffordDim 8 ∧ cliffordDim 8 = 65536
  chiral_half_dimension_sign_even : ∀ n : ℕ, 2 ≤ n → (-1 : ℤ) ^ (chiralHalfDim n) = 1
  normalized_scalar_factor_four_cancellation : ∀ (n : ℕ) (data : FactorFourScalarData n),
    normalizedScalarValue (n + 1) data.tr_level_succ = normalizedScalarValue n data.tr_level_n
  normalized_identity_trace_one : ∀ n : ℕ, normalizedScalarValue n (rawStageScalarValue n) = 1
  equal_shift_preserves_dimension_difference : ∀ (n : ℕ) (b : EqualShiftDimensionData n),
    integerDimensionDifference b.state_succ = integerDimensionDifference b.state_n

/-- Construct the arithmetic certificate from the proved formula lemmas. -/
theorem compile_split_clifford_dimension_arithmetic : SplitCliffordDimensionArithmeticCertificate where
  clifford_dim_sq := spinor_sq_eq_clifford
  chiral_sum := chiral_split_sum
  stage_four_dimension_formula_agreement := stage_four_dimension_formula_agreement
  stage_eight_dimension_formula_identity := stage_eight_dimension_formula_identity
  chiral_half_dimension_sign_even := chiral_half_dimension_sign_even
  normalized_scalar_factor_four_cancellation := normalized_scalar_factor_four_cancellation
  normalized_identity_trace_one := normalized_identity_trace_eq_one
  equal_shift_preserves_dimension_difference := equal_shift_preserves_dimension_difference

end InfoGeometry.SuperGrassmannian.SplitCliffordColimit
