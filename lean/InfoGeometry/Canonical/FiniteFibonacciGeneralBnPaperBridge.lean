import InfoGeometry.Canonical.FiniteFibonacciHigherAnyonPaperBridge
import InfoGeometry.Canonical.FiniteFibonacciGeneralBraidGenerators
import InfoGeometry.Canonical.FiniteFibonacciRegisterWords
import InfoGeometry.Canonical.FiniteFibonacciRegisterSubgroup
import InfoGeometry.Canonical.FiniteFibonacciSparseLowAnyonPaperBridge

/-!
# InfoGeometry.Canonical.FiniteFibonacciGeneralBnPaperBridge

Paper-facing bridge for the general `Bₙ` generator discussion.

The repository does not own a full general conformal-block monodromy family.
What it does own is the finite register / recursive-basis skeleton that the
paper's Section 7 abstracts:

* Fibonacci direct-sum recursion for the basis size;
* local generator indices for the left end, even generators, and the right end;
* separatedness of distinct even generators;
* finite block-diagonal no-leakage on the computational sector;
* the first explicit low-anyon templates (`n = 5,6,7,8`) as finite examples.

The determinant recurrence from the paper is represented here only as an
assumption-carrying schedule interface.  This file does not derive a general
matrix family or a theorem that the paper's determinant schedule follows from
repository-owned monodromy data.

No conformal blocks.
No all-`n` monodromy matrices.
No analytic continuation.
-/

namespace FiniteFibonacciGeneralBnPaperBridge

open FiniteFibonacciComputationalSpace
open FiniteFibonacciFusionMatrix
open FiniteFibonacciHigherAnyonBraiding
open FiniteFibonacciHigherAnyonPaperBridge
open FiniteFibonacciRegisterWords
open FiniteFibonacciRegisterSubgroup
open FiniteFibonacciRegisterWords
open FiniteFibonacciLowAnyonMatrices
open FiniteFibonacciSparseLowAnyonMatrices
open FiniteFibonacciSparseLowAnyonPaperBridge

/-- The general recursive basis step from the paper's Section 7. -/
theorem general_recursiveBasis_step (k : ℕ) :
    RecursiveFibonacciBlockBasis (k + 2) =
      (RecursiveFibonacciBlockBasis k ⊕ RecursiveFibonacciBlockBasis (k + 1)) :=
  finiteRecursiveBasis_step k

/-- The general recursive dimension step from the paper's Section 7. -/
theorem general_recursiveFibonacciDimension_step (k : ℕ) :
    recursiveFibonacciDimension (k + 2) =
      recursiveFibonacciDimension k + recursiveFibonacciDimension (k + 1) :=
  finiteRecursiveFibonacciDimension_step k

/-- The higher-anyon recursive dimension matches the general block count at shifted arity. -/
theorem general_recursiveDimension_eq_blockDimension (k : ℕ) :
    recursiveFibonacciDimension k =
      FiniteFibonacciGeneralBraidGenerators.fibonacciBlockDimension (k + 2) := by
  rw [recursiveFibonacciDimension_eq_fib_succ]
  simp [FiniteFibonacciGeneralBraidGenerators.fibonacciBlockDimension]

/-- The higher-anyon recursive basis has the same cardinality as the general block count. -/
theorem general_recursiveBasis_card_eq_blockDimension (k : ℕ) :
    Fintype.card (RecursiveFibonacciBlockBasis k) =
      FiniteFibonacciGeneralBraidGenerators.fibonacciBlockDimension (k + 2) := by
  rw [recursiveFibonacciBlockBasis_card, general_recursiveDimension_eq_blockDimension]

/-- Re-indexed recurrence for the general block count induced by the higher-anyon recursion. -/
theorem general_blockDimension_step_from_recursive (k : ℕ) :
    FiniteFibonacciGeneralBraidGenerators.fibonacciBlockDimension (k + 4) =
      FiniteFibonacciGeneralBraidGenerators.fibonacciBlockDimension (k + 2) +
        FiniteFibonacciGeneralBraidGenerators.fibonacciBlockDimension (k + 3) := by
  simpa using FiniteFibonacciGeneralBraidGenerators.fibonacciBlockDimension_step k

/-- The first recursive-basis cardinalities recover the explicit low-anyon examples `1,1,2,3,5,8,13`. -/
theorem general_recursiveBasis_card_eight :
    Fintype.card (RecursiveFibonacciBlockBasis 6) = 13 := by
  rw [general_recursiveBasis_card_eq_blockDimension]
  exact FiniteFibonacciGeneralBraidGenerators.fibonacciBlockDimension_eight

/-- The `n = 8` sparse template matches the recursive-basis cardinality at `k = 6`. -/
theorem general_sparse_basis8_matches_recursive_basis :
    Fintype.card FiniteFibonacciSparseLowAnyonMatrices.Basis8 =
      Fintype.card (RecursiveFibonacciBlockBasis 6) := by
  rw [sectionSix_basis8_card, general_recursiveBasis_card_eight]

/-- With endpoints `0,0`, local admissibility is exactly the `010` condition. -/
theorem general_tripleAdmissible_zero_zero_iff {middle : Bool} :
    TripleAdmissible false middle false ↔ middle = true := by
  constructor
  · intro h
    exact middle_eq_true_of_left_zero h
  · intro hm
    constructor <;> simp [AdjacentAdmissible, hm]

/-- With endpoints `0,1`, local admissibility is exactly the `011` condition. -/
theorem general_tripleAdmissible_zero_one_iff {middle : Bool} :
    TripleAdmissible false middle true ↔ middle = true := by
  constructor
  · intro h
    exact middle_eq_true_of_left_zero h
  · intro hm
    constructor <;> simp [AdjacentAdmissible, hm]

/-- With endpoints `1,0`, local admissibility is exactly the `110` condition. -/
theorem general_tripleAdmissible_one_zero_iff {middle : Bool} :
    TripleAdmissible true middle false ↔ middle = true := by
  constructor
  · intro h
    exact middle_eq_true_of_right_zero h
  · intro hm
    constructor <;> simp [AdjacentAdmissible, hm]

/-- The admissible `010` local block has the `q⁻⁴` singlet phase. -/
theorem general_localSingletPhase_of_zero_zero
    (q : Units ℂ) {middle : Bool} (h : TripleAdmissible false middle false) :
    localSingletPhase q (localBraidBlockKind false middle false) = some (q ^ (-4 : ℤ)) := by
  rw [localBraidBlockKind_of_zero_zero h]
  rfl

/-- The admissible `011` local block has the `q³` singlet phase. -/
theorem general_localSingletPhase_of_zero_one
    (q : Units ℂ) {middle : Bool} (h : TripleAdmissible false middle true) :
    localSingletPhase q (localBraidBlockKind false middle true) = some (q ^ (3 : ℤ)) := by
  rw [localBraidBlockKind_of_zero_one h]
  rfl

/-- The admissible `110` local block has the `q³` singlet phase. -/
theorem general_localSingletPhase_of_one_zero
    (q : Units ℂ) {middle : Bool} (h : TripleAdmissible true middle false) :
    localSingletPhase q (localBraidBlockKind true middle false) = some (q ^ (3 : ℤ)) := by
  rw [localBraidBlockKind_of_one_zero h]
  rfl

/-- Any `1 _ 1` local block reads out as the four-anyon `B = F R F` matrix. -/
theorem general_localDoubletMatrix_of_one_one
    (q : Units ℂ) (τ root : ℂ) (middle : Bool) :
    localDoubletMatrix q τ root (localBraidBlockKind true middle true) =
      some (fibonacciFusionMatrix τ root * fibonacciRMatrix q * fibonacciFusionMatrix τ root) := by
  rw [localBraidBlockKind_of_one_one middle]
  exact localDoubletMatrix_doublet q τ root

/-- The symbolic `B`-block entries read off the four-anyon `B = F R F` matrix. -/
noncomputable def general_doubletBlockEntries (q : Units ℂ) (τ root : ℂ) : BBlockEntries where
  B00 := fibonacciBMatrix q τ root 0 0
  B01 := fibonacciBMatrix q τ root 0 1
  B10 := fibonacciBMatrix q τ root 1 0
  B11 := fibonacciBMatrix q τ root 1 1

/-- The symbolic `B`-block reconstructed from the general doublet entries is exactly `F R F`. -/
theorem general_doubletBlockEntries_matrix
    (q : Units ℂ) (τ root : ℂ) :
    BBlockEntries.matrix (general_doubletBlockEntries q τ root) = fibonacciBMatrix q τ root := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The last generator's first block is the `010` singlet phase. -/
theorem general_lastGenerator_first_from_localSinglet
    {a b : ℕ} (q : Units ℂ) (i : Fin a) :
    FiniteFibonacciGeneralBraidGenerators.lastGenerator
        (a := a) (b := b) (q ^ (-4 : ℤ)) (q ^ (3 : ℤ)) (Sum.inl i) (Sum.inl i) =
      q ^ (-4 : ℤ) := by
  simpa using
    FiniteFibonacciGeneralBraidGenerators.lastGenerator_first
      (a := a) (b := b) (q ^ (-4 : ℤ)) (q ^ (3 : ℤ)) i

/-- The last generator's middle block is the `011` singlet phase. -/
theorem general_lastGenerator_middle_from_localSinglet
    {a b : ℕ} (q : Units ℂ) (i : Fin b) :
    FiniteFibonacciGeneralBraidGenerators.lastGenerator
        (a := a) (b := b) (q ^ (-4 : ℤ)) (q ^ (3 : ℤ))
        (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl i)) =
      q ^ (3 : ℤ) := by
  simpa using
    FiniteFibonacciGeneralBraidGenerators.lastGenerator_middle
      (a := a) (b := b) (q ^ (-4 : ℤ)) (q ^ (3 : ℤ)) i

/-- The last generator's last block is the `110` singlet phase. -/
theorem general_lastGenerator_last_from_localSinglet
    {a b : ℕ} (q : Units ℂ) (i : Fin a) :
    FiniteFibonacciGeneralBraidGenerators.lastGenerator
        (a := a) (b := b) (q ^ (-4 : ℤ)) (q ^ (3 : ℤ))
        (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr i)) =
      q ^ (3 : ℤ) := by
  simpa using
    FiniteFibonacciGeneralBraidGenerators.lastGenerator_last
      (a := a) (b := b) (q ^ (-4 : ℤ)) (q ^ (3 : ℤ)) i

/-- The last-but-one generator's top-left block uses the `B00` entry of the local `F R F` doublet. -/
theorem general_lastButOneGenerator_B00_from_localDoublet
    {a b : ℕ} (q : Units ℂ) (τ root : ℂ) (i : Fin a) :
    FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator
        (a := a) (b := b) (q ^ (3 : ℤ)) (general_doubletBlockEntries q τ root)
        (Sum.inl i) (Sum.inl i) =
      fibonacciBMatrix q τ root 0 0 := by
  simpa [general_doubletBlockEntries] using
    FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator_B00
      (a := a) (b := b) (q ^ (3 : ℤ)) (general_doubletBlockEntries q τ root) i

/-- The last-but-one generator's top-right block uses the `B01` entry of the local `F R F` doublet. -/
theorem general_lastButOneGenerator_B01_from_localDoublet
    {a b : ℕ} (q : Units ℂ) (τ root : ℂ) (i : Fin a) :
    FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator
        (a := a) (b := b) (q ^ (3 : ℤ)) (general_doubletBlockEntries q τ root)
        (Sum.inl i) (Sum.inr (Sum.inr i)) =
      fibonacciBMatrix q τ root 0 1 := by
  simpa [general_doubletBlockEntries] using
    FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator_B01
      (a := a) (b := b) (q ^ (3 : ℤ)) (general_doubletBlockEntries q τ root) i

/-- The last-but-one generator's middle block uses the `011` singlet phase. -/
theorem general_lastButOneGenerator_middle_from_localSinglet
    {a b : ℕ} (q : Units ℂ) (τ root : ℂ) (i : Fin b) :
    FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator
        (a := a) (b := b) (q ^ (3 : ℤ)) (general_doubletBlockEntries q τ root)
        (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl i)) =
      q ^ (3 : ℤ) := by
  simpa using
    FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator_middle
      (a := a) (b := b) (q ^ (3 : ℤ)) (general_doubletBlockEntries q τ root) i

/-- The last-but-one generator's bottom-left block uses the `B10` entry of the local `F R F` doublet. -/
theorem general_lastButOneGenerator_B10_from_localDoublet
    {a b : ℕ} (q : Units ℂ) (τ root : ℂ) (i : Fin a) :
    FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator
        (a := a) (b := b) (q ^ (3 : ℤ)) (general_doubletBlockEntries q τ root)
        (Sum.inr (Sum.inr i)) (Sum.inl i) =
      fibonacciBMatrix q τ root 1 0 := by
  simpa [general_doubletBlockEntries] using
    FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator_B10
      (a := a) (b := b) (q ^ (3 : ℤ)) (general_doubletBlockEntries q τ root) i

/-- The last-but-one generator's bottom-right block uses the `B11` entry of the local `F R F` doublet. -/
theorem general_lastButOneGenerator_B11_from_localDoublet
    {a b : ℕ} (q : Units ℂ) (τ root : ℂ) (i : Fin a) :
    FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator
        (a := a) (b := b) (q ^ (3 : ℤ)) (general_doubletBlockEntries q τ root)
        (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr i)) =
      fibonacciBMatrix q τ root 1 1 := by
  simpa [general_doubletBlockEntries] using
    FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator_B11
      (a := a) (b := b) (q ^ (3 : ℤ)) (general_doubletBlockEntries q τ root) i

/-- The last generator has no off-diagonal support inside the first singlet block. -/
theorem general_lastGenerator_first_offDiagonal_zero
    {a b : ℕ} (q : Units ℂ) {i j : Fin a} (hij : i ≠ j) :
    FiniteFibonacciGeneralBraidGenerators.lastGenerator
        (a := a) (b := b) (q ^ (-4 : ℤ)) (q ^ (3 : ℤ)) (Sum.inl i) (Sum.inl j) = 0 := by
  simp [FiniteFibonacciGeneralBraidGenerators.lastGenerator, hij]

/-- The last generator has no off-diagonal support inside the middle singlet block. -/
theorem general_lastGenerator_middle_offDiagonal_zero
    {a b : ℕ} (q : Units ℂ) {i j : Fin b} (hij : i ≠ j) :
    FiniteFibonacciGeneralBraidGenerators.lastGenerator
        (a := a) (b := b) (q ^ (-4 : ℤ)) (q ^ (3 : ℤ))
        (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl j)) = 0 := by
  simp [FiniteFibonacciGeneralBraidGenerators.lastGenerator, hij]

/-- The last generator has no off-diagonal support inside the last singlet block. -/
theorem general_lastGenerator_last_offDiagonal_zero
    {a b : ℕ} (q : Units ℂ) {i j : Fin a} (hij : i ≠ j) :
    FiniteFibonacciGeneralBraidGenerators.lastGenerator
        (a := a) (b := b) (q ^ (-4 : ℤ)) (q ^ (3 : ℤ))
        (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) = 0 := by
  simp [FiniteFibonacciGeneralBraidGenerators.lastGenerator, hij]

/-- The last generator has zero support from the first block to the middle block. -/
theorem general_lastGenerator_left_middle_zero
    {a b : ℕ} (q : Units ℂ) (i : Fin a) (j : Fin b) :
    FiniteFibonacciGeneralBraidGenerators.lastGenerator
        (a := a) (b := b) (q ^ (-4 : ℤ)) (q ^ (3 : ℤ))
        (Sum.inl i) (Sum.inr (Sum.inl j)) = 0 := by
  simp [FiniteFibonacciGeneralBraidGenerators.lastGenerator]

/-- The last generator has zero support from the first block to the last block. -/
theorem general_lastGenerator_left_right_zero
    {a b : ℕ} (q : Units ℂ) (i j : Fin a) :
    FiniteFibonacciGeneralBraidGenerators.lastGenerator
        (a := a) (b := b) (q ^ (-4 : ℤ)) (q ^ (3 : ℤ))
        (Sum.inl i) (Sum.inr (Sum.inr j)) = 0 := by
  simp [FiniteFibonacciGeneralBraidGenerators.lastGenerator]

/-- The last generator has zero support from the middle block to the first block. -/
theorem general_lastGenerator_middle_left_zero
    {a b : ℕ} (q : Units ℂ) (i : Fin b) (j : Fin a) :
    FiniteFibonacciGeneralBraidGenerators.lastGenerator
        (a := a) (b := b) (q ^ (-4 : ℤ)) (q ^ (3 : ℤ))
        (Sum.inr (Sum.inl i)) (Sum.inl j) = 0 := by
  simp [FiniteFibonacciGeneralBraidGenerators.lastGenerator]

/-- The last generator has zero support from the middle block to the last block. -/
theorem general_lastGenerator_middle_right_zero
    {a b : ℕ} (q : Units ℂ) (i : Fin b) (j : Fin a) :
    FiniteFibonacciGeneralBraidGenerators.lastGenerator
        (a := a) (b := b) (q ^ (-4 : ℤ)) (q ^ (3 : ℤ))
        (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr j)) = 0 := by
  simp [FiniteFibonacciGeneralBraidGenerators.lastGenerator]

/-- The last generator has zero support from the last block to the first block. -/
theorem general_lastGenerator_right_left_zero
    {a b : ℕ} (q : Units ℂ) (i j : Fin a) :
    FiniteFibonacciGeneralBraidGenerators.lastGenerator
        (a := a) (b := b) (q ^ (-4 : ℤ)) (q ^ (3 : ℤ))
        (Sum.inr (Sum.inr i)) (Sum.inl j) = 0 := by
  simp [FiniteFibonacciGeneralBraidGenerators.lastGenerator]

/-- The last generator has zero support from the last block to the middle block. -/
theorem general_lastGenerator_right_middle_zero
    {a b : ℕ} (q : Units ℂ) (i : Fin a) (j : Fin b) :
    FiniteFibonacciGeneralBraidGenerators.lastGenerator
        (a := a) (b := b) (q ^ (-4 : ℤ)) (q ^ (3 : ℤ))
        (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl j)) = 0 := by
  simp [FiniteFibonacciGeneralBraidGenerators.lastGenerator]

/-- The last-but-one generator has no off-diagonal support inside the top-left `B00` block. -/
theorem general_lastButOneGenerator_B00_offDiagonal_zero
    {a b : ℕ} (q : Units ℂ) (τ root : ℂ) {i j : Fin a} (hij : i ≠ j) :
    FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator
        (a := a) (b := b) (q ^ (3 : ℤ)) (general_doubletBlockEntries q τ root)
        (Sum.inl i) (Sum.inl j) = 0 := by
  simp [FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator, hij]

/-- The last-but-one generator has no off-diagonal support inside the top-right `B01` block. -/
theorem general_lastButOneGenerator_B01_offDiagonal_zero
    {a b : ℕ} (q : Units ℂ) (τ root : ℂ) {i j : Fin a} (hij : i ≠ j) :
    FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator
        (a := a) (b := b) (q ^ (3 : ℤ)) (general_doubletBlockEntries q τ root)
        (Sum.inl i) (Sum.inr (Sum.inr j)) = 0 := by
  simp [FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator, hij]

/-- The last-but-one generator has no off-diagonal support inside the middle singlet block. -/
theorem general_lastButOneGenerator_middle_offDiagonal_zero
    {a b : ℕ} (q : Units ℂ) (τ root : ℂ) {i j : Fin b} (hij : i ≠ j) :
    FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator
        (a := a) (b := b) (q ^ (3 : ℤ)) (general_doubletBlockEntries q τ root)
        (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl j)) = 0 := by
  simp [FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator, hij]

/-- The last-but-one generator has no off-diagonal support inside the bottom-left `B10` block. -/
theorem general_lastButOneGenerator_B10_offDiagonal_zero
    {a b : ℕ} (q : Units ℂ) (τ root : ℂ) {i j : Fin a} (hij : i ≠ j) :
    FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator
        (a := a) (b := b) (q ^ (3 : ℤ)) (general_doubletBlockEntries q τ root)
        (Sum.inr (Sum.inr i)) (Sum.inl j) = 0 := by
  simp [FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator, hij]

/-- The last-but-one generator has no off-diagonal support inside the bottom-right `B11` block. -/
theorem general_lastButOneGenerator_B11_offDiagonal_zero
    {a b : ℕ} (q : Units ℂ) (τ root : ℂ) {i j : Fin a} (hij : i ≠ j) :
    FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator
        (a := a) (b := b) (q ^ (3 : ℤ)) (general_doubletBlockEntries q τ root)
        (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) = 0 := by
  simp [FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator, hij]

/-- The last-but-one generator has zero support from the first block to the middle block. -/
theorem general_lastButOneGenerator_left_middle_zero
    {a b : ℕ} (q : Units ℂ) (τ root : ℂ) (i : Fin a) (j : Fin b) :
    FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator
        (a := a) (b := b) (q ^ (3 : ℤ)) (general_doubletBlockEntries q τ root)
        (Sum.inl i) (Sum.inr (Sum.inl j)) = 0 := by
  simp [FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator]

/-- The last-but-one generator has zero support from the middle block to the first block. -/
theorem general_lastButOneGenerator_middle_left_zero
    {a b : ℕ} (q : Units ℂ) (τ root : ℂ) (i : Fin b) (j : Fin a) :
    FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator
        (a := a) (b := b) (q ^ (3 : ℤ)) (general_doubletBlockEntries q τ root)
        (Sum.inr (Sum.inl i)) (Sum.inl j) = 0 := by
  simp [FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator]

/-- The last-but-one generator has zero support from the middle block to the last block. -/
theorem general_lastButOneGenerator_middle_right_zero
    {a b : ℕ} (q : Units ℂ) (τ root : ℂ) (i : Fin b) (j : Fin a) :
    FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator
        (a := a) (b := b) (q ^ (3 : ℤ)) (general_doubletBlockEntries q τ root)
        (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr j)) = 0 := by
  simp [FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator]

/-- The last-but-one generator has zero support from the last block to the middle block. -/
theorem general_lastButOneGenerator_right_middle_zero
    {a b : ℕ} (q : Units ℂ) (τ root : ℂ) (i : Fin a) (j : Fin b) :
    FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator
        (a := a) (b := b) (q ^ (3 : ℤ)) (general_doubletBlockEntries q τ root)
        (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl j)) = 0 := by
  simp [FiniteFibonacciGeneralBraidGenerators.lastButOneGenerator]

/-- The left end generator is `b₁`. -/
theorem general_leftEndBraidIndex :
    leftEndBraidIndex = 1 := by
  change 1 = 1
  rfl

/-- The right end generator is `b_{2N+1}`. -/
theorem general_rightEndBraidIndex (N : ℕ) :
    rightEndBraidIndex N = 2 * N + 1 := by
  change 2 * N + 1 = 2 * N + 1
  rfl

/-- The even generator attached to a qubit position is `b_{2(k+1)}`. -/
theorem general_evenBraidIndex (N : ℕ) (k : Fin N) :
    evenBraidIndex k = 2 * (k.val + 1) := by
  change 2 * (k.val + 1) = 2 * (k.val + 1)
  rfl

/-- Distinct even generators are separated Artin generators. -/
theorem general_evenBraidIndex_separated_of_lt {N : ℕ} {k l : Fin N}
    (h : k.val < l.val) :
    evenBraidIndex k + 1 < evenBraidIndex l :=
  evenBraidIndex_separated_of_lt h

/-- The register-word generator indices realize the paper's left/even/right pattern. -/
theorem general_registerGeneratorIndex_left {N : ℕ} :
    registerGeneratorIndex (RegisterGenerator.left : RegisterGenerator N) = 1 :=
  registerGeneratorIndex_left

/-- The register-word generator indices realize the paper's even-generator pattern. -/
theorem general_registerGeneratorIndex_even {N : ℕ} (k : Fin (N + 1)) :
    registerGeneratorIndex (RegisterGenerator.even k : RegisterGenerator N) =
      evenBraidIndex k :=
  registerGeneratorIndex_even k

/-- The register-word generator indices realize the paper's right-end pattern. -/
theorem general_registerGeneratorIndex_right {N : ℕ} :
    registerGeneratorIndex (RegisterGenerator.right : RegisterGenerator N) =
      2 * (N + 1) + 1 :=
  registerGeneratorIndex_right

/-- Finite register-word actions are local on the computational sector. -/
theorem general_registerWordBlockAction_preserves_computational
    {N : ℕ} {NC : Type*} (r b : Bool → Bool)
    (onNonComputational : NC → NC) (w : RegisterWord N)
    {x : FiniteFibonacciComputationalSpace.FibonacciBlockLabel (N + 1) NC}
    (hx : FiniteFibonacciComputationalSpace.FibonacciBlockLabel.IsComputational x) :
    FiniteFibonacciComputationalSpace.FibonacciBlockLabel.IsComputational
      (registerWordBlockAction r b onNonComputational w x) :=
  registerWordBlockAction_preserves_computational r b onNonComputational w hx

/-- The sparse `n = 7` template is the first eight-dimensional higher-anyon example. -/
theorem general_sparse_basis7_card :
    Fintype.card FiniteFibonacciSparseLowAnyonMatrices.Basis7 = 8 :=
  sectionSix_basis7_card

/-- The sparse `n = 8` template is the first thirteen-dimensional higher-anyon example. -/
theorem general_sparse_basis8_card :
    Fintype.card FiniteFibonacciSparseLowAnyonMatrices.Basis8 = 13 :=
  sectionSix_basis8_card

end FiniteFibonacciGeneralBnPaperBridge
