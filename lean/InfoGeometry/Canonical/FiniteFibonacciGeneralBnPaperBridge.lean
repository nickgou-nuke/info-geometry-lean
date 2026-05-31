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

The determinant recurrence from the paper is represented here only as a
hypothesis-carrying schedule interface, not as a derived general matrix theorem.

No conformal blocks.
No all-`n` monodromy matrices.
No analytic continuation.
-/

namespace InfoGeometry.Canonical.FiniteFibonacciGeneralBnPaperBridge

open InfoGeometry.Canonical.FiniteFibonacciComputationalSpace
open InfoGeometry.Canonical.FiniteFibonacciHigherAnyonBraiding
open InfoGeometry.Canonical.FiniteFibonacciHigherAnyonPaperBridge
open InfoGeometry.Canonical.FiniteFibonacciRegisterWords
open InfoGeometry.Canonical.FiniteFibonacciRegisterSubgroup
open InfoGeometry.Canonical.FiniteFibonacciRegisterWords
open InfoGeometry.Canonical.FiniteFibonacciSparseLowAnyonMatrices
open InfoGeometry.Canonical.FiniteFibonacciSparseLowAnyonPaperBridge

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

/-- The left end generator is `b₁`. -/
theorem general_leftEndBraidIndex :
    leftEndBraidIndex = 1 :=
  rfl

/-- The right end generator is `b_{2N+1}`. -/
theorem general_rightEndBraidIndex (N : ℕ) :
    rightEndBraidIndex N = 2 * N + 1 :=
  rfl

/-- The even generator attached to a qubit position is `b_{2(k+1)}`. -/
theorem general_evenBraidIndex (N : ℕ) (k : Fin N) :
    evenBraidIndex k = 2 * (k.val + 1) :=
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

/--
Hypothesis-carrying determinant schedule for the paper's Section 7 recurrence.

This does not derive the determinant sequence from a general matrix family; it
packages the recurrence as a proof-carrying interface, which is the honest
boundary currently owned by the repository.
-/
structure BraidDeterminantSchedule (q : Units ℂ) where
  /-- Determinant/phase value at each stage `n`. -/
  D : ℕ → Units ℂ
  /-- Recurrence `Dₙ = Dₙ₋₂ · Dₙ₋₁` for `n ≥ 4`. -/
  step : ∀ n : ℕ, 4 ≤ n → D n = D (n - 2) * D (n - 1)
  /-- Base value `D₂ = q⁻⁴`. -/
  init_two : D 2 = q ^ (-4 : ℤ)
  /-- Base value `D₃ = q³`. -/
  init_three : D 3 = q ^ (3 : ℤ)

end InfoGeometry.Canonical.FiniteFibonacciGeneralBnPaperBridge
