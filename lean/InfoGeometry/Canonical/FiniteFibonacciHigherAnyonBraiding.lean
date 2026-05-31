import InfoGeometry.Canonical.FiniteFibonacciElectronIndependence

/-!
# InfoGeometry.Canonical.FiniteFibonacciHigherAnyonBraiding

Finite higher-anyon braid-block interface for Fibonacci anyons.

Section 5 of the paper describes a recursive basis of `n`-point Fibonacci
conformal blocks by admissible Bratteli paths: the internal labels are `0/1`,
and no two zero labels occur consecutively.  Locally, a braid generator sees a
triple of adjacent sector labels.  The Fibonacci fusion rule forces singlets
when one endpoint of the triple is `0`, and a two-dimensional `B = F R F` block
when both endpoints are `1`.

This file formalizes only that finite combinatorial/algebraic skeleton:

* finite admissible `0/1` path codes with no consecutive zeros;
* the Fibonacci recurrence shape for recursively generated basis codes;
* local triple admissibility and the singlet/doublet classification;
* the higher-anyon local braid block uses the same finite `R`, `F`, and `B`
  readouts already proved for four anyons, hence is independent of electron
  triples by the previous interface.

No conformal-block construction.
No analytic continuation.
No recursive monodromy matrices.
No proof of Artin relations for all `n`.
-/

namespace InfoGeometry.Canonical.FiniteFibonacciHigherAnyonBraiding

open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
open InfoGeometry.Canonical.FiniteFibonacciElectronIndependence

/-- Sector labels: `false` is `[0]`, `true` is `[1]`. -/
abbrev SectorLabel := Bool

/-- Adjacent labels are admissible exactly when they are not both `0`. -/
def AdjacentAdmissible (a b : SectorLabel) : Prop :=
  a = true ∨ b = true

/-- A finite internal Bratteli label path has no consecutive zero labels. -/
def NoConsecutiveZero {m : ℕ} (α : Fin m → SectorLabel) : Prop :=
  ∀ (i : Fin m) (hnext : i.val + 1 < m),
    α i = false → α ⟨i.val + 1, hnext⟩ = true

/-- Finite path code for the internal labels of an `n`-anyon Fibonacci block. -/
def FibonacciPathCode (m : ℕ) : Type :=
  { α : Fin m → SectorLabel // NoConsecutiveZero α }

/-- The path after a zero label must have a one label. -/
theorem next_eq_true_of_current_eq_false {m : ℕ} {α : Fin m → SectorLabel}
    (hα : NoConsecutiveZero α) (i : Fin m) (hnext : i.val + 1 < m)
    (hi : α i = false) :
    α ⟨i.val + 1, hnext⟩ = true :=
  hα i hnext hi

/-- Recursive finite basis-code type with Fibonacci direct-sum shape. -/
def RecursiveFibonacciBlockBasis : ℕ → Type
  | 0 => PUnit
  | 1 => PUnit
  | k + 2 => RecursiveFibonacciBlockBasis k ⊕ RecursiveFibonacciBlockBasis (k + 1)

/-- Recursive Fibonacci dimension counter with `d₀ = d₁ = 1`. -/
def recursiveFibonacciDimension : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | k + 2 => recursiveFibonacciDimension k + recursiveFibonacciDimension (k + 1)

/-- The recursive basis has the direct-sum shape `Vₖ₊₂ = Vₖ ⊕ Vₖ₊₁`. -/
theorem recursiveBasis_step (k : ℕ) :
    RecursiveFibonacciBlockBasis (k + 2) =
      (RecursiveFibonacciBlockBasis k ⊕ RecursiveFibonacciBlockBasis (k + 1)) :=
  rfl

/-- The recursive dimension counter satisfies the Fibonacci recurrence. -/
theorem recursiveFibonacciDimension_step (k : ℕ) :
    recursiveFibonacciDimension (k + 2) =
      recursiveFibonacciDimension k + recursiveFibonacciDimension (k + 1) :=
  rfl

instance recursiveFibonacciBlockBasisFintype :
    ∀ n : ℕ, Fintype (RecursiveFibonacciBlockBasis n)
  | 0 => by
      simpa [RecursiveFibonacciBlockBasis] using (inferInstance : Fintype PUnit)
  | 1 => by
      simpa [RecursiveFibonacciBlockBasis] using (inferInstance : Fintype PUnit)
  | k + 2 => by
      letI := recursiveFibonacciBlockBasisFintype k
      letI := recursiveFibonacciBlockBasisFintype (k + 1)
      simpa [RecursiveFibonacciBlockBasis] using
        (inferInstance : Fintype (RecursiveFibonacciBlockBasis k ⊕ RecursiveFibonacciBlockBasis (k + 1)))

/-- The recursive basis type has exactly the recursive Fibonacci cardinality. -/
theorem recursiveFibonacciBlockBasis_card :
    ∀ n : ℕ,
      Fintype.card (RecursiveFibonacciBlockBasis n) = recursiveFibonacciDimension n
  | 0 => by
      letI := recursiveFibonacciBlockBasisFintype 0
      simp [RecursiveFibonacciBlockBasis, recursiveFibonacciDimension]
  | 1 => by
      letI := recursiveFibonacciBlockBasisFintype 1
      simp [RecursiveFibonacciBlockBasis, recursiveFibonacciDimension]
  | k + 2 => by
      letI := recursiveFibonacciBlockBasisFintype k
      letI := recursiveFibonacciBlockBasisFintype (k + 1)
      letI := recursiveFibonacciBlockBasisFintype (k + 2)
      simp [RecursiveFibonacciBlockBasis, recursiveFibonacciDimension,
        recursiveFibonacciBlockBasis_card k, recursiveFibonacciBlockBasis_card (k + 1)]

/-- The recursive dimension counter is the shifted Fibonacci sequence `fib (n + 1)`. -/
theorem recursiveFibonacciDimension_eq_fib_succ :
    ∀ n : ℕ, recursiveFibonacciDimension n = Nat.fib (n + 1)
  | 0 => by simp [recursiveFibonacciDimension]
  | 1 => by simp [recursiveFibonacciDimension]
  | k + 2 => by
      calc
        recursiveFibonacciDimension (k + 2)
            = recursiveFibonacciDimension k + recursiveFibonacciDimension (k + 1) := by
                rfl
        _ = Nat.fib (k + 1) + Nat.fib (k + 2) := by
              rw [recursiveFibonacciDimension_eq_fib_succ k,
                recursiveFibonacciDimension_eq_fib_succ (k + 1)]
        _ = Nat.fib (k + 3) := by
              symm
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                (Nat.fib_add_two (n := k + 1))

/-- Local admissibility for a braid generator seeing a triple of sector labels. -/
def TripleAdmissible (left middle right : SectorLabel) : Prop :=
  AdjacentAdmissible left middle ∧ AdjacentAdmissible middle right

/-- If the left endpoint is `0`, local admissibility forces the middle label to be `1`. -/
theorem middle_eq_true_of_left_zero {middle right : SectorLabel}
    (h : TripleAdmissible false middle right) :
    middle = true := by
  rcases h.1 with hleft | hmid
  · contradiction
  · exact hmid

/-- If the right endpoint is `0`, local admissibility forces the middle label to be `1`. -/
theorem middle_eq_true_of_right_zero {left middle : SectorLabel}
    (h : TripleAdmissible left middle false) :
    middle = true := by
  rcases h.2 with hmid | hright
  · exact hmid
  · contradiction

/-- The finite local braid block type predicted by Fibonacci fusion. -/
inductive LocalBraidBlockKind where
  /-- Singlet with endpoint/vacuum-channel phase `q⁻⁴`, corresponding to `010`. -/
  | singletQNegFour
  /-- Singlet with Fibonacci-channel phase `q³`, corresponding to `011` or `110`. -/
  | singletQThree
  /-- Two-dimensional block `B = F R F`, corresponding to endpoint pattern `1 _ 1`. -/
  | doubletB
  deriving DecidableEq, Repr

/-- Local braid-block classification for admissible triples. -/
def localBraidBlockKind (left middle right : SectorLabel) : LocalBraidBlockKind :=
  match left, middle, right with
  | false, true, false => LocalBraidBlockKind.singletQNegFour
  | false, true, true => LocalBraidBlockKind.singletQThree
  | true, true, false => LocalBraidBlockKind.singletQThree
  | true, _, true => LocalBraidBlockKind.doubletB
  | false, false, _ => LocalBraidBlockKind.singletQNegFour
  | true, false, false => LocalBraidBlockKind.singletQThree

@[simp]
theorem localBraidBlockKind_010 :
    localBraidBlockKind false true false = LocalBraidBlockKind.singletQNegFour :=
  rfl

@[simp]
theorem localBraidBlockKind_011 :
    localBraidBlockKind false true true = LocalBraidBlockKind.singletQThree :=
  rfl

@[simp]
theorem localBraidBlockKind_110 :
    localBraidBlockKind true true false = LocalBraidBlockKind.singletQThree :=
  rfl

@[simp]
theorem localBraidBlockKind_101 :
    localBraidBlockKind true false true = LocalBraidBlockKind.doubletB :=
  rfl

@[simp]
theorem localBraidBlockKind_111 :
    localBraidBlockKind true true true = LocalBraidBlockKind.doubletB :=
  rfl

/-- Any locally admissible triple with both endpoints `0` is the `010` singlet. -/
theorem localBraidBlockKind_of_zero_zero
    {middle : SectorLabel} (h : TripleAdmissible false middle false) :
    localBraidBlockKind false middle false = LocalBraidBlockKind.singletQNegFour := by
  have hm : middle = true := middle_eq_true_of_left_zero h
  cases hm
  rfl

/-- Any locally admissible triple with left endpoint `0` and right endpoint `1` is `011`. -/
theorem localBraidBlockKind_of_zero_one
    {middle : SectorLabel} (h : TripleAdmissible false middle true) :
    localBraidBlockKind false middle true = LocalBraidBlockKind.singletQThree := by
  have hm : middle = true := middle_eq_true_of_left_zero h
  cases hm
  rfl

/-- Any locally admissible triple with left endpoint `1` and right endpoint `0` is `110`. -/
theorem localBraidBlockKind_of_one_zero
    {middle : SectorLabel} (h : TripleAdmissible true middle false) :
    localBraidBlockKind true middle false = LocalBraidBlockKind.singletQThree := by
  have hm : middle = true := middle_eq_true_of_right_zero h
  cases hm
  rfl

/-- Any locally admissible triple with both endpoints `1` is a two-dimensional `B` block. -/
theorem localBraidBlockKind_of_one_one (middle : SectorLabel) :
    localBraidBlockKind true middle true = LocalBraidBlockKind.doubletB := by
  cases middle <;> rfl

/-- Scalar phase attached to a singlet local braid block. -/
def localSingletPhase (q : Units ℂ) : LocalBraidBlockKind → Option (Units ℂ)
  | LocalBraidBlockKind.singletQNegFour => some (q ^ (-4 : ℤ))
  | LocalBraidBlockKind.singletQThree => some (q ^ (3 : ℤ))
  | LocalBraidBlockKind.doubletB => none

/-- Matrix readout attached to a doublet local braid block. -/
noncomputable def localDoubletMatrix (q : Units ℂ) (τ root : ℂ) :
    LocalBraidBlockKind → Option (Matrix ChannelIndex ChannelIndex ℂ)
  | LocalBraidBlockKind.singletQNegFour => none
  | LocalBraidBlockKind.singletQThree => none
  | LocalBraidBlockKind.doubletB => some (fibonacciBMatrix q τ root)

/-- The local doublet readout is exactly the four-anyon `B = F R F` matrix. -/
theorem localDoubletMatrix_doublet (q : Units ℂ) (τ root : ℂ) :
    localDoubletMatrix q τ root LocalBraidBlockKind.doubletB =
      some (fibonacciFusionMatrix τ root * fibonacciRMatrix q * fibonacciFusionMatrix τ root) :=
  rfl

/-- Electron triples do not affect the local doublet braid block. -/
theorem localDoubletMatrix_independent_of_r
    (r s : ℕ) (q : Units ℂ) (τ root : ℂ) :
    (some (fibonacciBMatrixWithElectrons r q τ root) :
        Option (Matrix ChannelIndex ChannelIndex ℂ)) =
      some (fibonacciBMatrixWithElectrons s q τ root) := by
  rw [fibonacciBMatrixWithElectrons_independent_of_r]

end InfoGeometry.Canonical.FiniteFibonacciHigherAnyonBraiding
