import InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.FiniteFibonacciComputationalSpace

Finite computational-vector interface for Fibonacci anyons.

This file formalizes the finite combinatorial content of the computational
subspace construction for `2 * N + 2` Fibonacci anyons:

* an `N`-qubit computational vector is a bit assignment `Fin N → Bool`;
* the number of computational vectors is `2 ^ N`;
* the Fibonacci conformal-block dimension readout from the finite interface is
  `fib (2 * N + 1)`;
* the non-computational count is the complementary finite count;
* block-diagonal actions preserve the computational sector, expressing the
  finite no-leakage theorem in a theorem-owned way.

No conformal-block analysis.
No monodromy matrix construction.
No analytic continuation.
No physical fault-tolerance claim.
-/

namespace InfoGeometry.Canonical.FiniteFibonacciComputationalSpace

open FiniteFibonacciAnyonBraiding

/-- An `N`-qubit computational vector is an assignment of `N` bits. -/
abbrev ComputationalVector (N : ℕ) : Type :=
  Fin N → Bool

/-- There are exactly `2 ^ N` computational vectors. -/
theorem card_computationalVector (N : ℕ) :
    Fintype.card (ComputationalVector N) = 2 ^ N := by
  simp [ComputationalVector]

/-- The finite Fibonacci conformal-block dimension for `2 * N + 2` anyons. -/
def fibonacciBlockDimension (N : ℕ) : ℕ :=
  vacuumFusionDimension (2 * N + 2)

/-- The finite Fibonacci block dimension is `fib (2 * N + 1)`. -/
theorem fibonacciBlockDimension_eq_fib (N : ℕ) :
    fibonacciBlockDimension N = Nat.fib (2 * N + 1) :=
  vacuumFusionDimension_two_mul_add_two N

/-- The finite non-computational count as the complementary truncated count. -/
def nonComputationalCount (N : ℕ) : ℕ :=
  fibonacciBlockDimension N - 2 ^ N

/-- For one qubit, there is no non-computational state in this finite count. -/
theorem nonComputationalCount_one :
    nonComputationalCount 1 = 0 := by
  norm_num [nonComputationalCount, fibonacciBlockDimension,
    vacuumFusionDimension, Nat.fib]

/-- For two qubits, the finite non-computational count is `1`. -/
theorem nonComputationalCount_two :
    nonComputationalCount 2 = 1 := by
  norm_num [nonComputationalCount, fibonacciBlockDimension,
    vacuumFusionDimension, Nat.fib]

/-- For three qubits, the finite non-computational count is `5`. -/
theorem nonComputationalCount_three :
    nonComputationalCount 3 = 5 := by
  norm_num [nonComputationalCount, fibonacciBlockDimension,
    vacuumFusionDimension, Nat.fib]

/-- Translate a Boolean qubit label to a Fibonacci channel label. -/
def bitCharge : Bool → FibonacciCharge
  | false => FibonacciCharge.one
  | true => FibonacciCharge.eps

/-- One computational pail/rope block `(ε α ε)`. -/
def computationalBlock (b : Bool) : List FibonacciCharge :=
  [FibonacciCharge.eps, bitCharge b, FibonacciCharge.eps]

@[simp]
theorem computationalBlock_false :
    computationalBlock false =
      [FibonacciCharge.eps, FibonacciCharge.one, FibonacciCharge.eps] :=
  rfl

@[simp]
theorem computationalBlock_true :
    computationalBlock true =
      [FibonacciCharge.eps, FibonacciCharge.eps, FibonacciCharge.eps] :=
  rfl

/-- An abstract full block label split into computational and non-computational sectors. -/
inductive FibonacciBlockLabel (N : ℕ) (NC : Type*) where
  /-- Computational label, indexed by an `N`-bit vector. -/
  | computational : ComputationalVector N → FibonacciBlockLabel N NC
  /-- Non-computational label, indexed by a supplied complement type. -/
  | noncomputational : NC → FibonacciBlockLabel N NC
  deriving DecidableEq

namespace FibonacciBlockLabel

variable {N : ℕ} {NC : Type*}

/-- Predicate selecting the computational sector, with an explicit vector witness. -/
def IsComputational (x : FibonacciBlockLabel N NC) : Prop :=
  ∃ α : ComputationalVector N, x = computational α

@[simp]
theorem isComputational_computational (α : ComputationalVector N) :
    IsComputational (computational α : FibonacciBlockLabel N NC) :=
  ⟨α, rfl⟩

@[simp]
theorem not_isComputational_noncomputational (x : NC) :
    ¬ IsComputational (noncomputational x : FibonacciBlockLabel N NC) := by
  intro h
  rcases h with ⟨α, hα⟩
  cases hα

end FibonacciBlockLabel

/-- A block-diagonal action on computational plus non-computational sectors. -/
def blockDiagonalAction {N : ℕ} {NC : Type*}
    (onComputational : ComputationalVector N → ComputationalVector N)
    (onNonComputational : NC → NC) :
    FibonacciBlockLabel N NC → FibonacciBlockLabel N NC
  | FibonacciBlockLabel.computational α =>
      FibonacciBlockLabel.computational (onComputational α)
  | FibonacciBlockLabel.noncomputational x =>
      FibonacciBlockLabel.noncomputational (onNonComputational x)

/-- Block-diagonal actions preserve the computational sector: finite no leakage. -/
theorem blockDiagonalAction_preserves_computational {N : ℕ} {NC : Type*}
    (onComputational : ComputationalVector N → ComputationalVector N)
    (onNonComputational : NC → NC)
    {x : FibonacciBlockLabel N NC}
    (hx : FibonacciBlockLabel.IsComputational x) :
    FibonacciBlockLabel.IsComputational
      (blockDiagonalAction onComputational onNonComputational x) := by
  cases x with
  | computational α =>
      exact ⟨onComputational α, rfl⟩
  | noncomputational y =>
      rcases hx with ⟨α, hα⟩
      cases hα

/-- Block-diagonal actions preserve the non-computational sector as well. -/
theorem blockDiagonalAction_preserves_noncomputational {N : ℕ} {NC : Type*}
    (onComputational : ComputationalVector N → ComputationalVector N)
    (onNonComputational : NC → NC)
    (x : NC) :
    blockDiagonalAction onComputational onNonComputational
        (FibonacciBlockLabel.noncomputational x : FibonacciBlockLabel N NC) =
      FibonacciBlockLabel.noncomputational (onNonComputational x) :=
  rfl

/-- A local qubit operation modifies only one computational bit. -/
def localQubitAction {N : ℕ} (k : Fin N) (f : Bool → Bool)
    (α : ComputationalVector N) : ComputationalVector N :=
  Function.update α k (f (α k))

@[simp]
theorem localQubitAction_apply_same {N : ℕ} (k : Fin N) (f : Bool → Bool)
    (α : ComputationalVector N) :
    localQubitAction k f α k = f (α k) := by
  simp [localQubitAction]

@[simp]
theorem localQubitAction_apply_ne {N : ℕ} {k l : Fin N} (h : l ≠ k)
    (f : Bool → Bool) (α : ComputationalVector N) :
    localQubitAction k f α l = α l := by
  simp [localQubitAction, h]

/-- Local qubit operations give block-diagonal no-leakage actions. -/
def localQubitBlockAction {N : ℕ} {NC : Type*}
    (k : Fin N) (f : Bool → Bool) (onNonComputational : NC → NC) :
    FibonacciBlockLabel N NC → FibonacciBlockLabel N NC :=
  blockDiagonalAction (localQubitAction k f) onNonComputational

/-- Local qubit actions preserve the computational sector. -/
theorem localQubitBlockAction_preserves_computational {N : ℕ} {NC : Type*}
    (k : Fin N) (f : Bool → Bool) (onNonComputational : NC → NC)
    {x : FibonacciBlockLabel N NC}
    (hx : FibonacciBlockLabel.IsComputational x) :
    FibonacciBlockLabel.IsComputational
      (localQubitBlockAction k f onNonComputational x) :=
  blockDiagonalAction_preserves_computational
    (localQubitAction k f) onNonComputational hx

end InfoGeometry.Canonical.FiniteFibonacciComputationalSpace
