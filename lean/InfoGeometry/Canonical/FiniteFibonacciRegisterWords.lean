import InfoGeometry.Canonical.FiniteFibonacciRegisterSubgroup
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.FiniteFibonacciRegisterWords

Finite words in the Fibonacci register subgroup.

This file gives a finite, theorem-owned version of the register-subgroup action
on the computational sector.  For `N + 1` qubits, the allowed generators are:

* the left end generator, acting on qubit `0`;
* one even/middle generator for each qubit position;
* the right end generator, acting on the last qubit `N`.

The actual one-qubit maps are supplied explicitly as Boolean functions.  This is
only a finite combinatorial interface for block-diagonal no-leakage actions.

No concrete Fibonacci `R` or `B` matrix.
No conformal-block monodromy construction.
No analytic continuation theorem.
No universality or fault-tolerance claim.
-/

namespace InfoGeometry.Canonical.FiniteFibonacciRegisterWords

open FiniteFibonacciComputationalSpace
open FiniteFibonacciRegisterSubgroup

/-- Register-subgroup generators for `N + 1` qubits. -/
inductive RegisterGenerator (N : ℕ) where
  /-- Left end generator, acting on the first qubit. -/
  | left
  /-- Even generator assigned to a qubit position. -/
  | even : Fin (N + 1) → RegisterGenerator N
  /-- Right end generator, acting on the last qubit. -/
  | right
  deriving DecidableEq, Repr

/-- The first qubit position in an `N + 1` qubit register. -/
def firstQubit (N : ℕ) : Fin (N + 1) :=
  ⟨0, Nat.succ_pos N⟩

/-- The last qubit position in an `N + 1` qubit register. -/
def lastQubit (N : ℕ) : Fin (N + 1) :=
  ⟨N, Nat.lt_succ_self N⟩

/--
The Artin generator index represented by a register generator.
This records the paper's `b₁`, `b_{2i}`, `b_{2N+1}` pattern at the finite level.
-/
def registerGeneratorIndex {N : ℕ} : RegisterGenerator N → ℕ
  | RegisterGenerator.left => leftEndBraidIndex
  | RegisterGenerator.even k => evenBraidIndex k
  | RegisterGenerator.right => rightEndBraidIndex (N + 1)

@[simp]
theorem registerGeneratorIndex_left {N : ℕ} :
    registerGeneratorIndex (RegisterGenerator.left : RegisterGenerator N) = 1 :=
  rfl

@[simp]
theorem registerGeneratorIndex_even {N : ℕ} (k : Fin (N + 1)) :
    registerGeneratorIndex (RegisterGenerator.even k : RegisterGenerator N) =
      evenBraidIndex k :=
  rfl

@[simp]
theorem registerGeneratorIndex_right {N : ℕ} :
    registerGeneratorIndex (RegisterGenerator.right : RegisterGenerator N) =
      2 * (N + 1) + 1 :=
  rfl

/-- A finite word in register-subgroup generators. -/
abbrev RegisterWord (N : ℕ) := List (RegisterGenerator N)

/--
Computational action of a single register generator, parameterized by supplied
one-qubit maps for end (`r`) and even/middle (`b`) generators.
-/
def registerGeneratorComputationalAction {N : ℕ}
    (r b : Bool → Bool) :
    RegisterGenerator N → ComputationalVector (N + 1) → ComputationalVector (N + 1)
  | RegisterGenerator.left => localQubitAction (firstQubit N) r
  | RegisterGenerator.even k => localQubitAction k b
  | RegisterGenerator.right => localQubitAction (lastQubit N) r

/-- Evaluate a finite register word on computational vectors. -/
def registerWordComputationalAction {N : ℕ} (r b : Bool → Bool) :
    RegisterWord N → ComputationalVector (N + 1) → ComputationalVector (N + 1)
  | [], α => α
  | g :: w, α => registerGeneratorComputationalAction r b g
      (registerWordComputationalAction r b w α)

@[simp]
theorem registerWordComputationalAction_nil {N : ℕ} (r b : Bool → Bool)
    (α : ComputationalVector (N + 1)) :
    registerWordComputationalAction r b ([] : RegisterWord N) α = α :=
  rfl

@[simp]
theorem registerWordComputationalAction_cons {N : ℕ} (r b : Bool → Bool)
    (g : RegisterGenerator N) (w : RegisterWord N) (α : ComputationalVector (N + 1)) :
    registerWordComputationalAction r b (g :: w) α =
      registerGeneratorComputationalAction r b g
        (registerWordComputationalAction r b w α) :=
  rfl

/-- Register-word evaluation sends append to composition of finite actions. -/
theorem registerWordComputationalAction_append {N : ℕ} (r b : Bool → Bool)
    (u v : RegisterWord N) (α : ComputationalVector (N + 1)) :
    registerWordComputationalAction r b (u ++ v) α =
      registerWordComputationalAction r b u
        (registerWordComputationalAction r b v α) := by
  induction u with
  | nil => rfl
  | cons g u ih => simp [ih]

/-- The left generator changes only the first qubit. -/
theorem registerGeneratorComputationalAction_left_apply_first {N : ℕ}
    (r b : Bool → Bool) (α : ComputationalVector (N + 1)) :
    registerGeneratorComputationalAction r b RegisterGenerator.left α (firstQubit N) =
      r (α (firstQubit N)) := by
  simp [registerGeneratorComputationalAction, firstQubit]

/-- The right generator changes only the last qubit. -/
theorem registerGeneratorComputationalAction_right_apply_last {N : ℕ}
    (r b : Bool → Bool) (α : ComputationalVector (N + 1)) :
    registerGeneratorComputationalAction r b RegisterGenerator.right α (lastQubit N) =
      r (α (lastQubit N)) := by
  simp [registerGeneratorComputationalAction, lastQubit]

/-- An even generator changes only its assigned qubit. -/
theorem registerGeneratorComputationalAction_even_apply_same {N : ℕ}
    (r b : Bool → Bool) (k : Fin (N + 1)) (α : ComputationalVector (N + 1)) :
    registerGeneratorComputationalAction r b (RegisterGenerator.even k) α k = b (α k) := by
  simp [registerGeneratorComputationalAction]

/-- An even generator leaves all other qubits unchanged. -/
theorem registerGeneratorComputationalAction_even_apply_ne {N : ℕ}
    (r b : Bool → Bool) {k l : Fin (N + 1)} (h : l ≠ k)
    (α : ComputationalVector (N + 1)) :
    registerGeneratorComputationalAction r b (RegisterGenerator.even k) α l = α l := by
  simp [registerGeneratorComputationalAction, h]

/-- Block action induced by a register word, with an arbitrary NC-sector action. -/
def registerWordBlockAction {N : ℕ} {NC : Type*}
    (r b : Bool → Bool) (onNonComputational : NC → NC) (w : RegisterWord N) :
    FibonacciBlockLabel (N + 1) NC → FibonacciBlockLabel (N + 1) NC :=
  blockDiagonalAction (registerWordComputationalAction r b w) onNonComputational

/-- Register-word block actions preserve the computational sector: finite no leakage. -/
theorem registerWordBlockAction_preserves_computational {N : ℕ} {NC : Type*}
    (r b : Bool → Bool) (onNonComputational : NC → NC) (w : RegisterWord N)
    {x : FibonacciBlockLabel (N + 1) NC}
    (hx : FibonacciBlockLabel.IsComputational x) :
    FibonacciBlockLabel.IsComputational
      (registerWordBlockAction r b onNonComputational w x) :=
  blockDiagonalAction_preserves_computational
    (registerWordComputationalAction r b w) onNonComputational hx

/-- The empty register word acts as the identity on computational vectors. -/
theorem registerWordComputationalAction_empty_eq_id {N : ℕ} (r b : Bool → Bool) :
    registerWordComputationalAction r b ([] : RegisterWord N) =
      (id : ComputationalVector (N + 1) → ComputationalVector (N + 1)) := by
  funext α
  rfl

end InfoGeometry.Canonical.FiniteFibonacciRegisterWords
