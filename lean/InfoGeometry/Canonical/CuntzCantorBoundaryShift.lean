import Mathlib.Tactic
import InfoGeometry.Canonical.UHFInductiveColimitBoundary

/-!
# Cuntz-Cantor Boundary Shift

This module adds the finite boundary-action layer for the binary Cuntz-style
prefix shifts on the Cantor carrier used by `UHFInductiveColimitBoundary`.

The closed layer is deliberately topological/algebraic and finite-stage:
* prepend a binary branch bit to a Cantor boundary point;
* drop the head bit with the tail map;
* prove branch injectivity, disjointness, and cover;
* prove branch pullback of a finite cylinder is again a finite cylinder.

No Hilbert-space representation, C*-completion, Cuntz partial isometry theorem,
KMS state, measure theory, or zeta/RH consequence is asserted here.

#### BUCKET 1: CLOSED FINITE THEOREMS
`tail_prependBit`, `prependBit_head`, `prependBit_injective`,
`prependBit_tail_of_head`, `prependBit_range_cover`,
`prependBit_false_true_disjoint`, `boundaryPrefix_prependBit`, and
`cylinder_branch_pullback`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
Full Cuntz `O₂` partial-isometry representation, Hilbert-space adjoints,
orthogonal range projections, KMS dynamics, and analytic/zeta interpretations.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzCantorBoundaryShift

open InfoGeometry.Canonical.UHFInductiveColimitBoundary

/-- Prepend one branch bit to an infinite Cantor boundary point. -/
def prependBit (b : Bool) (x : CantorBoundary) : CantorBoundary :=
  fun n => if n = 0 then b else x (n - 1)

/-- Drop the head bit of an infinite Cantor boundary point. -/
def tail (x : CantorBoundary) : CantorBoundary :=
  fun n => x (n + 1)

/-- Finite prefix obtained by prepending a branch bit to a word. -/
def branchPrefix (n : ℕ) (b : Bool) (w : BitWord n) : BitWord (n + 1) :=
  fun i =>
    if h : i.1 = 0 then b
    else w ⟨i.1 - 1, by omega⟩

@[simp] theorem prependBit_zero (b : Bool) (x : CantorBoundary) :
    prependBit b x 0 = b := by
  simp [prependBit]

@[simp] theorem prependBit_succ (b : Bool) (x : CantorBoundary) (n : ℕ) :
    prependBit b x (n + 1) = x n := by
  simp [prependBit]

@[simp] theorem tail_apply (x : CantorBoundary) (n : ℕ) :
    tail x n = x (n + 1) := rfl

/-- Dropping the head after prepending a branch bit recovers the old boundary. -/
theorem tail_prependBit (b : Bool) (x : CantorBoundary) :
    tail (prependBit b x) = x := by
  ext n
  simp [tail]

/-- The head of a prepended boundary is the prepended branch bit. -/
theorem prependBit_head (b : Bool) (x : CantorBoundary) :
    prependBit b x 0 = b := by
  simp

/-- Each fixed branch-prepend map is injective. -/
theorem prependBit_injective (b : Bool) :
    Function.Injective (prependBit b) := by
  intro x y hxy
  have htail := congrArg tail hxy
  simpa [tail_prependBit] using htail

/-- A boundary whose head is `b` is recovered by prepending `b` to its tail. -/
theorem prependBit_tail_of_head {x : CantorBoundary} {b : Bool} (h : x 0 = b) :
    prependBit b (tail x) = x := by
  ext n
  cases n with
  | zero =>
      simpa using h.symm
  | succ n =>
      simp [tail]

/-- The two branch maps cover the full Cantor boundary. -/
theorem prependBit_range_cover (x : CantorBoundary) :
    x ∈ Set.range (prependBit false) ∪ Set.range (prependBit true) := by
  cases hx : x 0
  · left
    exact ⟨tail x, prependBit_tail_of_head hx⟩
  · right
    exact ⟨tail x, prependBit_tail_of_head hx⟩

/-- The two branch ranges are disjoint. -/
theorem prependBit_false_true_disjoint :
    Disjoint (Set.range (prependBit false)) (Set.range (prependBit true)) := by
  rw [Set.disjoint_left]
  intro x hxFalse hxTrue
  rcases hxFalse with ⟨a, rfl⟩
  rcases hxTrue with ⟨b, h⟩
  have hhead := congrFun h 0
  simp at hhead

@[simp] theorem branchPrefix_zero (n : ℕ) (b : Bool) (w : BitWord n) :
    branchPrefix n b w ⟨0, Nat.succ_pos n⟩ = b := by
  simp [branchPrefix]

@[simp] theorem branchPrefix_succ (n : ℕ) (b : Bool) (w : BitWord n) (i : Fin n) :
    branchPrefix n b w ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ = w i := by
  simp [branchPrefix]

/-- Prefixes commute with branch prepending. -/
theorem boundaryPrefix_prependBit (n : ℕ) (b : Bool) (x : CantorBoundary) :
    boundaryPrefix (n + 1) (prependBit b x) =
      branchPrefix n b (boundaryPrefix n x) := by
  ext i
  by_cases h : i.1 = 0
  · simp [boundaryPrefix, branchPrefix, prependBit, h]
  · simp [boundaryPrefix, branchPrefix, prependBit, h]

/-- Pull back a stage `n+1` diagonal observable along a branch. -/
def branchPullback (n : ℕ) (b : Bool) (f : DiagAlg (n + 1)) : DiagAlg n :=
  fun w => f (branchPrefix n b w)

/-- Pulling a finite cylinder back along a branch is again a finite cylinder. -/
theorem cylinder_branch_pullback (n : ℕ) (b : Bool) (f : DiagAlg (n + 1)) :
    (fun x : CantorBoundary => cylinder (n + 1) f (prependBit b x)) =
      cylinder n (branchPullback n b f) := by
  ext x
  simp [cylinder, branchPullback, boundaryPrefix_prependBit]

/-- Branch pullbacks of finite cylinders remain in the finite cylinder colimit. -/
theorem branch_pullback_mem_colimit (n : ℕ) (b : Bool) (f : DiagAlg (n + 1)) :
    cylinder n (branchPullback n b f) ∈ CylinderColimit := by
  exact cylinder_mem_colimit n (branchPullback n b f)

/-- Synthesis theorem combining branch coverage and cylinder pullback coherence. -/
theorem finite_cuntz_cantor_shift_synthesis :
    Function.Injective (prependBit false) ∧
    Function.Injective (prependBit true) ∧
    Disjoint (Set.range (prependBit false)) (Set.range (prependBit true)) ∧
    (∀ x : CantorBoundary, x ∈ Set.range (prependBit false) ∪ Set.range (prependBit true)) ∧
    (∀ n : ℕ, ∀ b : Bool, ∀ f : DiagAlg (n + 1),
      (fun x : CantorBoundary => cylinder (n + 1) f (prependBit b x)) =
        cylinder n (branchPullback n b f)) ∧
    (∀ n : ℕ, ∀ b : Bool, ∀ f : DiagAlg (n + 1),
      cylinder n (branchPullback n b f) ∈ CylinderColimit) :=
  ⟨prependBit_injective false, prependBit_injective true, prependBit_false_true_disjoint,
   prependBit_range_cover, cylinder_branch_pullback, branch_pullback_mem_colimit⟩

end InfoGeometry.Canonical.CuntzCantorBoundaryShift

end noncomputable section
