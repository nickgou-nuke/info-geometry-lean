import Std
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Meta.EssenceOfInductiveProof

The kernel-level essence of inductive mathematical proof.

The content is deliberately minimal and general:

* an inductive proof is a base case plus a successor-preservation rule;
* the natural numbers are the least successor-closed system containing `0`;
* recursive constructions are uniquely determined by their seed and step;
* invariants of finite recursive trajectories are proved by the same induction;
* strong induction is derived from ordinary induction.

This file is meta-mathematical only in the harmless sense that it states the
shape of induction as Lean theorems.  It introduces no axioms and no hidden
proof fields.
-/

namespace InfoGeometry.Meta.EssenceOfInductiveProof

/-! ## Predicate induction -/

/-- A predicate is closed under successor. -/
def SuccessorClosed (P : Nat → Prop) : Prop :=
  ∀ n : Nat, P n → P (n + 1)

/-- An inductive predicate has a base point and is closed under successor. -/
def IsInductivePredicate (P : Nat → Prop) : Prop :=
  P 0 ∧ SuccessorClosed P

/-- The direct expression of ordinary induction. -/
theorem induction_essence {P : Nat → Prop}
    (h0 : P 0) (hstep : SuccessorClosed P) :
    ∀ n : Nat, P n := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => exact hstep n ih

/-- Packaged ordinary induction from an inductive-predicate hypothesis. -/
theorem IsInductivePredicate.forall {P : Nat → Prop}
    (hP : IsInductivePredicate P) :
    ∀ n : Nat, P n :=
  induction_essence hP.1 hP.2

/-! ## The least successor-closed system -/

/-- The abstract reachability predicate generated from `0` by successor. -/
inductive Reachable : Nat → Prop where
  /-- Zero is reachable. -/
  | zero : Reachable 0
  /-- Successors of reachable numbers are reachable. -/
  | succ {n : Nat} : Reachable n → Reachable (n + 1)

/-- Every natural number is reachable from `0` by finitely many successors. -/
theorem reachable_all : ∀ n : Nat, Reachable n := by
  intro n
  induction n with
  | zero => exact Reachable.zero
  | succ n ih => exact Reachable.succ ih

/-- Reachability is equivalent to the canonical lower bound on natural numbers. -/
theorem reachable_iff_zero_le (n : Nat) :
    Reachable n ↔ 0 ≤ n := by
  constructor
  · intro _
    exact Nat.zero_le n
  · intro _
    exact reachable_all n

/--
Leastness of induction: any successor-closed predicate containing `0` contains
all reachable naturals.
-/
theorem Reachable.rec_on_predicate {P : Nat → Prop}
    (h0 : P 0) (hstep : SuccessorClosed P) :
    ∀ n : Nat, Reachable n → P n := by
  intro n hn
  induction hn with
  | zero => exact h0
  | succ hn ih => exact hstep _ ih

/-- Leastness plus reachability recovers ordinary induction. -/
theorem induction_from_reachability {P : Nat → Prop}
    (h0 : P 0) (hstep : SuccessorClosed P) :
    ∀ n : Nat, P n := by
  intro n
  exact Reachable.rec_on_predicate h0 hstep n (reachable_all n)

/-! ## Dependent towers and finite-stage invariant existence -/

/--
A dependent inductive tower: a stage at each finite depth, a bonding map to the
next depth, and an invariant predicate on each stage.

This is data only.  The seed and transport proof are supplied to the theorem
below rather than hidden in the structure.
-/
structure InductiveTower where
  /-- The stage/type at depth `n`. -/
  Stage : Nat → Type
  /-- The bonding/transport map from depth `n` to depth `n + 1`. -/
  bond : ∀ n : Nat, Stage n → Stage (n + 1)
  /-- The stagewise invariant. -/
  Invariant : ∀ n : Nat, Stage n → Prop

namespace InductiveTower

/-- The element obtained by iterating the bonding maps from a seed. -/
def propagate (T : InductiveTower) (x0 : T.Stage 0) : ∀ n : Nat, T.Stage n
  | 0 => x0
  | n + 1 => T.bond n (propagate T x0 n)

@[simp]
theorem propagate_zero (T : InductiveTower) (x0 : T.Stage 0) :
    T.propagate x0 0 = x0 := by
  rfl

@[simp]
theorem propagate_succ (T : InductiveTower) (x0 : T.Stage 0) (n : Nat) :
    T.propagate x0 (n + 1) = T.bond n (T.propagate x0 n) := by
  rfl

/--
The essence theorem for dependent finite towers: a seed plus stagewise transport
constructs an invariant element at every finite depth.
-/
theorem invariant_propagate (T : InductiveTower)
    {x0 : T.Stage 0}
    (h0 : T.Invariant 0 x0)
    (htransport : ∀ n : Nat, ∀ x : T.Stage n,
      T.Invariant n x → T.Invariant (n + 1) (T.bond n x)) :
    ∀ n : Nat, T.Invariant n (T.propagate x0 n) := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih => simpa using htransport n (T.propagate x0 n) ih

/-- Existence form of the tower induction theorem. -/
theorem exists_invariant_at_depth (T : InductiveTower)
    (hseed : ∃ x0 : T.Stage 0, T.Invariant 0 x0)
    (htransport : ∀ n : Nat, ∀ x : T.Stage n,
      T.Invariant n x → T.Invariant (n + 1) (T.bond n x)) :
    ∀ depth : Nat, ∃ x : T.Stage depth, T.Invariant depth x := by
  intro depth
  rcases hseed with ⟨x0, hx0⟩
  exact ⟨T.propagate x0 depth, T.invariant_propagate hx0 htransport depth⟩

/--
Point-free form of the same theorem, matching the seed/transport shape of
ordinary induction but for dependent finite towers.
-/
theorem eternity_of_invariant (T : InductiveTower)
    (hseed : ∃ x0 : T.Stage 0, T.Invariant 0 x0)
    (htransport : ∀ n : Nat, ∀ x : T.Stage n,
      T.Invariant n x → T.Invariant (n + 1) (T.bond n x))
    (depth : Nat) :
    ∃ x : T.Stage depth, T.Invariant depth x :=
  T.exists_invariant_at_depth hseed htransport depth

end InductiveTower

/--
Name used for the architectural reading of dependent induction: a sequence of
stages, a bonding map, and a stagewise invariant.

The seed and transport proofs remain explicit theorem inputs, so this is not a
hidden proof packet.
-/
abbrev InductiveEssence := InductiveTower

/--
The named "eternity of the invariant" theorem: an invariant seed transported by
every bonding map has an invariant representative at every finite depth.
-/
theorem eternity_of_the_invariant (E : InductiveEssence)
    (seed_exists : ∃ x : E.Stage 0, E.Invariant 0 x)
    (transport : ∀ n : Nat, ∀ x : E.Stage n,
      E.Invariant n x → E.Invariant (n + 1) (E.bond n x))
    (depth : Nat) :
    ∃ x : E.Stage depth, E.Invariant depth x :=
  E.eternity_of_invariant seed_exists transport depth

/-! ## Recursive construction and uniqueness -/

/-- The finite sequence generated by a seed and a time-dependent successor step. -/
def recursiveTrajectory {X : Type} (x0 : X) (step : Nat → X → X) : Nat → X
  | 0 => x0
  | n + 1 => step n (recursiveTrajectory x0 step n)

@[simp]
theorem recursiveTrajectory_zero {X : Type} (x0 : X) (step : Nat → X → X) :
    recursiveTrajectory x0 step 0 = x0 := by
  rfl

@[simp]
theorem recursiveTrajectory_succ {X : Type} (x0 : X) (step : Nat → X → X) (n : Nat) :
    recursiveTrajectory x0 step (n + 1) = step n (recursiveTrajectory x0 step n) := by
  rfl

/-- A sequence satisfying the same seed and step equation is the recursive trajectory. -/
theorem recursiveTrajectory_unique {X : Type}
    (x0 : X) (step : Nat → X → X) (y : Nat → X)
    (hy0 : y 0 = x0)
    (hysucc : ∀ n : Nat, y (n + 1) = step n (y n)) :
    ∀ n : Nat, y n = recursiveTrajectory x0 step n := by
  intro n
  induction n with
  | zero => exact hy0
  | succ n ih =>
      rw [hysucc n, recursiveTrajectory_succ, ih]

/-- Invariants of recursive trajectories are proved by induction. -/
theorem invariant_recursiveTrajectory {X : Type}
    {I : X → Prop} {x0 : X} {step : Nat → X → X}
    (h0 : I x0)
    (hstep : ∀ n : Nat, I (recursiveTrajectory x0 step n) →
      I (step n (recursiveTrajectory x0 step n))) :
    ∀ n : Nat, I (recursiveTrajectory x0 step n) := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih => simpa using hstep n ih

/-! ## Strong induction as ordinary induction on accumulated history -/

/-- Strong induction is derivable from ordinary induction. -/
theorem strong_induction_essence {P : Nat → Prop}
    (h : ∀ n : Nat, (∀ k : Nat, k < n → P k) → P n) :
    ∀ n : Nat, P n := by
  have hist : ∀ n : Nat, ∀ k : Nat, k < n → P k := by
    intro n
    induction n with
    | zero =>
        intro k hk
        exact False.elim (Nat.not_lt_zero k hk)
    | succ m ih =>
        intro k hk
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | heq
        · exact ih k hlt
        · rw [heq]
          exact h m ih
  intro n
  exact hist (n + 1) n (Nat.lt_succ_self n)

/-! ## Finite proof transport along implications -/

/-- If an inductive proof establishes `P`, and `P` implies `Q`, then `Q` holds everywhere. -/
theorem induction_transport {P Q : Nat → Prop}
    (h0 : P 0) (hstep : SuccessorClosed P)
    (hmap : ∀ n : Nat, P n → Q n) :
    ∀ n : Nat, Q n := by
  intro n
  exact hmap n (induction_essence h0 hstep n)

/-- Two predicates proven by the same induction can be conjoined stagewise. -/
theorem induction_pair {P Q : Nat → Prop}
    (hP0 : P 0) (hPstep : SuccessorClosed P)
    (hQ0 : Q 0) (hQstep : SuccessorClosed Q) :
    ∀ n : Nat, P n ∧ Q n := by
  intro n
  exact ⟨induction_essence hP0 hPstep n, induction_essence hQ0 hQstep n⟩

end InfoGeometry.Meta.EssenceOfInductiveProof
