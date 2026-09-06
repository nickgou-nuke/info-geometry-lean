import Mathlib.Tactic
import InfoGeometry.Meta.EssenceOfInductiveProof
import InfoGeometry.Canonical.CategoricalRecursiveClosureBridge
import InfoGeometry.Canonical.AFRecursiveLimitBridge

/-!
# InfoGeometry.Meta.InductionHandbook

Small theorem-checked handbook of induction patterns used in this repository.

It includes:

* ordinary structural induction on `Nat` and `List`;
* induction with `generalizing`;
* strong induction via `Nat.strong_induction_on`;
* categorical/direct-limit trajectory induction (`coneTrajectory`,
  `stageTrajectory`).
-/

namespace InfoGeometry.Meta.InductionHandbook

/-! ## 1. Structural induction -/

@[simp] theorem add_zero_right (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp

@[simp] theorem append_nil {α : Type} (xs : List α) : xs ++ [] = xs := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
      simp

/-! ## 2. `generalizing` pattern -/

@[simp] theorem add_assoc_via_generalizing (n m k : Nat) : (n + m) + k = n + (m + k) := by
  induction n generalizing m k with
  | zero => simp
  | succ n ih => simp [Nat.add_assoc]

/-! ## 3. Strong induction pattern -/

theorem strong_induction_example (n : Nat) :
    ∀ m < n + 1, m ≤ n := by
  refine Nat.strong_induction_on n ?_
  intro n ih m hm
  exact Nat.le_of_lt_succ hm

/-! ## 4. Recursors: `Nat.rec` / `List.rec` / custom inductive recursor -/

theorem add_zero_right_rec (n : Nat) : n + 0 = n := by
  refine Nat.rec (motive := fun t => t + 0 = t) ?h0 ?hs n
  · rfl
  · intro k hk
    simp

theorem append_nil_rec {α : Type} (xs : List α) : xs ++ [] = xs := by
  refine List.rec (motive := fun ys : List α => ys ++ [] = ys) ?hnil ?hcons xs
  · rfl
  · intro a as ih
    simp

/-- A tiny custom inductive tree for recursor examples. -/
inductive BinTree (α : Type)
  | leaf
  | node (left : BinTree α) (val : α) (right : BinTree α)
deriving Repr

namespace BinTree

/-- Structural recursive size. -/
def size {α : Type} : BinTree α → Nat
  | .leaf => 0
  | .node l _ r => size l + 1 + size r

@[simp] theorem size_leaf {α : Type} : size (leaf : BinTree α) = 0 := rfl

@[simp] theorem size_node {α : Type} (l r : BinTree α) (a : α) :
    size (node l a r) = size l + 1 + size r := rfl

/-- The structural definition agrees with the explicit generated recursor formula. -/
@[simp] theorem size_eq_rec {α : Type} (t : BinTree α) :
    size t =
      BinTree.rec (motive := fun _ => Nat)
        0
        (fun _ _ _ sl sr => sl + 1 + sr)
        t := by
  induction t with
  | leaf => rfl
  | node l a r ihl ihr =>
      simp [size, ihl, ihr]

end BinTree

/-! ## 5. `termination_by` for explicit recursive definitions -/

/-- Explicitly-terminated recursion by decreasing natural argument. -/
def sumDown : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumDown n
termination_by n => n

@[simp] theorem sumDown_zero : sumDown 0 = 0 := by
  simp [sumDown]

@[simp] theorem sumDown_succ (n : Nat) : sumDown (n + 1) = (n + 1) + sumDown n := by
  simp [sumDown]

theorem le_sumDown (n : Nat) : n ≤ sumDown n := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp [sumDown_succ]

/-! ## 6. Mutual recursion examples -/

mutual
  /-- Evenness predicate by mutual recursion. -/
  def isEven : Nat → Bool
    | 0 => true
    | n + 1 => isOdd n

  /-- Oddness predicate by mutual recursion. -/
  def isOdd : Nat → Bool
    | 0 => false
    | n + 1 => isEven n
end

@[simp] theorem isEven_zero : isEven 0 = true := rfl
@[simp] theorem isOdd_zero : isOdd 0 = false := rfl
@[simp] theorem isEven_succ (n : Nat) : isEven (n + 1) = isOdd n := rfl
@[simp] theorem isOdd_succ (n : Nat) : isOdd (n + 1) = isEven n := rfl

/-! ## 7. Match-driven recursion + equation lemmas -/

/-- Countdown list `[n, n-1, ..., 1]` (empty at `0`). -/
def descend : Nat → List Nat
  | 0 => []
  | n + 1 => (n + 1) :: descend n

@[simp] theorem descend_zero : descend 0 = [] := rfl
@[simp] theorem descend_succ (n : Nat) : descend (n + 1) = (n + 1) :: descend n := rfl

@[simp] theorem length_descend (n : Nat) : (descend n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [descend, ih]

/-! ## 8. `casesOn` / `recOn` / explicit motives / no-confusion -/

/-- `Nat.recOn` version of the right-zero law. -/
theorem add_zero_right_recOn (n : Nat) : n + 0 = n := by
  refine Nat.recOn n ?h0 ?hs
  · rfl
  · intro k hk
    simp

/-- `List.casesOn` as explicit case split. -/
theorem append_nil_casesOn {α : Type} (xs : List α) : xs ++ [] = xs := by
  refine List.casesOn xs ?hnil ?hcons
  · rfl
  · intro a as
    simp

/-- Dependent motive with `Nat.rec` (a dependent family `Fin n → Nat`). -/
def zeroVec : (n : Nat) → Fin n → Nat := by
  intro n
  refine Nat.rec (motive := fun k => Fin k → Nat) ?h0 ?hs n
  · intro i
    exact False.elim (Nat.not_lt_zero _ i.isLt)
  · intro k ih i
    by_cases h : i.1 < k
    · exact ih ⟨i.1, h⟩
    · exact 0

/-- Head constructor is never equal to `[]` (no-confusion style). -/
theorem cons_ne_nil {α : Type} (a : α) (as : List α) : a :: as ≠ [] := by
  intro h
  cases h

/-- Constructor injectivity (left component). -/
theorem cons_injective_left {α : Type} {a b : α} {as bs : List α}
    (h : a :: as = b :: bs) : a = b := by
  cases h
  rfl

/-- Constructor injectivity (right component). -/
theorem cons_injective_right {α : Type} {a b : α} {as bs : List α}
    (h : a :: as = b :: bs) : as = bs := by
  cases h
  rfl

/-- Custom inductive no-confusion: `node` is never `leaf`. -/
theorem BinTree.node_ne_leaf {α : Type}
    (l r : BinTree α) (a : α) : BinTree.node l a r ≠ BinTree.leaf := by
  intro h
  cases h

/-! ## 9. Strategy patterns: strengthen statement / helper lemma first -/

/--
Strengthened statement for list reverse over append.

This is the standard "generalize first" move: proving `reverse (xs ++ ys)`
requires an induction property polymorphic in `ys`.
-/
theorem reverse_append_demo {α : Type} (xs ys : List α) :
    (xs ++ ys).reverse = ys.reverse ++ xs.reverse := by
  induction xs generalizing ys with
  | nil =>
      simp
  | cons x xs ih =>
      simp [List.cons_append, ih, List.append_assoc]

/--
Target theorem obtained from the strengthened helper.
-/
theorem reverse_reverse_demo {α : Type} (xs : List α) :
    xs.reverse.reverse = xs := by
  exact List.reverse_reverse xs

/--
Another helper-lemma pattern: prove a transport lemma, then instantiate.
-/
theorem map_comp_demo {α β γ : Type} (f : β → γ) (g : α → β) (xs : List α) :
    xs.map (fun x => f (g x)) = (xs.map g).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      exact congrArg (List.cons (f (g x))) ih

theorem map_id_demo {α : Type} (xs : List α) :
    xs.map (fun x => x) = xs := by
  simp

/-! ## 10. Proof decomposition and contradiction patterns (CS2800-style) -/

theorem and_comm_demo (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro h
    rcases h with ⟨hP, hQ⟩
    exact ⟨hQ, hP⟩
  · intro h
    rcases h with ⟨hQ, hP⟩
    exact ⟨hP, hQ⟩

theorem exists_succ_nat (n : Nat) : ∃ m : Nat, m = n + 1 := by
  exact ⟨n + 1, rfl⟩

theorem succ_positive_forward (n : Nat) : 0 < n + 1 := by
  have h : n + 1 = Nat.succ n := by simp [Nat.succ_eq_add_one]
  rw [h]
  exact Nat.succ_pos n

theorem succ_positive_suffices (n : Nat) : 0 < n + 1 := by
  simp

theorem not_lt_zero_demo (n : Nat) : ¬ n < 0 := by
  intro h
  exact Nat.not_lt_zero n h

theorem ne_of_lt_demo {a b : Nat} (h : a < b) : a ≠ b := by
  by_contra hEq
  simp [hEq] at h

theorem impossible_lt_self (n : Nat) (h : n < n) : False := by
  exact False.elim (Nat.lt_irrefl n h)

/-! ## 11. Relation/closure patterns (L22-style) -/

/-- Small-step relation on naturals: either stay or increment by one. -/
inductive StepRel : Nat → Nat → Prop where
  | refl (n : Nat) : StepRel n n
  | succ (n : Nat) : StepRel n (n + 1)

/-- Reflexive closure is explicit in `StepRel`. -/
@[simp] theorem StepRel.refl' (n : Nat) : StepRel n n :=
  StepRel.refl n

/-- One-step successor is explicit in `StepRel`. -/
@[simp] theorem StepRel.succ' (n : Nat) : StepRel n (n + 1) :=
  StepRel.succ n

/-- Symmetry fails for `StepRel` in general (counterexample at `0,1`). -/
theorem StepRel.not_symmetric : ¬ (∀ a b, StepRel a b → StepRel b a) := by
  intro hsymm
  have h01 : StepRel 0 1 := StepRel.succ 0
  have h10 : StepRel 1 0 := hsymm 0 1 h01
  cases h10

/-- A clean finite-step reachability relation. -/
inductive Reach : Nat → Nat → Prop where
  | refl (n : Nat) : Reach n n
  | tail {a b : Nat} : Reach a b → Reach a (b + 1)

namespace Reach

/-- Reachability is reflexive. -/
@[simp] theorem refl' (n : Nat) : Reach n n := Reach.refl n

/-- Reachability is transitive. -/
theorem trans {a b c : Nat} (hab : Reach a b) (hbc : Reach b c) : Reach a c := by
  induction hbc with
  | refl => simpa using hab
  | tail h ih =>
      exact Reach.tail ih

/-- Reachability exactly means `a ≤ b`. -/
theorem iff_le {a b : Nat} : Reach a b ↔ a ≤ b := by
  constructor
  · intro h
    induction h with
    | refl => exact Nat.le_refl _
    | tail h ih => exact Nat.le_trans ih (Nat.le_succ _)
  · intro h
    induction h with
    | refl => exact Reach.refl a
    | @step b hb ih =>
        have : Reach a (b + 1) := Reach.tail ih
        simp [Nat.succ_eq_add_one] at this ⊢
        exact this

/-- Induction on derivations: any `Reach a b` gives monotonicity of all predicates stable under `+1`. -/
theorem induction_on_derivation
    (P : Nat → Prop)
    (hbase : ∀ n, P n)
    (hstep : ∀ n, P n → P (n + 1))
    {a b : Nat} (h : Reach a b) :
    P b := by
  induction h with
  | refl => exact hbase _
  | tail h ih => exact hstep _ ih

end Reach

/-! ## 12. Invariant/spec patterns (L28-style) -/

/-- Execute `k` unit ticks from initial state `s`. -/
def runTicks : Nat → Nat → Nat
  | 0, s => s
  | k + 1, s => runTicks k s + 1
termination_by k _ => k

@[simp] theorem runTicks_zero (s : Nat) : runTicks 0 s = s := by
  simp [runTicks]

@[simp] theorem runTicks_succ (k s : Nat) : runTicks (k + 1) s = runTicks k s + 1 := by
  simp [runTicks]

/-- Closed-form semantics (`implementation = spec`). -/
theorem runTicks_eq_add (k s : Nat) : runTicks k s = s + k := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
      simp [ih, Nat.add_left_comm, Nat.add_comm]

/-- Safety invariant: state never decreases under ticks. -/
theorem runTicks_monotone (k s : Nat) : s ≤ runTicks k s := by
  simp [runTicks_eq_add]

/-- Relational semantics for finite tick execution. -/
inductive TickClosure : Nat → Nat → Prop where
  | refl (s : Nat) : TickClosure s s
  | tick {a b : Nat} : TickClosure a b → TickClosure a (b + 1)

namespace TickClosure

/-- Every execution of `runTicks` is admitted by the relational semantics. -/
theorem sound (s k : Nat) : TickClosure s (runTicks k s) := by
  induction k generalizing s with
  | zero =>
      simpa [runTicks_zero] using TickClosure.refl s
  | succ k ih =>
      simpa [runTicks_succ] using TickClosure.tick (ih s)

/-- Every relational run has a finite fuel property in `runTicks`. -/
theorem complete {s t : Nat} (h : TickClosure s t) : ∃ k : Nat, runTicks k s = t := by
  induction h with
  | refl =>
      exact ⟨0, by simp [runTicks_zero]⟩
  | tick h ih =>
      rcases ih with ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      simp [runTicks_succ, hk]

/-- Relational and functional semantics coincide. -/
theorem iff_exists_runTicks {s t : Nat} : TickClosure s t ↔ ∃ k : Nat, runTicks k s = t := by
  constructor
  · exact complete
  · intro h
    rcases h with ⟨k, hk⟩
    simpa [hk] using sound s k

/-- Invariant transfer through relational derivations. -/
theorem lower_bound {s t : Nat} (h : TickClosure s t) : s ≤ t := by
  rcases complete h with ⟨k, hk⟩
  calc
    s ≤ s + k := Nat.le_add_right s k
    _ = runTicks k s := by symm; exact runTicks_eq_add k s
    _ = t := hk

/-- Case decomposition of a derivation (`refl` vs final `tick`). -/
theorem cases_last_step {s t : Nat} (h : TickClosure s t) :
    s = t ∨ ∃ u : Nat, t = u + 1 ∧ TickClosure s u := by
  cases h with
  | refl =>
      exact Or.inl rfl
  | tick hprev =>
      exact Or.inr ⟨_, rfl, hprev⟩

end TickClosure

/-! ## 13. Extending inductive types (conservative embedding pattern) -/

/-- Base arithmetic syntax (literals + addition). -/
inductive Arith where
  | lit : Nat → Arith
  | add : Arith → Arith → Arith
deriving Repr

namespace Arith

/-- Base evaluator. -/
def eval : Arith → Nat
  | .lit n => n
  | .add x y => eval x + eval y

end Arith

/-- Extended arithmetic syntax (adds multiplication). -/
inductive ArithExt where
  | lit : Nat → ArithExt
  | add : ArithExt → ArithExt → ArithExt
  | mul : ArithExt → ArithExt → ArithExt
deriving Repr

namespace ArithExt

/-- Extended evaluator. -/
def eval : ArithExt → Nat
  | .lit n => n
  | .add x y => eval x + eval y
  | .mul x y => eval x * eval y

/-- Forgetful map into base syntax (forgets `mul` by over-approximating as `add`). -/
def eraseMul : ArithExt → Arith
  | .lit n => .lit n
  | .add x y => .add (eraseMul x) (eraseMul y)
  | .mul x y => .add (eraseMul x) (eraseMul y)

/-- Fragment predicate: expressions generated without `mul`. -/
inductive IsAddFragment : ArithExt → Prop where
  | lit (n : Nat) : IsAddFragment (.lit n)
  | add {x y : ArithExt} :
      IsAddFragment x → IsAddFragment y → IsAddFragment (.add x y)

end ArithExt

namespace Arith

/-- Canonical embedding of base syntax into the extended syntax. -/
def embed : Arith → ArithExt
  | .lit n => .lit n
  | .add x y => .add (embed x) (embed y)

@[simp] theorem embed_lit (n : Nat) : embed (.lit n) = ArithExt.lit n := rfl

@[simp] theorem embed_add (x y : Arith) : embed (.add x y) = ArithExt.add (embed x) (embed y) := rfl

/-- Conservativity of evaluation on the embedded base fragment. -/
@[simp] theorem eval_embed (e : Arith) : ArithExt.eval (embed e) = eval e := by
  induction e with
  | lit n => rfl
  | add x y ihx ihy =>
      simp [embed, ArithExt.eval, eval, ihx, ihy]

end Arith

namespace ArithExt

/-- Any add-only extended term is exactly an embedded base term after `eraseMul`. -/
theorem embed_erase_of_isAddFragment :
    ∀ e : ArithExt, IsAddFragment e → Arith.embed (eraseMul e) = e := by
  intro e
  induction e with
  | lit n =>
      intro _
      rfl
  | add x y ihx ihy =>
      intro h
      cases h with
      | add hx hy =>
          simp [eraseMul, ihx hx, ihy hy]
  | mul x y =>
      intro h
      cases h

/-- On add-only terms, extended evaluation agrees with base evaluation of the erased term. -/
theorem eval_eq_eval_erase_of_isAddFragment
    (e : ArithExt) (h : IsAddFragment e) :
    eval e = Arith.eval (eraseMul e) := by
  calc
    eval e = eval (Arith.embed (eraseMul e)) := by
      simp [embed_erase_of_isAddFragment e h]
    _ = Arith.eval (eraseMul e) := Arith.eval_embed _

end ArithExt

/-! ## 14. Indexed inductive families and eliminators (Formath-style) -/

/-- Indexed family: evidence that a natural is even. -/
inductive Even : Nat → Prop where
  | zero : Even 0
  | add_two {n : Nat} : Even n → Even (n + 2)

namespace Even

@[simp] theorem zero' : Even 0 := zero

@[simp] theorem add_two' {n : Nat} (h : Even n) : Even (n + 2) := add_two h

/-- Recursor-driven proof (explicit eliminator) from `Even.rec`. -/
theorem exists_half : ∀ {n : Nat}, Even n → ∃ k : Nat, n = k + k := by
  intro n hn
  refine Even.rec (motive := fun m _ => ∃ k : Nat, m = k + k) ?h0 ?hstep hn
  · exact ⟨0, rfl⟩
  · intro m hm ih
    rcases ih with ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    omega

/-- Build `Even` evidence from the explicit half property. -/
theorem of_exists_half {n : Nat} (h : ∃ k : Nat, n = k + k) : Even n := by
  rcases h with ⟨k, hk⟩
  subst hk
  induction k with
  | zero => simp
  | succ k ih =>
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Even.add_two ih

/-- Good (indexed) and awkward (existential) encodings are equivalent. -/
def AwkwardEven (n : Nat) : Prop := ∃ k : Nat, n = k + k

theorem iff_awkward (n : Nat) : Even n ↔ AwkwardEven n := by
  constructor
  · intro h
    exact exists_half h
  · intro h
    exact of_exists_half h

end Even

/-! ## 15. Reference-style inductive design patterns -/

/-- Parameters are fixed across constructors. -/
inductive Tagged (α : Type) (tag : Nat) : Type where
  | mk : α → Tagged α tag

/-- Indices can vary per constructor output. -/
inductive TaggedI (α : Type) : Nat → Type where
  | mk : α → TaggedI α n

namespace Tagged

@[simp] def value {α : Type} {tag : Nat} : Tagged α tag → α
  | .mk a => a

@[simp] theorem mk_injective {α : Type} {tag : Nat} {a b : α} :
    (Tagged.mk (α := α) (tag := tag) a = Tagged.mk b) ↔ a = b := by
  constructor
  · intro h
    simpa using congrArg value h
  · intro h
    cases h
    rfl

end Tagged

namespace TaggedI

@[simp] def value {α : Type} {n : Nat} : TaggedI α n → α
  | .mk a => a

end TaggedI

/-- Generated no-confusion principle for disjoint constructors. -/
theorem option_none_ne_some {α : Type} (a : α) : (none : Option α) ≠ some a := by
  intro h
  cases h

/-- Generated injectivity theorem (`injEq`) for list constructors. -/
theorem list_cons_eq_iff {α : Type} (a b : α) (as bs : List α) :
    (a :: as = b :: bs) ↔ (a = b ∧ as = bs) := by
  simp

/-- Indexed relation encoding list length in the index (good for induction). -/
inductive HasLen (α : Type) : Nat → List α → Prop where
  | nil : HasLen α 0 []
  | cons {n : Nat} {x : α} {xs : List α} : HasLen α n xs → HasLen α (n + 1) (x :: xs)

namespace HasLen

/-- Canonical evidence: every list has length-indexed evidence at `xs.length`. -/
def ofList {α : Type} : (xs : List α) → HasLen α xs.length xs
  | [] => .nil
  | _ :: xs => by
      simpa using (HasLen.cons (ofList xs))

/-- Forgetful theorem from indexed evidence back to ordinary length equality. -/
theorem length_eq {α : Type} {n : Nat} {xs : List α} (h : HasLen α n xs) : xs.length = n := by
  induction h with
  | nil => rfl
  | cons h ih =>
      simp [List.length, ih]

/-- Awkward encoding (length as external equation). -/
def AwkwardLen (α : Type) (n : Nat) (xs : List α) : Prop := xs.length = n

/-- Convert awkward encoding into indexed evidence by transport. -/
theorem ofAwkward {α : Type} {n : Nat} {xs : List α} (h : AwkwardLen α n xs) : HasLen α n xs := by
  dsimp [AwkwardLen] at h
  subst n
  simpa using ofList xs

end HasLen

/-! ## 16. Natural numbers and induction (Logic & Proof style) -/

/-- Peano-style induction proof of `0 + n = n`. -/
theorem zero_add_ind (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp

/-- A small `calc` chain in the style of equational reasoning over `Nat`. -/
theorem add_one_eq_succ_calc (n : Nat) : n + 1 = Nat.succ n := by
  calc
    n + 1 = n + Nat.succ 0 := rfl
    _ = Nat.succ (n + 0) := by simp
    _ = Nat.succ n := by simp

/-- Recursion example on `Nat`. -/
def doubleRec : Nat → Nat
  | 0 => 0
  | n + 1 => doubleRec n + 2
termination_by n => n

@[simp] theorem doubleRec_zero : doubleRec 0 = 0 := by
  simp [doubleRec]

@[simp] theorem doubleRec_succ (n : Nat) : doubleRec (n + 1) = doubleRec n + 2 := by
  simp [doubleRec]

/-- Induction showing the recursive implementation matches the specification. -/
theorem doubleRec_eq_add (n : Nat) : doubleRec n = n + n := by
  induction n with
  | zero =>
      simp [doubleRec_zero]
  | succ n ih =>
      calc
        doubleRec (n + 1) = doubleRec n + 2 := by simp [doubleRec_succ]
        _ = (n + n) + 2 := by simp [ih]
        _ = (n + 1) + (n + 1) := by omega

/-- Recursor view (`Nat.rec`) of the same construction. -/
def doubleRecOn (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat)
    0
    (fun _ ih => ih + 2)
    n

@[simp] theorem doubleRecOn_eq_doubleRec (n : Nat) : doubleRecOn n = doubleRec n := by
  induction n with
  | zero =>
      simp [doubleRecOn]
  | succ n ih =>
      simpa [doubleRecOn, doubleRec, ih]

/-! ## 17. Infinite types in Lean (Logic & Proof style) -/

/-- The successor map as an embedding of `Nat` into itself. -/
def succEmbedding : Nat ↪ Nat where
  toFun := fun n => n + 1
  inj' := by
    intro a b h
    exact Nat.add_right_cancel h

@[simp] theorem succEmbedding_apply (n : Nat) : succEmbedding n = n + 1 := rfl

/-- The successor map is not surjective (`0` has no preimage). -/
theorem succ_not_surjective : ¬ Function.Surjective (fun n : Nat => n + 1) := by
  intro hsurj
  obtain ⟨n, hn⟩ := hsurj 0
  simp at hn

/-- Canonical infinitude of naturals. -/
theorem nat_infinite : Infinite Nat := by
  infer_instance

/-- Canonical finiteness of `Fin n`. -/
theorem fin_finite (n : Nat) : Finite (Fin n) := by
  infer_instance

/-- A diagonal function differs from every row of the table `F`. -/
theorem diagonal_differs (F : Nat → Nat → Bool) :
    let d : Nat → Bool := fun n => !(F n n)
    ∀ n : Nat, d ≠ F n := by
  intro d n hEq
  have hAt : d n = F n n := by
    simpa using congrArg (fun f => f n) hEq
  have hDiag : !(F n n) = F n n := by
    simp [d] at hAt ⊢
  cases hVal : F n n <;> simp [hVal] at hDiag

/-- Cantor-style consequence: no enumeration `Nat → (Nat → Bool)` is surjective. -/
theorem not_surjective_nat_to_boolfun (F : Nat → Nat → Bool) :
    ¬ Function.Surjective F := by
  intro hsurj
  let d : Nat → Bool := fun n => !(F n n)
  obtain ⟨n, hn⟩ := hsurj d
  have hneq : d ≠ F n := (diagonal_differs F) n
  exact hneq hn.symm

/-! ## 18. Structural recursion and induction -/

/-- Keep elements in odd positions by structural recursion on `List`. -/
def keepOdd {α : Type} : List α → List α
  | [] => []
  | [x] => [x]
  | x :: _ :: xs => x :: keepOdd xs

@[simp] theorem keepOdd_nil : keepOdd ([] : List α) = [] := by
  simp [keepOdd]

@[simp] theorem keepOdd_singleton (x : α) : keepOdd [x] = [x] := by
  simp [keepOdd]

@[simp] theorem keepOdd_cons_cons (x y : α) (xs : List α) :
    keepOdd (x :: y :: xs) = x :: keepOdd xs := by
  simp [keepOdd]

/-- Structural recursion on two arguments: recurse while both lists are nonempty. -/
def zipWith : (α → β → γ) → List α → List β → List γ
  | _, [], _ => []
  | _, _, [] => []
  | f, x :: xs, y :: ys => f x y :: zipWith f xs ys

@[simp] theorem zipWith_nil_left (f : α → β → γ) (ys : List β) : zipWith f [] ys = [] := by
  simp [zipWith]

@[simp] theorem zipWith_nil_right (f : α → β → γ) (xs : List α) : zipWith f xs [] = [] := by
  cases xs <;> rfl

theorem zipWith_length_le_left (f : α → β → γ) (xs : List α) (ys : List β) :
    (zipWith f xs ys).length ≤ xs.length := by
  induction xs generalizing ys with
  | nil => simp [zipWith]
  | cons x xs ih =>
      cases ys with
      | nil => simp [zipWith]
      | cons y ys =>
          simpa [zipWith] using Nat.succ_le_succ (ih ys)

theorem zipWith_length_le_right (f : α → β → γ) (xs : List α) (ys : List β) :
    (zipWith f xs ys).length ≤ ys.length := by
  induction ys generalizing xs with
  | nil =>
      have h : (zipWith f xs []).length = 0 := by simp
      rw [h]
      exact Nat.zero_le 0
  | cons y ys ih =>
      cases xs with
      | nil => simp [zipWith]
      | cons x xs =>
          simpa [zipWith] using Nat.succ_le_succ (ih xs)

/-- Another structural example from equations and recursion. -/
def doubleList : List α → List α
  | [] => []
  | x :: xs => x :: x :: doubleList xs

@[simp] theorem doubleList_length (xs : List α) : (doubleList xs).length = 2 * xs.length := by
  induction xs with
  | nil => simp [doubleList]
  | cons x xs ih =>
      calc
        (doubleList (x :: xs)).length = (doubleList xs).length + 2 := by simp [doubleList]
        _ = 2 * xs.length + 2 := by rw [ih]
        _ = 2 * (xs.length + 1) := by omega
        _ = 2 * (x :: xs).length := by simp

/-! ## 19. Inductive types and dependent eliminators (The Type System style) -/

/-- A length-indexed vector type defined as an indexed inductive. -/
inductive SizedList (α : Type) : Nat → Type where
  | nil : SizedList α 0
  | cons {n : Nat} : α → SizedList α n → SizedList α (n + 1)

namespace SizedList

/-- Convert indexed lists to plain `List`. -/
@[simp] def toList {α : Type} : ∀ {n : Nat}, SizedList α n → List α
  | 0, .nil => []
  | _ + 1, .cons x xs => x :: toList xs

@[simp] theorem toList_nil (α : Type) : (toList (n := 0) (nil : SizedList α 0)) = [] := rfl

@[simp] theorem toList_cons {α : Type} {n : Nat} (x : α) (xs : SizedList α n) :
    toList (n := n + 1) (cons x xs) = x :: toList xs := by
  rfl

@[simp] theorem length_toList {α : Type} {n : Nat} (xs : SizedList α n) :
    (toList xs).length = n := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [ih]

/-- A dependent map that preserves length. -/
def map {α β : Type} (f : α → β) : ∀ {n : Nat}, SizedList α n → SizedList β n
  | 0, .nil => .nil
  | _n + 1, .cons x xs => .cons (f x) (map f xs)

@[simp] theorem map_toList {α β : Type} (f : α → β) {n : Nat} (xs : SizedList α n) :
    toList (map f xs) = (toList xs).map f := by
  induction xs with
  | nil => simp [map]
  | cons x xs ih => simp [map, ih]

/-- Explicit constructor injectivity at the inductive level. -/
theorem cons_injective {α : Type} {n : Nat} {x y : α} {xs ys : SizedList α n}
    (h : cons x xs = cons y ys) : x = y ∧ xs = ys := by
  cases h
  exact ⟨rfl, rfl⟩


end SizedList

/-! ## 20. The natural numbers and induction (Lean proofs style) -/

/-- Repeated addition as multiplication in a recursive form. -/
def repeatAdd : Nat → Nat → Nat
  | _m, 0 => 0
  | m, n + 1 => m + repeatAdd m n

@[simp] theorem repeatAdd_zero (_m : Nat) : repeatAdd _m 0 = 0 := by
  induction _m with
  | zero => simp [repeatAdd]
  | succ _m ih => simp [repeatAdd]

@[simp] theorem repeatAdd_succ (m n : Nat) : repeatAdd m (n + 1) = m + repeatAdd m n := by
  rfl

theorem repeatAdd_eq_mul (m n : Nat) : repeatAdd m n = m * n := by
  induction n with
  | zero => simp [repeatAdd]
  | succ n ih =>
      calc
        repeatAdd m (n + 1) = m + repeatAdd m n := by rfl
        _ = m + (m * n) := by rw [ih]
        _ = m * (n + 1) := by
          simp [Nat.mul_succ, Nat.add_comm]

/-- Factorial via structural recursion on `Nat`. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n
termination_by n => n

@[simp] theorem fact_zero : fact 0 = 1 := by
  unfold fact
  rfl

@[simp] theorem fact_succ (n : Nat) : fact (n + 1) = (n + 1) * fact n := by
  simp [fact]

theorem fact_pos (n : Nat) : 0 < fact n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simpa [fact] using Nat.mul_pos (Nat.succ_pos n) ih

/-- A standard induction proof of commutativity of addition. -/
theorem add_comm_induction (a b : Nat) : a + b = b + a := by
  induction b with
  | zero => simp
  | succ b ih =>
      calc
        a + (b + 1) = (a + b) + 1 := by rfl
        _ = (b + a) + 1 := by rw [ih]
        _ = b + (a + 1) := by omega
        _ = (b + 1) + a := by omega

/-- A matching commutativity proof for multiplication via induction. -/
theorem mul_comm_induction (a b : Nat) : a * b = b * a := by
  induction b with
  | zero => simp
  | succ b ih =>
      calc
        a * (b + 1) = a * b + a := by simp [Nat.mul_succ]
        _ = b * a + a := by rw [ih]
        _ = (b + 1) * a := by simp [Nat.succ_mul]

/-! ## 21. Well-founded recursion and induction -/

/-- Recursion defined via the well-founded fixpoint combinator. -/
def wfCount : Nat → Nat :=
  WellFounded.fix Nat.lt_wfRel.wf (fun n rec =>
    match n with
    | 0 => 0
    | k + 1 => rec k (Nat.lt_succ_self k) + 1)

@[simp] theorem wfCount_zero : wfCount 0 = 0 := by
  unfold wfCount
  rw [WellFounded.fix_eq]

@[simp] theorem wfCount_succ (n : Nat) : wfCount (n + 1) = wfCount n + 1 := by
  unfold wfCount
  rw [WellFounded.fix_eq]

theorem wfCount_eq_id (n : Nat) : wfCount n = n := by
  induction n with
  | zero => simp
  | succ n ih => simp [wfCount_succ, ih]

/-- Accessibility for `<` in naturals follows directly from the well-foundedness property. -/
theorem wfAccessibleNat (n : Nat) : Acc (· < ·) n := by
  simpa [WellFoundedRelation.rel] using Nat.lt_wfRel.wf.apply n

/-- Another explicit well-founded induction on `<`. -/
theorem wf_induction_nat_example :
    ∀ n : Nat, ∀ m < n + 1, m ≤ n := by
  intro n
  refine Nat.lt_wfRel.wf.induction (C := fun t : Nat => ∀ m < t + 1, m ≤ t) n ?_
  intro t ih m hm
  exact Nat.le_of_lt_succ hm

/-- Non-structural recursion with `termination_by` and `decreasing_by`. -/
def logSteps : Nat → Nat
  | 0 => 0
  | n + 1 => logSteps ((n + 1) / 2) + 1
termination_by n => n
decreasing_by
  simpa using Nat.div_lt_self (Nat.succ_pos n) (by decide : 1 < 2)

@[simp] theorem logSteps_zero : logSteps 0 = 0 := by
  simp [logSteps]

@[simp] theorem logSteps_pos (n : Nat) : logSteps (n + 1) = logSteps ((n + 1) / 2) + 1 := by
  simp [logSteps]

/-- A custom well-founded recursive definition on a binary-branch measure. -/
def stair : Nat → Nat → Nat
  | 0, 0 => 0
  | 0, m + 1 => stair 0 m + 1
  | n + 1, m => stair n m + 1
termination_by n m => n + m + 1
decreasing_by
  all_goals omega

@[simp] theorem stair_zero : stair 0 m = m := by
  induction m with
  | zero => simp [stair]
  | succ m ih => simp [stair, ih]

@[simp] theorem stair_eq_add (n m : Nat) : stair n m = n + m := by
  induction n with
  | zero => simp [stair_zero]
  | succ n ih =>
      induction m with
      | zero => simp [stair, ih]
      | succ m ihm =>
          calc
            stair (n + 1) (m + 1) = stair n (m + 1) + 1 := by simp [stair]
            _ = n + (m + 1) + 1 := by rw [ih]
            _ = n + 1 + (m + 1) := by omega

/-! ## 22. Induction and recursion (Theorem Proving in Lean 4) -/

/-- Replication by structural recursion on the counter. -/
def replicateNat {α : Type} : Nat → α → List α
  | 0, _ => []
  | n + 1, a => a :: replicateNat n a

@[simp] theorem replicateNat_zero {α : Type} (a : α) : replicateNat (α := α) 0 a = [] := by
  rfl

@[simp] theorem replicateNat_succ {α : Type} (n : Nat) (a : α) : replicateNat (α := α) (n + 1) a = a :: replicateNat n a := by
  rfl

theorem replicateNat_length {α : Type} (n : Nat) (a : α) : (replicateNat n a).length = n := by
  induction n with
  | zero => simp [replicateNat]
  | succ n ih => simp [replicateNat, ih]

/-- Same property proved through `Nat.rec` with an explicit motive. -/
theorem replicateNat_length_rec {α : Type} (n : Nat) (a : α) : (replicateNat n a).length = n := by
  refine Nat.rec (motive := fun t => (replicateNat t a).length = t) ?h0 ?hs n
  · rfl
  · intro k ih
    simp [replicateNat, ih]

/-- Folding out a recursion equation from a `Nat.rec` proof. -/
theorem replicateNat_eq (n : Nat) (a : α) : replicateNat n a = List.replicate n a := by
  induction n with
  | zero => simp [replicateNat]
  | succ n ih =>
      calc
        replicateNat (n + 1) a = a :: replicateNat n a := by simp [replicateNat]
        _ = a :: List.replicate n a := by exact congrArg (List.cons a) ih
        _ = List.replicate (n + 1) a := by simpa using (List.replicate_succ (a := a) (n := n)).symm

/-! ## 23. Mutual recursion (Theorem Proving in Lean 4) -/

/-- The chapter’s mutual-recursion example is already present earlier as `(isEven, isOdd)`.
    Here we extract the negation relation in one theorem via induction on the pair. -/
theorem isEven_isOdd_negations (n : Nat) : isEven n = !isOdd n ∧ isOdd n = !isEven n := by
  induction n with
  | zero => simp [isEven, isOdd]
  | succ n ih =>
      rcases ih with ⟨he, ho⟩
      constructor
      · rw [isEven, isOdd]
        exact ho
      · rw [isEven, isOdd]
        exact he

/-- A single extracted relation from the mutual equations. -/
theorem isEven_not_isOdd (n : Nat) : isEven n = !isOdd n := by
  exact (isEven_isOdd_negations n).1

/-- A concrete alternating recursion: a Boolean “flicker” with odd/even steps. -/
def flicker : Nat → Bool
  | 0 => true
  | n + 1 => not (flicker n)

@[simp] theorem flicker_zero : flicker 0 = true := by
  rfl

@[simp] theorem flicker_succ (n : Nat) : flicker (n + 1) = not (flicker n) := by
  rfl

/-- The alternating recursion matches parity from the mutual predicates above. -/
theorem flicker_eq_isEven (n : Nat) : flicker n = isEven n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        flicker (n + 1) = not (flicker n) := by rfl
        _ = not (isEven n) := by simp [ih]
        _ = isOdd n := by
          exact (isEven_isOdd_negations n).2.symm
        _ = isEven (n + 1) := by exact (isEven_succ n).symm

/-! ## 24. Axiomatic foundations (Theorem Proving in Lean 4) -/

/-- Propositional extensionality (`propext`, an axiomatic principle in Lean). -/
theorem prop_extensionality (P Q : Prop) (h : P ↔ Q) : P = Q := by
  exact propext h

/-- Classical excluded middle (`em`). -/
theorem excluded_middle (P : Prop) : P ∨ ¬ P := by
  classical
  exact em P

/-- Extracting a canonical property from `Nonempty` via classical choice. -/
theorem choose_property_exists {α : Type} (h : Nonempty α) : ∃ a : α, a = Classical.choice h := by
  classical
  exact ⟨Classical.choice h, rfl⟩

/-- A right inverse is obtained from surjectivity using choice. -/
theorem rightInverse_of_surjective {α β : Type} (f : α → β) (hf : Function.Surjective f) :
    ∃ g : β → α, Function.RightInverse g f := by
  classical
  refine ⟨fun b => Classical.choose (hf b), ?_⟩
  intro b
  exact Classical.choose_spec (hf b)

/-- A right inverse immediately gives surjectivity. -/
theorem surjective_of_rightInverse {α β : Type} (f : α → β) (g : β → α)
    (hg : Function.RightInverse g f) : Function.Surjective f := by
  intro b
  exact ⟨g b, hg b⟩

/-- Function extensionality from pointwise equality. -/
theorem funext_example {α : Type} {β : α → Type} (f g : ∀ a, β a)
    (h : ∀ a, f a = g a) : f = g := by
  funext a
  exact h a

/-! ## 25. Repo-specific categorical induction patterns -/

section Categorical

open InfoGeometry.Canonical.CategoricalRecursiveClosureBridge
open InfoGeometry.Canonical.AFRecursiveLimitBridge

universe u

variable {Stage : Nat → Type u} [∀ n : Nat, Semiring (Stage n)]
variable {Limit : Type u} [Semiring Limit]

/-- Local recursive trajectory used in this handbook's examples. -/
def coneTrajectory
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (x0 : Stage 0) : ∀ i : Nat, Stage i :=
  fun n => Nat.rec (motive := fun i => Stage i) x0 (fun k ih => bond k ih) n

/-- Stage-wise constant image in any compatible cone. -/
theorem coneTrajectory_image_constant
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (toLimit : ∀ n : Nat, Stage n →+* Limit)
    (hcone : InfoGeometry.Algebra.InfiniteSuperClosureLemmas.CompatibleCone bond toLimit)
    (x0 : Stage 0) :
    ∀ n : Nat, toLimit n (coneTrajectory bond x0 n) = toLimit 0 x0 :=
  cone_stageImage_constant
    bond toLimit hcone (coneTrajectory bond x0)
    (by
      intro n
      cases n <;> rfl)

/-- AF trajectory notation matches the categorical trajectory in this reduced presentation. -/
def stageTrajectory
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (x0 : Stage 0) : ∀ i : Nat, Stage i :=
  coneTrajectory bond x0

/-- Stage trajectory is constant in a compatible direct-limit cone image. -/
theorem stageTrajectory_image_constant
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (toLimit : ∀ n : Nat, Stage n →+* Limit)
    (hcone : InfoGeometry.Algebra.InfiniteSuperClosureLemmas.CompatibleCone bond toLimit)
    (x0 : Stage 0) :
    ∀ n : Nat,
      toLimit n (stageTrajectory bond x0 n) = toLimit 0 x0 :=
  coneTrajectory_image_constant
    bond toLimit hcone x0

end Categorical

end InfoGeometry.Meta.InductionHandbook
