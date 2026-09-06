import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic

/-!
# Local Free Monoid Compatibility Layer

The original file was a copied Lean-3-era Mathlib file.  This compact layer
keeps the `FreeMonoid'` API used by the braid development, with `FreeMonoid' α`
implemented as `List α`.
-/

variable {α β γ M N : Type*}

/-- Free monoid over an alphabet, represented by lists. -/
abbrev FreeMonoid' (α : Type*) := List α

namespace FreeMonoid'

instance : Monoid (FreeMonoid' α) where
  one := []
  mul := List.append
  mul_one := List.append_nil
  one_mul := List.nil_append
  mul_assoc := List.append_assoc

instance : CancelMonoid (FreeMonoid' α) where
  mul_left_cancel _ _ _ := List.append_cancel_left
  mul_right_cancel _ _ _ := List.append_cancel_right

instance : Inhabited (FreeMonoid' α) := ⟨1⟩

/-- Identity equivalence with lists. -/
def toList : FreeMonoid' α ≃ List α := Equiv.refl _

/-- Identity equivalence from lists. -/
def ofList : List α ≃ FreeMonoid' α := Equiv.refl _

@[simp] theorem toList_one : toList (1 : FreeMonoid' α) = [] := rfl
@[simp] theorem ofList_nil : ofList ([] : List α) = (1 : FreeMonoid' α) := rfl
@[simp] theorem toList_mul (xs ys : FreeMonoid' α) :
    toList (xs * ys) = toList xs ++ toList ys := rfl
@[simp] theorem ofList_append (xs ys : List α) :
    ofList (xs ++ ys) = ofList xs * ofList ys := rfl

/-- Embed one generator as a singleton word. -/
def of (x : α) : FreeMonoid' α := [x]

@[simp] theorem toList_of (x : α) : toList (of x) = [x] := rfl
@[simp] theorem ofList_singleton (x : α) : ofList [x] = of x := rfl
@[simp] theorem ofList_cons (x : α) (xs : List α) :
    ofList (x :: xs) = of x * ofList xs := rfl
@[simp] theorem toList_of_mul (x : α) (xs : FreeMonoid' α) :
    toList (of x * xs) = x :: toList xs := rfl

theorem of_injective : Function.Injective (@of α) := by
  intro a b h
  exact List.singleton_injective h

/-- Word length. -/
def length (a : FreeMonoid' α) : ℕ := List.length a

@[simp] theorem length_one : length (1 : FreeMonoid' α) = 0 := rfl

@[simp] theorem eq_one_of_length_eq_zero {a : FreeMonoid' α} (h : length a = 0) :
    a = 1 :=
  List.eq_nil_of_length_eq_zero h

@[simp] theorem length_of {m : α} : length (of m) = 1 := rfl

theorem length_eq_one {a : FreeMonoid' α} :
    length a = 1 ↔ ∃ m, a = of m := by
  constructor
  · intro h
    cases a with
    | nil =>
        change List.length ([] : List α) = 1 at h
        simp at h
    | cons x xs =>
        cases xs with
        | nil => exact ⟨x, rfl⟩
        | cons _ _ => simp [length] at h
  · rintro ⟨m, rfl⟩
    rfl

theorem length_eq_two {v : FreeMonoid' α} :
    v.length = 2 ↔ ∃ c d, v = of c * of d := by
  constructor
  · intro h
    obtain ⟨a, b, hv⟩ := List.length_eq_two.mp h
    exact ⟨a, b, by simpa [of] using hv⟩
  · rintro ⟨a, b, rfl⟩
    rfl

@[simp] theorem length_mul (a b : FreeMonoid' α) :
    (a * b).length = a.length + b.length :=
  List.length_append

theorem of_neq_one (a : α) : of a ≠ (1 : FreeMonoid' α) := by
  intro h
  have := congrArg length h
  simp [length, of] at this

/-- Set of symbols appearing in a word. -/
def symbols [DecidableEq α] (a : FreeMonoid' α) : Finset α := a.toFinset

@[simp] theorem symbols_one [DecidableEq α] : symbols (1 : FreeMonoid' α) = ∅ := rfl
@[simp] theorem symbols_of [DecidableEq α] {m : α} :
    symbols (of m : FreeMonoid' α) = {m} := rfl

@[simp] theorem symbols_mul [DecidableEq α] {a b : FreeMonoid' α} :
    symbols (a * b : FreeMonoid' α) = symbols a ∪ symbols b := by
  ext x
  change x ∈ (a ++ b).toFinset ↔ x ∈ a.toFinset ∪ b.toFinset
  simp [List.mem_append]

def mem (m : α) (a : FreeMonoid' α) := m ∈ toList a

instance : Membership α (FreeMonoid' α) := ⟨fun a m => mem m a⟩

theorem mem_one_iff {m : α} : m ∈ (1 : FreeMonoid' α) ↔ False := by
  change m ∈ ([] : List α) ↔ False
  simp

@[simp] theorem mem_of {m n : α} : m ∈ (of n : FreeMonoid' α) ↔ m = n := by
  change m ∈ ([n] : List α) ↔ m = n
  exact List.mem_singleton

theorem mem_of_self {m : α} : m ∈ (of m : FreeMonoid' α) := by
  simp

@[simp] theorem mem_mul {m : α} {a b : FreeMonoid' α} :
    m ∈ (a * b : FreeMonoid' α) ↔ m ∈ a ∨ m ∈ b := by
  change m ∈ (a ++ b) ↔ m ∈ a ∨ m ∈ b
  exact List.mem_append

@[simp] theorem mem_symbols [DecidableEq α] {m : α} {a : FreeMonoid' α} :
    m ∈ symbols a ↔ m ∈ a := by
  change m ∈ a.toFinset ↔ List.Mem m a
  exact (@List.mem_toFinset α _ a m)

/-- Recursor using `1` and `of x * xs`. -/
def recOn {C : FreeMonoid' α → Sort*} (xs : FreeMonoid' α) (h0 : C 1)
    (ih : ∀ x xs, C xs → C (of x * xs)) : C xs :=
  List.rec h0 ih xs

@[simp] theorem recOn_one {C : FreeMonoid' α → Sort*} (h0 : C 1)
    (ih : ∀ x xs, C xs → C (of x * xs)) :
    @recOn α C 1 h0 ih = h0 := rfl

@[simp] theorem recOn_of_mul {C : FreeMonoid' α → Sort*} (x : α) (xs : FreeMonoid' α)
    (h0 : C 1) (ih : ∀ x xs, C xs → C (of x * xs)) :
    @recOn α C (of x * xs) h0 ih = ih x xs (recOn xs h0 ih) := rfl

@[elab_as_elim]
protected theorem inductionOn {C : FreeMonoid' α → Prop} (z : FreeMonoid' α) (one : C 1)
    (of_case : ∀ x : α, C (of x))
    (mul_case : ∀ x y : FreeMonoid' α, C x → C y → C (x * y)) :
    C z := by
  induction (z : List α) with
  | nil => exact one
  | cons x xs ih =>
      exact mul_case (of x) xs (of_case x) ih

@[elab_as_elim]
protected theorem inductionOn' {p : FreeMonoid' α → Prop} (a : FreeMonoid' α)
    (one : p (1 : FreeMonoid' α)) (mul_of : ∀ b a, p a → p (of b * a)) : p a := by
  induction a with
  | nil => exact one
  | cons x xs ih => exact mul_of x xs ih

theorem eq_one_or_has_last_elem (u : FreeMonoid' α) :
    u = 1 ∨ ∃ front last, u = front * of last := by
  simpa [of] using (List.eq_nil_or_concat u)

def casesOn {C : FreeMonoid' α → Sort*} (xs : FreeMonoid' α) (h0 : C 1)
    (ih : ∀ x xs, C (of x * xs)) : C xs :=
  List.casesOn xs h0 ih

@[simp] theorem casesOn_one {C : FreeMonoid' α → Sort*} (h0 : C 1)
    (ih : ∀ x xs, C (of x * xs)) :
    @casesOn α C 1 h0 ih = h0 := rfl

@[simp] theorem casesOn_of_mul {C : FreeMonoid' α → Sort*} (x : α) (xs : FreeMonoid' α)
    (h0 : C 1) (ih : ∀ x xs, C (of x * xs)) :
    @casesOn α C (of x * xs) h0 ih = ih x xs := rfl

theorem hom_eq [Monoid M] ⦃f g : FreeMonoid' α →* M⦄
    (h : ∀ x, f (of x) = g (of x)) : f = g := by
  ext l
  induction l using FreeMonoid'.inductionOn' with
  | one => simp
  | mul_of x xs ih => simp [ih, h x]

def prodAux [Monoid M] : List M → M
  | xs => xs.prod

lemma prodAux_eq [Monoid M] : ∀ l : List M, prodAux l = l.prod
  | _ => rfl

/-- Universal lift from generators to a monoid. -/
def lift [Monoid M] : (α → M) ≃ (FreeMonoid' α →* M) where
  toFun f :=
    { toFun := fun l => (l.map f).prod
      map_one' := by
        change List.prod ([] : List M) = 1
        rfl
      map_mul' := by
        intro x y
        change (List.map f (x ++ y)).prod = (List.map f x).prod * (List.map f y).prod
        rw [List.map_append, List.prod_append] }
  invFun f x := f (of x)
  left_inv f := by
    funext x
    simp [of]
  right_inv f := hom_eq fun x => by
    simp [of]

@[simp] theorem lift_eval_of [Monoid M] (f : α → M) (x : α) :
    lift f (of x) = f x := by
  simp [lift, of]

theorem lift_apply [Monoid M] (f : α → M) (l : FreeMonoid' α) :
    lift f l = (l.map f).prod := rfl

theorem lift_comp_of [Monoid M] (f : α → M) : lift f ∘ of = f := by
  funext x
  exact lift_eval_of f x

@[simp] theorem lift_restrict [Monoid M] (f : FreeMonoid' α →* M) :
    lift (f ∘ of) = f :=
  hom_eq fun _ => lift_eval_of _ _

/-- Map a word through a function on generators. -/
def map (f : α → β) : FreeMonoid' α →* FreeMonoid' β where
  toFun l := List.map f l
  map_one' := by
    change List.map f ([] : List α) = ([] : List β)
    rfl
  map_mul' := by
    intro x y
    change List.map f (x ++ y) = List.map f x ++ List.map f y
    exact List.map_append

@[simp] theorem map_apply (f : α → β) (x : FreeMonoid' α) :
    map f x = List.map f x := rfl

@[simp] theorem map_of (f : α → β) (x : α) : map f (of x) = of (f x) := by
  change List.map f [x] = [f x]
  rfl

@[simp] theorem mem_map {f : α → β} {m : β} {a : FreeMonoid' α} :
    m ∈ map f a ↔ ∃ n ∈ a, f n = m := by
  change m ∈ List.map f a ↔ ∃ n, n ∈ a ∧ f n = m
  exact List.mem_map

theorem map_map {f : α → β} {g : γ → α} {x : FreeMonoid' γ} :
    map f (map g x) = map (f ∘ g) x := by
  change List.map f (List.map g x) = List.map (f ∘ g) x
  exact List.map_map

theorem toList_map (f : α → β) (xs : FreeMonoid' α) :
    toList (map f xs) = xs.toList.map f := by
  rfl

theorem map_surjective (f : α → β) :
    Function.Surjective f → Function.Surjective (map f) := by
  intro hf d
  induction d using FreeMonoid'.inductionOn' with
  | one =>
      refine ⟨1, ?_⟩
      change List.map f ([] : List α) = ([] : List β)
      rfl
  | mul_of head tail ih =>
      obtain ⟨preHead, rfl⟩ := hf head
      obtain ⟨preTail, rfl⟩ := ih
      refine ⟨of preHead * preTail, ?_⟩
      change List.map f (preHead :: preTail) = f preHead :: List.map f preTail
      rfl

/-- Reverse a word. -/
def reverse : FreeMonoid' α → FreeMonoid' α := List.reverse

@[simp] theorem reverse_of {a : α} : reverse (of a) = of a := rfl

@[simp] theorem reverse_mul {a b : FreeMonoid' α} : reverse (a * b) = reverse b * reverse a :=
  List.reverse_append

@[simp] theorem reverse_reverse {a : FreeMonoid' α} : reverse (reverse a) = a :=
  List.reverse_reverse _

@[simp] theorem reverse_length {a : FreeMonoid' α} : a.reverse.length = a.length :=
  List.length_reverse

def congr_iso {α : Type u} {β : Type v} (e : α ≃ β) : FreeMonoid' α ≃* FreeMonoid' β where
  toFun := map e
  invFun := map e.symm
  left_inv := by intro x; induction x <;> simp [map_apply]
  right_inv := by intro x; induction x <;> simp [map_apply]
  map_mul' := by
    intro x y
    change List.map e (x ++ y) = List.map e x ++ List.map e y
    exact List.map_append

def map_rel (e : α ≃ β) (rel : FreeMonoid' α → FreeMonoid' α → Prop) :
    FreeMonoid' β → FreeMonoid' β → Prop :=
  fun a b => rel ((congr_iso e).symm a) ((congr_iso e).symm b)

def comap_rel (e : α ≃ β) (rel : FreeMonoid' β → FreeMonoid' β → Prop) :
    FreeMonoid' α → FreeMonoid' α → Prop :=
  fun a b => rel (congr_iso e a) (congr_iso e b)

theorem length_eq_three {v : FreeMonoid' α} (h : v.length = 3) :
    ∃ a b c : α, v = of a * of b * of c := by
  cases v with
  | nil =>
      change List.length ([] : List α) = 3 at h
      simp at h
  | cons a rest1 =>
      cases rest1 with
      | nil =>
          change List.length ([a] : List α) = 3 at h
          simp at h
      | cons b rest2 =>
          cases rest2 with
          | nil =>
              change List.length ([a, b] : List α) = 3 at h
              simp at h
          | cons c rest3 =>
              have hrest : rest3.length = 0 := by
                simpa using Nat.succ.inj (Nat.succ.inj (Nat.succ.inj h))
              have : rest3 = [] := List.eq_nil_of_length_eq_zero hrest
              subst rest3
              exact ⟨a, b, c, rfl⟩

end FreeMonoid'
