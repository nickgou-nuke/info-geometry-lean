import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Tactic

set_option linter.unusedSimpArgs false

/-!
# Grothendieck Groups, Products, and the Dimension Isomorphism

This file constructs the Grothendieck group of a commutative additive monoid
as a quotient of formal differences. It proves the group laws, the universal
property, the cancellation/injectivity criterion, product decomposition, and
the concrete dimension calculation for the additive monoid `ℕ`.

The final theorem owners are:

* `grothendieckProdEquiv :
    Grothendieck (A × B) ≃+ Grothendieck A × Grothendieck B`
* `grothendieckEquivInt : Grothendieck ℕ ≃+ ℤ`

This is the finite algebraic core of the calculation `K₀(Spec F) ≅ ℤ`: the
monoid of finite vector-space dimensions is `ℕ`, and its Grothendieck
completion is `ℤ`.

## Audit Protocol Map
- BUCKET 1: CLOSED FINITE THEOREMS:
  `grothendieck_refl`, `grothendieck_symm`, `grothendieck_trans`,
  `grothendieck_add_compat`, `grothendieck_neg_compat`,
  `grothendieck_add_assoc`, `grothendieck_add_comm`, `grothendieck_zero_add`,
  `grothendieck_add_zero`, `grothendieck_add_left_neg`, `grothendieckMap`,
  `grothendieckMap_add`, `idempotent_invariance_split`,
  `lift_raw_compat`, `grothendieckLift`, `grothendieckLift_comp`,
  `grothendieckLift_unique`, `grothendieckMap_injective_of_cancellation`,
  `cancellation_of_grothendieckMap_injective`,
  `grothendieckMap_injective_iff_cancellation`, `grothendieckProdHom`,
  `grothendieckProdInl`, `grothendieckProdInr`, `grothendieckProdFrom`,
  `grothendieckProdFrom_to`, `grothendieckProdTo_from`,
  `grothendieckProdEquiv`, `to_int_raw`,
  `to_int_raw_compat`, `grothendieckToInt`, `grothendieckToInt_injective`,
  `grothendieckToInt_surjective`, `grothendieckEquivInt`.
- BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES: None.
- BUCKET 3: OPEN CLOSURE DEBT: None.
-/

variable {M : Type*} [AddCommMonoid M]

/-- Formal difference equivalence: `(a,b) ~ (c,d)` iff `a + d = b + c` stably. -/
def GrothendieckRel (x y : M × M) : Prop :=
  ∃ k : M, x.1 + y.2 + k = x.2 + y.1 + k

theorem grothendieck_refl (x : M × M) : GrothendieckRel x x := by
  use 0
  simp [add_assoc, add_comm, add_left_comm]

theorem grothendieck_symm {x y : M × M}
    (h : GrothendieckRel x y) : GrothendieckRel y x := by
  rcases h with ⟨k, hk⟩
  use k
  calc
    y.1 + x.2 + k = x.2 + y.1 + k := by simp [add_assoc, add_comm, add_left_comm]
    _ = x.1 + y.2 + k := hk.symm
    _ = y.2 + x.1 + k := by simp [add_assoc, add_comm, add_left_comm]

theorem grothendieck_trans {x y z : M × M}
    (h1 : GrothendieckRel x y) (h2 : GrothendieckRel y z) :
    GrothendieckRel x z := by
  rcases h1 with ⟨k1, hk1⟩
  rcases h2 with ⟨k2, hk2⟩
  use k1 + k2 + y.1 + y.2
  calc
    x.1 + z.2 + (k1 + k2 + y.1 + y.2)
        = (x.1 + y.2 + k1) + (y.1 + z.2 + k2) := by
          simp [add_assoc, add_comm, add_left_comm]
    _ = (x.2 + y.1 + k1) + (y.2 + z.1 + k2) := by rw [hk1, hk2]
    _ = x.2 + z.1 + (k1 + k2 + y.1 + y.2) := by
      simp [add_assoc, add_comm, add_left_comm]

/-- The setoid on pairs used to quotient formal differences. -/
def grothendieckSetoid (M : Type*) [AddCommMonoid M] : Setoid (M × M) where
  r := GrothendieckRel
  iseqv := {
    refl := grothendieck_refl
    symm := fun h => grothendieck_symm h
    trans := fun h1 h2 => grothendieck_trans h1 h2
  }

/-- The Grothendieck group of a commutative additive monoid. -/
def Grothendieck (M : Type*) [AddCommMonoid M] : Type _ :=
  Quotient (grothendieckSetoid M)

theorem grothendieck_add_compat {x1 x2 y1 y2 : M × M}
    (hx : GrothendieckRel x1 x2) (hy : GrothendieckRel y1 y2) :
    GrothendieckRel (x1.1 + y1.1, x1.2 + y1.2) (x2.1 + y2.1, x2.2 + y2.2) := by
  rcases hx with ⟨k1, hk1⟩
  rcases hy with ⟨k2, hk2⟩
  use k1 + k2
  calc
    (x1.1 + y1.1) + (x2.2 + y2.2) + (k1 + k2)
        = (x1.1 + x2.2 + k1) + (y1.1 + y2.2 + k2) := by
          simp [add_assoc, add_comm, add_left_comm]
    _ = (x1.2 + x2.1 + k1) + (y1.2 + y2.1 + k2) := by rw [hk1, hk2]
    _ = (x1.2 + y1.2) + (x2.1 + y2.1) + (k1 + k2) := by
      simp [add_assoc, add_comm, add_left_comm]

def grothendieckAdd : Grothendieck M → Grothendieck M → Grothendieck M :=
  Quotient.map₂ (fun x y => (x.1 + y.1, x.2 + y.2)) (by
    intro _ _ hx _ _ hy
    exact grothendieck_add_compat hx hy)

def grothendieckZero : Grothendieck M :=
  Quotient.mk (grothendieckSetoid M) (0, 0)

theorem grothendieck_neg_compat {x y : M × M}
    (h : GrothendieckRel x y) : GrothendieckRel (x.2, x.1) (y.2, y.1) := by
  rcases h with ⟨k, hk⟩
  use k
  exact hk.symm

def grothendieckNeg : Grothendieck M → Grothendieck M :=
  Quotient.map (fun x => (x.2, x.1)) (by
    intro _ _ h
    exact grothendieck_neg_compat h)

theorem grothendieck_add_assoc (a b c : Grothendieck M) :
    grothendieckAdd (grothendieckAdd a b) c = grothendieckAdd a (grothendieckAdd b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro x y z
  apply Quotient.sound
  use 0
  simp [add_assoc, add_comm, add_left_comm]

theorem grothendieck_add_comm (a b : Grothendieck M) :
    grothendieckAdd a b = grothendieckAdd b a := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  apply Quotient.sound
  use 0
  simp [add_assoc, add_comm, add_left_comm]

theorem grothendieck_zero_add (a : Grothendieck M) :
    grothendieckAdd grothendieckZero a = a := by
  refine Quotient.inductionOn a ?_
  intro x
  apply Quotient.sound
  use 0
  simp [add_assoc, add_comm, add_left_comm]

theorem grothendieck_add_zero (a : Grothendieck M) :
    grothendieckAdd a grothendieckZero = a := by
  refine Quotient.inductionOn a ?_
  intro x
  apply Quotient.sound
  use 0
  simp [add_assoc, add_comm, add_left_comm]

theorem grothendieck_add_left_neg (a : Grothendieck M) :
    grothendieckAdd (grothendieckNeg a) a = grothendieckZero := by
  refine Quotient.inductionOn a ?_
  intro x
  apply Quotient.sound
  use 0
  simp [add_assoc, add_comm, add_left_comm]

instance : Add (Grothendieck M) :=
  ⟨grothendieckAdd⟩

instance : Zero (Grothendieck M) :=
  ⟨grothendieckZero⟩

instance : Neg (Grothendieck M) :=
  ⟨grothendieckNeg⟩

instance : Sub (Grothendieck M) :=
  ⟨fun a b => grothendieckAdd a (grothendieckNeg b)⟩

instance : AddCommGroup (Grothendieck M) where
  add := (· + ·)
  add_assoc := grothendieck_add_assoc
  zero := 0
  zero_add := grothendieck_zero_add
  add_zero := grothendieck_add_zero
  neg := Neg.neg
  neg_add_cancel := grothendieck_add_left_neg
  add_comm := grothendieck_add_comm
  sub := (· - ·)
  sub_eq_add_neg _ _ := rfl
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- The canonical additive monoid homomorphism into the Grothendieck group. -/
def grothendieckMap (M : Type*) [AddCommMonoid M] : M →+ Grothendieck M where
  toFun m := Quotient.mk (grothendieckSetoid M) (m, 0)
  map_zero' := rfl
  map_add' x y := by
    apply Quotient.sound
    use 0
    simp [add_assoc, add_comm, add_left_comm]

/-- The canonical Grothendieck map is additive. -/
theorem grothendieckMap_add (x y : M) :
    grothendieckMap M (x + y) = grothendieckMap M x + grothendieckMap M y :=
  (grothendieckMap M).map_add x y

/--
If an object value splits additively as `x = y + z`, then its Grothendieck
image splits as the sum of the two component images.  This is the finite
algebraic shadow of split-idempotent invariance.
-/
theorem idempotent_invariance_split (x y z : M) (h_split : x = y + z) :
    grothendieckMap M x = grothendieckMap M y + grothendieckMap M z := by
  rw [h_split]
  exact grothendieckMap_add y z

theorem lift_raw_compat {A : Type*} [AddCommGroup A]
    (f : M →+ A) {x y : M × M} (h : GrothendieckRel x y) :
    f x.1 - f x.2 = f y.1 - f y.2 := by
  rcases h with ⟨k, hk⟩
  have h_map : f (x.1 + y.2 + k) = f (x.2 + y.1 + k) := by rw [hk]
  simp only [map_add] at h_map
  have h_cancel : f x.1 + f y.2 = f x.2 + f y.1 := by
    exact add_right_cancel h_map
  calc
    f x.1 - f x.2 = f x.1 + f y.2 - f y.2 - f x.2 := by abel
    _ = f x.2 + f y.1 - f y.2 - f x.2 := by rw [h_cancel]
    _ = f y.1 - f y.2 := by abel

/-- The unique lifted group homomorphism factoring any monoid map into an additive group. -/
def grothendieckLift {A : Type*} [AddCommGroup A] (f : M →+ A) : Grothendieck M →+ A where
  toFun := Quotient.lift (fun x => f x.1 - f x.2) (by
    intro _ _ h
    exact lift_raw_compat f h)
  map_zero' := by
    change f 0 - f 0 = 0
    rw [map_zero, sub_self]
  map_add' a b := by
    refine Quotient.inductionOn₂ a b ?_
    intro x y
    change f (x.1 + y.1) - f (x.2 + y.2)
        = (f x.1 - f x.2) + (f y.1 - f y.2)
    rw [map_add, map_add]
    abel

theorem grothendieckLift_comp {A : Type*} [AddCommGroup A]
    (f : M →+ A) (m : M) :
    grothendieckLift f (grothendieckMap M m) = f m := by
  change f m - f 0 = f m
  rw [map_zero, sub_zero]

theorem grothendieckLift_unique {A : Type*} [AddCommGroup A]
    (f : M →+ A) (g : Grothendieck M →+ A)
    (h_comp : ∀ m, g (grothendieckMap M m) = f m) (x : Grothendieck M) :
    g x = grothendieckLift f x := by
  refine Quotient.inductionOn x ?_
  intro y
  have h_decomp : Quotient.mk (grothendieckSetoid M) y =
      grothendieckMap M y.1 - grothendieckMap M y.2 := by
    apply Quotient.sound
    use 0
    simp [add_assoc, add_comm, add_left_comm]
  rw [h_decomp]
  rw [map_sub, map_sub]
  rw [h_comp, h_comp]
  rw [grothendieckLift_comp f y.1, grothendieckLift_comp f y.2]

/-- Cancellation for a commutative additive monoid. -/
def IsCancellationMonoid (M : Type*) [AddCommMonoid M] : Prop :=
  ∀ a b c : M, a + c = b + c → a = b

theorem grothendieckMap_injective_of_cancellation
    (h_cancel : IsCancellationMonoid M) :
    Function.Injective (grothendieckMap M) := by
  intro a b hab
  change Quotient.mk (grothendieckSetoid M) (a, 0)
      = Quotient.mk (grothendieckSetoid M) (b, 0) at hab
  rcases Quotient.exact hab with ⟨k, hk⟩
  exact h_cancel a b k (by simpa [add_zero, zero_add] using hk)

theorem cancellation_of_grothendieckMap_injective
    (h_inj : Function.Injective (grothendieckMap M)) :
    IsCancellationMonoid M := by
  intro a b c hab
  have h_rel : GrothendieckRel (a, 0) (b, 0) := by
    use c
    simpa [add_zero, zero_add] using hab
  have h_eq : grothendieckMap M a = grothendieckMap M b := by
    apply Quotient.sound
    exact h_rel
  exact h_inj h_eq

theorem grothendieckMap_injective_iff_cancellation :
    Function.Injective (grothendieckMap M) ↔ IsCancellationMonoid M := by
  constructor
  · exact cancellation_of_grothendieckMap_injective
  · exact grothendieckMap_injective_of_cancellation

/-!
## Product decomposition

The Grothendieck completion preserves finite products of commutative additive
monoids. This is the finite algebraic content behind product decompositions
such as diagonal-block `K₀` decompositions.
-/

variable {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]

/-- The generator map from a product monoid into the product of Grothendieck groups. -/
def grothendieckProdHom (A B : Type*) [AddCommMonoid A] [AddCommMonoid B] :
    A × B →+ Grothendieck A × Grothendieck B where
  toFun p := (grothendieckMap A p.1, grothendieckMap B p.2)
  map_zero' := by
    ext <;> rfl
  map_add' x y := by
    ext
    · exact (grothendieckMap A).map_add x.1 y.1
    · exact (grothendieckMap B).map_add x.2 y.2

/-- The first component insertion into the Grothendieck group of a product monoid. -/
def grothendieckProdInl (A B : Type*) [AddCommMonoid A] [AddCommMonoid B] :
    A →+ Grothendieck (A × B) where
  toFun a := grothendieckMap (A × B) (a, 0)
  map_zero' := rfl
  map_add' x y := by
    simpa using (grothendieckMap (A × B)).map_add (x, 0) (y, 0)

/-- The second component insertion into the Grothendieck group of a product monoid. -/
def grothendieckProdInr (A B : Type*) [AddCommMonoid A] [AddCommMonoid B] :
    B →+ Grothendieck (A × B) where
  toFun b := grothendieckMap (A × B) (0, b)
  map_zero' := rfl
  map_add' x y := by
    simpa using (grothendieckMap (A × B)).map_add (0, x) (0, y)

/-- The forward product decomposition homomorphism. -/
def grothendieckProdTo (A B : Type*) [AddCommMonoid A] [AddCommMonoid B] :
    Grothendieck (A × B) →+ Grothendieck A × Grothendieck B :=
  grothendieckLift (grothendieckProdHom A B)

/-- The first generator map into the product of Grothendieck groups. -/
def grothendieckProdLeftHom (A B : Type*) [AddCommMonoid A] [AddCommMonoid B] :
    A →+ Grothendieck A × Grothendieck B where
  toFun a := (grothendieckMap A a, 0)
  map_zero' := by
    ext <;> rfl
  map_add' x y := by
    ext
    · exact (grothendieckMap A).map_add x y
    · simp

/-- The second generator map into the product of Grothendieck groups. -/
def grothendieckProdRightHom (A B : Type*) [AddCommMonoid A] [AddCommMonoid B] :
    B →+ Grothendieck A × Grothendieck B where
  toFun b := (0, grothendieckMap B b)
  map_zero' := by
    ext <;> rfl
  map_add' x y := by
    ext
    · simp
    · exact (grothendieckMap B).map_add x y

/-- The first component map into the product of Grothendieck groups. -/
def grothendieckProdLeftMap (A B : Type*) [AddCommMonoid A] [AddCommMonoid B] :
    Grothendieck A →+ Grothendieck A × Grothendieck B where
  toFun u := (u, 0)
  map_zero' := by
    ext <;> simp
  map_add' u v := by
    ext <;> simp

/-- The second component map into the product of Grothendieck groups. -/
def grothendieckProdRightMap (A B : Type*) [AddCommMonoid A] [AddCommMonoid B] :
    Grothendieck B →+ Grothendieck A × Grothendieck B where
  toFun v := (0, v)
  map_zero' := by
    ext <;> simp
  map_add' u v := by
    ext <;> simp

/-- The inverse product decomposition homomorphism. -/
def grothendieckProdFrom (A B : Type*) [AddCommMonoid A] [AddCommMonoid B] :
    Grothendieck A × Grothendieck B →+ Grothendieck (A × B) where
  toFun p :=
    grothendieckLift (grothendieckProdInl A B) p.1 +
      grothendieckLift (grothendieckProdInr A B) p.2
  map_zero' := by
    change
      grothendieckLift (grothendieckProdInl A B) 0 +
          grothendieckLift (grothendieckProdInr A B) 0 =
        0
    rw [map_zero, map_zero, zero_add]
  map_add' x y := by
    change
      grothendieckLift (grothendieckProdInl A B) (x.1 + y.1) +
          grothendieckLift (grothendieckProdInr A B) (x.2 + y.2) =
        (grothendieckLift (grothendieckProdInl A B) x.1 +
            grothendieckLift (grothendieckProdInr A B) x.2) +
          (grothendieckLift (grothendieckProdInl A B) y.1 +
            grothendieckLift (grothendieckProdInr A B) y.2)
    rw [map_add, map_add]
    abel

theorem grothendieckProdTo_inl (u : Grothendieck A) :
    grothendieckProdTo A B (grothendieckLift (grothendieckProdInl A B) u) =
      grothendieckProdLeftMap A B u := by
  let h₁ : Grothendieck A →+ Grothendieck A × Grothendieck B :=
    (grothendieckProdTo A B).comp (grothendieckLift (grothendieckProdInl A B))
  let h₂ : Grothendieck A →+ Grothendieck A × Grothendieck B :=
    grothendieckProdLeftMap A B
  have h₁_factor :
      ∀ a, h₁ (grothendieckMap A a) = grothendieckProdLeftHom A B a := by
    intro a
    change
      grothendieckProdTo A B
          (grothendieckLift (grothendieckProdInl A B) (grothendieckMap A a)) =
        (grothendieckMap A a, 0)
    rw [grothendieckLift_comp]
    change grothendieckLift (grothendieckProdHom A B) (grothendieckMap (A × B) (a, 0)) =
      (grothendieckMap A a, 0)
    rw [grothendieckLift_comp]
    rfl
  have h₂_factor :
      ∀ a, h₂ (grothendieckMap A a) = grothendieckProdLeftHom A B a := by
    intro a
    rfl
  exact
    (grothendieckLift_unique (grothendieckProdLeftHom A B) h₁ h₁_factor u).trans
      (grothendieckLift_unique (grothendieckProdLeftHom A B) h₂ h₂_factor u).symm

theorem grothendieckProdTo_inr (v : Grothendieck B) :
    grothendieckProdTo A B (grothendieckLift (grothendieckProdInr A B) v) =
      grothendieckProdRightMap A B v := by
  let h₁ : Grothendieck B →+ Grothendieck A × Grothendieck B :=
    (grothendieckProdTo A B).comp (grothendieckLift (grothendieckProdInr A B))
  let h₂ : Grothendieck B →+ Grothendieck A × Grothendieck B :=
    grothendieckProdRightMap A B
  have h₁_factor :
      ∀ b, h₁ (grothendieckMap B b) = grothendieckProdRightHom A B b := by
    intro b
    change
      grothendieckProdTo A B
          (grothendieckLift (grothendieckProdInr A B) (grothendieckMap B b)) =
        (0, grothendieckMap B b)
    rw [grothendieckLift_comp]
    change grothendieckLift (grothendieckProdHom A B) (grothendieckMap (A × B) (0, b)) =
      (0, grothendieckMap B b)
    rw [grothendieckLift_comp]
    rfl
  have h₂_factor :
      ∀ b, h₂ (grothendieckMap B b) = grothendieckProdRightHom A B b := by
    intro b
    rfl
  exact
    (grothendieckLift_unique (grothendieckProdRightHom A B) h₁ h₁_factor v).trans
      (grothendieckLift_unique (grothendieckProdRightHom A B) h₂ h₂_factor v).symm

theorem grothendieckProdFrom_to (x : Grothendieck (A × B)) :
    grothendieckProdFrom A B (grothendieckProdTo A B x) = x := by
  have h_factor :
      (grothendieckProdFrom A B).comp (grothendieckProdTo A B) x =
        grothendieckLift (grothendieckMap (A × B)) x := by
    refine
      grothendieckLift_unique (grothendieckMap (A × B))
        ((grothendieckProdFrom A B).comp (grothendieckProdTo A B)) ?_ x
    intro p
    change
      grothendieckProdFrom A B (grothendieckProdTo A B (grothendieckMap (A × B) p)) =
        grothendieckMap (A × B) p
    change
      grothendieckProdFrom A B
          (grothendieckLift (grothendieckProdHom A B) (grothendieckMap (A × B) p)) =
        grothendieckMap (A × B) p
    rw [grothendieckLift_comp]
    change
      grothendieckLift (grothendieckProdInl A B) (grothendieckMap A p.1) +
          grothendieckLift (grothendieckProdInr A B) (grothendieckMap B p.2) =
        grothendieckMap (A × B) p
    rw [grothendieckLift_comp, grothendieckLift_comp]
    change
      grothendieckMap (A × B) (p.1, 0) + grothendieckMap (A × B) (0, p.2) =
        grothendieckMap (A × B) p
    rw [← map_add]
    congr 1
    ext <;> simp
  have h_id :
      AddMonoidHom.id (Grothendieck (A × B)) x =
        grothendieckLift (grothendieckMap (A × B)) x := by
    exact
      grothendieckLift_unique (grothendieckMap (A × B))
        (AddMonoidHom.id (Grothendieck (A × B))) (by intro p; rfl) x
  exact h_factor.trans h_id.symm

theorem grothendieckProdTo_from (y : Grothendieck A × Grothendieck B) :
    grothendieckProdTo A B (grothendieckProdFrom A B y) = y := by
  cases y with
  | mk u v =>
      change
        grothendieckProdTo A B
            (grothendieckLift (grothendieckProdInl A B) u +
              grothendieckLift (grothendieckProdInr A B) v) =
          (u, v)
      rw [map_add, grothendieckProdTo_inl, grothendieckProdTo_inr]
      ext <;> simp [grothendieckProdLeftMap, grothendieckProdRightMap]

/-- The Grothendieck group of a product monoid is the product of Grothendieck groups. -/
noncomputable def grothendieckProdEquiv :
    Grothendieck (A × B) ≃+ Grothendieck A × Grothendieck B where
  toFun := grothendieckProdTo A B
  invFun := grothendieckProdFrom A B
  left_inv := grothendieckProdFrom_to
  right_inv := grothendieckProdTo_from
  map_add' := map_add (grothendieckProdTo A B)

/-!
## The dimension isomorphism `Grothendieck ℕ ≃+ ℤ`

The additive monoid of isomorphism classes of finite-dimensional vector spaces
over a field is classified by dimension, hence by `ℕ`. Its Grothendieck
completion is therefore computed by the explicit quotient isomorphism below.
-/

/-- The raw integer value of a formal difference of natural numbers. -/
def to_int_raw (x : ℕ × ℕ) : ℤ :=
  (x.1 : ℤ) - (x.2 : ℤ)

theorem to_int_raw_compat {x y : ℕ × ℕ} (h : GrothendieckRel x y) :
    to_int_raw x = to_int_raw y := by
  dsimp [to_int_raw]
  rcases h with ⟨k, hk⟩
  have h_cast := congrArg (fun n : ℕ => (n : ℤ)) hk
  push_cast at h_cast
  omega

/-- The quotient homomorphism sending a formal natural-number difference to an integer. -/
def grothendieckToInt : Grothendieck ℕ →+ ℤ where
  toFun := Quotient.lift to_int_raw (by
    intro x y h
    exact to_int_raw_compat h)
  map_zero' := by
    change (0 : ℤ) - (0 : ℤ) = 0
    simp [add_comm, add_left_comm, add_assoc]
  map_add' a b := by
    refine Quotient.inductionOn₂ a b ?_
    intro x y
    change ((x.1 + y.1 : ℕ) : ℤ) - ((x.2 + y.2 : ℕ) : ℤ)
        = ((x.1 : ℤ) - (x.2 : ℤ)) + ((y.1 : ℤ) - (y.2 : ℤ))
    push_cast
    ring

theorem grothendieckToInt_injective : Function.Injective grothendieckToInt := by
  intro a b hab
  revert hab
  refine Quotient.inductionOn₂ a b ?_
  intro x y hab
  change (x.1 : ℤ) - (x.2 : ℤ) = (y.1 : ℤ) - (y.2 : ℤ) at hab
  apply Quotient.sound
  use 0
  simp only [add_zero]
  have h_int : ((x.1 + y.2 : ℕ) : ℤ) = ((x.2 + y.1 : ℕ) : ℤ) := by
    push_cast
    omega
  exact Nat.cast_inj.mp h_int

theorem grothendieckToInt_surjective : Function.Surjective grothendieckToInt := by
  intro n
  use Quotient.mk (grothendieckSetoid ℕ) (n.toNat, (-n).toNat)
  change ((n.toNat : ℕ) : ℤ) - (((-n).toNat : ℕ) : ℤ) = n
  exact n.toNat_sub_toNat_neg

/-- The dimension isomorphism computing `K₀(Spec F)` as `ℤ`. -/
noncomputable def grothendieckEquivInt : Grothendieck ℕ ≃+ ℤ :=
  AddEquiv.ofBijective grothendieckToInt
    ⟨grothendieckToInt_injective, grothendieckToInt_surjective⟩
