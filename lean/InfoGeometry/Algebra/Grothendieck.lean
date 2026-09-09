import Mathlib.Tactic
open Setoid

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

universe u
variable {M : Type u} [AddCommMonoid M]

/-! ## Equivalence relation -/

def GrothendieckRel (x y : M × M) : Prop := ∃ k : M, x.1 + y.2 + k = x.2 + y.1 + k

theorem grothendieck_refl (x : M × M) : GrothendieckRel x x := by
  use 0; simp [add_comm]

theorem grothendieck_symm {x y : M × M} (h : GrothendieckRel x y) : GrothendieckRel y x := by
  rcases h with ⟨k, hk⟩; use k
  calc
    y.1 + x.2 + k = x.2 + y.1 + k := by simp [add_comm, add_left_comm, add_assoc]
    _ = x.1 + y.2 + k := by rw [hk]
    _ = y.2 + x.1 + k := by simp [add_comm, add_left_comm, add_assoc]

theorem grothendieck_trans {x y z : M × M} (h1 : GrothendieckRel x y) (h2 : GrothendieckRel y z) : GrothendieckRel x z := by
  rcases h1 with ⟨k1, hk1⟩; rcases h2 with ⟨k2, hk2⟩
  use k1 + k2 + y.1 + y.2
  calc
    x.1 + z.2 + (k1 + k2 + y.1 + y.2) = (x.1 + y.2 + k1) + (y.1 + z.2 + k2) := by abel
    _ = (x.2 + y.1 + k1) + (y.2 + z.1 + k2) := by rw [hk1, hk2]
    _ = x.2 + z.1 + (k1 + k2 + y.1 + y.2) := by abel

def grothendieckSetoid (M : Type u) [AddCommMonoid M] : Setoid (M × M) where
  r := GrothendieckRel
  iseqv := {
    refl := grothendieck_refl
    symm := λ {x y} h => grothendieck_symm h
    trans := λ {x y z} h1 h2 => grothendieck_trans h1 h2
  }

def Grothendieck (M : Type u) [AddCommMonoid M] : Type u := Quotient (grothendieckSetoid M)

/-! ## Group operations -/

theorem grothendieck_add_compat {x1 x2 y1 y2 : M × M} (hx : GrothendieckRel x1 x2) (hy : GrothendieckRel y1 y2) :
    GrothendieckRel (x1.1 + y1.1, x1.2 + y1.2) (x2.1 + y2.1, x2.2 + y2.2) := by
  rcases hx with ⟨k1, hk1⟩; rcases hy with ⟨k2, hk2⟩
  use k1 + k2
  calc
    (x1.1 + y1.1) + (x2.2 + y2.2) + (k1 + k2) = (x1.1 + x2.2 + k1) + (y1.1 + y2.2 + k2) := by
      simp [add_comm, add_left_comm, add_assoc]
    _ = (x1.2 + x2.1 + k1) + (y1.2 + y2.1 + k2) := by rw [hk1, hk2]
    _ = (x1.2 + y1.2) + (x2.1 + y2.1) + (k1 + k2) := by
      simp [add_comm, add_left_comm, add_assoc]

def grothendieckAdd : Grothendieck M → Grothendieck M → Grothendieck M :=
  Quotient.map₂ (fun (x y : M × M) => (x.1 + y.1, x.2 + y.2))
    (by intro a b ha c d hc; exact grothendieck_add_compat ha hc)

def grothendieckZero : Grothendieck M := Quotient.mk (grothendieckSetoid M) (0, 0)

theorem grothendieck_neg_compat {x y : M × M} (h : GrothendieckRel x y) : GrothendieckRel (x.2, x.1) (y.2, y.1) := by
  rcases h with ⟨k, hk⟩; use k
  calc
    (x.2, x.1).1 + (y.2, y.1).2 + k = x.2 + y.1 + k := rfl
    _ = x.1 + y.2 + k := by rw [← hk]
    _ = (x.2, x.1).2 + (y.2, y.1).1 + k := rfl

def grothendieckNeg : Grothendieck M → Grothendieck M :=
  Quotient.map (fun (x : M × M) => (x.2, x.1))
    (by intro a b h; exact grothendieck_neg_compat h)

/-! ## Group axioms -/

theorem grothendieck_add_assoc (a b c : Grothendieck M) :
    grothendieckAdd (grothendieckAdd a b) c = grothendieckAdd a (grothendieckAdd b c) := by
  refine Quotient.inductionOn₃ (s₁ := grothendieckSetoid M) (s₂ := grothendieckSetoid M)
    (s₃ := grothendieckSetoid M) a b c ?_
  intro x y z
  apply Quotient.sound
  use 0
  simp [add_comm, add_left_comm, add_assoc]

theorem grothendieck_add_comm (a b : Grothendieck M) :
    grothendieckAdd a b = grothendieckAdd b a := by
  refine Quotient.inductionOn₂ (s₁ := grothendieckSetoid M) (s₂ := grothendieckSetoid M) a b ?_
  intro x y
  apply Quotient.sound
  use 0
  simp [add_comm, add_left_comm, add_assoc]

theorem grothendieck_zero_add (a : Grothendieck M) :
    grothendieckAdd grothendieckZero a = a := by
  refine Quotient.inductionOn (s := grothendieckSetoid M) a ?_
  intro x
  apply Quotient.sound
  use 0
  simp [add_comm, add_left_comm, add_assoc]

theorem grothendieck_add_zero (a : Grothendieck M) :
    grothendieckAdd a grothendieckZero = a := by
  refine Quotient.inductionOn (s := grothendieckSetoid M) a ?_
  intro x
  apply Quotient.sound
  use 0
  simp [add_comm, add_left_comm, add_assoc]

theorem grothendieck_add_left_neg (a : Grothendieck M) :
    grothendieckAdd (grothendieckNeg a) a = grothendieckZero := by
  refine Quotient.inductionOn (s := grothendieckSetoid M) a ?_
  intro x
  apply Quotient.sound
  use 0
  simp [add_comm, add_left_comm, add_assoc]

/-! ## AddCommGroup instance -/

instance : AddCommGroup (Grothendieck M) where
  add := grothendieckAdd
  add_assoc := grothendieck_add_assoc
  zero := grothendieckZero
  zero_add := grothendieck_zero_add
  add_zero := grothendieck_add_zero
  neg := grothendieckNeg
  add_comm := grothendieck_add_comm
  neg_add_cancel := grothendieck_add_left_neg
  nsmul := λ n a => (Nat.rec grothendieckZero (λ _ ih => grothendieckAdd ih a) n : Grothendieck M)
  nsmul_zero := λ a => rfl
  nsmul_succ := λ n a => rfl
  zsmul := λ z a =>
    match z with
    | Int.ofNat n => (Nat.rec grothendieckZero (λ _ ih => grothendieckAdd ih a) n : Grothendieck M)
    | Int.negSucc n => grothendieckNeg (Nat.rec grothendieckZero (λ _ ih => grothendieckAdd ih a) (n+1) : Grothendieck M)
  zsmul_zero' := λ a => rfl
  zsmul_succ' := λ n a => rfl
  zsmul_neg' := λ n a => rfl

/-! ## Canonical monoid homomorphism -/

/-- The canonical additive monoid homomorphism from M into its Grothendieck group. -/
def grothendieckMap (M : Type u) [AddCommMonoid M] : M →+ Grothendieck M where
  toFun m := Quotient.mk (grothendieckSetoid M) (m, 0)
  map_zero' := rfl
  map_add' x y := by
    apply Quotient.sound
    use 0
    simp

/-- `mk (a, 0) - mk (b, 0) = mk (a, b)` in the Grothendieck group. -/
theorem grothendieck_sub_mk (a b : M) :
    grothendieckMap M a - grothendieckMap M b = Quotient.mk (grothendieckSetoid M) (a, b) := by
  apply Quotient.sound
  use 0
  simp [add_comm, add_left_comm, add_assoc]

/-! ## Universal property -/

theorem g_raw_compat {A : Type*} [AddCommGroup A] (f : M →+ A) {x y : M × M} (h : GrothendieckRel x y) :
    f x.1 - f x.2 = f y.1 - f y.2 := by
  rcases h with ⟨k, hk⟩
  have h_cancel : f x.1 + f y.2 = f x.2 + f y.1 := by
    calc
      f x.1 + f y.2 = (f x.1 + f y.2 + f k) - f k := by abel
      _ = (f (x.1 + y.2 + k)) - f k := by simp
      _ = (f (x.2 + y.1 + k)) - f k := by rw [hk]
      _ = (f x.2 + f y.1 + f k) - f k := by simp
      _ = f x.2 + f y.1 := by abel
  calc
    f x.1 - f x.2 = (f x.1 + f y.2) - f y.2 - f x.2 := by abel
    _ = (f x.2 + f y.1) - f y.2 - f x.2 := by rw [h_cancel]
    _ = f y.1 - f y.2 := by abel

def grothendieckLift {A : Type*} [AddCommGroup A] (f : M →+ A) : Grothendieck M →+ A where
  toFun := Quotient.lift (s := grothendieckSetoid M) (fun (x : M × M) => f x.1 - f x.2)
    (by intro x y h; apply g_raw_compat f; exact h)
  map_zero' := by
    calc
      (Quotient.lift (fun (x : M × M) => f x.1 - f x.2) (by intro x y h; apply g_raw_compat f; exact h)) (0 : Grothendieck M)
          = (Quotient.lift (fun (x : M × M) => f x.1 - f x.2) (by intro x y h; apply g_raw_compat f; exact h)) grothendieckZero := rfl
      _ = f (0 : M) - f (0 : M) := rfl
      _ = (0 : A) - (0 : A) := by simp
      _ = (0 : A) := by simp
  map_add' a b := by
    refine Quotient.inductionOn₂ (s₁ := grothendieckSetoid M) (s₂ := grothendieckSetoid M) a b ?_
    intro x y
    let X : Grothendieck M := Quotient.mk (grothendieckSetoid M) x
    let Y : Grothendieck M := Quotient.mk (grothendieckSetoid M) y
    let L := Quotient.lift (s := grothendieckSetoid M) (fun (x : M × M) => f x.1 - f x.2) (by intro x y h; apply g_raw_compat f; exact h)
    have h1 : L (X + Y) = L (grothendieckAdd X Y) := rfl
    have h2 : L (grothendieckAdd X Y) = L (Quotient.mk (grothendieckSetoid M) (x.1 + y.1, x.2 + y.2)) := rfl
    have h3 : L (Quotient.mk (grothendieckSetoid M) (x.1 + y.1, x.2 + y.2)) = f (x.1 + y.1) - f (x.2 + y.2) := rfl
    have h4 : L X = f x.1 - f x.2 := rfl
    have h5 : L Y = f y.1 - f y.2 := rfl
    calc
      L (X + Y) = L (grothendieckAdd X Y) := by simpa using h1
      _ = L (Quotient.mk (grothendieckSetoid M) (x.1 + y.1, x.2 + y.2)) := by simpa using h2
      _ = f (x.1 + y.1) - f (x.2 + y.2) := by simpa using h3
      _ = (f x.1 - f x.2) + (f y.1 - f y.2) := by
        simp; abel
      _ = L X + L Y := by simp [h4, h5]

theorem grothendieckLift_comp {A : Type*} [AddCommGroup A] (f : M →+ A) (m : M) :
    grothendieckLift f (grothendieckMap M m) = f m := by
  simp [grothendieckMap, grothendieckLift]

/-- Every element of the Grothendieck group is a difference of images of the canonical map. -/
theorem grothendieck_eq_sub (x : Grothendieck M) : ∃ a b : M, x = grothendieckMap M a - grothendieckMap M b := by
  refine Quotient.inductionOn (s := grothendieckSetoid M) x ?_
  intro y
  refine ⟨y.1, y.2, ?_⟩
  rw [← grothendieck_sub_mk y.1 y.2]

theorem grothendieckLift_unique {A : Type*} [AddCommGroup A] (f : M →+ A) (g : Grothendieck M →+ A)
    (h_comp : ∀ m, g (grothendieckMap M m) = f m) (x : Grothendieck M) : g x = grothendieckLift f x := by
  rcases grothendieck_eq_sub x with ⟨a, b, hx⟩
  rw [hx, map_sub, map_sub, h_comp a, h_comp b, grothendieckLift_comp f a, grothendieckLift_comp f b]

/-! ## Equivalence to cancellation property -/

def IsCancellationMonoid (M : Type u) [AddCommMonoid M] : Prop :=
  ∀ a b c : M, a + c = b + c → a = b

theorem grothendieckMap_injective_of_cancellation (h_cancel : IsCancellationMonoid M) :
    Function.Injective (grothendieckMap M) := by
  intro a b hab
  have h_rel : GrothendieckRel (a, 0) (b, 0) := Quotient.exact (by
    simpa [grothendieckMap] using hab)
  rcases h_rel with ⟨k, hk⟩
  have h_simp : a + k = b + k := by
    simpa [add_comm, add_left_comm, add_assoc] using hk
  exact h_cancel a b k h_simp

theorem cancellation_of_grothendieckMap_injective (h_inj : Function.Injective (grothendieckMap M)) :
    IsCancellationMonoid M := by
  intro a b c hab
  have h_rel : GrothendieckRel (a, 0) (b, 0) := by
    use c
    calc
      (a, 0).1 + (b, 0).2 + c = a + 0 + c := rfl
      _ = a + c := by simp
      _ = b + c := by rw [hab]
      _ = 0 + b + c := by simp
      _ = (a, 0).2 + (b, 0).1 + c := rfl
  have h_eq : grothendieckMap M a = grothendieckMap M b := by
    apply Quotient.sound; exact h_rel
  exact h_inj h_eq

theorem grothendieckMap_injective_iff_cancellation :
    Function.Injective (grothendieckMap M) ↔ IsCancellationMonoid M := by
  constructor
  · exact cancellation_of_grothendieckMap_injective
  · exact grothendieckMap_injective_of_cancellation

/-! ## K₀(Spec F) ≅ ℤ -/

section grothendieckNat

def to_int_raw (x : ℕ × ℕ) : ℤ := (x.1 : ℤ) - (x.2 : ℤ)

theorem to_int_raw_compat {x y : ℕ × ℕ} (h : GrothendieckRel x y) : to_int_raw x = to_int_raw y := by
  dsimp [to_int_raw]
  rcases h with ⟨k, hk⟩
  have h_cast := congrArg (fun (n : ℕ) => (n : ℤ)) hk
  push_cast at h_cast
  omega

def grothendieckToInt : Grothendieck ℕ →+ ℤ where
  toFun := Quotient.lift (s := grothendieckSetoid ℕ) to_int_raw (by
    intro x y h; apply to_int_raw_compat; exact h)
  map_zero' := by
    calc
      (Quotient.lift (s := grothendieckSetoid ℕ) to_int_raw (by intro x y h; apply to_int_raw_compat; exact h)) (0 : Grothendieck ℕ)
          = (Quotient.lift (s := grothendieckSetoid ℕ) to_int_raw (by intro x y h; apply to_int_raw_compat; exact h)) grothendieckZero := rfl
      _ = to_int_raw (0, 0) := rfl
      _ = (0 : ℤ) := by simp [to_int_raw]
  map_add' a b := by
    refine Quotient.inductionOn₂ (s₁ := grothendieckSetoid ℕ) (s₂ := grothendieckSetoid ℕ) a b ?_
    intro x y
    let X : Grothendieck ℕ := Quotient.mk (grothendieckSetoid ℕ) x
    let Y : Grothendieck ℕ := Quotient.mk (grothendieckSetoid ℕ) y
    let L := Quotient.lift (s := grothendieckSetoid ℕ) to_int_raw (by intro x y h; apply to_int_raw_compat; exact h)
    have h1 : L (X + Y) = L (grothendieckAdd X Y) := rfl
    have h2 : L (grothendieckAdd X Y) = L (Quotient.mk (grothendieckSetoid ℕ) (x.1 + y.1, x.2 + y.2)) := rfl
    have h3 : L (Quotient.mk (grothendieckSetoid ℕ) (x.1 + y.1, x.2 + y.2)) = to_int_raw (x.1 + y.1, x.2 + y.2) := rfl
    have h_to_int : to_int_raw (x.1 + y.1, x.2 + y.2) = ((x.1 : ℤ) - (x.2 : ℤ)) + ((y.1 : ℤ) - (y.2 : ℤ)) := by
      dsimp [to_int_raw]
      ring
    have hLX : L X = to_int_raw (x.1, x.2) := rfl
    have hLY : L Y = to_int_raw (y.1, y.2) := rfl
    calc
      L (X + Y) = L (grothendieckAdd X Y) := by simpa using h1
      _ = L (Quotient.mk (grothendieckSetoid ℕ) (x.1 + y.1, x.2 + y.2)) := by simpa using h2
      _ = to_int_raw (x.1 + y.1, x.2 + y.2) := by simpa using h3
      _ = ((x.1 : ℤ) - (x.2 : ℤ)) + ((y.1 : ℤ) - (y.2 : ℤ)) := by simpa using h_to_int
      _ = to_int_raw (x.1, x.2) + to_int_raw (y.1, y.2) := by simp [to_int_raw]
      _ = L X + L Y := by simp [hLX, hLY]

theorem grothendieckToInt_injective : Function.Injective grothendieckToInt := by
  intro a b hab
  revert hab
  refine Quotient.inductionOn₂ (s₁ := grothendieckSetoid ℕ) (s₂ := grothendieckSetoid ℕ) a b ?_
  intro x y h
  have h_eq_int : (x.1 : ℤ) - (x.2 : ℤ) = (y.1 : ℤ) - (y.2 : ℤ) := by
    simpa [grothendieckToInt] using h
  apply Quotient.sound
  use 0
  rw [add_zero, add_zero]
  apply (Nat.cast_inj (R := ℤ)).mp
  have h_int : (x.1 + y.2 : ℤ) = (x.2 + y.1 : ℤ) := by
    linarith
  simpa using h_int

theorem grothendieckToInt_surjective : Function.Surjective grothendieckToInt := by
  intro n
  use Quotient.mk (grothendieckSetoid ℕ) (n.toNat, (-n).toNat)
  simp [grothendieckToInt, to_int_raw]

/-- K₀(Spec F) ≅ ℤ via the Grothendieck group of ℕ. -/
noncomputable def grothendieckEquivInt : Grothendieck ℕ ≃+ ℤ :=
  AddEquiv.ofBijective grothendieckToInt ⟨grothendieckToInt_injective, grothendieckToInt_surjective⟩

end grothendieckNat

/-! ## Functoriality -/

section functoriality

variable {N P : Type u} [AddCommMonoid N] [AddCommMonoid P]

/-- The induced group homomorphism on Grothendieck groups from a monoid homomorphism. -/
def grothendieckFunctor (f : M →+ N) : Grothendieck M →+ Grothendieck N :=
  grothendieckLift ((grothendieckMap N).comp f)

theorem grothendieckFunctor_mk (f : M →+ N) (x : M × M) :
    grothendieckFunctor f (Quotient.mk (grothendieckSetoid M) x) =
      Quotient.mk (grothendieckSetoid N) (f x.1, f x.2) := by
  simpa [grothendieckFunctor, grothendieckLift, grothendieckMap] using grothendieck_sub_mk (f x.1) (f x.2)

theorem grothendieckFunctor_id : grothendieckFunctor (AddMonoidHom.id M) = AddMonoidHom.id (Grothendieck M) := by
  ext x
  calc
    grothendieckFunctor (AddMonoidHom.id M) x = grothendieckLift ((grothendieckMap M).comp (AddMonoidHom.id M)) x := rfl
    _ = grothendieckLift (grothendieckMap M) x := by simp
    _ = (AddMonoidHom.id (Grothendieck M)) x := by
      symm; apply grothendieckLift_unique (grothendieckMap M) (AddMonoidHom.id (Grothendieck M)) (by simp) x

theorem grothendieckFunctor_comp (f : M →+ N) (g : N →+ P) :
    grothendieckFunctor (g.comp f) = (grothendieckFunctor g).comp (grothendieckFunctor f) := by
  ext x
  calc
    grothendieckFunctor (g.comp f) x = grothendieckLift ((grothendieckMap P).comp (g.comp f)) x := rfl
    _ = ((grothendieckFunctor g).comp (grothendieckFunctor f)) x := by
      symm
      apply grothendieckLift_unique ((grothendieckMap P).comp (g.comp f))
        ((grothendieckFunctor g).comp (grothendieckFunctor f))
        (by
          intro m
          calc
            ((grothendieckFunctor g).comp (grothendieckFunctor f)) (grothendieckMap M m)
                = grothendieckFunctor g (grothendieckFunctor f (grothendieckMap M m)) := rfl
            _ = grothendieckFunctor g (grothendieckMap N (f m)) := by
              simp [grothendieckFunctor_mk, grothendieckMap]
            _ = grothendieckMap P (g (f m)) := by
              simp [grothendieckFunctor_mk, grothendieckMap]
            _ = ((grothendieckMap P).comp (g.comp f)) m := by simp)
        x

end functoriality
