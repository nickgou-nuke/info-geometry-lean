import Mathlib.Tactic

/-!
# Intrinsic Peirce spaces and operator externalisation

This owner starts with two orthogonal idempotents and defines the two Peirce
off-diagonal spaces as subtypes.  Pair/triple expressions are retained as
functions until explicit closure hypotheses turn them into endomorphisms.
No coordinates, cross product, matrix representation, or Lie-algebra
identification is assumed.
-/

namespace InfoGeometry.Canonical

structure PeirceIdempotents (A : Type*) [Add A] [Mul A] [One A] [Zero A] where
  uPlus : A
  uMinus : A
  plus_sq : uPlus * uPlus = uPlus
  minus_sq : uMinus * uMinus = uMinus
  plus_minus : uPlus * uMinus = 0
  minus_plus : uMinus * uPlus = 0
  resolve_one : uPlus + uMinus = 1

namespace PeirceIdempotents

variable {A : Type*} [AddCommGroup A] [Mul A] [One A]
variable {P : PeirceIdempotents A}

def inVPlus (P : PeirceIdempotents A) (x : A) : Prop :=
  P.uPlus * x = x ∧ x * P.uMinus = x

def inVMinus (P : PeirceIdempotents A) (x : A) : Prop :=
  P.uMinus * x = x ∧ x * P.uPlus = x

def VPlus (P : PeirceIdempotents A) :=
  {x : A // inVPlus P x}

def VMinus (P : PeirceIdempotents A) :=
  {x : A // inVMinus P x}

def commutator (x y : A) : A := x * y - y * x

def jordanPolarization (x y : A) : A := x * y + y * x

def mixedProductPlusMinus (x : VPlus P) (y : VMinus P) : A := x.1 * y.1

def mixedProductMinusPlus (y : VMinus P) (x : VPlus P) : A := y.1 * x.1

def triplePlus (x : VPlus P) (y : VMinus P) (z : VPlus P) : A :=
  (x.1 * y.1) * z.1 + (z.1 * y.1) * x.1

def tripleMinus (y : VMinus P) (x : VPlus P) (w : VMinus P) : A :=
  (y.1 * x.1) * w.1 + (w.1 * x.1) * y.1

def kPlus (x z : VPlus P) (y : VMinus P) : A :=
  triplePlus x y z - triplePlus z y x

def kMinus (y w : VMinus P) (x : VPlus P) : A :=
  tripleMinus y x w - tripleMinus w x y

theorem commutator_eq_sub (x y : A) :
    commutator x y = x * y - y * x := rfl

theorem jordanPolarization_comm (x y : A) :
    jordanPolarization x y = jordanPolarization y x := by
  unfold jordanPolarization
  exact add_comm (x * y) (y * x)

theorem kPlus_antisymm (x z : VPlus P) (y : VMinus P) :
    kPlus x z y = -kPlus z x y := by
  simp [kPlus, sub_eq_add_neg, add_comm]

theorem kMinus_antisymm (y w : VMinus P) (x : VPlus P) :
    kMinus y w x = -kMinus w y x := by
  simp [kMinus, sub_eq_add_neg, add_comm]

theorem kPlus_eq_zero_of_outer_symmetric
    (houter : ∀ (x z : VPlus P) (y : VMinus P),
      triplePlus x y z = triplePlus z y x)
    (x z : VPlus P) (y : VMinus P) :
    kPlus x z y = 0 := by
  unfold kPlus
  rw [houter x z y]
  simp only [sub_self]

theorem kMinus_eq_zero_of_outer_symmetric
    (houter : ∀ (y w : VMinus P) (x : VPlus P),
      tripleMinus y x w = tripleMinus w x y)
    (y w : VMinus P) (x : VPlus P) :
    kMinus y w x = 0 := by
  unfold kMinus
  rw [houter y w x]
  simp only [sub_self]

def dPlus
    (hclosed : ∀ (x : VPlus P) (y : VMinus P) (z : VPlus P),
      inVPlus P (triplePlus x y z))
    (x : VPlus P) (y : VMinus P) : VPlus P → VPlus P :=
  fun z => ⟨triplePlus x y z, hclosed x y z⟩

def dMinus
    (hclosed : ∀ (y : VMinus P) (x : VPlus P) (w : VMinus P),
      inVMinus P (tripleMinus y x w))
    (y : VMinus P) (x : VPlus P) : VMinus P → VMinus P :=
  fun w => ⟨tripleMinus y x w, hclosed y x w⟩

def pairOperatorSeedsPlus
    (hclosed : ∀ (x : VPlus P) (y : VMinus P) (z : VPlus P),
      inVPlus P (triplePlus x y z)) : Set (VPlus P → VPlus P) :=
  Set.range (fun xy : VPlus P × VMinus P => dPlus hclosed xy.1 xy.2)

def pairOperatorSeedsMinus
    (hclosed : ∀ (y : VMinus P) (x : VPlus P) (w : VMinus P),
      inVMinus P (tripleMinus y x w)) : Set (VMinus P → VMinus P) :=
  Set.range (fun yx : VMinus P × VPlus P => dMinus hclosed yx.1 yx.2)

end PeirceIdempotents

end InfoGeometry.Canonical
