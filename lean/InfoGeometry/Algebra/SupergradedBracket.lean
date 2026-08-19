import InfoGeometry.Algebra.InvariantTransport

/-!
# Supergraded brackets

This file gives the algebraic superbracket used by the finite-stage and
finite-to-infinite induction lanes.

The parity input is explicit (`Bool`): `true` means odd and `false` means even.
Thus the superbracket is the ordinary commutator except in the odd--odd case,
where it is the anticommutator.  No completion, analytic limit, or hidden
proof-carrying packet is introduced.
-/

namespace InfoGeometry.Algebra.SupergradedBracket

universe u

/-- Associative commutator. -/
abbrev commutator {A : Type u} [Mul A] [Sub A] (x y : A) : A :=
  InfoGeometry.Algebra.InvariantTransport.commutator x y

/-- Odd--odd anticommutator. -/
abbrev anticommutator {A : Type u} [Mul A] [Add A] (x y : A) : A :=
  InfoGeometry.Algebra.InvariantTransport.anticommutator x y

/--
The parity-controlled superbracket.

`true` denotes odd parity.  Odd--odd brackets are anticommutators; all other
parity combinations are ordinary commutators.
-/
def superBracket {A : Type u} [Mul A] [Add A] [Sub A]
    (px py : Bool) (x y : A) : A :=
  if px && py then anticommutator x y else commutator x y

def parityAdd (p q : Bool) : Bool := Bool.xor p q

@[simp] theorem parityAdd_false_left (p : Bool) :
    parityAdd false p = p := by
  cases p <;> rfl

@[simp] theorem parityAdd_false_right (p : Bool) :
    parityAdd p false = p := by
  cases p <;> rfl

theorem parityAdd_comm (p q : Bool) :
    parityAdd p q = parityAdd q p := by
  cases p <;> cases q <;> rfl

theorem parityAdd_assoc (p q r : Bool) :
    parityAdd (parityAdd p q) r = parityAdd p (parityAdd q r) := by
  cases p <;> cases q <;> cases r <;> rfl

@[simp]
theorem superBracket_odd_odd {A : Type u} [Mul A] [Add A] [Sub A] (x y : A) :
    superBracket true true x y = anticommutator x y := by
  rfl

@[simp]
theorem superBracket_even_left {A : Type u} [Mul A] [Add A] [Sub A]
    (py : Bool) (x y : A) :
    superBracket false py x y = commutator x y := by
  cases py <;> rfl

@[simp]
theorem superBracket_even_right {A : Type u} [Mul A] [Add A] [Sub A]
    (px : Bool) (x y : A) :
    superBracket px false x y = commutator x y := by
  cases px <;> rfl

variable {A B : Type u} [Ring A] [Ring B]

/-- Ring homomorphisms preserve commutators. -/
theorem map_commutator (φ : A →+* B) (x y : A) :
    φ (commutator x y) = commutator (φ x) (φ y) := by
  exact (InvariantTransport.commutator_transport φ x y).symm

/-- Ring homomorphisms preserve odd--odd anticommutators. -/
theorem map_anticommutator (φ : A →+* B) (x y : A) :
    φ (anticommutator x y) = anticommutator (φ x) (φ y) := by
  exact (InvariantTransport.anticommutator_transport φ x y).symm

theorem superBracket_jacobi
    {A : Type u} [Ring A] (p q r : Bool) (x y z : A) :
    (if p && r then -1 else 1) *
          superBracket p (parityAdd q r) x
            (superBracket q r y z) +
      (if q && p then -1 else 1) *
          superBracket q (parityAdd r p) y
            (superBracket r p z x) +
      (if r && q then -1 else 1) *
          superBracket r (parityAdd p q) z
            (superBracket p q x y) = 0 := by
  cases p <;> cases q <;> cases r <;>
    simp [superBracket, parityAdd, commutator, anticommutator,
      InvariantTransport.commutator, InvariantTransport.anticommutator] <;>
    noncomm_ring

/-- Ring homomorphisms preserve parity-controlled superbrackets. -/
theorem map_superBracket (φ : A →+* B) (px py : Bool) (x y : A) :
    φ (superBracket px py x y) = superBracket px py (φ x) (φ y) := by
  cases px <;> cases py <;> simp [superBracket, map_commutator, map_anticommutator]

/-- Actual homogeneity for a grading automorphism, not merely a parity label. -/
def IsHomogeneous {A : Type u} [Ring A]
    (γ : A →+* A) (p : Bool) (x : A) : Prop :=
  γ x = if p then -x else x

theorem isHomogeneous_even_iff {A : Type u} [Ring A]
    (γ : A →+* A) (x : A) :
    IsHomogeneous γ false x ↔ γ x = x := by
  simp [IsHomogeneous]

theorem isHomogeneous_odd_iff {A : Type u} [Ring A]
    (γ : A →+* A) (x : A) :
    IsHomogeneous γ true x ↔ γ x = -x := by
  simp [IsHomogeneous]

theorem map_isHomogeneous
    {A B : Type u} [Ring A] [Ring B]
    (γA : A →+* A) (γB : B →+* B) (φ : A →+* B)
    (hγ : ∀ x, γB (φ x) = φ (γA x))
    {p : Bool} {x : A}
    (hx : IsHomogeneous γA p x) :
    IsHomogeneous γB p (φ x) := by
  unfold IsHomogeneous at hx ⊢
  rw [hγ, hx]
  cases p <;> simp

/-- Superbracket transport in the direction convenient for image calculations. -/
theorem superBracket_transport (φ : A →+* B) (px py : Bool) (x y : A) :
    superBracket px py (φ x) (φ y) = φ (superBracket px py x y) := by
  exact (map_superBracket φ px py x y).symm

theorem superBracket_label_swap
    (px py : Bool) (x y : A) :
    superBracket px py x y =
      if px && py then superBracket py px y x else -superBracket py px y x := by
  cases px <;> cases py <;>
    simp [superBracket, commutator, anticommutator,
      InvariantTransport.commutator, InvariantTransport.anticommutator,
      sub_eq_add_neg] <;>
    first | noncomm_ring | abel

/-- A finite superbracket identity transports through a ring homomorphism. -/
theorem superBracket_eq_transport
    (φ : A →+* B) {px py : Bool} {x y z : A}
    (h : superBracket px py x y = z) :
    superBracket px py (φ x) (φ y) = φ z := by
  rw [superBracket_transport, h]

/-- A zero superbracket identity transports through a ring homomorphism. -/
theorem superBracket_zero_transport
    (φ : A →+* B) {px py : Bool} {x y : A}
    (h : superBracket px py x y = 0) :
    superBracket px py (φ x) (φ y) = 0 := by
  rw [superBracket_transport, h, map_zero]

section Chain

variable {Stage : Nat → Type u} [∀ n : Nat, Ring (Stage n)]

/-- Stagewise superbracket closure for transported homogeneous elements. -/
def SuperBracketClosureAt
    (px py : Bool)
    (X Y Z : ∀ n : Nat, Stage n) (n : Nat) : Prop :=
  superBracket px py (X n) (Y n) = Z n

/-- One-step preservation of a superbracket closure relation. -/
theorem superBracketClosure_step
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (px py : Bool)
    (X Y Z : ∀ n : Nat, Stage n)
    (n : Nat)
    (hX : bond n (X n) = X (n + 1))
    (hY : bond n (Y n) = Y (n + 1))
    (hZ : bond n (Z n) = Z (n + 1))
    (h : SuperBracketClosureAt px py X Y Z n) :
    SuperBracketClosureAt px py X Y Z (n + 1) := by
  unfold SuperBracketClosureAt at h ⊢
  rw [← hX, ← hY, ← hZ]
  exact superBracket_eq_transport (bond n) h

/-- Finite induction of a superbracket closure relation along a ring-hom chain. -/
theorem superBracketClosure_all
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (px py : Bool)
    (X Y Z : ∀ n : Nat, Stage n)
    (h0 : SuperBracketClosureAt px py X Y Z 0)
    (hX : ∀ n, bond n (X n) = X (n + 1))
    (hY : ∀ n, bond n (Y n) = Y (n + 1))
    (hZ : ∀ n, bond n (Z n) = Z (n + 1)) :
    ∀ n : Nat, SuperBracketClosureAt px py X Y Z n := by
  intro n
  induction n with
  | zero =>
      exact h0
  | succ n ih =>
      exact superBracketClosure_step bond px py X Y Z n (hX n) (hY n) (hZ n) ih

end Chain

end InfoGeometry.Algebra.SupergradedBracket
