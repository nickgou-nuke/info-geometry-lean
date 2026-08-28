import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.FiniteInvariantTransport

Finite-stage invariant transport.

This file proves concrete preservation lemmas for finite inductive chains of
operator algebras.

No structures.
No wrappers.
No colimit claim.
No placeholder proofs.

The point is simple:

If each bonding map is a ring homomorphism, then the local operator identities
that define the finite cell are preserved at every finite transported stage.
-/

namespace InfoGeometry.Canonical.FiniteInvariantTransport

/-- Apply `k` consecutive finite-stage transition maps starting at stage `n`. -/
def chainApply {α : Type*} (next : Nat → α → α) (n : Nat) : Nat → α → α
  | 0, x => x
  | k + 1, x => next (n + k) (chainApply next n k x)

@[simp] theorem chainApply_zero {α : Type*}
    (next : Nat → α → α) (n : Nat) (x : α) :
    chainApply next n 0 x = x := rfl

@[simp] theorem chainApply_succ {α : Type*}
    (next : Nat → α → α) (n k : Nat) (x : α) :
    chainApply next n (k + 1) x =
      next (n + k) (chainApply next n k x) := rfl

theorem chainApply_add {α : Type*}
    (next : Nat → α → α) (n k l : Nat) (x : α) :
    chainApply next n (k + l) x =
      chainApply next (n + k) l (chainApply next n k x) := by
  induction l with
  | zero => simp [chainApply]
  | succ l ih =>
      simp [Nat.add_succ, chainApply, ih, Nat.add_assoc]

/--
Generic finite-chain predicate transport.

If `next n` sends stage-`n` invariants to stage-`n+1` invariants, then the
invariant holds after any finite number of steps.

This is the bare induction principle for finite operator stages.
-/
theorem invariant_preserved_along_finite_chain
    {α : Type*}
    (next : Nat → α → α)
    (Inv : Nat → α → Prop)
    (hnext : ∀ n x, Inv n x → Inv (n + 1) (next n x))
    (n k : Nat) (x : α)
    (hx : Inv n x) :
    Inv (n + k) (chainApply next n k x) := by
  induction k with
  | zero =>
      simpa [chainApply] using hx
  | succ k ih =>
      simpa [chainApply, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hnext (n + k) (chainApply next n k x) ih

theorem chainApply_add_preserved
    {A : Type*} [Semiring A]
    (φ : Nat → A →+* A)
    (n k : Nat) (x y : A) :
    chainApply (fun i a => φ i a) n k (x + y) =
      chainApply (fun i a => φ i a) n k x +
        chainApply (fun i a => φ i a) n k y := by
  induction k with
  | zero => simp [chainApply]
  | succ k ih =>
      simp [chainApply, ih, map_add]

theorem chainApply_mul_preserved
    {A : Type*} [Semiring A]
    (φ : Nat → A →+* A)
    (n k : Nat) (x y : A) :
    chainApply (fun i a => φ i a) n k (x * y) =
      chainApply (fun i a => φ i a) n k x *
        chainApply (fun i a => φ i a) n k y := by
  induction k with
  | zero => simp [chainApply]
  | succ k ih =>
      simp [chainApply, ih, map_mul]

theorem chainApply_neg_preserved
    {A : Type*} [Ring A]
    (φ : Nat → A →+* A)
    (n k : Nat) (x : A) :
    chainApply (fun i a => φ i a) n k (-x) =
      -chainApply (fun i a => φ i a) n k x := by
  induction k with
  | zero => simp [chainApply]
  | succ k ih =>
      simp [chainApply, ih, map_neg]

theorem chainApply_sub_preserved
    {A : Type*} [Ring A]
    (φ : Nat → A →+* A)
    (n k : Nat) (x y : A) :
    chainApply (fun i a => φ i a) n k (x - y) =
      chainApply (fun i a => φ i a) n k x -
        chainApply (fun i a => φ i a) n k y := by
  induction k with
  | zero => simp [chainApply]
  | succ k ih =>
      simp [chainApply, ih, map_sub]

theorem chainApply_zero_preserved
    {A : Type*} [Semiring A]
    (φ : Nat → A →+* A)
    (n k : Nat) :
    chainApply (fun i a => φ i a) n k 0 = 0 := by
  induction k with
  | zero => simp [chainApply]
  | succ k ih =>
      simp [chainApply, ih]

theorem chainApply_one_preserved
    {A : Type*} [Semiring A]
    (φ : Nat → A →+* A)
    (n k : Nat) :
    chainApply (fun i a => φ i a) n k 1 = 1 := by
  induction k with
  | zero => simp [chainApply]
  | succ k ih =>
      simp [chainApply, ih]

/-! ## Inner derivations along a finite stage chain -/

/-- A compatible generator family transports its commutator action through
    every finite composite of the bonding ring homomorphisms. -/
theorem chainApply_commutator_preserved
    {A : Type*} [Ring A]
    (φ : Nat → A →+* A) (K : Nat → A)
    (hK : ∀ n, φ n (K n) = K (n + 1))
    (n k : Nat) (X : A) :
    chainApply (fun i a => φ i a) n k (K n * X - X * K n) =
      K (n + k) * chainApply (fun i a => φ i a) n k X -
        chainApply (fun i a => φ i a) n k X * K (n + k) := by
  induction k with
  | zero => simp [chainApply]
  | succ k ih =>
      simp only [chainApply]
      rw [ih, map_sub, map_mul, map_mul, hK (n + k)]
      simp only [Nat.add_assoc]

/--
Square-zero/nilpotent identity is preserved along a finite chain of ring
homomorphisms.

This is the finite transport theorem for odd/lightlike/nilpotent operators.
-/
theorem square_zero_preserved_along_ringHom_chain
    {A : Type*} [Semiring A]
    (φ : Nat → A →+* A)
    (n k : Nat) {q : A}
    (hq : q * q = 0) :
    chainApply (fun i x => φ i x) n k q *
      chainApply (fun i x => φ i x) n k q = 0 := by
  induction k with
  | zero =>
      simpa [chainApply] using hq
  | succ k ih =>
      calc
        φ (n + k) (chainApply (fun i x => φ i x) n k q) *
            φ (n + k) (chainApply (fun i x => φ i x) n k q)
            =
          φ (n + k)
            (chainApply (fun i x => φ i x) n k q *
             chainApply (fun i x => φ i x) n k q) := by
              rw [map_mul]
        _ = φ (n + k) 0 := by
              rw [ih]
        _ = 0 := by
              simp

/--
Idempotency is preserved along a finite chain of ring homomorphisms.

This is the finite transport theorem for projectors/sectors.
-/
theorem idempotent_preserved_along_ringHom_chain
    {A : Type*} [Semiring A]
    (φ : Nat → A →+* A)
    (n k : Nat) {p : A}
    (hp : p * p = p) :
    chainApply (fun i x => φ i x) n k p *
      chainApply (fun i x => φ i x) n k p =
    chainApply (fun i x => φ i x) n k p := by
  induction k with
  | zero =>
      simpa [chainApply] using hp
  | succ k ih =>
      calc
        φ (n + k) (chainApply (fun i x => φ i x) n k p) *
            φ (n + k) (chainApply (fun i x => φ i x) n k p)
            =
          φ (n + k)
            (chainApply (fun i x => φ i x) n k p *
             chainApply (fun i x => φ i x) n k p) := by
              rw [map_mul]
        _ = φ (n + k) (chainApply (fun i x => φ i x) n k p) := by
              rw [ih]

/--
Orthogonality of two sector projectors is preserved along a finite chain of
ring homomorphisms.
-/
theorem orthogonal_preserved_along_ringHom_chain
    {A : Type*} [Semiring A]
    (φ : Nat → A →+* A)
    (n k : Nat) {p q : A}
    (hpq : p * q = 0) :
    chainApply (fun i x => φ i x) n k p *
      chainApply (fun i x => φ i x) n k q = 0 := by
  induction k with
  | zero =>
      simpa [chainApply] using hpq
  | succ k ih =>
      calc
        φ (n + k) (chainApply (fun i x => φ i x) n k p) *
            φ (n + k) (chainApply (fun i x => φ i x) n k q)
            =
          φ (n + k)
            (chainApply (fun i x => φ i x) n k p *
             chainApply (fun i x => φ i x) n k q) := by
              rw [map_mul]
        _ = φ (n + k) 0 := by
              rw [ih]
        _ = 0 := by
              simp

/--
A ring homomorphism preserves an anticommutator identity.

This is the one-step theorem for odd-odd closure:

  x y + y x = h.
-/
theorem ringHom_preserves_anticommutator
    {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+* B)
    {x y h : A}
    (hxy : x * y + y * x = h) :
    f x * f y + f y * f x = f h := by
  calc
    f x * f y + f y * f x
        = f (x * y) + f (y * x) := by
            rw [map_mul, map_mul]
    _   = f (x * y + y * x) := by
            rw [← map_add]
    _   = f h := by
            rw [hxy]

/--
A ring homomorphism preserves a commutator identity.

This is the one-step theorem for bracket/central-lane closure:

  x y - y x = c.
-/
theorem ringHom_preserves_commutator
    {A B : Type*} [Ring A] [Ring B]
    (f : A →+* B)
    {x y c : A}
    (hxy : x * y - y * x = c) :
    f x * f y - f y * f x = f c := by
  calc
    f x * f y - f y * f x
        = f (x * y) - f (y * x) := by
            rw [map_mul, map_mul]
    _   = f (x * y - y * x) := by
            rw [← map_sub]
    _   = f c := by
            rw [hxy]

/--
An anticommutator identity is preserved along a finite chain of ring
endomorphisms.

This is the finite-stage version of odd-odd closure transport.
-/
theorem anticommutator_preserved_along_ringHom_chain
    {A : Type*} [Semiring A]
    (φ : Nat → A →+* A)
    (n k : Nat) {x y h : A}
    (hxy : x * y + y * x = h) :
    chainApply (fun i a => φ i a) n k x *
        chainApply (fun i a => φ i a) n k y
      +
      chainApply (fun i a => φ i a) n k y *
        chainApply (fun i a => φ i a) n k x
        =
    chainApply (fun i a => φ i a) n k h := by
  induction k with
  | zero =>
      simpa [chainApply] using hxy
  | succ k ih =>
      calc
        φ (n + k) (chainApply (fun i a => φ i a) n k x) *
            φ (n + k) (chainApply (fun i a => φ i a) n k y)
          +
          φ (n + k) (chainApply (fun i a => φ i a) n k y) *
            φ (n + k) (chainApply (fun i a => φ i a) n k x)
            =
          φ (n + k)
            (chainApply (fun i a => φ i a) n k x *
                chainApply (fun i a => φ i a) n k y
              +
              chainApply (fun i a => φ i a) n k y *
                chainApply (fun i a => φ i a) n k x) := by
              rw [map_add, map_mul, map_mul]
        _ = φ (n + k) (chainApply (fun i a => φ i a) n k h) := by
              rw [ih]

/--
A commutator identity is preserved along a finite chain of ring endomorphisms.

This is the finite-stage version of central-lane/bracket transport.
-/
theorem commutator_preserved_along_ringHom_chain
    {A : Type*} [Ring A]
    (φ : Nat → A →+* A)
    (n k : Nat) {x y c : A}
    (hxy : x * y - y * x = c) :
    chainApply (fun i a => φ i a) n k x *
        chainApply (fun i a => φ i a) n k y
      -
      chainApply (fun i a => φ i a) n k y *
        chainApply (fun i a => φ i a) n k x
        =
    chainApply (fun i a => φ i a) n k c := by
  induction k with
  | zero =>
      simpa [chainApply] using hxy
  | succ k ih =>
      calc
        φ (n + k) (chainApply (fun i a => φ i a) n k x) *
            φ (n + k) (chainApply (fun i a => φ i a) n k y)
          -
          φ (n + k) (chainApply (fun i a => φ i a) n k y) *
            φ (n + k) (chainApply (fun i a => φ i a) n k x)
            =
          φ (n + k)
            (chainApply (fun i a => φ i a) n k x *
                chainApply (fun i a => φ i a) n k y
              -
              chainApply (fun i a => φ i a) n k y *
                chainApply (fun i a => φ i a) n k x) := by
              rw [map_sub, map_mul, map_mul]
        _ = φ (n + k) (chainApply (fun i a => φ i a) n k c) := by
              rw [ih]

end InfoGeometry.Canonical.FiniteInvariantTransport
