import Mathlib.Tactic

/-!
# InfoGeometry.Meta.InductiveInvariantPacket

Finite-stage invariance transport for supergraded operator closure packets.

This file does not construct an analytic colimit. It proves the finite
Erlangen-style rule:

  structure-preserving bonding maps transport local closure identities.

Global centrality in a larger target is not transported by an arbitrary
non-surjective embedding.  The unconditional theorem therefore proves
centrality on the image.  A separate theorem recovers global target centrality
when the bonding map is surjective.

The infinite limit requires a separate completion/continuity interface.
-/

namespace InfoGeometry.Meta.InductiveInvariantPacket

/--
A star-preserving ring homomorphism.

This is the minimal algebraic shape needed to transport identities involving
multiplication, addition, zero, one, subtraction, and the star/adjoint operation.
-/
structure StarRingHom
    (A B : Type*) [Ring A] [StarRing A] [Ring B] [StarRing B] where
  toRingHom : A →+* B
  map_star' : ∀ x : A, toRingHom (star x) = star (toRingHom x)

namespace StarRingHom

variable
    {A B : Type*} [Ring A] [StarRing A] [Ring B] [StarRing B]

instance : CoeFun (StarRingHom A B) (fun _ => A → B) where
  coe φ := φ.toRingHom

@[simp] theorem map_zero (φ : StarRingHom A B) :
    φ 0 = 0 :=
  φ.toRingHom.map_zero

@[simp] theorem map_one (φ : StarRingHom A B) :
    φ 1 = 1 :=
  φ.toRingHom.map_one

@[simp] theorem map_add (φ : StarRingHom A B) (x y : A) :
    φ (x + y) = φ x + φ y :=
  φ.toRingHom.map_add x y

@[simp] theorem map_mul (φ : StarRingHom A B) (x y : A) :
    φ (x * y) = φ x * φ y :=
  φ.toRingHom.map_mul x y

@[simp] theorem map_neg (φ : StarRingHom A B) (x : A) :
    φ (-x) = -φ x :=
  φ.toRingHom.map_neg x

@[simp] theorem map_sub (φ : StarRingHom A B) (x y : A) :
    φ (x - y) = φ x - φ y :=
  φ.toRingHom.map_sub x y

@[simp] theorem map_star (φ : StarRingHom A B) (x : A) :
    φ (star x) = star (φ x) :=
  φ.map_star' x

variable {C : Type*} [Ring C] [StarRing C]

/-- Identity star-preserving ring homomorphism. -/
def id (A : Type*) [Ring A] [StarRing A] : StarRingHom A A where
  toRingHom := RingHom.id A
  map_star' := by
    intro x
    rfl

/-- Composition of star-preserving ring homomorphisms. -/
def comp (ψ : StarRingHom B C) (φ : StarRingHom A B) : StarRingHom A C where
  toRingHom := ψ.toRingHom.comp φ.toRingHom
  map_star' := by
    intro x
    simp

/-- Apply a star-preserving endomorphism chain from stage index `n` for `k` steps. -/
def chain (φ : Nat → StarRingHom A A) (n : Nat) : Nat → StarRingHom A A
  | 0 => id A
  | k + 1 => comp (φ (n + k)) (chain φ n k)

@[simp] theorem chain_zero (φ : Nat → StarRingHom A A) (n : Nat) :
    chain φ n 0 = id A := by
  rfl

/-- Readback for one successor step of a finite star-hom chain. -/
theorem chain_succ_apply (φ : Nat → StarRingHom A A) (n k : Nat) (x : A) :
    chain φ n (k + 1) x = φ (n + k) (chain φ n k x) := by
  rfl

end StarRingHom

/--
Local supergraded closure packet.

This records only finite algebraic identities:
* odd nilpotency;
* even projector;
* odd-odd closure;
* parity/odd anticommutation;
* central-lane commutation inside the current finite stage.
-/
structure SupergradedClosureAt
    (A : Type*) [Ring A] [StarRing A] where
  /-- Odd hopping/supercharge lane. -/
  Q : A
  /-- Even Hamiltonian/projector/closure lane. -/
  H : A
  /-- Parity or sector projector. -/
  P : A
  /-- Central-defect lane. -/
  C : A
  /-- Odd square-zero condition. -/
  odd_sq_zero : Q * Q = 0
  /-- Even projector/idempotent condition. -/
  parity_idempotent : P * P = P
  /-- Odd-odd closure into the even lane. -/
  odd_odd_closure : Q * star Q + star Q * Q = H
  /-- Parity flips the odd lane. -/
  parity_odd_anticomm : P * Q + Q * P = 0
  /-- Central lane commutes with every element at this finite stage. -/
  central_commutes : ∀ X : A, C * X = X * C

namespace SupergradedClosureAt

variable
    {A B : Type*} [Ring A] [StarRing A] [Ring B] [StarRing B]

/-- Image-level centrality transported by a star-preserving bonding map. -/
def ImageCentral (I : SupergradedClosureAt A) (φ : StarRingHom A B) : Prop :=
  ∀ X : A, φ I.C * φ X = φ X * φ I.C

/--
The finite closure relations transported to the image of a bonding map.

This is intentionally image-local: no global centrality in `B` is asserted.
-/
def ImageClosure (I : SupergradedClosureAt A) (φ : StarRingHom A B) : Prop :=
  φ I.Q * φ I.Q = 0 ∧
  φ I.P * φ I.P = φ I.P ∧
  φ I.Q * star (φ I.Q) + star (φ I.Q) * φ I.Q = φ I.H ∧
  φ I.P * φ I.Q + φ I.Q * φ I.P = 0 ∧
  ImageCentral I φ

/-- Square-zero odd lane transports under a star-preserving bonding map. -/
theorem map_odd_sq_zero
    (I : SupergradedClosureAt A) (φ : StarRingHom A B) :
    φ I.Q * φ I.Q = 0 := by
  calc
    φ I.Q * φ I.Q = φ (I.Q * I.Q) := by simp
    _ = φ 0 := by rw [I.odd_sq_zero]
    _ = 0 := by simp

/-- Projector/idempotent parity lane transports under a bonding map. -/
theorem map_parity_idempotent
    (I : SupergradedClosureAt A) (φ : StarRingHom A B) :
    φ I.P * φ I.P = φ I.P := by
  calc
    φ I.P * φ I.P = φ (I.P * I.P) := by simp
    _ = φ I.P := by rw [I.parity_idempotent]

/-- Odd-odd star closure transports under a star-preserving bonding map. -/
theorem map_odd_odd_closure
    (I : SupergradedClosureAt A) (φ : StarRingHom A B) :
    φ I.Q * star (φ I.Q) + star (φ I.Q) * φ I.Q = φ I.H := by
  calc
    φ I.Q * star (φ I.Q) + star (φ I.Q) * φ I.Q
        = φ I.Q * φ (star I.Q) + φ (star I.Q) * φ I.Q := by simp
    _ = φ (I.Q * star I.Q) + φ (star I.Q * I.Q) := by simp
    _ = φ (I.Q * star I.Q + star I.Q * I.Q) := by simp
    _ = φ I.H := by rw [I.odd_odd_closure]

/-- Parity/odd anticommutation transports under a bonding map. -/
theorem map_parity_odd_anticomm
    (I : SupergradedClosureAt A) (φ : StarRingHom A B) :
    φ I.P * φ I.Q + φ I.Q * φ I.P = 0 := by
  calc
    φ I.P * φ I.Q + φ I.Q * φ I.P
        = φ (I.P * I.Q) + φ (I.Q * I.P) := by simp
    _ = φ (I.P * I.Q + I.Q * I.P) := by simp
    _ = φ 0 := by rw [I.parity_odd_anticomm]
    _ = 0 := by simp

/-- Centrality transports on the image of a bonding map. -/
theorem map_image_central
    (I : SupergradedClosureAt A) (φ : StarRingHom A B) :
    ImageCentral I φ := by
  intro X
  calc
    φ I.C * φ X = φ (I.C * X) := by simp
    _ = φ (X * I.C) := by rw [I.central_commutes X]
    _ = φ X * φ I.C := by simp

/--
Finite Erlangen transport theorem: all local closure identities hold on the
image of a star-preserving bonding map.
-/
theorem map_image_closure
    (I : SupergradedClosureAt A) (φ : StarRingHom A B) :
    ImageClosure I φ := by
  exact
    ⟨map_odd_sq_zero I φ,
      map_parity_idempotent I φ,
      map_odd_odd_closure I φ,
      map_parity_odd_anticomm I φ,
      map_image_central I φ⟩

/--
All local closure identities are preserved on the image of every finite
star-preserving endomorphism chain.

This is the finite inductive-system invariance theorem for a common ambient
algebra: compose any bounded number of bonding maps, and the transported packet
still satisfies the supergraded closure relations on the transported image.
-/
theorem chain_image_closure
    (I : SupergradedClosureAt A) (φ : Nat → StarRingHom A A) (n k : Nat) :
    ImageClosure I (StarRingHom.chain φ n k) :=
  map_image_closure I (StarRingHom.chain φ n k)

/-- Centrality is preserved on the image of every finite star-hom chain. -/
theorem chain_image_central
    (I : SupergradedClosureAt A) (φ : Nat → StarRingHom A A) (n k : Nat) :
    ImageCentral I (StarRingHom.chain φ n k) :=
  map_image_central I (StarRingHom.chain φ n k)

/-- Square-zero odd closure after a finite star-hom chain. -/
theorem chain_odd_sq_zero
    (I : SupergradedClosureAt A) (φ : Nat → StarRingHom A A) (n k : Nat) :
    StarRingHom.chain φ n k I.Q * StarRingHom.chain φ n k I.Q = 0 :=
  map_odd_sq_zero I (StarRingHom.chain φ n k)

/-- Projector/idempotent closure after a finite star-hom chain. -/
theorem chain_parity_idempotent
    (I : SupergradedClosureAt A) (φ : Nat → StarRingHom A A) (n k : Nat) :
    StarRingHom.chain φ n k I.P * StarRingHom.chain φ n k I.P =
      StarRingHom.chain φ n k I.P :=
  map_parity_idempotent I (StarRingHom.chain φ n k)

/-- Odd-odd closure after a finite star-hom chain. -/
theorem chain_odd_odd_closure
    (I : SupergradedClosureAt A) (φ : Nat → StarRingHom A A) (n k : Nat) :
    StarRingHom.chain φ n k I.Q * star (StarRingHom.chain φ n k I.Q) +
        star (StarRingHom.chain φ n k I.Q) * StarRingHom.chain φ n k I.Q =
      StarRingHom.chain φ n k I.H :=
  map_odd_odd_closure I (StarRingHom.chain φ n k)

/-- Parity/odd anticommutation after a finite star-hom chain. -/
theorem chain_parity_odd_anticomm
    (I : SupergradedClosureAt A) (φ : Nat → StarRingHom A A) (n k : Nat) :
    StarRingHom.chain φ n k I.P * StarRingHom.chain φ n k I.Q +
        StarRingHom.chain φ n k I.Q * StarRingHom.chain φ n k I.P = 0 :=
  map_parity_odd_anticomm I (StarRingHom.chain φ n k)

/--
If the bonding map is surjective, image-centrality upgrades to global centrality
in the target algebra.
-/
def map_global_closure_of_surjective
    (I : SupergradedClosureAt A) (φ : StarRingHom A B)
    (hφ : Function.Surjective φ) :
    SupergradedClosureAt B where
  Q := φ I.Q
  H := φ I.H
  P := φ I.P
  C := φ I.C
  odd_sq_zero := map_odd_sq_zero I φ
  parity_idempotent := map_parity_idempotent I φ
  odd_odd_closure := map_odd_odd_closure I φ
  parity_odd_anticomm := map_parity_odd_anticomm I φ
  central_commutes := by
    intro Y
    rcases hφ Y with ⟨X, rfl⟩
    exact map_image_central I φ X

end SupergradedClosureAt

end InfoGeometry.Meta.InductiveInvariantPacket
