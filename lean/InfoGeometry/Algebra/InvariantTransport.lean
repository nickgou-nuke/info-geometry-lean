import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Algebra.InvariantTransport

Concrete transport lemmas for finite-stage operator invariants.

These lemmas are the finite inductive-chain mechanism:

* square-zero elements remain square-zero;
* idempotents remain idempotent;
* involutions remain involutions;
* anticommutators are preserved;
* commutators are preserved;
* CAR identities are preserved;
* central-lane commutation is preserved on the image.

No inductive-limit wrapper is introduced here. These are direct algebraic
equalities for one structure-preserving bonding map.
-/

namespace InfoGeometry.Algebra.InvariantTransport

/-- Associative commutator. -/
def commutator {A : Type*} [Mul A] [Sub A] (x y : A) : A :=
  x * y - y * x

/-- Fermionic anticommutator. -/
def anticommutator {A : Type*} [Mul A] [Add A] (x y : A) : A :=
  x * y + y * x

variable {A B : Type*} [Ring A] [Ring B]

/--
Square-zero transport.

If `x² = 0`, then its image under a ring homomorphism is also square-zero.
-/
theorem square_zero_transport
    (φ : A →+* B) {x : A}
    (hx : x * x = 0) :
    φ x * φ x = 0 := by
  simpa using congrArg φ hx

/--
Idempotent transport.

If `p² = p`, then its image is also idempotent.
-/
theorem idempotent_transport
    (φ : A →+* B) {p : A}
    (hp : p * p = p) :
    φ p * φ p = φ p := by
  simpa using congrArg φ hp

/--
Involution transport.

If `P² = 1`, then its image also squares to `1`.
-/
theorem involution_transport
    (φ : A →+* B) {P : A}
    (hP : P * P = 1) :
    φ P * φ P = 1 := by
  simpa using congrArg φ hP

/--
Commutator transport.

A ring homomorphism preserves associative commutators.
-/
theorem commutator_transport
    (φ : A →+* B) (x y : A) :
    commutator (φ x) (φ y) = φ (commutator x y) := by
  simp [commutator]

/--
Anticommutator transport.

A ring homomorphism preserves fermionic anticommutators.
-/
theorem anticommutator_transport
    (φ : A →+* B) (x y : A) :
    anticommutator (φ x) (φ y) = φ (anticommutator x y) := by
  simp [anticommutator]

/--
Zero anticommutator transport.

If `{x,y}=0`, then `{φ x, φ y}=0`.
-/
theorem anticommutator_zero_transport
    (φ : A →+* B) {x y : A}
    (hxy : anticommutator x y = 0) :
    anticommutator (φ x) (φ y) = 0 := by
  rw [anticommutator_transport]
  simp [hxy]

/--
Zero commutator transport.

If `[x,y]=0`, then `[φ x, φ y]=0`.
-/
theorem commutator_zero_transport
    (φ : A →+* B) {x y : A}
    (hxy : commutator x y = 0) :
    commutator (φ x) (φ y) = 0 := by
  rw [commutator_transport]
  simp [hxy]

/--
CAR same-mode transport.

If `{a,a†}=1`, then `{φ a, φ a†}=1`.
-/
theorem car_same_mode_transport
    (φ : A →+* B) {a aDag : A}
    (hcar : anticommutator a aDag = 1) :
    anticommutator (φ a) (φ aDag) = 1 := by
  rw [anticommutator_transport]
  simp [hcar]

/--
CAR cross-mode transport.

If `{a,b}=0`, then `{φ a, φ b}=0`.
-/
theorem car_cross_mode_transport
    (φ : A →+* B) {a b : A}
    (hcar : anticommutator a b = 0) :
    anticommutator (φ a) (φ b) = 0 :=
  anticommutator_zero_transport φ hcar

/--
Central commutator transport.

If `[x,y]=c`, then `[φ x, φ y]=φ c`.
-/
theorem commutator_eq_transport
    (φ : A →+* B) {x y c : A}
    (hxy : commutator x y = c) :
    commutator (φ x) (φ y) = φ c := by
  rw [commutator_transport]
  simp [hxy]

/--
Central-lane image commutation.

If `c` commutes with every element of the source algebra, then `φ c`
commutes with every element in the image of `φ`.
-/
theorem central_commutes_on_image_transport
    (φ : A →+* B) {c : A}
    (hc : ∀ x : A, c * x = x * c)
    (x : A) :
    φ c * φ x = φ x * φ c := by
  simpa using congrArg φ (hc x)

/--
Parity anticommutation transport.

If a parity operator `P` anticommutes with an odd operator `q`, then their
images still anticommute.
-/
theorem parity_anticommutes_odd_transport
    (φ : A →+* B) {P q : A}
    (h : anticommutator P q = 0) :
    anticommutator (φ P) (φ q) = 0 :=
  anticommutator_zero_transport φ h

/--
Parity packet transport.

If `P²=1` and `{P,q}=0`, then the image has the same parity/odd relation.
-/
theorem parity_packet_transport
    (φ : A →+* B) {P q : A}
    (hP : P * P = 1)
    (hanti : anticommutator P q = 0) :
    φ P * φ P = 1 ∧ anticommutator (φ P) (φ q) = 0 :=
  ⟨involution_transport φ hP, anticommutator_zero_transport φ hanti⟩

/--
Projector pair transport.

If `p` and `q` are complementary orthogonal projectors, their images are also
complementary orthogonal projectors.
-/
theorem complementary_projectors_transport
    (φ : A →+* B) {p q : A}
    (hp : p * p = p)
    (hq : q * q = q)
    (hpq : p * q = 0)
    (hqp : q * p = 0)
    (hsum : p + q = 1) :
    φ p * φ p = φ p ∧
    φ q * φ q = φ q ∧
    φ p * φ q = 0 ∧
    φ q * φ p = 0 ∧
    φ p + φ q = 1 := by
  constructor
  · exact idempotent_transport φ hp
  constructor
  · exact idempotent_transport φ hq
  constructor
  · simpa using congrArg φ hpq
  constructor
  · simpa using congrArg φ hqp
  · simpa using congrArg φ hsum

end InfoGeometry.Algebra.InvariantTransport
