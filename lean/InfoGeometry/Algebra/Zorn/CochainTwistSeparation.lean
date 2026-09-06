import InfoGeometry.Algebra.Zorn.Z2ThreeCochainBridge

/-!
# Binary cochain twists and their associators

The product is modified by a TWO-cochain, not by a three-variable associator.
The associator is its explicitly computed coboundary. It can be a nonconstant
function while representing the trivial cohomology class. The concrete
identification with a Zorn multiplication table belongs to a separate owner.

This file reuses `associatorCochain`, `twistedScalar`, `Z2Grade`, and `signUnit`.
It does not identify a general sign cochain with an octonion multiplication.
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.CochainTwistSeparation

open InfoGeometry.Algebra.Zorn.Z2ThreeCochainBridge

variable {R G : Type*} [CommRing R] [AddCommGroup G]

/-- Exact binary cocycle equation, equivalent to a trivial associator. -/
theorem associator_eq_one_iff (F : G → G → Rˣ) (x y z : G) :
    associatorCochain F x y z = 1 ↔
      F x y * F (x + y) z = F y z * F x (y + z) := by
  constructor
  · intro h
    have hm := congrArg (fun u : Rˣ => u * (F y z * F x (y + z))) h
    simpa [associatorCochain, mul_assoc] using hm
  · intro h
    rw [associatorCochain, h]
    simp [mul_assoc, mul_comm, mul_left_comm]

/-- Trivial associator really gives equality of the two homogeneous products. -/
theorem homogeneous_associative_of_cocycle
    (F : G → G → Rˣ)
    (hF : ∀ x y z, F x y * F (x + y) z = F y z * F x (y + z))
    (x y z : G) (a b c : R) :
    twistedScalar F (x + y) z (twistedScalar F x y a b) c =
      twistedScalar F x (y + z) a (twistedScalar F y z b c) := by
  rw [twistedScalar_associator, (associator_eq_one_iff F x y z).2 (hF x y z)]
  simp

/-- Coboundary is multiplicative under pointwise multiplication of two-cochains. -/
theorem associator_mul (F H : G → G → Rˣ) (x y z : G) :
    associatorCochain (fun a b => F a b * H a b) x y z =
      associatorCochain F x y z * associatorCochain H x y z := by
  simp only [associatorCochain, mul_inv_rev]
  ac_rfl

/-- Pointwise inversion of the two-cochain inverts its associator. -/
theorem associator_inv (F : G → G → Rˣ) (x y z : G) :
    associatorCochain (fun a b => (F a b)⁻¹) x y z =
      (associatorCochain F x y z)⁻¹ := by
  simp only [associatorCochain, mul_inv_rev, inv_inv]
  ac_rfl

/-- The binary multiplier carrying one coefficient table to another. -/
def relativeTwist (F H : G → G → Rˣ) (x y : G) : Rˣ :=
  H x y * (F x y)⁻¹

/-- Multiplication by the relative two-cochain recovers the target table. -/
theorem relativeTwist_mul (F H : G → G → Rˣ) (x y : G) :
    relativeTwist F H x y * F x y = H x y := by
  simp [relativeTwist, mul_assoc]

/-- The precise transformation law of the associator under a binary twist. -/
theorem associator_relativeTwist (F H : G → G → Rˣ) (x y z : G) :
    associatorCochain (relativeTwist F H) x y z =
      associatorCochain H x y z * (associatorCochain F x y z)⁻¹ := by
  unfold relativeTwist
  rw [associator_mul, associator_inv]

/-- When the source table is associative, the target associator is the
coboundary of the relative TWO-cochain. -/
theorem target_associator_is_relative_coboundary
    (F H : G → G → Rˣ)
    (hF : ∀ x y z, associatorCochain F x y z = 1) (x y z : G) :
    associatorCochain H x y z =
      associatorCochain (relativeTwist F H) x y z := by
  rw [associator_relativeTwist, hF]
  simp

/-- The same binary twist satisfies the genuine pentagon coefficient equation. -/
theorem relativeTwist_pentagon (F H : G → G → Rˣ) (x y z w : G) :
    associatorCochain (relativeTwist F H) x y z *
        associatorCochain (relativeTwist F H) x (y + z) w *
        associatorCochain (relativeTwist F H) y z w =
      associatorCochain (relativeTwist F H) (x + y) z w *
        associatorCochain (relativeTwist F H) x y (z + w) :=
  associatorCochain_cocycle (relativeTwist F H) x y z w

/-- Normalized two-cochains have a normalized associator in the first slot. -/
theorem associator_zero_left (F : G → G → Rˣ)
    (h0 : ∀ x, F 0 x = 1) (y z : G) :
    associatorCochain F 0 y z = 1 := by
  simp [associatorCochain, h0]

/-- Normalization in the middle slot requires both unit laws. -/
theorem associator_zero_middle (F : G → G → Rˣ)
    (h0 : ∀ x, F 0 x = 1) (h1 : ∀ x, F x 0 = 1) (x z : G) :
    associatorCochain F x 0 z = 1 := by
  simp [associatorCochain, h0, h1]

/-- Normalization in the last slot. -/
theorem associator_zero_right (F : G → G → Rˣ)
    (h1 : ∀ x, F x 0 = 1) (x y : G) :
    associatorCochain F x y 0 = 1 := by
  simp [associatorCochain, h1]

/-- The existing real sign unit converts parity addition into multiplication. -/
theorem signUnit_add (a b : ZMod 2) :
    signUnit (a + b) = signUnit a * signUnit b := by
  fin_cases a <;> fin_cases b
  · simp [signUnit]
  · simp [signUnit]
  · simp [signUnit]
  · simp [signUnit]
    change (1 + 1 : ZMod 2) = 0
    exact ZMod.natCast_self 2

/-- A bilinear parity exponent is always an associative coefficient table. -/
theorem bilinear_sign_cocycle
    (β : G →+ (G →+ ZMod 2)) (x y z : G) :
    signUnit (β x y) * signUnit (β (x + y) z) =
      signUnit (β y z) * signUnit (β x (y + z)) := by
  simp only [map_add, AddMonoidHom.add_apply, signUnit_add]
  ac_rfl

/-- Consequently a bilinear exponent cannot activate an octonionic associator. -/
theorem bilinear_sign_associator_one
    (β : G →+ (G →+ ZMod 2)) (x y z : G) :
    associatorCochain (fun a b => signUnit (β a b)) x y z = 1 :=
  (associator_eq_one_iff _ x y z).2 (bilinear_sign_cocycle β x y z)

/-- The associativity conclusion is about the actual homogeneous products. -/
theorem bilinear_sign_homogeneous_associative
    (β : G →+ (G →+ ZMod 2)) (x y z : G) (a b c : ℝ) :
    twistedScalar (fun u v => signUnit (β u v)) (x + y) z
        (twistedScalar (fun u v => signUnit (β u v)) x y a b) c =
      twistedScalar (fun u v => signUnit (β u v)) x (y + z) a
        (twistedScalar (fun u v => signUnit (β u v)) y z b c) :=
  homogeneous_associative_of_cocycle _ (bilinear_sign_cocycle β) x y z a b c

end InfoGeometry.Algebra.Zorn.CochainTwistSeparation
