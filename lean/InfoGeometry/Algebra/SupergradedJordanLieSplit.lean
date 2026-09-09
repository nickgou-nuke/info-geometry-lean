import InfoGeometry.Algebra.SupergradedBracket
import Mathlib.Tactic

/-!
# The graded Jordan/Lie split

For a homogeneous pair the associative product has two canonical children:
the graded-symmetric (Jordan) product and the superbracket.  This file keeps
the statement algebraic and finite; it does not install a Lie-superalgebra
instance or assert any analytic completion.
-/

namespace InfoGeometry.Algebra.SupergradedBracket

variable {R A : Type*} [Field R] [Ring A] [Algebra R A]
  [NeZero (2 : R)]

/-- The Koszul sign attached to two Boolean parity labels. -/
def gradedSign (px py : Bool) : R :=
  if px && py then (-1 : R) else 1

@[simp] theorem gradedSign_swap (px py : Bool) :
    gradedSign (R := R) px py = gradedSign (R := R) py px := by
  cases px <;> cases py <;> simp [gradedSign]

@[simp] theorem gradedSign_mul_self (px py : Bool) :
    gradedSign (R := R) px py * gradedSign (R := R) px py = 1 := by
  cases px <;> cases py <;> simp [gradedSign]

theorem superBracket_eq_mul_sub_sign (px py : Bool) (x y : A) :
    superBracket px py x y =
      x * y - gradedSign (R := R) px py • (y * x) := by
  cases px <;> cases py <;>
    simp [superBracket, gradedSign,
      InfoGeometry.Algebra.SupergradedBracket.commutator,
      InfoGeometry.Algebra.SupergradedBracket.anticommutator, sub_eq_add_neg]

/-- The graded-symmetric/Jordan companion of `superBracket`. -/
def gradedJordanProduct (px py : Bool) (x y : A) : A :=
  (2 : R)⁻¹ • (x * y + gradedSign (R := R) px py • (y * x))

theorem gradedProduct_decomposition (px py : Bool) (x y : A) :
    x * y =
      gradedJordanProduct (R := R) px py x y +
        (2 : R)⁻¹ • superBracket px py x y := by
  have hhalf_add_sub (u v : A) :
      (2 : R)⁻¹ • (u + v) + (2 : R)⁻¹ • (u - v) = u := by
    rw [smul_add, smul_sub]
    have h : (2 : R)⁻¹ + (2 : R)⁻¹ = 1 := by
      rw [← mul_two]
      exact inv_mul_cancel₀ (NeZero.ne (2 : R))
    calc
      (2 : R)⁻¹ • u + (2 : R)⁻¹ • v +
          ((2 : R)⁻¹ • u - (2 : R)⁻¹ • v) =
        ((2 : R)⁻¹ + (2 : R)⁻¹) • u +
          ((2 : R)⁻¹ • v - (2 : R)⁻¹ • v) := by
            rw [add_smul]
            abel
      _ = u := by rw [h, one_smul]; abel
  have hhalf_sub_add (u v : A) :
      (2 : R)⁻¹ • (u - v) + (2 : R)⁻¹ • (u + v) = u := by
    rw [add_comm]
    exact hhalf_add_sub u v
  have hhalf_add_sub_expanded (u v : A) :
      u = (2 : R)⁻¹ • u + (2 : R)⁻¹ • v +
        ((2 : R)⁻¹ • u - (2 : R)⁻¹ • v) := by
    simpa [smul_add, smul_sub] using (hhalf_add_sub u v).symm
  have hhalf_sub_add_expanded (u v : A) :
      u = (2 : R)⁻¹ • u - (2 : R)⁻¹ • v +
        ((2 : R)⁻¹ • u + (2 : R)⁻¹ • v) := by
    simpa [smul_add, smul_sub] using (hhalf_sub_add u v).symm
  cases px <;> cases py <;>
    simp [gradedJordanProduct, gradedSign, superBracket,
      InfoGeometry.Algebra.SupergradedBracket.commutator,
      InfoGeometry.Algebra.SupergradedBracket.anticommutator]
  · simpa only [smul_sub, InfoGeometry.Algebra.SupergradedBracket.commutator] using
      hhalf_add_sub_expanded (x * y) (y * x)
  · simpa only [smul_sub, InfoGeometry.Algebra.SupergradedBracket.commutator] using
      hhalf_add_sub_expanded (x * y) (y * x)
  · simpa only [smul_sub, InfoGeometry.Algebra.SupergradedBracket.commutator] using
      hhalf_add_sub_expanded (x * y) (y * x)
  · simpa [sub_eq_add_neg,
      InfoGeometry.Algebra.SupergradedBracket.anticommutator] using
      hhalf_sub_add_expanded (x * y) (y * x)

theorem gradedJordanProduct_swap (px py : Bool) (x y : A) :
    gradedJordanProduct (R := R) px py x y =
      gradedSign (R := R) px py •
        gradedJordanProduct (R := R) py px y x := by
  cases px <;> cases py <;>
    simp [gradedJordanProduct, gradedSign, smul_smul, add_comm,
      add_left_comm, add_assoc]

theorem superBracket_graded_skew (px py : Bool) (x y : A) :
    superBracket px py x y =
      - gradedSign (R := R) px py • superBracket py px y x := by
  cases px <;> cases py <;>
    simp [superBracket, gradedSign,
      InfoGeometry.Algebra.SupergradedBracket.commutator,
      InfoGeometry.Algebra.SupergradedBracket.anticommutator,
      smul_smul, add_comm, add_left_comm, add_assoc]

theorem superBracket_superJacobi (px py pz : Bool) (x y z : A) :
    gradedSign (R := R) px pz •
          superBracket px (py ^^ pz) x (superBracket py pz y z) +
        gradedSign (R := R) py px •
          superBracket py (pz ^^ px) y (superBracket pz px z x) +
        gradedSign (R := R) pz py •
          superBracket pz (px ^^ py) z (superBracket px py x y) = 0 := by
  cases px <;> cases py <;> cases pz <;>
    simp [gradedSign, superBracket,
      InfoGeometry.Algebra.SupergradedBracket.commutator,
      InfoGeometry.Algebra.SupergradedBracket.anticommutator,
      Bool.xor, smul_add, smul_sub, smul_smul] <;>
    noncomm_ring

@[simp] theorem gradedJordanProduct_odd_odd (x y : A) :
    gradedJordanProduct (R := R) true true x y =
      (2 : R)⁻¹ • (x * y - y * x) := by
  simp [gradedJordanProduct, gradedSign, sub_eq_add_neg]

@[simp] theorem superBracket_odd_odd_as_anticommutator (x y : A) :
    superBracket true true x y = x * y + y * x := by
  rfl

@[simp] theorem superBracket_even_even_as_commutator (x y : A) :
    superBracket false false x y = x * y - y * x := by
  rfl

@[simp] theorem superBracket_even_odd_as_commutator (x y : A) :
    superBracket false true x y = x * y - y * x := by
  rfl

@[simp] theorem superBracket_odd_even_as_commutator (x y : A) :
    superBracket true false x y = x * y - y * x := by
  rfl

@[simp] theorem gradedJordanProduct_even_even (x y : A) :
    gradedJordanProduct (R := R) false false x y =
      (2 : R)⁻¹ • (x * y + y * x) := by
  simp [gradedJordanProduct, gradedSign]

theorem odd_odd_product_split_of_pair
    (Qplus Qminus Pplus Pminus : A)
    (hplus : Qplus * Qminus = Pplus)
    (hminus : Qminus * Qplus = Pminus) :
    superBracket true true Qplus Qminus = Pplus + Pminus ∧
      gradedJordanProduct (R := R) true true Qplus Qminus =
        (2 : R)⁻¹ • (Pplus - Pminus) := by
  constructor
  · rw [superBracket_odd_odd_as_anticommutator, hplus, hminus]
  · rw [gradedJordanProduct_odd_odd, hplus, hminus]

end InfoGeometry.Algebra.SupergradedBracket
