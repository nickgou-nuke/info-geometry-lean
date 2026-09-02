import Mathlib.Tactic
import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication

/-!
# Generic Zorn split octonions and the integral lattice

This is the scalar-parametric owner for the Zorn model.  The existing
`SplitOct` is recovered by taking `R = ℤ`; the rational scalar extension is
obtained by taking `R = ℚ`.  No maximal-order or particle-physics claim is
encoded here.
-/

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

namespace InfoGeometry.OperatorAlgebra.GenericZorn

variable {R : Type*} [CommRing R]

@[ext]
structure ZornSplitOctonion (R : Type*) [CommRing R] where
  a : R
  b : R
  x0 : R
  x1 : R
  x2 : R
  y0 : R
  y1 : R
  y2 : R

def toCanonical (x : ZornSplitOctonion R) : InfoGeometry.Canonical.ZornMatrix R :=
  { a := x.a
    b := x.b
    x := ![x.x0, x.x1, x.x2]
    y := ![x.y0, x.y1, x.y2] }

def fromCanonical (x : InfoGeometry.Canonical.ZornMatrix R) : ZornSplitOctonion R :=
  { a := x.a
    b := x.b
    x0 := x.x 0
    x1 := x.x 1
    x2 := x.x 2
    y0 := x.y 0
    y1 := x.y 1
    y2 := x.y 2 }

def canonicalEquiv : ZornSplitOctonion R ≃ InfoGeometry.Canonical.ZornMatrix R where
  toFun := toCanonical
  invFun := fromCanonical
  left_inv x := by
    cases x
    rfl
  right_inv x := by
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl

def zero (R : Type*) [CommRing R] : ZornSplitOctonion R :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

instance : Zero (ZornSplitOctonion R) := ⟨zero R⟩

def add (x y : ZornSplitOctonion R) : ZornSplitOctonion R :=
  ⟨x.a + y.a, x.b + y.b, x.x0 + y.x0, x.x1 + y.x1, x.x2 + y.x2,
    x.y0 + y.y0, x.y1 + y.y1, x.y2 + y.y2⟩

instance : Add (ZornSplitOctonion R) := ⟨add⟩

def neg (x : ZornSplitOctonion R) : ZornSplitOctonion R :=
  ⟨-x.a, -x.b, -x.x0, -x.x1, -x.x2, -x.y0, -x.y1, -x.y2⟩

instance : Neg (ZornSplitOctonion R) := ⟨neg⟩

theorem add_zero (x : ZornSplitOctonion R) : x + 0 = x := by
  cases x
  change add _ (zero R) = _
  congr <;> simp [add, zero]

theorem zero_add (x : ZornSplitOctonion R) : 0 + x = x := by
  cases x
  change add (zero R) _ = _
  congr <;> simp [add, zero]

theorem add_comm (x y : ZornSplitOctonion R) : x + y = y + x := by
  cases x
  cases y
  change add _ _ = add _ _
  apply ZornSplitOctonion.ext <;>
    simp [add, _root_.add_comm]

theorem add_assoc (x y z : ZornSplitOctonion R) :
    (x + y) + z = x + (y + z) := by
  cases x
  cases y
  cases z
  change add (add _ _) _ = add _ (add _ _)
  apply ZornSplitOctonion.ext <;>
    simp [add, _root_.add_assoc]

theorem add_left_neg (x : ZornSplitOctonion R) : -x + x = 0 := by
  cases x
  change add (neg _) _ = zero R
  apply ZornSplitOctonion.ext <;>
    simp [add, neg, zero]

theorem add_neg_cancel_right (x : ZornSplitOctonion R) : x + -x = 0 := by
  cases x
  change add _ (neg _) = zero R
  apply ZornSplitOctonion.ext <;>
    simp [add, neg, zero]

def one (R : Type*) [CommRing R] : ZornSplitOctonion R :=
  ⟨1, 1, 0, 0, 0, 0, 0, 0⟩

theorem toCanonical_zero :
    toCanonical (zero R) = (0 : InfoGeometry.Canonical.ZornMatrix R) := by
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · rfl
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem toCanonical_add (x y : ZornSplitOctonion R) :
    toCanonical (x + y) = toCanonical x + toCanonical y := by
  cases x with
  | mk a b x0 x1 x2 y0 y1 y2 =>
    cases y with
    | mk c d u0 u1 u2 v0 v1 v2 =>
      apply InfoGeometry.Canonical.ZornMatrix.ext
      · rfl
      · rfl
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> rfl

theorem toCanonical_neg (x : ZornSplitOctonion R) :
    toCanonical (-x) = -toCanonical x := by
  cases x with
  | mk a b x0 x1 x2 y0 y1 y2 =>
      apply InfoGeometry.Canonical.ZornMatrix.ext
      · rfl
      · rfl
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> rfl

theorem toCanonical_one :
    toCanonical (one R) = (1 : InfoGeometry.Canonical.ZornMatrix R) := by
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · rfl
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

def scalar (r : R) : ZornSplitOctonion R :=
  ⟨r, r, 0, 0, 0, 0, 0, 0⟩

theorem toCanonical_scalar (r : R) :
    toCanonical (scalar r) =
      ({ a := r, b := r, x := ![0, 0, 0], y := ![0, 0, 0] } :
        InfoGeometry.Canonical.ZornMatrix R) := by
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · rfl
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

def mul (x y : ZornSplitOctonion R) : ZornSplitOctonion R :=
  ⟨ x.a * y.a + (x.x0 * y.y0 + x.x1 * y.y1 + x.x2 * y.y2),
    x.b * y.b + (x.y0 * y.x0 + x.y1 * y.x1 + x.y2 * y.x2),
    x.a * y.x0 + y.b * x.x0 - (x.y1 * y.y2 - x.y2 * y.y1),
    x.a * y.x1 + y.b * x.x1 - (x.y2 * y.y0 - x.y0 * y.y2),
    x.a * y.x2 + y.b * x.x2 - (x.y0 * y.y1 - x.y1 * y.y0),
    x.b * y.y0 + y.a * x.y0 + (x.x1 * y.x2 - x.x2 * y.x1),
    x.b * y.y1 + y.a * x.y1 + (x.x2 * y.x0 - x.x0 * y.x2),
    x.b * y.y2 + y.a * x.y2 + (x.x0 * y.x1 - x.x1 * y.x0) ⟩

theorem mul_add (x y z : ZornSplitOctonion R) :
    mul x (y + z) = mul x y + mul x z := by
  cases x
  cases y
  cases z
  change mul _ (add _ _) = add (mul _ _) (mul _ _)
  apply ZornSplitOctonion.ext <;>
    simp [mul, add] <;> ring

theorem add_mul (x y z : ZornSplitOctonion R) :
    mul (x + y) z = mul x z + mul y z := by
  cases x
  cases y
  cases z
  change mul (add _ _) _ = add (mul _ _) (mul _ _)
  apply ZornSplitOctonion.ext <;>
    simp [mul, add] <;> ring

theorem toCanonical_mul (x y : ZornSplitOctonion R) :
    toCanonical (mul x y) = toCanonical x * toCanonical y := by
  cases x with
  | mk a b x0 x1 x2 y0 y1 y2 =>
    cases y with
    | mk c d u0 u1 u2 v0 v1 v2 =>
      apply InfoGeometry.Canonical.ZornMatrix.ext
      · simp [toCanonical, mul, InfoGeometry.Canonical.ZornMatrix.mul,
          InfoGeometry.Canonical.ZornMatrix.dot]
      · simp [toCanonical, mul, InfoGeometry.Canonical.ZornMatrix.mul,
          InfoGeometry.Canonical.ZornMatrix.dot]
      · funext i
        fin_cases i <;>
          simp [toCanonical, mul, InfoGeometry.Canonical.ZornMatrix.mul,
            InfoGeometry.Canonical.ZornMatrix.cross, Matrix.vecHead, Matrix.vecTail]
      · funext i
        fin_cases i <;>
          simp [toCanonical, mul, InfoGeometry.Canonical.ZornMatrix.mul,
            InfoGeometry.Canonical.ZornMatrix.cross, Matrix.vecHead, Matrix.vecTail]

def norm (x : ZornSplitOctonion R) : R :=
  x.a * x.b - (x.x0 * x.y0 + x.x1 * x.y1 + x.x2 * x.y2)

def conjugate (x : ZornSplitOctonion R) : ZornSplitOctonion R :=
  ⟨x.b, x.a, -x.x0, -x.x1, -x.x2, -x.y0, -x.y1, -x.y2⟩

@[simp] theorem conjugate_zero : conjugate (zero R) = zero R := by
  ext <;> simp [conjugate, zero]

@[simp] theorem conjugate_one : conjugate (one R) = one R := by
  ext <;> simp [conjugate, one]

@[simp] theorem conjugate_scalar (r : R) :
    conjugate (scalar r) = scalar r := by
  ext <;> simp [conjugate, scalar]

@[simp] theorem conjugate_conjugate (x : ZornSplitOctonion R) :
    conjugate (conjugate x) = x := by
  cases x
  ext <;> simp [conjugate]

theorem toCanonical_conjugate (x : ZornSplitOctonion R) :
    toCanonical (conjugate x) =
      InfoGeometry.Canonical.ZornMatrix.conjugate (toCanonical x) := by
  cases x with
  | mk a b x0 x1 x2 y0 y1 y2 =>
      apply InfoGeometry.Canonical.ZornMatrix.ext
      · rfl
      · rfl
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> rfl

/-! Cayley conjugation is the anti-involution underlying the Zorn model. -/
theorem conjugate_mul (x y : ZornSplitOctonion R) :
    conjugate (mul x y) = mul (conjugate y) (conjugate x) := by
  cases x with
  | mk a b x0 x1 x2 y0 y1 y2 =>
    cases y with
    | mk c d u0 u1 u2 v0 v1 v2 =>
      ext <;> simp [conjugate, mul]
      all_goals ring

theorem scalar_injective : Function.Injective (scalar : R → ZornSplitOctonion R) := by
  intro r s h
  exact congrArg ZornSplitOctonion.a h

theorem norm_mul (x y : ZornSplitOctonion R) :
    norm (mul x y) = norm x * norm y := by
  cases x with
  | mk a b x0 x1 x2 y0 y1 y2 =>
    cases y with
    | mk c d u0 u1 u2 v0 v1 v2 =>
      simp [norm, mul]
      ring_nf

theorem norm_eq_zero_left_or_right_of_mul_eq_zero
    [NoZeroDivisors R] (x y : ZornSplitOctonion R)
    (hxy : mul x y = zero R) :
    norm x = 0 ∨ norm y = 0 := by
  have hnorm : norm x * norm y = 0 := by
    have h := congrArg norm hxy
    rw [norm_mul] at h
    simpa [norm, zero] using h
  exact eq_zero_or_eq_zero_of_mul_eq_zero hnorm

theorem mul_conjugate (x : ZornSplitOctonion R) :
    mul x (conjugate x) = scalar (norm x) := by
  cases x
  ext <;> simp [mul, conjugate, scalar, norm]
  · ring
  · ring
  · ring
  · ring
  · ring
  · ring
  · ring
  · ring

theorem norm_conjugate (x : ZornSplitOctonion R) :
    norm (conjugate x) = norm x := by
  cases x
  simp [norm, conjugate]
  ring

theorem norm_scalar (r : R) : norm (scalar r) = r * r := by
  simp [norm, scalar]

def integralEmbedding (x : SplitOct) : ZornSplitOctonion ℚ :=
  ⟨x.a, x.b, x.x0, x.x1, x.x2, x.y0, x.y1, x.y2⟩

theorem integralEmbedding_injective :
    Function.Injective integralEmbedding := by
  intro x y h
  cases x with
  | mk a b x0 x1 x2 y0 y1 y2 =>
    cases y with
    | mk c d u0 u1 u2 v0 v1 v2 =>
      cases h
      rfl

def integralLattice : Set (ZornSplitOctonion ℚ) :=
  Set.range integralEmbedding

theorem integral_norm (x : SplitOct) :
    norm (integralEmbedding x) = (detZ x : ℚ) := by
  simp [norm, integralEmbedding, detZ]

theorem integral_mul_embedding (x y : SplitOct) :
    mul (integralEmbedding x) (integralEmbedding y) =
      integralEmbedding (mulZ x y) := by
  cases x with
  | mk a b x0 x1 x2 y0 y1 y2 =>
    cases y with
    | mk c d u0 u1 u2 v0 v1 v2 =>
      ext <;> simp [integralEmbedding, mul, mulZ]

theorem integral_lattice_mul_closed
    {x y : ZornSplitOctonion ℚ}
    (hx : x ∈ integralLattice) (hy : y ∈ integralLattice) :
    mul x y ∈ integralLattice := by
  rcases hx with ⟨x, rfl⟩
  rcases hy with ⟨y, rfl⟩
  exact ⟨mulZ x y, (integral_mul_embedding x y).symm⟩

/-- A concrete rational Cartan coordinate. -/
abbrev cartanCharge (x : ZornSplitOctonion ℚ) : ℚ := x.a

/-- The finite charge labels used by this explicitly specified state sector. -/
def chargeValue : Fin 6 → ℚ :=
  ![0, -1, 1 / 3, -(1 / 3), 2 / 3, -(2 / 3)]

def chargeState (i : Fin 6) : ZornSplitOctonion ℚ :=
  { a := chargeValue i, b := 0,
    x0 := 0, x1 := 0, x2 := 0,
    y0 := 0, y1 := 0, y2 := 0 }

theorem cartanCharge_state (i : Fin 6) :
    cartanCharge (chargeState i) = chargeValue i := rfl

theorem charge_image :
    Set.range (fun i : Fin 6 => cartanCharge (chargeState i)) =
      ({0, -1, 1 / 3, -(1 / 3), 2 / 3, -(2 / 3)} : Set ℚ) := by
  ext q
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [cartanCharge, chargeState, chargeValue]
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by simp [cartanCharge, chargeState, chargeValue]
      ⟩
    · exact ⟨1, by simp [cartanCharge, chargeState, chargeValue]
      ⟩
    · exact ⟨2, by simp [cartanCharge, chargeState, chargeValue]
      ⟩
    · exact ⟨3, by simp [cartanCharge, chargeState, chargeValue]
      ⟩
    · exact ⟨4, by simp [cartanCharge, chargeState, chargeValue]
      ⟩
    · exact ⟨5, by simp [cartanCharge, chargeState, chargeValue]
      ⟩

end InfoGeometry.OperatorAlgebra.GenericZorn
