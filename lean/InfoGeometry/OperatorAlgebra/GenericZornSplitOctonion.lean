import Mathlib.Tactic
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

variable {R : Type*} [CommRing R]

def zero : ZornSplitOctonion R :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

def coordEquiv : ZornSplitOctonion R ≃
    R × R × R × R × R × R × R × R where
  toFun x := (x.a, x.b, x.x0, x.x1, x.x2, x.y0, x.y1, x.y2)
  invFun t :=
    { a := t.1, b := t.2.1, x0 := t.2.2.1, x1 := t.2.2.2.1,
      x2 := t.2.2.2.2.1, y0 := t.2.2.2.2.2.1,
      y1 := t.2.2.2.2.2.2.1, y2 := t.2.2.2.2.2.2.2 }
  left_inv := by intro x; rfl
  right_inv := by intro t; cases t <;> rfl

instance : Add (ZornSplitOctonion R) :=
  ⟨fun x y =>
    { a := x.a + y.a, b := x.b + y.b,
      x0 := x.x0 + y.x0, x1 := x.x1 + y.x1, x2 := x.x2 + y.x2,
      y0 := x.y0 + y.y0, y1 := x.y1 + y.y1, y2 := x.y2 + y.y2 }⟩

instance : Zero (ZornSplitOctonion R) := ⟨zero⟩

instance : Neg (ZornSplitOctonion R) :=
  ⟨fun x =>
    { a := -x.a, b := -x.b, x0 := -x.x0, x1 := -x.x1, x2 := -x.x2,
      y0 := -x.y0, y1 := -x.y1, y2 := -x.y2 }⟩

instance : Sub (ZornSplitOctonion R) :=
  ⟨fun x y => x + -y⟩

instance : AddCommGroup (ZornSplitOctonion R) :=
  Equiv.addCommGroup coordEquiv

instance : SMul R (ZornSplitOctonion R) :=
  ⟨fun r x =>
    { a := r * x.a, b := r * x.b, x0 := r * x.x0, x1 := r * x.x1,
      x2 := r * x.x2, y0 := r * x.y0, y1 := r * x.y1, y2 := r * x.y2 }⟩

instance : Module R (ZornSplitOctonion R) :=
  Equiv.module R coordEquiv

def one : ZornSplitOctonion R :=
  ⟨1, 1, 0, 0, 0, 0, 0, 0⟩

def scalar (r : R) : ZornSplitOctonion R :=
  ⟨r, r, 0, 0, 0, 0, 0, 0⟩

def mul (x y : ZornSplitOctonion R) : ZornSplitOctonion R :=
  ⟨ x.a * y.a + (x.x0 * y.y0 + x.x1 * y.y1 + x.x2 * y.y2),
    x.b * y.b + (x.y0 * y.x0 + x.y1 * y.x1 + x.y2 * y.x2),
    x.a * y.x0 + y.b * x.x0 - (x.y1 * y.y2 - x.y2 * y.y1),
    x.a * y.x1 + y.b * x.x1 - (x.y2 * y.y0 - x.y0 * y.y2),
    x.a * y.x2 + y.b * x.x2 - (x.y0 * y.y1 - x.y1 * y.y0),
    x.b * y.y0 + y.a * x.y0 + (x.x1 * y.x2 - x.x2 * y.x1),
    x.b * y.y1 + y.a * x.y1 + (x.x2 * y.x0 - x.x0 * y.x2),
    x.b * y.y2 + y.a * x.y2 + (x.x0 * y.x1 - x.x1 * y.x0) ⟩

def norm (x : ZornSplitOctonion R) : R :=
  x.a * x.b - (x.x0 * x.y0 + x.x1 * x.y1 + x.x2 * x.y2)

def conjugate (x : ZornSplitOctonion R) : ZornSplitOctonion R :=
  ⟨x.b, x.a, -x.x0, -x.x1, -x.x2, -x.y0, -x.y1, -x.y2⟩

theorem norm_mul (x y : ZornSplitOctonion R) :
    norm (mul x y) = norm x * norm y := by
  cases x with
  | mk a b x0 x1 x2 y0 y1 y2 =>
    cases y with
    | mk c d u0 u1 u2 v0 v1 v2 =>
      simp [norm, mul]
      ring_nf

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

def integralEmbedding (x : SplitOct) : ZornSplitOctonion ℚ :=
  ⟨x.a, x.b, x.x0, x.x1, x.x2, x.y0, x.y1, x.y2⟩

def integralLattice : Set (ZornSplitOctonion ℚ) :=
  Set.range integralEmbedding

theorem integral_norm (x : SplitOct) :
    norm (integralEmbedding x) = (detZ x : ℚ) := by
  cases x
  simp [integralEmbedding, norm, detZ]

theorem integral_mul_embedding (x y : SplitOct) :
    mul (integralEmbedding x) (integralEmbedding y) =
      integralEmbedding (mulZ x y) := by
  cases x with
  | mk a b x0 x1 x2 y0 y1 y2 =>
    cases y with
    | mk c d u0 u1 u2 v0 v1 v2 =>
      ext <;> simp [integralEmbedding, mul, mulZ]
      all_goals norm_num

theorem integral_lattice_mul_closed
    {x y : ZornSplitOctonion ℚ}
    (hx : x ∈ integralLattice) (hy : y ∈ integralLattice) :
    mul x y ∈ integralLattice := by
  rcases hx with ⟨x, rfl⟩
  rcases hy with ⟨y, rfl⟩
  exact ⟨mulZ x y, (integral_mul_embedding x y).symm⟩

/-- A concrete rational Cartan coordinate. -/
def cartanChargeFn (x : ZornSplitOctonion ℚ) : ℚ := x.a

def cartanCharge : ZornSplitOctonion ℚ →ₗ[ℚ] ℚ where
  toFun := cartanChargeFn
  map_add' := by intro x y; rfl
  map_smul' := by intro r x; rfl

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
    fin_cases i <;> simp [cartanCharge, cartanChargeFn, chargeState, chargeValue]
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩

end InfoGeometry.OperatorAlgebra.GenericZorn
