import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Concrete split Cayley coordinates

The coordinate-level split Cayley owner.  This file intentionally stops before
any claim identifying its automorphism group with a Chevalley group.
-/
namespace InfoGeometry.Algebra.Zorn

abbrev Vec3 (R : Type*) := Fin 3 → R

structure SplitCayley (R : Type*) where
  a : R
  u : Vec3 R
  v : Vec3 R
  b : R

namespace SplitCayley

variable {R : Type*} [CommRing R]

@[ext] theorem ext {x y : SplitCayley R}
    (ha : x.a = y.a) (hu : x.u = y.u) (hv : x.v = y.v) (hb : x.b = y.b) : x = y := by
  cases x
  cases y
  simp_all

instance : Zero (SplitCayley R) := ⟨⟨0, 0, 0, 0⟩⟩
instance : One (SplitCayley R) := ⟨⟨1, 0, 0, 1⟩⟩
instance : Add (SplitCayley R) := ⟨fun x y => ⟨x.a + y.a, x.u + y.u, x.v + y.v, x.b + y.b⟩⟩
instance : Neg (SplitCayley R) := ⟨fun x => ⟨-x.a, -x.u, -x.v, -x.b⟩⟩
instance : Sub (SplitCayley R) := ⟨fun x y => ⟨x.a - y.a, x.u - y.u, x.v - y.v, x.b - y.b⟩⟩
instance : SMul R (SplitCayley R) := ⟨fun r x => ⟨r * x.a, r • x.u, r • x.v, r * x.b⟩⟩

@[simp] theorem one_a : (1 : SplitCayley R).a = 1 := rfl
@[simp] theorem one_u : (1 : SplitCayley R).u = 0 := rfl
@[simp] theorem one_v : (1 : SplitCayley R).v = 0 := rfl
@[simp] theorem one_b : (1 : SplitCayley R).b = 1 := rfl

@[simp] theorem smul_def (r : R) (x : SplitCayley R) :
    r • x = ⟨r * x.a, r • x.u, r • x.v, r * x.b⟩ := rfl

def dot (u v : Vec3 R) : R := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

theorem dot_swap (u v : Vec3 R) : dot u v = dot v u := by
  simp [dot]
  ring

theorem dot_neg_left (u v : Vec3 R) : dot (-u) v = -dot u v := by
  simp [dot]
  ring

theorem dot_neg_right (u v : Vec3 R) : dot u (-v) = -dot u v := by
  simp [dot]
  ring

def cross (u v : Vec3 R) : Vec3 R := ![
  u 1 * v 2 - u 2 * v 1,
  u 2 * v 0 - u 0 * v 2,
  u 0 * v 1 - u 1 * v 0]

theorem cross_eq_mathlib (u v : Vec3 R) :
    cross u v = crossProduct u v := by
  funext i
  fin_cases i <;> simp [cross, cross_apply]

theorem cross_swap (u v : Vec3 R) : cross u v = -cross v u := by
  funext i
  fin_cases i <;> simp [cross] <;> ring

theorem cross_add_left (u u' v : Vec3 R) :
    cross (u + u') v = cross u v + cross u' v := by
  funext i
  fin_cases i <;> simp [cross] <;> ring

theorem cross_add_right (u v v' : Vec3 R) :
    cross u (v + v') = cross u v + cross u v' := by
  funext i
  fin_cases i <;> simp [cross] <;> ring

theorem cross_smul_left (r : R) (u v : Vec3 R) :
    cross (r • u) v = r • cross u v := by
  funext i
  fin_cases i <;> simp [cross, Pi.smul_apply] <;> ring

theorem cross_smul_right (r : R) (u v : Vec3 R) :
    cross u (r • v) = r • cross u v := by
  funext i
  fin_cases i <;> simp [cross, Pi.smul_apply] <;> ring

theorem cross_neg_left (u v : Vec3 R) :
    cross (-u) v = -cross u v := by
  rw [show -u = (-1 : R) • u by ext i; simp]
  rw [cross_smul_left]
  simp

theorem cross_neg_right (u v : Vec3 R) :
    cross u (-v) = -cross u v := by
  rw [show -v = (-1 : R) • v by ext i; simp]
  rw [cross_smul_right]
  simp

theorem cross_neg_neg (u v : Vec3 R) :
    cross (-u) (-v) = cross u v := by
  rw [cross_neg_left, cross_neg_right]
  simp

theorem dot_cross_left (u v : Vec3 R) : dot u (cross u v) = 0 := by
  simp [dot, cross]
  ring

theorem dot_cross_right (u v : Vec3 R) : dot v (cross u v) = 0 := by
  simp [dot, cross]
  ring

theorem cross_norm_sq (u v : Vec3 R) :
    dot (cross u v) (cross u v) =
      dot u u * dot v v - dot u v * dot u v := by
  simp [dot, cross]
  ring

theorem dot_cross_det (u v w : Vec3 R) :
    dot u (cross v w) = Matrix.det ![u, v, w] := by
  simp [dot, cross, Matrix.det_fin_three]
  ring

/- The scalar triple product is the orientation 3-form represented by the
   coordinate cross product.  Keeping this as a theorem (rather than adding
   an abstract form field) makes the determinant the source of truth. -/
def volume3 (u v w : Vec3 R) : R := dot u (cross v w)

/-- The native oriented volume pairing as an actual trilinear alternating map.
It is Mathlib's determinant alternating map, not a structure carrying assumed
alternation laws. -/
def volume3Alternating : (Vec3 R) [⋀^Fin 3]→ₗ[R] R :=
  Matrix.detRowAlternating

@[simp] theorem volume3Alternating_apply (u v w : Vec3 R) :
    volume3Alternating ![u, v, w] = Matrix.det ![u, v, w] :=
  rfl

theorem volume3_eq_det (u v w : Vec3 R) :
    volume3 u v w = Matrix.det ![u, v, w] := by
  exact dot_cross_det u v w

/-- The scalar triple product is exactly the evaluation of the native
alternating volume tensor. -/
theorem volume3_eq_alternating (u v w : Vec3 R) :
    volume3 u v w = volume3Alternating ![u, v, w] := by
  rw [volume3_eq_det, volume3Alternating_apply]

/-- Repeated arguments vanish by the native `AlternatingMap` law. -/
theorem volume3Alternating_eq_zero_of_eq
    (u : Fin 3 → Vec3 R) {i j : Fin 3} (h : u i = u j) (hij : i ≠ j) :
    volume3Alternating u = 0 :=
  volume3Alternating.map_eq_zero_of_eq u h hij

theorem dot_cross_cyclic (u v w : Vec3 R) :
    dot (cross u v) w = dot u (cross v w) := by
  simp [dot, cross]
  ring

/-- Cyclic permutation preserves the native oriented volume tensor. -/
theorem volume3_cyclic (u v w : Vec3 R) :
    volume3 u v w = volume3 v w u := by
  rw [volume3_eq_det, volume3_eq_det]
  simp [Matrix.det_fin_three]
  ring

/-- Moving the last two inputs across the cross/dot pairing reverses sign. -/
theorem dot_cross_swap_right (u v w : Vec3 R) :
    dot (cross u v) w = -dot (cross u w) v := by
  rw [dot_cross_cyclic, dot_cross_cyclic]
  rw [cross_swap]
  simp [dot]
  ring

theorem volume3_swap_first_second (u v w : Vec3 R) :
    volume3 v u w = -volume3 u v w := by
  rw [volume3_eq_det, volume3_eq_det]
  simp [Matrix.det_fin_three]
  ring

theorem volume3_swap_second_third (u v w : Vec3 R) :
    volume3 u w v = -volume3 u v w := by
  calc
    volume3 u w v = volume3 w v u := volume3_cyclic u w v
    _ = -volume3 v w u := volume3_swap_first_second v w u
    _ = -volume3 u v w := by
      rw [volume3_cyclic v w u, volume3_cyclic w u v]

theorem volume3_swap_first_third (u v w : Vec3 R) :
    volume3 w v u = -volume3 u v w := by
  calc
    volume3 w v u = -volume3 v w u := volume3_swap_first_second v w u
    _ = -volume3 u v w := by
      rw [volume3_cyclic v w u, volume3_cyclic w u v]

theorem volume3_repeated (u w : Vec3 R) : volume3 u u w = 0 := by
  rw [volume3_eq_det]
  simp [Matrix.det_fin_three]
  ring

/- The Euclidean dot pairing on the concrete three-slot carrier is
   nondegenerate.  Thus the cross product is characterized by its scalar
   triple-product pairing, not merely by a coordinate formula. -/
theorem cross_eq_of_dot_eq (u v x : Vec3 R)
    (h : ∀ w, dot w x = dot w (cross u v)) :
    x = cross u v := by
  funext i
  have hi := h (Pi.single i 1)
  fin_cases i <;> simpa [dot, Pi.single_apply] using hi

/-- The coordinate cross product is uniquely determined by the metric and the
oriented volume pairing.  Thus `cross v w` is not extra structure beyond the
proved scalar-triple-product identity in this finite model. -/
theorem dot_eq_det_iff_eq_cross (x v w : Vec3 R) :
    (∀ u : Vec3 R, dot u x = Matrix.det ![u, v, w]) ↔ x = cross v w := by
  constructor
  · intro h
    have h0 := h ![(1 : R), 0, 0]
    have h1 := h ![(0 : R), 1, 0]
    have h2 := h ![(0 : R), 0, 1]
    ext i
    fin_cases i
    · simpa [dot, cross, Matrix.det_fin_three] using h0
    · simpa [dot, cross, Matrix.det_fin_three, sub_eq_add_neg, add_comm] using h1
    · simpa [dot, cross, Matrix.det_fin_three] using h2
  · rintro rfl u
    exact dot_cross_det u v w

def mul (x y : SplitCayley R) : SplitCayley R :=
  { a := x.a * y.a + dot x.u y.v
    u := x.a • y.u + y.b • x.u - cross x.v y.v
    v := x.b • y.v + y.a • x.v + cross x.u y.u
    b := x.b * y.b + dot x.v y.u }

theorem mul_a_native (x y : SplitCayley R) :
    (mul x y).a = x.a * y.a + dot x.u y.v := by
  rfl

theorem mul_b_native (x y : SplitCayley R) :
    (mul x y).b = x.b * y.b + dot x.v y.u := by
  rfl

theorem mul_u_native (x y : SplitCayley R) :
    (mul x y).u = x.a • y.u + y.b • x.u - crossProduct x.v y.v := by
  simp [mul, cross_eq_mathlib]

theorem mul_v_native (x y : SplitCayley R) :
    (mul x y).v = x.b • y.v + y.a • x.v + crossProduct x.u y.u := by
  simp [mul, cross_eq_mathlib]

instance : Mul (SplitCayley R) := ⟨mul⟩

@[simp] theorem mul_one (x : SplitCayley R) : x * (1 : SplitCayley R) = x := by
  rcases x with ⟨a, u, v, b⟩
  change mul { a := a, u := u, v := v, b := b }
      { a := 1, u := 0, v := 0, b := 1 } =
    { a := a, u := u, v := v, b := b }
  apply ext
  · simp [mul, dot]
  · funext i
    fin_cases i <;> simp [mul, cross]
  · funext i
    fin_cases i <;> simp [mul, cross]
  · simp [mul, dot]

@[simp] theorem one_mul (x : SplitCayley R) : (1 : SplitCayley R) * x = x := by
  rcases x with ⟨a, u, v, b⟩
  change mul (1 : SplitCayley R)
      { a := a, u := u, v := v, b := b } =
    { a := a, u := u, v := v, b := b }
  apply ext
  · simp [mul, dot]
  · funext i
    fin_cases i <;> simp [mul, cross]
  · funext i
    fin_cases i <;> simp [mul, cross]
  · simp [mul, dot]

@[simp] theorem mul_zero (x : SplitCayley R) : x * (0 : SplitCayley R) = 0 := by
  rcases x with ⟨a, u, v, b⟩
  change mul { a := a, u := u, v := v, b := b }
      { a := 0, u := 0, v := 0, b := 0 } =
        ({ a := 0, u := 0, v := 0, b := 0 } : SplitCayley R)
  apply ext
  · simp [mul, dot]
  · funext i
    fin_cases i <;> simp [mul, cross] <;> rfl
  · funext i
    fin_cases i <;> simp [mul, cross] <;> rfl
  · simp [mul, dot]

@[simp] theorem zero_mul (x : SplitCayley R) : (0 : SplitCayley R) * x = 0 := by
  rcases x with ⟨a, u, v, b⟩
  change mul ({ a := 0, u := 0, v := 0, b := 0 } : SplitCayley R)
      { a := a, u := u, v := v, b := b } =
        ({ a := 0, u := 0, v := 0, b := 0 } : SplitCayley R)
  apply ext
  · simp [mul, dot]
  · funext i
    fin_cases i <;> simp [mul, cross] <;> rfl
  · funext i
    fin_cases i <;> simp [mul, cross] <;> rfl
  · simp [mul, dot]

def conj (x : SplitCayley R) : SplitCayley R := ⟨x.b, -x.u, -x.v, x.a⟩

def norm (x : SplitCayley R) : R := x.a * x.b - dot x.u x.v

theorem conj_a_native (x : SplitCayley R) :
    (conj x).a = x.b := by
  rfl

theorem conj_b_native (x : SplitCayley R) :
    (conj x).b = x.a := by
  rfl

@[simp] theorem cross_self_neg (w : Vec3 R) : cross w (-w) = 0 := by
  funext i
  fin_cases i <;> simp [cross] <;> ring

@[simp] theorem cross_neg_self (w : Vec3 R) : cross (-w) w = 0 := by
  funext i
  fin_cases i <;> simp [cross] <;> ring

@[simp] theorem conj_involutive (x : SplitCayley R) : conj (conj x) = x := by
  cases x
  ext <;> simp [conj]

@[simp] theorem mul_conj (x : SplitCayley R) :
    x * conj x = norm x • (1 : SplitCayley R) := by
  cases x with
  | mk a u v b =>
    change mul { a := a, u := u, v := v, b := b } (conj { a := a, u := u, v := v, b := b }) =
      norm { a := a, u := u, v := v, b := b } • (1 : SplitCayley R)
    apply ext
    all_goals dsimp [mul, conj, norm]
    · change a * b + dot u (-v) = (a * b - dot u v) * 1
      simp [dot]
      ring
    · change a • (-u) + a • u - cross v (-v) = (a * b - dot u v) • 0
      simp [cross_self_neg]
    · change b • (-v) + b • v + cross u (-u) = (a * b - dot u v) • 0
      simp [cross_self_neg]
    · change b * a + dot v (-u) = (a * b - dot u v) * 1
      simp [dot]
      ring

@[simp] theorem conj_mul (x : SplitCayley R) :
    conj x * x = norm x • (1 : SplitCayley R) := by
  cases x with
  | mk a u v b =>
    change mul (conj { a := a, u := u, v := v, b := b }) { a := a, u := u, v := v, b := b } =
      norm { a := a, u := u, v := v, b := b } • (1 : SplitCayley R)
    apply ext
    all_goals dsimp [mul, conj, norm]
    · change b * a + dot (-u) v = (a * b - dot u v) * 1
      simp [dot]
      ring
    · change b • u + b • (-u) - cross (-v) v = (a * b - dot u v) • 0
      simp [cross_neg_self]
    · change a • v + a • (-v) + cross (-u) u = (a * b - dot u v) • 0
      simp [cross_neg_self]
    · change a * b + dot (-v) u = (a * b - dot u v) * 1
      simp [dot]
      ring

@[simp] theorem norm_conj (x : SplitCayley R) : norm (conj x) = norm x := by
  cases x
  simp [conj, norm, dot]
  ring

@[simp] theorem norm_one : norm (1 : SplitCayley R) = 1 := by
  simp [norm, dot]

@[simp] theorem norm_zero : norm (0 : SplitCayley R) = 0 := by
  change (0 : R) * 0 - dot (0 : Vec3 R) 0 = 0
  simp [dot]

@[simp] theorem norm_neg (x : SplitCayley R) : norm (-x) = norm x := by
  rcases x with ⟨a, u, v, b⟩
  change (-a) * (-b) - dot (-u) (-v) = a * b - dot u v
  simp [dot]

/-- The split Cayley quadratic form is multiplicative for the native product. -/
theorem norm_mul (x y : SplitCayley R) : norm (x * y) = norm x * norm y := by
  rcases x with ⟨a, u, v, b⟩
  rcases y with ⟨c, p, q, d⟩
  change
    (a * c + dot u q) * (b * d + dot v p) -
        dot (a • p + d • u - cross v q) (b • q + c • v + cross u p) =
      (a * b - dot u v) * (c * d - dot p q)
  simp [dot, cross, Pi.smul_apply]
  ring

@[simp] theorem norm_smul (r : R) (x : SplitCayley R) :
    norm (r • x) = r * r * norm x := by
  rcases x with ⟨a, u, v, b⟩
  simp [smul_def, norm, dot, Pi.smul_apply]
  ring

@[simp] theorem norm_smul_one (r : R) :
    norm (r • (1 : SplitCayley R)) = r * r := by
  rw [norm_smul, norm_one]
  simp

theorem conj_mul_reverse (x y : SplitCayley R) :
    conj (x * y) = conj y * conj x := by
  rcases x with ⟨a, u, v, b⟩
  rcases y with ⟨c, p, q, d⟩
  change conj (mul { a := a, u := u, v := v, b := b }
      { a := c, u := p, v := q, b := d }) =
    mul (conj { a := c, u := p, v := q, b := d })
      (conj { a := a, u := u, v := v, b := b })
  dsimp [conj, mul]
  apply ext
  · change b * d + dot v p = d * b + dot (-p) (-v)
    rw [dot_neg_left, dot_neg_right, dot_swap]
    ring
  · change -(a • p + d • u - cross v q) =
      d • (-u) + a • (-p) - cross (-q) (-v)
    rw [cross_neg_neg]
    rw [cross_swap q v]
    module
  · change -(b • q + c • v + cross u p) =
      c • (-v) + b • (-q) + cross (-p) (-u)
    rw [cross_neg_neg]
    rw [cross_swap p u]
    module
  · change a * c + dot u q = c * a + dot (-q) (-u)
    rw [dot_neg_left, dot_neg_right, dot_swap]
    ring

end SplitCayley
end InfoGeometry.Algebra.Zorn
