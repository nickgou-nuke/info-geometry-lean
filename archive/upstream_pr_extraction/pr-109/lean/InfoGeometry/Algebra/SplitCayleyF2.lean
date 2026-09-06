import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! A self-contained split Cayley (Zorn matrix) carrier over `𝔽₂`.

The multiplication is the Zorn multiplication in Lopatin--Zubkov,
arXiv:2208.08122v3, §1.2.  The split form is `αβ - u⋅v`; it is not a
positive-definite octonion model and no existing G₂ owner is imported here.
-/

namespace InfoGeometry.Algebra.SplitCayleyF2

abbrev Scalar := ZMod 2
abbrev Vec3 := Fin 3 → Scalar
abbrev Mat3 := Matrix (Fin 3) (Fin 3) Scalar

@[simp] theorem vec3_literal_apply_zero (a b c : Scalar) :
    (![a, b, c] : Vec3) 0 = a := by
  rfl

@[simp] theorem vec3_literal_apply_one (a b c : Scalar) :
    (![a, b, c] : Vec3) 1 = b := by
  rfl

@[simp] theorem vec3_literal_apply_two (a b c : Scalar) :
    (![a, b, c] : Vec3) 2 = c := by
  rfl

@[ext]
structure Cayley where
  α : Scalar
  u : Vec3
  v : Vec3
  β : Scalar
deriving DecidableEq, Fintype

def dot (u v : Vec3) : Scalar := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

def cross (u v : Vec3) : Vec3 :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

def mul (x y : Cayley) : Cayley where
  α := x.α * y.α + dot x.u y.v
  u := fun i =>
    (x.α * y.u i + y.β * x.u i) - cross x.v y.v i
  v := fun i =>
    (y.α * x.v i + x.β * y.v i) + cross x.u y.u i
  β := dot x.v y.u + x.β * y.β

def one : Cayley :=
  { α := 1, u := ![0, 0, 0], v := ![0, 0, 0], β := 1 }

def zero : Cayley :=
  { α := 0, u := ![0, 0, 0], v := ![0, 0, 0], β := 0 }

def add (x y : Cayley) : Cayley where
  α := x.α + y.α
  u := fun i => x.u i + y.u i
  v := fun i => x.v i + y.v i
  β := x.β + y.β

theorem add_zero (x : Cayley) : add x zero = x := by
  apply Cayley.ext
  · simp [add, zero]
  · funext i
    fin_cases i <;> simp [add, zero]
  · funext i
    fin_cases i <;> simp [add, zero]
  · simp [add, zero]

theorem zero_add (x : Cayley) : add zero x = x := by
  apply Cayley.ext
  · simp [add, zero]
  · funext i
    fin_cases i <;> simp [add, zero]
  · funext i
    fin_cases i <;> simp [add, zero]
  · simp [add, zero]

def norm (x : Cayley) : Scalar := x.α * x.β - dot x.u x.v

/-! The two elementary automorphism formulas from Lopatin--Zubkov §1.3.
They are recorded before any claim that they preserve multiplication. -/

def delta1 (r : Vec3) (x : Cayley) : Cayley where
  α := x.α - dot r x.v
  u := fun i => (x.α - x.β - dot r x.v) * r i + x.u i
  v := fun i => x.v i - cross x.u r i
  β := x.β + dot r x.v

def delta2 (r : Vec3) (x : Cayley) : Cayley where
  α := x.α + dot x.u r
  u := fun i => x.u i + cross x.v r i
  v := fun i => (-x.α + x.β - dot x.u r) * r i + x.v i
  β := x.β - dot x.u r

/-! A concrete even permutation from `SL₃(F₂)`. -/
def cyclic (u : Vec3) : Vec3 := ![u 2, u 0, u 1]

def cyclicAction (x : Cayley) : Cayley :=
  { α := x.α, u := cyclic x.u, v := cyclic x.v, β := x.β }

def cyclicMatrix : Mat3 :=
  !![0, 1, 0; 0, 0, 1; 1, 0, 0]

def shearU (u : Vec3) : Vec3 := ![u 0 + u 1, u 1, u 2]

def shearV (v : Vec3) : Vec3 := ![v 0, v 1 + v 0, v 2]

def shearAction (x : Cayley) : Cayley :=
  { α := x.α, u := shearU x.u, v := shearV x.v, β := x.β }

def shearMatrix : Mat3 :=
  !![1, 0, 0; 1, 1, 0; 0, 0, 1]

theorem cyclicMatrix_det : cyclicMatrix.det = 1 := by
  decide

theorem shearMatrix_det : shearMatrix.det = 1 := by
  decide

instance : Mul Cayley := ⟨mul⟩
instance : One Cayley := ⟨one⟩

structure Automorphism where
  toEquiv : Cayley ≃ Cayley
  map_mul' : ∀ x y, toEquiv (x * y) = toEquiv x * toEquiv y
  map_one' : toEquiv 1 = 1

instance : CoeFun Automorphism (fun _ => Cayley → Cayley) :=
  ⟨fun φ => φ.toEquiv⟩

@[simp] theorem dot_comm (u v : Vec3) : dot u v = dot v u := by
  simp [dot, mul_comm]

@[simp] theorem cross_self (u : Vec3) : cross u u = 0 := by
  funext i
  fin_cases i <;> simp [cross, mul_comm]

theorem dot_cross_left (u v : Vec3) : dot u (cross u v) = 0 := by
  simp [dot, cross]
  ring

theorem dot_cross_right (u v : Vec3) : dot u (cross v u) = 0 := by
  simp [dot, cross]
  ring

theorem dot_cross_cyclic (u v w : Vec3) :
    dot u (cross v w) = dot v (cross w u) := by
  simp [dot, cross]
  ring

theorem cross_dot_product (u v w z : Vec3) :
    dot (cross u v) (cross w z) =
      dot u w * dot v z - dot u z * dot v w := by
  simp [dot, cross]
  ring

end InfoGeometry.Algebra.SplitCayleyF2
