import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Concrete split Cayley coordinates

The coordinate-level split Cayley owner.  This file intentionally stops before
any claim identifying its automorphism group with a Chevalley group.
-/
namespace SplitCayley

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

def cross (u v : Vec3 R) : Vec3 R := ![
  u 1 * v 2 - u 2 * v 1,
  u 2 * v 0 - u 0 * v 2,
  u 0 * v 1 - u 1 * v 0]

def mul (x y : SplitCayley R) : SplitCayley R :=
  { a := x.a * y.a + dot x.u y.v
    u := x.a • y.u + y.b • x.u - cross x.v y.v
    v := x.b • y.v + y.a • x.v + cross x.u y.u
    b := x.b * y.b + dot x.v y.u }

instance : Mul (SplitCayley R) := ⟨mul⟩

def conj (x : SplitCayley R) : SplitCayley R := ⟨x.b, -x.u, -x.v, x.a⟩
def norm (x : SplitCayley R) : R := x.a * x.b - dot x.u x.v

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
      simp [cross_self_neg, smul_def]
    · change b • (-v) + b • v + cross u (-u) = (a * b - dot u v) • 0
      simp [cross_self_neg, smul_def]
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
      simp [cross_neg_self, smul_def]
    · change a • v + a • (-v) + cross (-u) u = (a * b - dot u v) • 0
      simp [cross_neg_self, smul_def]
    · change a * b + dot (-v) u = (a * b - dot u v) * 1
      simp [dot]
      ring

@[simp] theorem norm_conj (x : SplitCayley R) : norm (conj x) = norm x := by
  cases x
  simp [conj, norm, dot]
  ring

end SplitCayley
end SplitCayley
