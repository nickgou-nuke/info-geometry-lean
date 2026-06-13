import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic

namespace InfoGeometry.Algebra

variable (R : Type*) [CommRing R]

abbrev Vec3 := Fin 3 → R

namespace Vec3

variable {R : Type*} [CommRing R]

def dot (v w : Vec3 R) : R :=
  v 0 * w 0 + v 1 * w 1 + v 2 * w 2

def cross (v w : Vec3 R) : Vec3 R :=
  ![v 1 * w 2 - v 2 * w 1,
    v 2 * w 0 - v 0 * w 2,
    v 0 * w 1 - v 1 * w 0]

def add (v w : Vec3 R) : Vec3 R :=
  ![v 0 + w 0, v 1 + w 1, v 2 + w 2]

def sub (v w : Vec3 R) : Vec3 R :=
  ![v 0 - w 0, v 1 - w 1, v 2 - w 2]

def smul (r : R) (v : Vec3 R) : Vec3 R :=
  ![r * v 0, r * v 1, r * v 2]

end Vec3

/-- Zorn matrices represent Split Octonions over R, possessing non-associative limits. --/
@[ext]
structure ZornMatrix where
  a : R
  v : Vec3 R
  w : Vec3 R
  b : R

namespace ZornMatrix

variable {R : Type*} [CommRing R]

def zornTrace (Z : ZornMatrix R) : R := 
  Z.a + Z.b

def zornNorm (Z : ZornMatrix R) : R :=
  Z.a * Z.b - Vec3.dot Z.v Z.w 

def add (X Y : ZornMatrix R) : ZornMatrix R where
  a := X.a + Y.a
  v := Vec3.add X.v Y.v
  w := Vec3.add X.w Y.w
  b := X.b + Y.b

def sub (X Y : ZornMatrix R) : ZornMatrix R where
  a := X.a - Y.a
  v := Vec3.sub X.v Y.v
  w := Vec3.sub X.w Y.w
  b := X.b - Y.b

def smul (r : R) (X : ZornMatrix R) : ZornMatrix R where
  a := r * X.a
  v := Vec3.smul r X.v
  w := Vec3.smul r X.w
  b := r * X.b

def mul (X Y : ZornMatrix R) : ZornMatrix R where
  a := X.a * Y.a + Vec3.dot X.v Y.w
  v := Vec3.sub (Vec3.add (Vec3.smul X.a Y.v) (Vec3.smul Y.b X.v)) (Vec3.cross X.w Y.w)
  w := Vec3.add (Vec3.add (Vec3.smul Y.a X.w) (Vec3.smul X.b Y.w)) (Vec3.cross X.v Y.v)
  b := Vec3.dot X.w Y.v + X.b * Y.b

def I : ZornMatrix R where
  a := 1
  v := ![0, 0, 0]
  w := ![0, 0, 0]
  b := 1

def zero : ZornMatrix R where
  a := 0
  v := ![0, 0, 0]
  w := ![0, 0, 0]
  b := 0

instance : Add (ZornMatrix R) := ⟨add⟩
instance : Sub (ZornMatrix R) := ⟨sub⟩
instance : Mul (ZornMatrix R) := ⟨mul⟩
instance : HSMul R (ZornMatrix R) (ZornMatrix R) := ⟨smul⟩
instance : Zero (ZornMatrix R) := ⟨zero⟩

lemma dot_cross_self (v : Vec3 R) : Vec3.dot v (Vec3.cross v v) = 0 := by
  dsimp [Vec3.dot, Vec3.cross]
  ring

lemma cross_self (v : Vec3 R) : Vec3.cross v v = ![0, 0, 0] := by
  dsimp [Vec3.cross]
  funext i
  fin_cases i <;> simp <;> ring

/-- 
The 2-Potent Operator Boundary Limit of the Zorn matrix.
Even though the Zorn matrix multiplication is non-associative,
each element satisfies its characteristic equation.
X^2 - Tr(X)X + Det(X)I = 0
-/
theorem zorn_characteristic_equation (X : ZornMatrix R) :
    X * X - (zornTrace X) • X + (zornNorm X) • (I : ZornMatrix R) = (0 : ZornMatrix R) := by
  sorry

end ZornMatrix
end InfoGeometry.Algebra
