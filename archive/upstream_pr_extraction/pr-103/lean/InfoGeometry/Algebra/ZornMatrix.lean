import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.NoncommRing

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

theorem cross_add_swap (v w : Vec3 R) :
    Vec3.add (Vec3.cross v w) (Vec3.cross w v) = ![0, 0, 0] := by
  funext i
  fin_cases i <;>
    simp [Vec3.add, Vec3.cross] <;>
    ring

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

/-- The additive/module transport equivalence for the native Zorn carrier. -/
def coordEquiv : ZornMatrix R ≃ (R × (Fin 3 → R) × (Fin 3 → R) × R) where
  toFun Z := (Z.a, Z.v, Z.w, Z.b)
  invFun c := { a := c.1, v := c.2.1, w := c.2.2.1, b := c.2.2.2 }
  left_inv Z := by
    cases Z
    rfl
  right_inv c := by
    rcases c with ⟨a, v, w, b⟩
    rfl

/-- Standard coordinate vector in `R^3`. --/
def Vec3.basis (i : Fin 3) : Vec3 R :=
  fun j => if j = i then 1 else 0

@[simp] theorem Vec3.basis_expand (i : Fin 3) :
    ![Vec3.basis (R := R) i 0, Vec3.basis (R := R) i 1,
      Vec3.basis (R := R) i 2] = Vec3.basis (R := R) i := by
  funext j
  fin_cases j <;> rfl

/-- Upper-left diagonal idempotent. --/
def E11 : ZornMatrix R where
  a := 1
  v := ![0, 0, 0]
  w := ![0, 0, 0]
  b := 0

/-- Lower-right diagonal idempotent. --/
def E22 : ZornMatrix R where
  a := 0
  v := ![0, 0, 0]
  w := ![0, 0, 0]
  b := 1

/-- Upper off-diagonal Zorn basis element. --/
def U (i : Fin 3) : ZornMatrix R where
  a := 0
  v := Vec3.basis i
  w := ![0, 0, 0]
  b := 0

/-- Lower off-diagonal Zorn basis element. --/
def V (i : Fin 3) : ZornMatrix R where
  a := 0
  v := ![0, 0, 0]
  w := Vec3.basis i
  b := 0

instance : Add (ZornMatrix R) := ⟨add⟩
instance : Sub (ZornMatrix R) := ⟨sub⟩
instance : Mul (ZornMatrix R) := ⟨mul⟩
instance : HSMul R (ZornMatrix R) (ZornMatrix R) := ⟨smul⟩
instance : Zero (ZornMatrix R) := ⟨zero⟩

instance : AddCommGroup (ZornMatrix R) :=
  Equiv.addCommGroup coordEquiv

instance : Module R (ZornMatrix R) :=
  Equiv.module R coordEquiv

@[simp] theorem add_apply (X Y : ZornMatrix R) : (X + Y) = add X Y := rfl

@[simp] theorem smul_apply (r : R) (X : ZornMatrix R) : r • X = smul r X := rfl

@[simp] theorem mul_eq_mul (X Y : ZornMatrix R) : X * Y = mul X Y := rfl

@[simp] theorem mul_a (X Y : ZornMatrix R) :
    (X * Y).a = X.a * Y.a + Vec3.dot X.v Y.w := rfl

@[simp] theorem mul_v (X Y : ZornMatrix R) :
    (X * Y).v =
      Vec3.sub
        (Vec3.add (Vec3.smul X.a Y.v) (Vec3.smul Y.b X.v))
        (Vec3.cross X.w Y.w) := rfl

@[simp] theorem mul_w (X Y : ZornMatrix R) :
    (X * Y).w =
      Vec3.add
        (Vec3.add (Vec3.smul Y.a X.w) (Vec3.smul X.b Y.w))
        (Vec3.cross X.v Y.v) := rfl

@[simp] theorem mul_b (X Y : ZornMatrix R) :
    (X * Y).b = Vec3.dot X.w Y.v + X.b * Y.b := rfl

theorem zornNorm_mul (X Y : ZornMatrix R) :
    zornNorm (X * Y) = zornNorm X * zornNorm Y := by
  simp [zornNorm, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul] ;
    ring

@[simp] theorem add_a (X Y : ZornMatrix R) : (X + Y).a = X.a + Y.a := rfl

@[simp] theorem add_v (X Y : ZornMatrix R) : (X + Y).v = Vec3.add X.v Y.v := rfl

@[simp] theorem add_w (X Y : ZornMatrix R) : (X + Y).w = Vec3.add X.w Y.w := rfl

@[simp] theorem add_b (X Y : ZornMatrix R) : (X + Y).b = X.b + Y.b := rfl

@[simp] theorem sub_a (X Y : ZornMatrix R) : (X - Y).a = X.a - Y.a := rfl

@[simp] theorem sub_v (X Y : ZornMatrix R) : (X - Y).v = Vec3.sub X.v Y.v := rfl

@[simp] theorem sub_w (X Y : ZornMatrix R) : (X - Y).w = Vec3.sub X.w Y.w := rfl

@[simp] theorem sub_b (X Y : ZornMatrix R) : (X - Y).b = X.b - Y.b := rfl

@[simp] theorem smul_a (r : R) (X : ZornMatrix R) : (r • X).a = r * X.a := rfl

@[simp] theorem smul_v (r : R) (X : ZornMatrix R) : (r • X).v = Vec3.smul r X.v := rfl

@[simp] theorem smul_w (r : R) (X : ZornMatrix R) : (r • X).w = Vec3.smul r X.w := rfl

@[simp] theorem smul_b (r : R) (X : ZornMatrix R) : (r • X).b = r * X.b := rfl

@[simp] theorem neg_a (X : ZornMatrix R) : (-X).a = -X.a := rfl

@[simp] theorem neg_v (X : ZornMatrix R) : (-X).v = fun i => -X.v i := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem neg_w (X : ZornMatrix R) : (-X).w = fun i => -X.w i := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem neg_b (X : ZornMatrix R) : (-X).b = -X.b := rfl

@[simp] theorem zero_eq_zero : (0 : ZornMatrix R) = zero := rfl

@[simp] theorem E11_mul_E11 : (E11 : ZornMatrix R) * E11 = E11 := by
  ext j <;>
    simp [E11, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

@[simp] theorem E22_mul_E22 : (E22 : ZornMatrix R) * E22 = E22 := by
  ext j <;>
    simp [E22, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

@[simp] theorem E11_mul_E22 : (E11 : ZornMatrix R) * E22 = 0 := by
  ext j <;>
    simp [E11, E22, zero, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

@[simp] theorem E22_mul_E11 : (E22 : ZornMatrix R) * E11 = 0 := by
  ext j <;>
    simp [E11, E22, zero, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

@[simp] theorem E11_add_E22 :
    (E11 : ZornMatrix R) + E22 = I := by
  apply ZornMatrix.ext
  · simp [E11, E22, I, add]
  · funext j; fin_cases j <;> simp [E11, E22, I, add, Vec3.add]
  · funext j; fin_cases j <;> simp [E11, E22, I, add, Vec3.add]
  · simp [E11, E22, I, add]

@[simp] theorem I_mul (X : ZornMatrix R) : (I : ZornMatrix R) * X = X := by
  apply ZornMatrix.ext
  · simp [I, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
  · funext j; fin_cases j <;>
      simp [I, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
  · funext j; fin_cases j <;>
      simp [I, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
  · simp [I, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

@[simp] theorem mul_I (X : ZornMatrix R) : X * (I : ZornMatrix R) = X := by
  apply ZornMatrix.ext
  · simp [I, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
  · funext j; fin_cases j <;>
      simp [I, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
  · funext j; fin_cases j <;>
      simp [I, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
  · simp [I, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

@[simp] theorem E11_mul_U (i : Fin 3) : (E11 : ZornMatrix R) * U i = U i := by
  apply ZornMatrix.ext
  · simp [E11, U, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]
  · funext j; simp [E11, U, mul, Vec3.dot, Vec3.cross, Vec3.add,
      Vec3.sub, Vec3.smul]
  · funext j; simp [E11, U, mul, Vec3.dot, Vec3.cross, Vec3.add,
      Vec3.sub, Vec3.smul]
  · simp [E11, U, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]

@[simp] theorem U_mul_E22 (i : Fin 3) : (U i : ZornMatrix R) * E22 = U i := by
  apply ZornMatrix.ext
  · simp [E22, U, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]
  · funext j; simp [E22, U, mul, Vec3.dot, Vec3.cross, Vec3.add,
      Vec3.sub, Vec3.smul]
  · funext j; simp [E22, U, mul, Vec3.dot, Vec3.cross, Vec3.add,
      Vec3.sub, Vec3.smul]
  · simp [E22, U, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]

@[simp] theorem E22_mul_V (i : Fin 3) : (E22 : ZornMatrix R) * V i = V i := by
  apply ZornMatrix.ext
  · simp [E22, V, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]
  · funext j; simp [E22, V, mul, Vec3.dot, Vec3.cross, Vec3.add,
      Vec3.sub, Vec3.smul]
  · funext j; simp [E22, V, mul, Vec3.dot, Vec3.cross, Vec3.add,
      Vec3.sub, Vec3.smul]
  · simp [E22, V, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]

@[simp] theorem V_mul_E11 (i : Fin 3) : (V i : ZornMatrix R) * E11 = V i := by
  apply ZornMatrix.ext
  · simp [E11, V, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]
  · funext j; simp [E11, V, mul, Vec3.dot, Vec3.cross, Vec3.add,
      Vec3.sub, Vec3.smul]
  · funext j; simp [E11, V, mul, Vec3.dot, Vec3.cross, Vec3.add,
      Vec3.sub, Vec3.smul]
  · simp [E11, V, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]

@[simp] theorem E11_mul_V (i : Fin 3) : (E11 : ZornMatrix R) * V i = 0 := by
  apply ZornMatrix.ext
  · simp [E11, V, zero, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]
  · funext j; simp [E11, V, zero, mul, Vec3.dot, Vec3.cross, Vec3.add,
      Vec3.sub, Vec3.smul]
  · funext j; simp [E11, V, zero, mul, Vec3.dot, Vec3.cross, Vec3.add,
      Vec3.sub, Vec3.smul]
  · simp [E11, V, zero, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]

@[simp] theorem V_mul_E22 (i : Fin 3) : (V i : ZornMatrix R) * E22 = 0 := by
  apply ZornMatrix.ext
  · simp [E22, V, zero, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]
  · funext j; simp [E22, V, zero, mul, Vec3.dot, Vec3.cross, Vec3.add,
      Vec3.sub, Vec3.smul]
  · funext j; simp [E22, V, zero, mul, Vec3.dot, Vec3.cross, Vec3.add,
      Vec3.sub, Vec3.smul]
  · simp [E22, V, zero, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]

@[simp] theorem E22_mul_U (i : Fin 3) : (E22 : ZornMatrix R) * U i = 0 := by
  apply ZornMatrix.ext
  · simp [E22, U, zero, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]
  · funext j; simp [E22, U, zero, mul, Vec3.dot, Vec3.cross, Vec3.add,
      Vec3.sub, Vec3.smul]
  · funext j; simp [E22, U, zero, mul, Vec3.dot, Vec3.cross, Vec3.add,
      Vec3.sub, Vec3.smul]
  · simp [E22, U, zero, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]

@[simp] theorem U_mul_E11 (i : Fin 3) : (U i : ZornMatrix R) * E11 = 0 := by
  apply ZornMatrix.ext
  · simp [E11, U, zero, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]
  · funext j; simp [E11, U, zero, mul, Vec3.dot, Vec3.cross, Vec3.add,
      Vec3.sub, Vec3.smul]
  · funext j; simp [E11, U, zero, mul, Vec3.dot, Vec3.cross, Vec3.add,
      Vec3.sub, Vec3.smul]
  · simp [E11, U, zero, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]

@[simp] theorem U_mul_self_zero (i : Fin 3) : (U i : ZornMatrix R) * U i = 0 := by
  fin_cases i <;>
    ext j <;>
      simp [U, zero, Vec3.basis, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

@[simp] theorem V_mul_self_zero (i : Fin 3) : (V i : ZornMatrix R) * V i = 0 := by
  fin_cases i <;>
    ext j <;>
      simp [V, zero, Vec3.basis, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

@[simp] theorem U_mul_V_self (i : Fin 3) : (U i : ZornMatrix R) * V i = E11 := by
  fin_cases i <;>
    ext j <;>
      simp [U, V, E11, Vec3.basis, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

@[simp] theorem V_mul_U_self (i : Fin 3) : (V i : ZornMatrix R) * U i = E22 := by
  fin_cases i <;>
    ext j <;>
      simp [U, V, E22, Vec3.basis, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

@[simp] theorem U_mul_V (i j : Fin 3) :
    (U i : ZornMatrix R) * V j = if i = j then E11 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [U, V, E11, zero, Vec3.basis, mul, Vec3.dot, Vec3.cross,
      Vec3.add, Vec3.sub, Vec3.smul]

@[simp] theorem V_mul_U (i j : Fin 3) :
    (V i : ZornMatrix R) * U j = if i = j then E22 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [U, V, E22, zero, Vec3.basis, mul, Vec3.dot, Vec3.cross,
      Vec3.add, Vec3.sub, Vec3.smul]

@[simp] theorem U_mul_U (i j : Fin 3) :
    (U i : ZornMatrix R) * U j =
      { a := 0
        v := ![0, 0, 0]
        w := Vec3.cross (Vec3.basis i) (Vec3.basis j)
        b := 0 } := by
  apply ZornMatrix.ext
  · simp [U, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
  · funext k
    simp [U, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
  · simp [U, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
  · simp [U, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

@[simp] theorem V_mul_V (i j : Fin 3) :
    (V i : ZornMatrix R) * V j =
      { a := 0
        v := Vec3.smul (-1) (Vec3.cross (Vec3.basis i) (Vec3.basis j))
        w := ![0, 0, 0]
        b := 0 } := by
  apply ZornMatrix.ext
  · simp [V, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
  · simp [V, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
  · funext k
    simp [V, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
  · simp [V, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

theorem U_anticommute (i j : Fin 3) :
    (U i : ZornMatrix R) * U j + U j * U i = 0 := by
  rw [U_mul_U, U_mul_U]
  apply ZornMatrix.ext
  · simp [ZornMatrix.add, zero]
  · funext k
    fin_cases k <;> simp [ZornMatrix.add, zero, Vec3.add]
  · funext k
    have h := congrFun
      (Vec3.cross_add_swap (Vec3.basis (R := R) i)
        (Vec3.basis (R := R) j)) k
    simpa [ZornMatrix.add, zero, Vec3.add] using h
  · simp [ZornMatrix.add, zero]

theorem V_anticommute (i j : Fin 3) :
    (V i : ZornMatrix R) * V j + V j * V i = 0 := by
  rw [V_mul_V, V_mul_V]
  apply ZornMatrix.ext
  · simp [ZornMatrix.add, zero]
  · funext k
    have h := congrFun
      (congrArg (Vec3.smul (-1 : R))
        (Vec3.cross_add_swap (Vec3.basis (R := R) i)
          (Vec3.basis (R := R) j))) k
    simpa [ZornMatrix.add, zero, Vec3.add, Vec3.smul, add_comm] using h
  · funext k
    fin_cases k <;> simp [ZornMatrix.add, zero, Vec3.add]
  · simp [ZornMatrix.add, zero]

theorem U_V_anticommutator (i j : Fin 3) :
    (U i : ZornMatrix R) * V j + V j * U i =
      if i = j then I else 0 := by
  rw [U_mul_V, V_mul_U]
  by_cases h : i = j
  · subst j
    simp [I, E11, E22, ZornMatrix.add, Vec3.add]
  · have h' : ¬j = i := by
      intro hji
      exact h hji.symm
    simp [h, h', zero, ZornMatrix.add, Vec3.add]

theorem U_one_mul_U_zero :
    (U 1 : ZornMatrix R) * U 0 = -(V 2) := by
  ext j
  · simp [U, V, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]
  · fin_cases j <;>
      simp [U, V, mul, Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add,
        Vec3.sub, Vec3.smul]
  · fin_cases j <;>
      simp [U, V, mul, Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add,
        Vec3.sub, Vec3.smul]
  · simp [U, V, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]

@[simp] theorem U_two_mul_U_one :
    (U 2 : ZornMatrix R) * U 1 = -(V 0) := by
  ext j
  · simp [U, V, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]
  · fin_cases j <;>
      simp [U, V, mul, Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add,
        Vec3.sub, Vec3.smul]
  · fin_cases j <;>
      simp [U, V, mul, Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add,
        Vec3.sub, Vec3.smul]
  · simp [U, V, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]

@[simp] theorem U_zero_mul_U_two :
    (U 0 : ZornMatrix R) * U 2 = -(V 1) := by
  ext j
  · simp [U, V, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]
  · fin_cases j <;>
      simp [U, V, mul, Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add,
        Vec3.sub, Vec3.smul]
  · fin_cases j <;>
      simp [U, V, mul, Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add,
        Vec3.sub, Vec3.smul]
  · simp [U, V, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]

@[simp] theorem V_zero_mul_V_one :
    (V 0 : ZornMatrix R) * V 1 = -(U 2) := by
  ext j
  · simp [U, V, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]
  · fin_cases j <;>
      simp [U, V, mul, Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add,
        Vec3.sub, Vec3.smul]
  · fin_cases j <;>
      simp [U, V, mul, Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add,
        Vec3.sub, Vec3.smul]
  · simp [U, V, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]

@[simp] theorem V_one_mul_V_two :
    (V 1 : ZornMatrix R) * V 2 = -(U 0) := by
  ext j
  · simp [U, V, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]
  · fin_cases j <;>
      simp [U, V, mul, Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add,
        Vec3.sub, Vec3.smul]
  · fin_cases j <;>
      simp [U, V, mul, Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add,
        Vec3.sub, Vec3.smul]
  · simp [U, V, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]

@[simp] theorem V_two_mul_V_zero :
    (V 2 : ZornMatrix R) * V 0 = -(U 1) := by
  ext j
  · simp [U, V, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]
  · fin_cases j <;>
      simp [U, V, mul, Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add,
        Vec3.sub, Vec3.smul]
  · fin_cases j <;>
      simp [U, V, mul, Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add,
        Vec3.sub, Vec3.smul]
  · simp [U, V, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]

@[simp] theorem V_one_mul_V_zero :
    (V 1 : ZornMatrix R) * V 0 = U 2 := by
  ext j
  · simp [U, V, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]
  · fin_cases j <;>
      simp [U, V, mul, Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add,
        Vec3.sub, Vec3.smul]
  · fin_cases j <;>
      simp [U, V, mul, Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add,
        Vec3.sub, Vec3.smul]
  · simp [U, V, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]

@[simp] theorem V_two_mul_V_one :
    (V 2 : ZornMatrix R) * V 1 = U 0 := by
  ext j
  · simp [U, V, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]
  · fin_cases j <;>
      simp [U, V, mul, Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add,
        Vec3.sub, Vec3.smul]
  · fin_cases j <;>
      simp [U, V, mul, Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add,
        Vec3.sub, Vec3.smul]
  · simp [U, V, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]

@[simp] theorem V_zero_mul_V_two :
    (V 0 : ZornMatrix R) * V 2 = U 1 := by
  ext j
  · simp [U, V, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]
  · fin_cases j <;>
      simp [U, V, mul, Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add,
        Vec3.sub, Vec3.smul]
  · fin_cases j <;>
      simp [U, V, mul, Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add,
        Vec3.sub, Vec3.smul]
  · simp [U, V, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]

@[simp] theorem U_zero_mul_U_one : (U 0 : ZornMatrix R) * U 1 = V 2 := by
  ext j
  · simp [U, V, Vec3.basis, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
  · fin_cases j <;>
      simp [U, V, Vec3.basis, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
  · fin_cases j <;>
      simp [U, V, Vec3.basis, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
  · simp [U, V, Vec3.basis, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

@[simp] theorem U_one_mul_U_two : (U 1 : ZornMatrix R) * U 2 = V 0 := by
  ext j
  · simp [U, V, Vec3.basis, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
  · fin_cases j <;>
      simp [U, V, Vec3.basis, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
  · fin_cases j <;>
      simp [U, V, Vec3.basis, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
  · simp [U, V, Vec3.basis, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

@[simp] theorem U_two_mul_U_zero : (U 2 : ZornMatrix R) * U 0 = V 1 := by
  ext j
  · simp [U, V, Vec3.basis, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
  · fin_cases j <;>
      simp [U, V, Vec3.basis, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
  · fin_cases j <;>
      simp [U, V, Vec3.basis, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
  · simp [U, V, Vec3.basis, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

/-- A concrete associator property: the Zorn product is not associative. --/
theorem nonassociative_property [Nontrivial R] :
    ((U 0 : ZornMatrix R) * U 1) * U 2 ≠ U 0 * (U 1 * U 2) := by
  intro h
  have hleft : ((U 0 : ZornMatrix R) * U 1) * U 2 = E22 := by
    rw [U_zero_mul_U_one, V_mul_U_self]
  have hright : (U 0 : ZornMatrix R) * (U 1 * U 2) = E11 := by
    rw [U_one_mul_U_two, U_mul_V_self]
  have hdiag : (E22 : ZornMatrix R) = E11 := by
    exact hleft.symm.trans (h.trans hright)
  have ha := congrArg ZornMatrix.a hdiag
  simp [E11, E22] at ha

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
  change add (sub (mul X X) (smul (zornTrace X) X))
      (smul (zornNorm X) (I : ZornMatrix R)) = zero
  ext j
  · simp [mul, sub, add, smul, zornTrace, zornNorm, I, zero,
      Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
    ring_nf
  · fin_cases j <;>
      simp [mul, sub, add, smul, zornTrace, zornNorm, I, zero,
        Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul] <;>
      ring_nf
  · fin_cases j <;>
      simp [mul, sub, add, smul, zornTrace, zornNorm, I, zero,
        Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul] <;>
      ring_nf
  · simp [mul, sub, add, smul, zornTrace, zornNorm, I, zero,
      Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
    ring_nf

/--
The reduced determinant of the scalar pencil `I - tX` is the quadratic
trace-norm polynomial `1 - t Tr(X) + t² N(X)`.
-/
theorem zornNorm_I_sub_smul (t : R) (X : ZornMatrix R) :
    zornNorm ((I : ZornMatrix R) - t • X) =
      1 - t * zornTrace X + t ^ 2 * zornNorm X := by
  change zornNorm (sub (I : ZornMatrix R) (smul t X)) =
    1 - t * zornTrace X + t ^ 2 * zornNorm X
  simp [sub, smul, zornTrace, zornNorm, I, Vec3.dot, Vec3.sub, Vec3.smul]
  ring_nf

/-- AI Studio alias: Cayley-Hamilton for Zorn matrices. --/
theorem cayley_hamilton (X : ZornMatrix R) :
    X * X - (zornTrace X) • X + (zornNorm X) • (I : ZornMatrix R) = 0 :=
  zorn_characteristic_equation X

/-- AI Studio alias: the Fredholm-style quadratic determinant expansion. --/
theorem fredholm_expansion (t : R) (X : ZornMatrix R) :
    zornNorm ((I : ZornMatrix R) - t • X) =
      1 - t * zornTrace X + t ^ 2 * zornNorm X :=
  zornNorm_I_sub_smul t X

end ZornMatrix
end InfoGeometry.Algebra
