import Mathlib

namespace SplitOctonionZornKKS

abbrev Q := ℚ
abbrev Vec3 := Q × Q × Q

def vadd (x y : Vec3) : Vec3 :=
  (x.1 + y.1, x.2.1 + y.2.1, x.2.2 + y.2.2)

def vneg (x : Vec3) : Vec3 :=
  (-x.1, -x.2.1, -x.2.2)

def vsub (x y : Vec3) : Vec3 := vadd x (vneg y)

def smul (a : Q) (x : Vec3) : Vec3 :=
  (a * x.1, a * x.2.1, a * x.2.2)

def dot (x y : Vec3) : Q :=
  x.1 * y.1 + x.2.1 * y.2.1 + x.2.2 * y.2.2

def cross (x y : Vec3) : Vec3 :=
  (x.2.1 * y.2.2 - x.2.2 * y.2.1,
   x.2.2 * y.1 - x.1 * y.2.2,
   x.1 * y.2.1 - x.2.1 * y.1)

def e1 : Vec3 := (1, 0, 0)
def e2 : Vec3 := (0, 1, 0)
def zvec : Vec3 := (0, 0, 0)

structure Zorn where
  a : Q
  u : Vec3
  v : Vec3
  b : Q
  deriving DecidableEq, Repr

def zmul (X Y : Zorn) : Zorn where
  a := X.a * Y.a + dot X.u Y.v
  u := vsub (vadd (smul X.a Y.u) (smul Y.b X.u)) (cross X.v Y.v)
  v := vadd (vadd (smul Y.a X.v) (smul X.b Y.v)) (cross X.u Y.u)
  b := dot X.v Y.u + X.b * Y.b

def zconj (X : Zorn) : Zorn where
  a := X.b
  u := vneg X.u
  v := vneg X.v
  b := X.a

def znorm (X : Zorn) : Q := X.a * X.b - dot X.u X.v

def zassoc (X Y Z : Zorn) : Zorn :=
  let lhs := zmul (zmul X Y) Z
  let rhs := zmul X (zmul Y Z)
  { a := lhs.a - rhs.a
    u := vsub lhs.u rhs.u
    v := vsub lhs.v rhs.v
    b := lhs.b - rhs.b }

def oneZ : Zorn := ⟨1, zvec, zvec, 1⟩
def zeroDivisor : Zorn := ⟨1, e1, e1, 1⟩
def U1 : Zorn := ⟨0, e1, zvec, 0⟩
def U2 : Zorn := ⟨0, e2, zvec, 0⟩
def L1 : Zorn := ⟨0, zvec, e1, 0⟩
def associatorValue : Zorn := zassoc U1 L1 U2

theorem zorn_zero_divisor_norm : znorm zeroDivisor = 0 := by
  norm_num [zeroDivisor, znorm, dot, e1]

theorem zorn_one_norm : znorm oneZ = 1 := by
  norm_num [oneZ, znorm, dot, zvec]

theorem zorn_conjugate_zero_divisor_norm :
    znorm (zconj zeroDivisor) = znorm zeroDivisor := by
  norm_num [zconj, zeroDivisor, znorm, dot, e1, vneg]

theorem zorn_associator_value_nonzero :
    associatorValue.u = e2 ∧
      associatorValue ≠ { a := 0, u := zvec, v := zvec, b := 0 } := by
  constructor
  · norm_num [associatorValue, zassoc, zmul, vsub, vadd, vneg, smul, dot, cross,
      U1, U2, L1, e1, e2, zvec]
  · intro h
    have hu := congrArg Zorn.u h
    norm_num [associatorValue, zassoc, zmul, vsub, vadd, vneg, smul, dot, cross,
      U1, U2, L1, e1, e2, zvec] at hu

def mobiusTwist (k : Int) : Int := -k

def kleinRelated (k l : Int) : Prop :=
  k = l ∨ k = mobiusTwist l

def kleinPairInvariant (k : Int) : Int := k + mobiusTwist k

theorem mobius_klein_relations (k : Int) :
    mobiusTwist (mobiusTwist k) = k ∧
      kleinRelated k (mobiusTwist k) ∧ kleinPairInvariant k = 0 := by
  constructor
  · simp [mobiusTwist]
  constructor
  · right
    simp [mobiusTwist]
  · simp [kleinPairInvariant, mobiusTwist]

def tripotentSpectralPolynomial (d : Int) : Int := d * d * d - d

theorem tripotent_spectral_root (d : Int) (hd : d = -1 ∨ d = 0 ∨ d = 1) :
    tripotentSpectralPolynomial d = 0 := by
  rcases hd with rfl | rfl | rfl <;> norm_num [tripotentSpectralPolynomial]

end SplitOctonionZornKKS
