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

abbrev Zorn := Q × Vec3 × Vec3 × Q

namespace Zorn

def a (X : Zorn) : Q := X.1
def u (X : Zorn) : Vec3 := X.2.1
def v (X : Zorn) : Vec3 := X.2.2.1
def b (X : Zorn) : Q := X.2.2.2

end Zorn

def zmul (X Y : Zorn) : Zorn :=
  (X.a * Y.a + dot X.u Y.v,
    vsub (vadd (smul X.a Y.u) (smul Y.b X.u)) (cross X.v Y.v),
    vadd (vadd (smul Y.a X.v) (smul X.b Y.v)) (cross X.u Y.u),
    dot X.v Y.u + X.b * Y.b)

def zconj (X : Zorn) : Zorn := (X.b, vneg X.u, vneg X.v, X.a)

def znorm (X : Zorn) : Q := X.a * X.b - dot X.u X.v

def zassoc (X Y Z : Zorn) : Zorn :=
  let lhs := zmul (zmul X Y) Z
  let rhs := zmul X (zmul Y Z)
  (lhs.a - rhs.a, vsub lhs.u rhs.u, vsub lhs.v rhs.v, lhs.b - rhs.b)

def oneZ : Zorn := (1, zvec, zvec, 1)
def zeroDivisor : Zorn := (1, e1, e1, 1)
def U1 : Zorn := (0, e1, zvec, 0)
def U2 : Zorn := (0, e2, zvec, 0)
def L1 : Zorn := (0, zvec, e1, 0)
def associatorValue : Zorn := zassoc U1 L1 U2

theorem zorn_zero_divisor_norm : znorm zeroDivisor = 0 := by
  norm_num [Zorn.a, Zorn.u, Zorn.v, Zorn.b, zeroDivisor, znorm, dot, e1]

theorem zorn_one_norm : znorm oneZ = 1 := by
  norm_num [Zorn.a, Zorn.u, Zorn.v, Zorn.b, oneZ, znorm, dot, zvec]

theorem zorn_conjugate_zero_divisor_norm :
    znorm (zconj zeroDivisor) = znorm zeroDivisor := by
  norm_num [Zorn.a, Zorn.u, Zorn.v, Zorn.b, zconj, zeroDivisor, znorm, dot, e1, vneg]

theorem zorn_associator_value_nonzero :
    associatorValue.u = e2 ∧
      associatorValue ≠ (0, zvec, zvec, 0) := by
  constructor
  · norm_num [Zorn.a, Zorn.u, Zorn.v, Zorn.b, associatorValue, zassoc, zmul, vsub, vadd, vneg, smul, dot, cross,
      U1, U2, L1, e1, e2, zvec]
  · intro h
    have hu := congrArg Zorn.u h
    norm_num [Zorn.a, Zorn.u, Zorn.v, Zorn.b, associatorValue, zassoc, zmul, vsub, vadd, vneg, smul, dot, cross,
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
