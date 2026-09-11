import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Algebra.SplitAlgebraHierarchyBridge

/-- **Definition**: Split-Complex Numbers over a Commutative Ring R.
    z = x + j y where j^2 = 1. -/
@[ext]
structure SplitComplex (R : Type*) [CommRing R] where
  re : R
  j_im : R

namespace SplitComplex

variable {R : Type*} [CommRing R]

def add (z1 z2 : SplitComplex R) : SplitComplex R :=
  ⟨z1.re + z2.re, z1.j_im + z2.j_im⟩

def mul (z1 z2 : SplitComplex R) : SplitComplex R :=
  ⟨z1.re * z2.re + z1.j_im * z2.j_im, z1.re * z2.j_im + z1.j_im * z2.re⟩

def conj (z : SplitComplex R) : SplitComplex R :=
  ⟨z.re, -z.j_im⟩

def normSq (z : SplitComplex R) : R :=
  z.re * z.re - z.j_im * z.j_im

/-- Positive and Negative Idempotent Basis Elements e+ and e-.
    e+ = 1/2 (1 + j), e- = 1/2 (1 - j). -/
def ePlus [Invertible (2 : R)] : SplitComplex R :=
  ⟨⅟(2 : R), ⅟(2 : R)⟩

def eMinus [Invertible (2 : R)] : SplitComplex R :=
  ⟨⅟(2 : R), -⅟(2 : R)⟩

/-- **Theorem**: Idempotent Completeness e+ + e- = 1. -/
theorem e_plus_add_e_minus [Invertible (2 : R)] :
    add (ePlus (R := R)) (eMinus (R := R)) = ⟨1, 0⟩ := by
  dsimp [add, ePlus, eMinus]
  ext
  · calc ⅟(2 : R) + ⅟(2 : R)
      _ = (2 : R) * ⅟(2 : R) := by ring
      _ = 1 := mul_invOf_self (2 : R)
  · ring

/-- **Theorem**: Idempotent Orthogonality e+ * e- = 0. -/
theorem e_plus_mul_e_minus [Invertible (2 : R)] :
    mul (ePlus (R := R)) (eMinus (R := R)) = ⟨0, 0⟩ := by
  dsimp [mul, ePlus, eMinus]
  ext <;> ring

/-- **Theorem**: Hyperbolic Norm Multiplicativity N(z1 z2) = N(z1) N(z2). -/
theorem normSq_mul (z1 z2 : SplitComplex R) :
    normSq (mul z1 z2) = normSq z1 * normSq z2 := by
  dsimp [normSq, mul]
  ring

end SplitComplex

/-- **Definition**: Split-Quaternion Algebra over R.
    q = w + x i + y j + z k where i^2 = -1, j^2 = +1, k^2 = +1. -/
@[ext]
structure SplitQuaternion (R : Type*) [CommRing R] where
  w : R
  x : R
  y : R
  z : R

namespace SplitQuaternion

variable {R : Type*} [CommRing R]

def mul (q1 q2 : SplitQuaternion R) : SplitQuaternion R := ⟨
  q1.w * q2.w - q1.x * q2.x + q1.y * q2.y + q1.z * q2.z,
  q1.w * q2.x + q1.x * q2.w - q1.y * q2.z + q1.z * q2.y,
  q1.w * q2.y + q1.y * q2.w - q1.x * q2.z + q1.z * q2.x,
  q1.w * q2.z + q1.z * q2.w + q1.x * q2.y - q1.y * q2.x
⟩

def normSq (q : SplitQuaternion R) : R :=
  q.w * q.w + q.x * q.x - q.y * q.y - q.z * q.z

/-- **Theorem**: Split-Quaternion Norm Multiplicativity N(q1 q2) = N(q1) N(q2). -/
theorem normSq_mul (q1 q2 : SplitQuaternion R) :
    normSq (mul q1 q2) = normSq q1 * normSq q2 := by
  dsimp [normSq, mul]
  ring

end SplitQuaternion

/-- **Theorem**: Master Split-Algebra Hierarchy Synthesis.
    Unifies:
    1. Split-complex idempotent basis e+ + e- = 1 and orthogonality e+ e- = 0.
    2. Split-complex hyperbolic norm multiplicativity N(z1 z2) = N(z1) N(z2).
    3. Split-quaternion norm multiplicativity N(q1 q2) = N(q1) N(q2) over signature (2,2). -/
theorem master_split_algebra_hierarchy_synthesis
    {R : Type*} [CommRing R] [Invertible (2 : R)]
    (z1 z2 : SplitComplex R) (q1 q2 : SplitQuaternion R) :
    (SplitComplex.add (SplitComplex.ePlus (R := R)) (SplitComplex.eMinus (R := R)) = ⟨1, 0⟩) ∧
    (SplitComplex.mul (SplitComplex.ePlus (R := R)) (SplitComplex.eMinus (R := R)) = ⟨0, 0⟩) ∧
    (SplitComplex.normSq (SplitComplex.mul z1 z2) = SplitComplex.normSq z1 * SplitComplex.normSq z2) ∧
    (SplitQuaternion.normSq (SplitQuaternion.mul q1 q2) = SplitQuaternion.normSq q1 * SplitQuaternion.normSq q2) := ⟨
  SplitComplex.e_plus_add_e_minus,
  SplitComplex.e_plus_mul_e_minus,
  SplitComplex.normSq_mul z1 z2,
  SplitQuaternion.normSq_mul q1 q2
⟩

end InfoGeometry.Algebra.SplitAlgebraHierarchyBridge
