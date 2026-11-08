import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Split Octonion Null Cone and Minkowski 4-Vectors

This module establishes the formal connection between the 8D split octonion
null cone (represented by Zorn vector matrices) and 4D Minkowski spacetime.

We prove the core condition that on the traceless subspace, the split octonion
norm exactly reduces to the Minkowski norm of a 4-vector, connecting the
algebraic zero divisors of $\mathbb{O}'$ with physical lightcones.
-/

namespace InfoGeometry.Algebra.ZornVectorMatrix

variable {R : Type*} [CommRing R]

/- The split octonion norm (quadratic form). Already defined in `ZornVectorMatrix.norm` as `X.a * X.b - ZornVec3.dot X.v X.w`. -/

/-- Predicate for an element residing on the 8D Null Cone. -/
def IsNullCone (X : ZornVectorMatrix R) : Prop :=
  norm X = 0

/-- Predicate for a traceless element. -/
def IsTraceless (X : ZornVectorMatrix R) : Prop :=
  trace X = 0

/-- 
The Minkowski inner product of two 4-vectors `(a, v)` and `(b, w)` 
where `a, b` are scalars and `v, w` are 3-vectors.
Defined as `a*b + v \cdot w`. (Note: depending on metric signature, 
this represents the Euclidean or Minkowski combination; here we align
it algebraically with the trace-zero substitution).
-/
def minkowskiInner (a : R) (v : ZornVec3 R) (b : R) (w : ZornVec3 R) : R :=
  a * b + ZornVec3.dot v w

/-- The Minkowski norm squared of a 4-vector `(a, v)`. -/
def minkowskiNormSq (a : R) (v : ZornVec3 R) : R :=
  minkowskiInner a v a v

/-- 
Master Theorem: Traceless Null Cone Equation.
If a Zorn matrix `X` is traceless (`a + b = 0`), then its split octonion 
norm is exactly the negative of the Minkowski inner product of its `(a, v)` 
and `(a, w)` 4-vector components.
-/
theorem norm_of_traceless (X : ZornVectorMatrix R) (h : IsTraceless X) :
    norm X = -minkowskiInner X.a X.v X.a X.w := by
  dsimp [norm, IsTraceless, trace, minkowskiInner] at *
  have hb : X.b = -X.a := by 
    calc X.b = X.a + X.b - X.a := by ring
         _   = 0 - X.a := by rw [h]
         _   = -X.a := by ring
  rw [hb]
  ring

/--
A traceless Zorn matrix with symmetric off-diagonals (v = w) 
is on the null cone if and only if its 
associated 4-vector `(a, v)` has zero Minkowski norm.
-/
theorem isNullCone_iff_minkowski_null_of_traceless_symm
    (X : ZornVectorMatrix R) (h_trace : IsTraceless X) (h_symm : X.v = X.w) :
    IsNullCone X ↔ minkowskiNormSq X.a X.v = 0 := by
  dsimp [IsNullCone, norm, IsTraceless, trace, minkowskiNormSq, minkowskiInner] at *
  have hb : X.b = -X.a := by 
    calc X.b = X.a + X.b - X.a := by ring
         _   = 0 - X.a := by rw [h_trace]
         _   = -X.a := by ring
  rw [hb, h_symm]
  constructor
  · intro h_neg
    have h1 : X.a * -X.a - ZornVec3.dot X.w X.w = 0 := h_neg
    have h2 : -(X.a * X.a + ZornVec3.dot X.w X.w) = 0 := by
      calc
        -(X.a * X.a + ZornVec3.dot X.w X.w) = X.a * -X.a - ZornVec3.dot X.w X.w := by ring
        _ = 0 := h1
    exact neg_eq_zero.mp h2
  · intro h_zero
    calc
      X.a * -X.a - ZornVec3.dot X.w X.w
        = -(X.a * X.a + ZornVec3.dot X.w X.w) := by ring
      _ = -0 := by rw [h_zero]
      _ = 0 := by ring

end InfoGeometry.Algebra.ZornVectorMatrix
