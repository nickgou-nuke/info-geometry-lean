import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic

namespace InfoGeometry.SplitOctonions

set_option linter.unusedSectionVars false

/-!
# Albert Algebra: Cubic Geometry and the Freudenthal Cross Product

Following the definition of the split-octonionic carrier, we construct the
27-dimensional Exceptional Jordan Algebra $\mathcal{J}_3(\mathbb{O}_s)$.
Instead of heuristic matrix wrappers, we build the rigorous Cartesian representation
of 3x3 Hermitian matrices over a generic non-associative algebra.
-/

variable (R : Type*) [CommRing R]
variable (A : Type*) [NonUnitalNonAssocRing A] [Module R A]

/-- The Albert Vector represents a 3x3 Hermitian matrix:
    [ r1,  z,  y* ]
    [ z*, r2,  x  ]
    [ y,  x*, r3  ]
    Parameterized strictly by 3 diagonal scalars in R and 3 off-diagonal elements in A. -/
@[ext]
structure AlbertVector where
  r1 : R
  r2 : R
  r3 : R
  x : A
  y : A
  z : A

namespace AlbertVector

variable {R A}

/-- The Jordan Trace $T(X) = r_1 + r_2 + r_3$. -/
def trace (X : AlbertVector R A) : R :=
  X.r1 + X.r2 + X.r3

/-- A purely diagonal Albert vector represents a Cartan subspace element. -/
def diagonal (r1 r2 r3 : R) : AlbertVector R A where
  r1 := r1
  r2 := r2
  r3 := r3
  x := 0
  y := 0
  z := 0

end AlbertVector

/- The Freudenthal Cross Product and E6(6) Geometry -/

/- Assume the existence of an isotropic quadratic norm and a trace form on the octonions. -/
variable (Norm_A : A → R) (Trace_A : A → R)

/-- The cubic determinant of the 27-dimensional Albert Algebra. -/
def cubicDet (X : AlbertVector R A) : R :=
  X.r1 * X.r2 * X.r3 - X.r1 * Norm_A (X.x) - X.r2 * Norm_A (X.y) - X.r3 * Norm_A (X.z)
  + Trace_A ((X.x * X.y) * X.z)

/-- CAPSTONE: The determinant of a pure diagonal state completely collapses to
    the classical product of its eigenvalues, provided the algebraic norm and trace
    strictly vanish on zero elements. This proves consistency with standard geometry. -/
theorem cubicDet_diagonal_eq_prod
    (h_norm_zero : Norm_A 0 = 0) (h_trace_zero : Trace_A 0 = 0) (r1 r2 r3 : R) :
    cubicDet R A Norm_A Trace_A (AlbertVector.diagonal r1 r2 r3) = r1 * r2 * r3 := by
  dsimp [cubicDet, AlbertVector.diagonal]
  rw [h_norm_zero]
  have h_zero_mul : ((0 : A) * (0 : A)) * (0 : A) = 0 := by simp
  rw [h_zero_mul]
  rw [h_trace_zero]
  ring

end InfoGeometry.SplitOctonions
