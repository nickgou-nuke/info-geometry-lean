import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# InfoGeometry.Canonical.BiQuaternionKahlerFinite

Finite algebraic owner for the biquaternion/Kähler language used in the
manuscript notes.

This file does not construct a smooth hyperkähler manifold, a Lagrangian field
theory, a Hamiltonian flow on an infinite-dimensional phase space, a partition
function, or Noether currents.  It closes the finite `R^4` algebraic core:
three quaternionic complex structures, their symplectic readout, a Poisson-style
skew bracket, an identity Fisher/Hessian metric, and a small finite Casimir
matrix identity.

#### BUCKET 1: CLOSED FINITE THEOREMS
`I`, `J`, and `K` square to `-1`, satisfy `IJ = K` and `JI = -K`; the
`I`-Kähler form `ω_I(x,y) = <Ix,y>` is skew; the induced finite bracket is
skew; the identity Fisher metric is symmetric and nonnegative; a toy two-matrix
Casimir readout vanishes.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
Smooth manifolds, Kähler potentials as differentiable functions, Hamiltonian
vector fields, Legendre transforms, canonical ensembles, Fisher-Rao geometry
from an analytic Massieu potential, Hodge integration, Killing/Noether
conservation laws, and physical field equations.
-/

namespace InfoGeometry.Canonical.BiQuaternionKahlerFinite

open Matrix

abbrev R4 : Type :=
  Fin 4 → ℝ

abbrev Mat4 : Type :=
  Matrix (Fin 4) (Fin 4) ℝ

/-- Euclidean finite dot product on `R^4`. -/
def dot4 (x y : R4) : ℝ :=
  ∑ i, x i * y i

/-- First quaternionic complex structure on `R^4`. -/
def I4c : Mat4 :=
  !![(0 : ℝ), -1, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, -1;
     0, 0, 1, 0]

/-- Second quaternionic complex structure on `R^4`. -/
def J4c : Mat4 :=
  !![(0 : ℝ), 0, -1, 0;
     0, 0, 0, 1;
     1, 0, 0, 0;
     0, -1, 0, 0]

/-- Third quaternionic complex structure on `R^4`. -/
def K4c : Mat4 :=
  !![(0 : ℝ), 0, 0, -1;
     0, 0, -1, 0;
     0, 1, 0, 0;
     1, 0, 0, 0]

theorem I4c_sq : I4c * I4c = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [I4c, Matrix.mul_apply, Fin.sum_univ_four]

theorem J4c_sq : J4c * J4c = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J4c, Matrix.mul_apply, Fin.sum_univ_four]

theorem K4c_sq : K4c * K4c = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [K4c, Matrix.mul_apply, Fin.sum_univ_four]

theorem I4c_mul_J4c : I4c * J4c = K4c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [I4c, J4c, K4c, Matrix.mul_apply, Fin.sum_univ_four]

theorem J4c_mul_I4c : J4c * I4c = -K4c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [I4c, J4c, K4c, Matrix.mul_apply, Fin.sum_univ_four]

/-- Finite Kähler-form readout from the first complex structure. -/
def symplecticI (x y : R4) : ℝ :=
  dot4 (I4c.mulVec x) y

theorem symplecticI_skew (x y : R4) :
    symplecticI x y = -symplecticI y x := by
  dsimp [symplecticI, dot4]
  simp [I4c, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- A finite Poisson-style bracket on coordinate gradients. -/
def finitePoissonBracket (dF dG : R4) : ℝ :=
  symplecticI dF dG

theorem finitePoissonBracket_skew (dF dG : R4) :
    finitePoissonBracket dF dG = -finitePoissonBracket dG dF :=
  symplecticI_skew dF dG

/-- Identity Fisher/Hessian metric for the free quadratic finite model. -/
def fisherMetric (_q : R4) : Mat4 :=
  1

theorem fisherMetric_symmetric (q : R4) :
    (fisherMetric q)ᵀ = fisherMetric q := by
  simp [fisherMetric]

theorem fisherMetric_quadratic_nonneg (q v : R4) :
    0 ≤ dot4 v ((fisherMetric q).mulVec v) := by
  dsimp [fisherMetric, dot4]
  simp [Matrix.one_mulVec, Fin.sum_univ_succ]
  nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]

abbrev Mat2 : Type :=
  Matrix (Fin 2) (Fin 2) ℝ

/-- Real `σ_x` generator. -/
def sigmaX : Mat2 :=
  !![(0 : ℝ), 1; 1, 0]

/-- Real symplectic generator `J`, a real shadow of `-i σ_y`. -/
def sigmaYReal : Mat2 :=
  !![(0 : ℝ), -1; 1, 0]

/-- A finite quadratic Casimir readout for the pair `(sigmaX, sigmaYReal)`. -/
def toyCasimir2 (A B : Mat2) : Mat2 :=
  A * A + B * B

theorem toyCasimir2_sigmaX_sigmaYReal :
    toyCasimir2 sigmaX sigmaYReal = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toyCasimir2, sigmaX, sigmaYReal]

end InfoGeometry.Canonical.BiQuaternionKahlerFinite
