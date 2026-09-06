import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

/-!
# The Infinite Sequence of Kinematic Clifford Algebras

By tracing the Wigner-Inönü contraction recursively from Planar Quaternions (SE(2))
to the 2D Cayley-Klein 9-fold geometries, and then to the 3D Cayley-Klein 27-fold
geometries, we arrive at the natural infinite colimit:

The **N-dimensional Kinematic Clifford Algebra** $Cl(\vec{\kappa})$.

For any vector $\vec{\kappa} \in \mathbb{R}^N$ with components $\kappa_i \in \{-1, 0, 1\}$,
the associated Clifford algebra classifies the $3^N$ possible kinematic
geometries of an $N$-dimensional space.

The limit as $N \to \infty$ produces the universal kinematic enveloping algebra,
whose representations encompass all conformal, Euclidean, Galilean, and Minkowski
super-symmetries.
-/

namespace InfoGeometry.Algebra

/-- 
The quadratic form associated with a kinematic signature $\vec{\kappa}$.
For a vector space $V = \mathbb{R}^n$ with basis $e_i$, $Q(e_i) = \kappa_i$.
-/
def kinematicQuadraticForm (n : ℕ) (kappa : Fin n → ℝ) : QuadraticMap ℝ (Fin n → ℝ) ℝ :=
  Matrix.toQuadraticMap' (Matrix.diagonal kappa)

/--
The N-dimensional Kinematic Clifford Algebra.
By varying the signature `kappa`, this algebra spans the entire $3^N$ 
kinematic equivalence class hierarchy.
-/
abbrev KinematicCliffordAlgebra (n : ℕ) (kappa : Fin n → ℝ) :=
  CliffordAlgebra (kinematicQuadraticForm n kappa)

/-- 
The generators of the Kinematic Clifford Algebra.
Each basis vector $e_i$ injects into the Clifford algebra, 
satisfying $(e_i)^2 = \kappa_i$.
-/
def kinematicGenerator (n : ℕ) (kappa : Fin n → ℝ) (i : Fin n) : KinematicCliffordAlgebra n kappa :=
  let basis_vector : Fin n → ℝ := fun j ↦ if i = j then 1 else 0
  CliffordAlgebra.ι (kinematicQuadraticForm n kappa) basis_vector

end InfoGeometry.Algebra
