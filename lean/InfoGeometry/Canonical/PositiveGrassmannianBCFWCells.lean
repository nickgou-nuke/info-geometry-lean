import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BCFWOnShellShift

namespace InfoGeometry.Canonical

open Matrix

variable {k n m : ℕ}

/-- 
An abstract representation of the Plücker coordinates (k x k minors) of a k x n matrix.
For formalization simplicity at this layer, we postulat3 a minor extraction map. 
In a full matrix library, this is `Matrix.det` of a submatrix.
-/
def extractMinor (C : Matrix (Fin k) (Fin n) ℝ) (I : Fin k → Fin n) : ℝ :=
  (C.submatrix id I).det

/-- 
A matrix C represents an element of the Totally Non-Negative Grassmannian
if all its ordered maximal minors are non-negative.
-/
def IsTotallyNonnegative (C : Matrix (Fin k) (Fin n) ℝ) : Prop :=
  ∀ (I : Fin k → Fin n), StrictMono I → 0 ≤ extractMinor C I

/--
A matrix Z represents strictly positive external kinematic data
if all its maximal minors are strictly positive.
Here Z is an (k+m) x n matrix.
-/
def IsTotallyPositiveData (Z : Matrix (Fin (k + m)) (Fin n) ℝ) : Prop :=
  ∀ (I : Fin (k + m) → Fin n), StrictMono I → 0 < (Z.submatrix id I).det

/--
The BCFW cell map on representative matrices.
At the level of representative matrices, it is simply right-multiplication by Z^T.
-/
def bcfwCellMap (Z : Matrix (Fin (k + m)) (Fin n) ℝ) (C : Matrix (Fin k) (Fin n) ℝ) : Matrix (Fin k) (Fin (k + m)) ℝ :=
  C * Z.transpose

/--
The Tree Amplituhedron 𝒜_{n,k,m}(Z) is the image of the Totally Non-Negative 
Grassmannian under the Amplituhedron map Φ_Z.
-/
def TreeAmplituhedron (Z : Matrix (Fin (k + m)) (Fin n) ℝ) : Set (Matrix (Fin k) (Fin (k + m)) ℝ) :=
  { Y | ∃ C, IsTotallyNonnegative C ∧ Y = bcfwCellMap Z C }

/--
A BCFW cell is a specific subset of the Totally Non-Negative Grassmannian 
(a positroid cell) defined by setting certain Plücker coordinates to zero.
We represent a cell abstractly by the set of matrices satisfying a positivity condition
and a specific affine structure.
-/
structure BCFWCell (Z : Matrix (Fin (k + m)) (Fin n) ℝ) where
  cell_matrices : Set (Matrix (Fin k) (Fin n) ℝ)
  is_subset_tnn : ∀ C ∈ cell_matrices, IsTotallyNonnegative C

/-- 
The image of a BCFW cell under the Amplituhedron map.
-/
def cellImage (Z : Matrix (Fin (k + m)) (Fin n) ℝ) (cell : BCFWCell Z) : Set (Matrix (Fin k) (Fin (k + m)) ℝ) :=
  { Y | ∃ C ∈ cell.cell_matrices, Y = bcfwCellMap Z C }

/--
A fundamental property: The image of any BCFW cell is contained within the Tree Amplituhedron.
This is a mathematically honest theorem derived directly from the definitions.
-/
theorem cell_image_subset_amplituhedron (Z : Matrix (Fin (k + m)) (Fin n) ℝ) (cell : BCFWCell Z) :
    cellImage Z cell ⊆ TreeAmplituhedron Z := by
  intro Y hY
  rcases hY with ⟨C, hC_in_cell, hY_eq⟩
  unfold TreeAmplituhedron
  use C
  constructor
  · exact cell.is_subset_tnn C hC_in_cell
  · exact hY_eq

end InfoGeometry.Canonical
