import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BCFWOnShellShift

namespace InfoGeometry.Canonical

open Matrix

variable {k n m : ℕ}

/-- 
The determinant of the `k × k` submatrix selected by `I`. When `I` is
strictly monotone, this is the corresponding ordered maximal minor (Plücker
coordinate) of `C`.
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
The image of the totally nonnegative representative matrices under the
linear map `C ↦ C * Zᵀ`. This definition is available for arbitrary `Z`;
it does not require `IsTotallyPositiveData Z`, so it does not by itself
establish the usual positive-kinematics amplituhedron hypotheses.
-/
def TreeAmplituhedron (Z : Matrix (Fin (k + m)) (Fin n) ℝ) : Set (Matrix (Fin k) (Fin (k + m)) ℝ) :=
  { Y | ∃ C, IsTotallyNonnegative C ∧ Y = bcfwCellMap Z C }

/-- Image of a set of representative matrices under the map `C ↦ C * Zᵀ`. -/
def cellImage (Z : Matrix (Fin (k + m)) (Fin n) ℝ)
    (cell : Set (Matrix (Fin k) (Fin n) ℝ)) :
    Set (Matrix (Fin k) (Fin (k + m)) ℝ) :=
  {Y | ∃ C ∈ cell, Y = bcfwCellMap Z C}

/-- The image of a set contained in the TNN matrices lies in the image of all
TNN matrices under the same linear map. -/
theorem cell_image_subset_amplituhedron
    (Z : Matrix (Fin (k + m)) (Fin n) ℝ)
    (cell : Set (Matrix (Fin k) (Fin n) ℝ))
    (hcell : ∀ C ∈ cell, IsTotallyNonnegative C) :
    cellImage Z cell ⊆ TreeAmplituhedron Z := by
  intro Y hY
  rcases hY with ⟨C, hC_in_cell, hY_eq⟩
  unfold TreeAmplituhedron
  use C
  constructor
  · exact hcell C hC_in_cell
  · exact hY_eq

end InfoGeometry.Canonical
