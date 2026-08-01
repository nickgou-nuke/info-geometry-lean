import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge

open ExteriorAlgebra

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}

/-- **Definition**: Homogeneous Exterior Algebra Degree Predicate IsHomogeneousExteriorDegree k x for x ∈ ⋀^k V. -/
def IsHomogeneousExteriorDegree (k : ℕ) (x : ExteriorAlgebra R V) : Prop :=
  x ∈ (Submodule.span R (Set.range (fun (v : Fin k → V) => List.prod (List.ofFn (fun i => ι R (v i))))))

/-- **Definition**: Entrywise Matrix Homogeneity MatrixIsHomogeneous k M for M ∈ Matrix_{n×n}(⋀^k V). -/
def MatrixIsHomogeneous (k : ℕ) (M : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)) : Prop :=
  ∀ i j, IsHomogeneousExteriorDegree k (M i j)

/-- **Theorem**: Homogeneous 1-Form Matrix Entrywise Degree. -/
theorem matrix_one_form_homogeneous (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hA : MatrixIsHomogeneous 1 A) (i j : Fin n) :
    IsHomogeneousExteriorDegree 1 (A i j) :=
  hA i j

/-- **Theorem**: Homogeneous 2-Form Matrix Entrywise Degree. -/
theorem matrix_two_form_homogeneous (F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hF : MatrixIsHomogeneous 2 F) (i j : Fin n) :
    IsHomogeneousExteriorDegree 2 (F i j) :=
  hF i j

end InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge
