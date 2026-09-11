import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

/-- **Theorem**: Master Exterior Homogeneous Degree & Matrix Homogeneity Synthesis.
    Unifies:
    1. Homogeneous exterior algebra degree predicate IsHomogeneousExteriorDegree k x for x ∈ ⋀^k V.
    2. Matrix entrywise homogeneity predicate MatrixIsHomogeneous k M for M ∈ Matrix_{n×n}(⋀^k V).
    3. Proof closure for 1-form connection matrix entrywise degree (k = 1) and 2-form curvature matrix entrywise degree (k = 2). -/
theorem master_exterior_homogeneous_degree_synthesis
    (A F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hA : MatrixIsHomogeneous 1 A)
    (hF : MatrixIsHomogeneous 2 F)
    (i j : Fin n) :
    (IsHomogeneousExteriorDegree 1 (A i j)) ∧
    (IsHomogeneousExteriorDegree 2 (F i j)) := ⟨
  matrix_one_form_homogeneous A hA i j,
  matrix_two_form_homogeneous F hF i j
⟩

end InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge
