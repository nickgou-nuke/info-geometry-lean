import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

/-- The abstract space of canonical differential forms for positive geometries. -/
structure CanonicalFormSpace (Ω : Type*) (Boundary : Type*) where
  wedge : Ω → Ω → Ω
  residue : Ω → Boundary → Ω

/-- A positive geometry A is uniquely associated with its canonical form Ω(A). 
    The boundary of A has components B, which are themselves positive geometries. -/
structure PositiveGeometry (A : Type*) (Ω : Type*) (Boundary : Type*) where
  space : CanonicalFormSpace Ω Boundary
  canonicalForm : A → Ω
  boundaryGeometry : A → Boundary → A
  /-- The fundamental law of positive geometries: Res_B Ω(A) = Ω(B) -/
  residue_canonicalForm_boundary : ∀ (a : A) (B : Boundary), 
    space.residue (canonicalForm a) B = canonicalForm (boundaryGeometry a B)

/-- 
A product boundary B ≃ B_L × B_R induces a factorization of the canonical form:
Ω(B) = Ω(B_L) ∧ Ω(B_R).
We define this structurally for given left and right sub-geometries.
-/
abbrev ProductBoundaryFactorization {A Ω Boundary : Type*}
    (geom : PositiveGeometry A Ω Boundary) (a : A) (B : Boundary) (b_L b_R : A) : Prop :=
  geom.canonicalForm (geom.boundaryGeometry a B) =
    geom.space.wedge (geom.canonicalForm b_L) (geom.canonicalForm b_R)

/-- 
BCFW boundary factorization: If B is a BCFW product boundary of an amplituhedron A, 
then the residue of A at B factorizes into the wedge product of the left and right canonical forms.
-/
theorem bcfwBoundary_factorization {A Ω Boundary : Type*} 
    (geom : PositiveGeometry A Ω Boundary) (a : A) (B : Boundary) (b_L b_R : A) 
    (h_prod : ProductBoundaryFactorization geom a B b_L b_R) :
    geom.space.residue (geom.canonicalForm a) B = geom.space.wedge (geom.canonicalForm b_L) (geom.canonicalForm b_R) := by
  rw [geom.residue_canonicalForm_boundary]
  exact h_prod

open scoped BigOperators

/-- 
The BCFW Recursion from Residue Sum.
If the canonical form of the tree Amplituhedron is fully determined by its residues 
on the BCFW shift poles (boundaries), then Ω(A) is the sum of these residues.
Using the product boundary factorization, this yields the BCFW recursion relation 
entirely within the language of Positive Geometries.
-/
theorem bcfw_recursion_from_residue_sum {A Ω Boundary : Type*} [AddCommMonoid Ω]
    (geom : PositiveGeometry A Ω Boundary) (a : A) (bcfw_boundaries : Finset Boundary) 
    (left right : Boundary → A)
    (h_product : ∀ B ∈ bcfw_boundaries, ProductBoundaryFactorization geom a B (left B) (right B))
    (h_cauchy : geom.canonicalForm a = ∑ B ∈ bcfw_boundaries, geom.space.residue (geom.canonicalForm a) B) :
    geom.canonicalForm a = ∑ B ∈ bcfw_boundaries, geom.space.wedge (geom.canonicalForm (left B)) (geom.canonicalForm (right B)) := by
  rw [h_cauchy]
  apply Finset.sum_congr rfl
  intro B hB
  have h_fact := h_product B hB
  rw [geom.residue_canonicalForm_boundary]
  exact h_fact

end InfoGeometry.Canonical
