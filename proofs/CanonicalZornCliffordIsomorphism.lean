import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import proofs.CanonicalZornCliffordRepresentation

/-!
# First finite-dimensional certificates for the Zorn Clifford isomorphism

This module proves the two prerequisites that do not depend on a classification
of complex Clifford algebras:

* the quadratic form underlying the canonical Zorn gamma action is
  nondegenerate, in the precise `SeparatingLeft` sense;
* the endomorphism algebra of the sixteen-dimensional Zorn Dirac carrier has
  complex dimension `256`.

No injectivity or algebra-isomorphism claim is made here.  Those require a
separate constructive spanning/linear-independence argument for Clifford
monomials (or an independently formalized simplicity theorem).
-/

noncomputable section

namespace CanonicalZornCliffordIsomorphism

open CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation

/-! ## Nondegeneracy of the coordinate quadratic form -/

/-- The associated bilinear form of the eight-coordinate Zorn determinant is
left-separating.  Each coordinate is detected by its hyperbolically paired
coordinate vector. -/
theorem coordinateQuadratic_separatingLeft :
    (QuadraticMap.associated (R := ℂ) coordinateQuadratic).SeparatingLeft := by
  intro x hx
  funext i
  fin_cases i
  · have h := hx (Pi.single 7 1)
    simp [QuadraticMap.associated_apply, coordinateQuadratic,
      coordinateQuadraticFun] at h
    have hx0 : x 0 = 0 := by linear_combination h
    simpa using hx0
  · have h := hx (Pi.single 4 1)
    simp [QuadraticMap.associated_apply, coordinateQuadratic,
      coordinateQuadraticFun] at h
    have hx1 : x 1 = 0 := by linear_combination -h
    simpa using hx1
  · have h := hx (Pi.single 5 1)
    simp [QuadraticMap.associated_apply, coordinateQuadratic,
      coordinateQuadraticFun] at h
    have hx2 : x 2 = 0 := by linear_combination -h
    simpa using hx2
  · have h := hx (Pi.single 6 1)
    simp [QuadraticMap.associated_apply, coordinateQuadratic,
      coordinateQuadraticFun] at h
    have hx3 : x 3 = 0 := by linear_combination -h
    simpa using hx3
  · have h := hx (Pi.single 1 1)
    simp [QuadraticMap.associated_apply, coordinateQuadratic,
      coordinateQuadraticFun] at h
    have hx4 : x 4 = 0 := by linear_combination -h
    simpa using hx4
  · have h := hx (Pi.single 2 1)
    simp [QuadraticMap.associated_apply, coordinateQuadratic,
      coordinateQuadraticFun] at h
    have hx5 : x 5 = 0 := by linear_combination -h
    simpa using hx5
  · have h := hx (Pi.single 3 1)
    simp [QuadraticMap.associated_apply, coordinateQuadratic,
      coordinateQuadraticFun] at h
    have hx6 : x 6 = 0 := by linear_combination -h
    simpa using hx6
  · have h := hx (Pi.single 0 1)
    simp [QuadraticMap.associated_apply, coordinateQuadratic,
      coordinateQuadraticFun] at h
    have hx7 : x 7 = 0 := by linear_combination h
    simpa using hx7

/-- Nondegeneracy transported from coordinates to the strictly typed vector
copy of the canonical Zorn carrier. -/
theorem vectorQuadratic_separatingLeft :
    (QuadraticMap.associated (R := ℂ) vectorQuadratic).SeparatingLeft := by
  intro V hV
  let e := copyLinearEquivCoordinates TrialitySector.vector
  apply e.injective
  rw [e.map_zero]
  apply coordinateQuadratic_separatingLeft (e V)
  intro y
  have h := hV (e.symm y)
  simpa [vectorQuadratic, e] using h

/-! ## Dimension of the target endomorphism algebra -/

/-- The endomorphism algebra of the sixteen-dimensional Zorn Dirac carrier
has complex dimension `16 * 16 = 256`. -/
theorem diracEnd_finrank :
    Module.finrank ℂ (Module.End ℂ DiracSpinor16) = 256 := by
  rw [Module.finrank_linearMap, diracSpinor_finrank]

end CanonicalZornCliffordIsomorphism

end noncomputable section
