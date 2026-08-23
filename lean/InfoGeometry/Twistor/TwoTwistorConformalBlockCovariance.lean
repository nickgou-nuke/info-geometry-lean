import InfoGeometry.Twistor.TwoTwistorSpacetimeNode
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases

/-!
# Block-fractional covariance of the two-twistor spacetime node

For the repository incidence convention

`ω = i X π`,

a block linear transformation of twistor coordinates

`ω' = A ω + B π`,
`π' = C ω + D π`

induces the fractional transformation

`X' = (A X - i B) (i C X + D)⁻¹`

whenever the denominator is nonsingular.

This owner proves that covariance directly from the native Penrose incidence
map and the uniqueness theorem in `TwoTwistorSpacetimeNode`.

The block datum below is deliberately not called an `SU(2,2)` element: no
pseudo-unitary group law or preservation theorem is assumed here.  A future
`SU(2,2)` owner may specialize this theorem after constructing the genuine
subgroup and proving its block action.
-/

noncomputable section

namespace InfoGeometry.Twistor.TwoTwistorConformalBlockCovariance

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.TwoTwistorSpacetimeNode
open Matrix

/-- Four `2 × 2` blocks acting linearly on `Twistor4 = Spinor2 × Spinor2`. -/
structure ConformalBlock where
  A : Mat2C
  B : Mat2C
  C : Mat2C
  D : Mat2C

/-- Linear block action on a Penrose twistor. -/
def transformTwistor (G : ConformalBlock) (Z : Twistor4) : Twistor4 :=
  (G.A.mulVec Z.1 + G.B.mulVec Z.2,
    G.C.mulVec Z.1 + G.D.mulVec Z.2)

/-- Denominator matrix `i C X + D` in the fractional spacetime action. -/
def denominator (G : ConformalBlock) (X : ComplexSpacetime) : Mat2C :=
  Complex.I • (G.C * X) + G.D

/-- Numerator matrix `A X - i B` in the fractional spacetime action. -/
def numerator (G : ConformalBlock) (X : ComplexSpacetime) : Mat2C :=
  G.A * X - Complex.I • G.B

/-- Fractional block action induced by the incidence convention `ω = i X π`. -/
def fractionalSpacetimeTransform
    (G : ConformalBlock) (X : ComplexSpacetime)
    (_h : Matrix.det (denominator G X) ≠ 0) : ComplexSpacetime :=
  numerator G X * (denominator G X)⁻¹

/-- The native incidence upper spinor is exactly `i • (X *ᵥ π)`. -/
theorem omegaLinearMap_eq_I_smul_mulVec
    (X : ComplexSpacetime) (π : Spinor2) :
    omegaLinearMap X π = Complex.I • X.mulVec π := by
  funext a
  simp [omegaLinearMap, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Under incidence, the transformed lower spinor is `(i C X + D) π`. -/
theorem transformTwistor_snd_of_incident
    (G : ConformalBlock) (X : ComplexSpacetime) (Z : Twistor4)
    (hZ : incidenceLinearMap X Z.2 = Z) :
    (transformTwistor G Z).2 = (denominator G X).mulVec Z.2 := by
  have hfst : omegaLinearMap X Z.2 = Z.1 := congrArg Prod.fst hZ
  rw [← hfst, omegaLinearMap_eq_I_smul_mulVec]
  simp [transformTwistor, denominator, Matrix.add_mulVec,
    Matrix.smul_mulVec, Matrix.mulVec_mulVec, smul_add]

/-- Under incidence, the transformed upper spinor is
`i • ((A X - i B) *ᵥ π)`. -/
theorem transformTwistor_fst_of_incident
    (G : ConformalBlock) (X : ComplexSpacetime) (Z : Twistor4)
    (hZ : incidenceLinearMap X Z.2 = Z) :
    (transformTwistor G Z).1 =
      Complex.I • (numerator G X).mulVec Z.2 := by
  have hfst : omegaLinearMap X Z.2 = Z.1 := congrArg Prod.fst hZ
  rw [← hfst, omegaLinearMap_eq_I_smul_mulVec]
  ext a
  simp [transformTwistor, numerator, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]
  ring

/-- The fractional transform cancels its denominator on the right. -/
theorem fractionalSpacetimeTransform_mul_denominator
    (G : ConformalBlock) (X : ComplexSpacetime)
    (h : Matrix.det (denominator G X) ≠ 0) :
    fractionalSpacetimeTransform G X h * denominator G X = numerator G X := by
  have hunit : IsUnit (Matrix.det (denominator G X)) :=
    isUnit_iff_ne_zero.mpr h
  simp [fractionalSpacetimeTransform, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul (denominator G X) hunit]

/-- Incidence is covariant under the block action and the induced fractional
spacetime transformation. -/
theorem transformTwistor_incident_fractional
    (G : ConformalBlock) (X : ComplexSpacetime) (Z : Twistor4)
    (hZ : incidenceLinearMap X Z.2 = Z)
    (hden : Matrix.det (denominator G X) ≠ 0) :
    incidenceLinearMap (fractionalSpacetimeTransform G X hden)
        (transformTwistor G Z).2 = transformTwistor G Z := by
  apply Prod.ext
  · rw [transformTwistor_snd_of_incident G X Z hZ]
    rw [omegaLinearMap_eq_I_smul_mulVec]
    rw [← Matrix.mulVec_mulVec]
    rw [fractionalSpacetimeTransform_mul_denominator G X hden]
    exact (transformTwistor_fst_of_incident G X Z hZ).symm
  · rfl

/-- Main covariance theorem: the node reconstructed from the transformed
independent twistor pair is the fractional transform of the original node. -/
theorem reconstructedSpacetimeNode_block_covariant
    (G : ConformalBlock) (Z₁ Z₂ : Twistor4)
    (h : AreIndependentRays Z₁ Z₂)
    (h' : AreIndependentRays (transformTwistor G Z₁) (transformTwistor G Z₂))
    (hden : Matrix.det
      (denominator G (reconstructedSpacetimeNode Z₁ Z₂ h)) ≠ 0) :
    reconstructedSpacetimeNode (transformTwistor G Z₁) (transformTwistor G Z₂) h' =
      fractionalSpacetimeTransform G (reconstructedSpacetimeNode Z₁ Z₂ h) hden := by
  let X := reconstructedSpacetimeNode Z₁ Z₂ h
  let X' := fractionalSpacetimeTransform G X hden
  have hinc₁ : incidenceLinearMap X Z₁.2 = Z₁ :=
    reconstructedNode_incident_first Z₁ Z₂ h
  have hinc₂ : incidenceLinearMap X Z₂.2 = Z₂ :=
    reconstructedNode_incident_second Z₁ Z₂ h
  have htrans₁ :
      incidenceLinearMap X' (transformTwistor G Z₁).2 = transformTwistor G Z₁ := by
    exact transformTwistor_incident_fractional G X Z₁ hinc₁ hden
  have htrans₂ :
      incidenceLinearMap X' (transformTwistor G Z₂).2 = transformTwistor G Z₂ := by
    exact transformTwistor_incident_fractional G X Z₂ hinc₂ hden
  have huniq := reconstructedSpacetimeNode_eq_of_incident
    (transformTwistor G Z₁) (transformTwistor G Z₂) h' X' htrans₁ htrans₂
  exact huniq.symm

end InfoGeometry.Twistor.TwoTwistorConformalBlockCovariance
