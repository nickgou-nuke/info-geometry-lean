import InfoGeometry.Twistor.PenroseIncidence
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases

/-!
# Two-twistor reconstruction of a spacetime node

Two Penrose twistors `Z₁ = (ω₁,π₁)` and `Z₂ = (ω₂,π₂)` determine a unique
complex spacetime matrix whenever the two lower spinors are linearly
independent.  In matrix form the two incidence equations are

`Ω = i X Π`,

where `Π` and `Ω` have the two spinors as columns.  If `det Π ≠ 0`, then

`X = -i Ω Π⁻¹`.

This file proves existence and uniqueness using mathlib's nonsingular matrix
inverse.  It is a finite incidence theorem.  It does not yet construct a
curved connection, geodesic triangulation, or holonomy.
-/

noncomputable section

namespace InfoGeometry.Twistor.TwoTwistorSpacetimeNode

open InfoGeometry.Twistor.PenroseIncidence
open Matrix

abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Matrix whose columns are the two lower Penrose spinors `π₁,π₂`. -/
def twistorSpinorMatrixPi (Z₁ Z₂ : Twistor4) : Mat2C :=
  !![Z₁.2 0, Z₂.2 0;
     Z₁.2 1, Z₂.2 1]

/-- Matrix whose columns are the two upper Penrose spinors `ω₁,ω₂`. -/
def twistorSpinorMatrixOmega (Z₁ Z₂ : Twistor4) : Mat2C :=
  !![Z₁.1 0, Z₂.1 0;
     Z₁.1 1, Z₂.1 1]

/-- Independence of the two rays means that their lower spinors form an
invertible `2 × 2` matrix. -/
def AreIndependentRays (Z₁ Z₂ : Twistor4) : Prop :=
  Matrix.det (twistorSpinorMatrixPi Z₁ Z₂) ≠ 0

/-- The reconstructed complex spacetime node `X = -i Ω Π⁻¹`. -/
def reconstructedSpacetimeNode
    (Z₁ Z₂ : Twistor4) (_h : AreIndependentRays Z₁ Z₂) : ComplexSpacetime :=
  (-Complex.I) •
    (twistorSpinorMatrixOmega Z₁ Z₂ *
      (twistorSpinorMatrixPi Z₁ Z₂)⁻¹)

/-- Multiplying the reconstructed node by the spinor-column matrix gives
`-i Ω`. -/
theorem reconstructedNode_mul_pi
    (Z₁ Z₂ : Twistor4) (h : AreIndependentRays Z₁ Z₂) :
    reconstructedSpacetimeNode Z₁ Z₂ h * twistorSpinorMatrixPi Z₁ Z₂ =
      (-Complex.I) • twistorSpinorMatrixOmega Z₁ Z₂ := by
  let Π := twistorSpinorMatrixPi Z₁ Z₂
  let Ω := twistorSpinorMatrixOmega Z₁ Z₂
  have hunit : IsUnit Π.det := isUnit_iff_ne_zero.mpr h
  change ((-Complex.I) • (Ω * Π⁻¹)) * Π = (-Complex.I) • Ω
  rw [Matrix.smul_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul Π hunit,
    Matrix.mul_one]

/-- Matrix form of the two simultaneous incidence equations:
`i X Π = Ω`. -/
theorem reconstructedNode_incidence_matrix
    (Z₁ Z₂ : Twistor4) (h : AreIndependentRays Z₁ Z₂) :
    Complex.I •
        (reconstructedSpacetimeNode Z₁ Z₂ h * twistorSpinorMatrixPi Z₁ Z₂) =
      twistorSpinorMatrixOmega Z₁ Z₂ := by
  rw [reconstructedNode_mul_pi Z₁ Z₂ h]
  simp [smul_smul, Complex.I_mul_I]

/-- The reconstructed node is incident with the first twistor. -/
theorem reconstructedNode_incident_first
    (Z₁ Z₂ : Twistor4) (h : AreIndependentRays Z₁ Z₂) :
    incidenceLinearMap (reconstructedSpacetimeNode Z₁ Z₂ h) Z₁.2 = Z₁ := by
  apply Prod.ext
  · funext a
    have hm := congrFun (congrFun
      (reconstructedNode_incidence_matrix Z₁ Z₂ h) a) 0
    simpa [twistorSpinorMatrixPi, twistorSpinorMatrixOmega,
      incidenceLinearMap, omegaLinearMap, Matrix.mul_apply,
      Fin.sum_univ_two] using hm
  · rfl

/-- The reconstructed node is incident with the second twistor. -/
theorem reconstructedNode_incident_second
    (Z₁ Z₂ : Twistor4) (h : AreIndependentRays Z₁ Z₂) :
    incidenceLinearMap (reconstructedSpacetimeNode Z₁ Z₂ h) Z₂.2 = Z₂ := by
  apply Prod.ext
  · funext a
    have hm := congrFun (congrFun
      (reconstructedNode_incidence_matrix Z₁ Z₂ h) a) 1
    simpa [twistorSpinorMatrixPi, twistorSpinorMatrixOmega,
      incidenceLinearMap, omegaLinearMap, Matrix.mul_apply,
      Fin.sum_univ_two] using hm
  · rfl

/-- Existence: two independent lower spinors determine a spacetime matrix
incident with both twistors. -/
theorem reconstructedNode_satisfies_incidence
    (Z₁ Z₂ : Twistor4) (h : AreIndependentRays Z₁ Z₂) :
    incidenceLinearMap (reconstructedSpacetimeNode Z₁ Z₂ h) Z₁.2 = Z₁ ∧
      incidenceLinearMap (reconstructedSpacetimeNode Z₁ Z₂ h) Z₂.2 = Z₂ :=
  ⟨reconstructedNode_incident_first Z₁ Z₂ h,
    reconstructedNode_incident_second Z₁ Z₂ h⟩

/-- Two native incidence equations imply the corresponding matrix equation
`i X Π = Ω`. -/
theorem incidence_pair_implies_matrix_equation
    (Z₁ Z₂ : Twistor4) (X : ComplexSpacetime)
    (h₁ : incidenceLinearMap X Z₁.2 = Z₁)
    (h₂ : incidenceLinearMap X Z₂.2 = Z₂) :
    Complex.I • (X * twistorSpinorMatrixPi Z₁ Z₂) =
      twistorSpinorMatrixOmega Z₁ Z₂ := by
  ext a j
  fin_cases j
  · have hfst := congrArg Prod.fst h₁
    have ha := congrFun hfst a
    simpa [twistorSpinorMatrixPi, twistorSpinorMatrixOmega,
      incidenceLinearMap, omegaLinearMap, Matrix.mul_apply,
      Fin.sum_univ_two] using ha
  · have hfst := congrArg Prod.fst h₂
    have ha := congrFun hfst a
    simpa [twistorSpinorMatrixPi, twistorSpinorMatrixOmega,
      incidenceLinearMap, omegaLinearMap, Matrix.mul_apply,
      Fin.sum_univ_two] using ha

/-- Uniqueness: if two complex spacetime matrices are incident with both
independent twistors, the matrices coincide. -/
theorem spacetimeNode_unique
    (Z₁ Z₂ : Twistor4) (h : AreIndependentRays Z₁ Z₂)
    (X₁ X₂ : ComplexSpacetime)
    (hX₁₁ : incidenceLinearMap X₁ Z₁.2 = Z₁)
    (hX₁₂ : incidenceLinearMap X₁ Z₂.2 = Z₂)
    (hX₂₁ : incidenceLinearMap X₂ Z₁.2 = Z₁)
    (hX₂₂ : incidenceLinearMap X₂ Z₂.2 = Z₂) :
    X₁ = X₂ := by
  let Π := twistorSpinorMatrixPi Z₁ Z₂
  have hunit : IsUnit Π.det := isUnit_iff_ne_zero.mpr h
  have hmat₁ := incidence_pair_implies_matrix_equation Z₁ Z₂ X₁ hX₁₁ hX₁₂
  have hmat₂ := incidence_pair_implies_matrix_equation Z₁ Z₂ X₂ hX₂₁ hX₂₂
  have hi : (Complex.I : ℂ) ≠ 0 := by norm_num
  have hscaled : Complex.I • (X₁ * Π) = Complex.I • (X₂ * Π) :=
    hmat₁.trans hmat₂.symm
  have hprod : X₁ * Π = X₂ * Π := by
    ext i j
    have hij := congrFun (congrFun hscaled i) j
    change Complex.I * (X₁ * Π) i j = Complex.I * (X₂ * Π) i j at hij
    exact mul_left_cancel₀ hi hij
  have hright := congrArg (fun A : Mat2C => A * Π⁻¹) hprod
  simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv Π hunit] using hright

/-- The reconstructed node is the unique simultaneous incidence solution. -/
theorem reconstructedSpacetimeNode_eq_of_incident
    (Z₁ Z₂ : Twistor4) (h : AreIndependentRays Z₁ Z₂)
    (X : ComplexSpacetime)
    (hX₁ : incidenceLinearMap X Z₁.2 = Z₁)
    (hX₂ : incidenceLinearMap X Z₂.2 = Z₂) :
    X = reconstructedSpacetimeNode Z₁ Z₂ h := by
  apply spacetimeNode_unique Z₁ Z₂ h X (reconstructedSpacetimeNode Z₁ Z₂ h)
  · exact hX₁
  · exact hX₂
  · exact reconstructedNode_incident_first Z₁ Z₂ h
  · exact reconstructedNode_incident_second Z₁ Z₂ h

end InfoGeometry.Twistor.TwoTwistorSpacetimeNode
