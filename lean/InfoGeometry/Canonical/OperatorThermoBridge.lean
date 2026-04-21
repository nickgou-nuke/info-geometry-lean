import InfoGeometry.Canonical.Operators
import InfoGeometry.Potential.Thermo

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.OperatorThermoBridge

Thin sign-convention bridge between the operatorial Onsager surface and the
scalar Legendre/Massieu thermodynamic layer.

This file does not claim a full identification between operatorial transport
data and a concrete scalar Legendre model. It only records the dictionary used
by the operator lane:

- scalar log-readout is treated as the operatorial Massieu/free-energy readout,
- diagonal Onsager response is treated as the dissipative entropy-production
  scalar,
- canonical scalar thermo signs from `Potential.Thermo` remain the reference
  convention for names like `canonicalEnergy`, `canonicalEntropy`, and
  `canonicalFreeEnergy`.
-/

namespace InfoGeometry.Canonical.OperatorThermoBridge

open InfoGeometry.Canonical.Operators
open InfoGeometry.LogPotential
open InfoGeometry.LogPotential.LegendreModel
open InfoGeometry.Krein

section Bridge

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedSpace ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- Operator-lane Massieu readout, named to match the scalar thermodynamic convention. -/
@[rep_depth transport]
noncomputable def operatorMassieuReadout
    (ω : EndH →L[ℝ] ℝ) (X A : EndH) (t : ℝ) : ℝ :=
  operatorFreeEnergyReadout (E := E) ω X A t

/-- Operator-lane canonical free-energy readout, same scalar as the Massieu readout at this bridge level. -/
@[rep_depth transport]
noncomputable def operatorCanonicalFreeEnergyReadout
    (ω : EndH →L[ℝ] ℝ) (X A : EndH) (t : ℝ) : ℝ :=
  operatorMassieuReadout (E := E) ω X A t

/-- Operator-lane canonical entropy production is the diagonal Onsager scalar. -/
@[rep_depth transport]
noncomputable def operatorCanonicalEntropyProduction
    (P : PotentialDatum (E := E)) (X A : EndH) : ℝ :=
  entropyProduction (E := E) P X A

@[rep_depth transport]
theorem operatorCanonicalFreeEnergyReadout_eq_massieu
    (ω : EndH →L[ℝ] ℝ) (X A : EndH) (t : ℝ) :
    operatorCanonicalFreeEnergyReadout (E := E) ω X A t
      =
    operatorMassieuReadout (E := E) ω X A t := by
  rfl

@[rep_depth transport]
theorem operatorCanonicalEntropyProduction_eq_onsagerDiagonal
    (P : PotentialDatum (E := E)) (X A : EndH) :
    operatorCanonicalEntropyProduction (E := E) P X A
      =
    onsagerCoefficient (E := E) P (thermodynamicForce (E := E) X)
      (thermodynamicForce (E := E) X) A := by
  exact entropyProduction_eq_onsagerDiagonal (E := E) P X A

@[rep_depth transport]
theorem operatorCanonicalEntropyProduction_nonneg_of_probe_hessian_nonneg
    (P : PotentialDatum (E := E))
    (hP : ∀ X A : EndH, 0 ≤ P.probe (operatorFisherDiagonal (E := E) X A))
    (X A : EndH) :
    0 ≤ operatorCanonicalEntropyProduction (E := E) P X A := by
  exact entropyProduction_nonneg_of_probe_hessian_nonneg (E := E) P hP X A

/-- Scalar canonical thermodynamic free energy keeps the Gibbs-sign convention `F = - ε ψ`. -/
@[rep_depth transport]
theorem scalarCanonicalFreeEnergy_sign
    (M : LegendreModel) (ε θ : ℝ) :
    M.canonicalFreeEnergy ε θ = -ε * M.massieu θ := by
  simpa using M.canonicalFreeEnergy_def ε θ

/-- Scalar canonical entropy keeps the Gibbs-sign convention `S = ψ - θη`. -/
@[rep_depth transport]
theorem scalarCanonicalEntropy_sign
    (M : LegendreModel) (θ : ℝ) :
    M.canonicalEntropy θ = M.massieu θ - θ * M.dualCoord θ := by
  simpa using M.canonicalEntropy_def θ

/-- Scalar canonical energy keeps the Gibbs-sign convention `U = -η`. -/
@[rep_depth transport]
theorem scalarCanonicalEnergy_sign
    (M : LegendreModel) (θ : ℝ) :
    M.canonicalEnergy θ = -M.dualCoord θ := by
  simpa using M.canonicalEnergy_def θ

end Bridge

end InfoGeometry.Canonical.OperatorThermoBridge
