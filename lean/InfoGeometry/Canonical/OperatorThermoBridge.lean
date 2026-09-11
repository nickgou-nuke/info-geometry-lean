import InfoGeometry.Canonical.Operators
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Potential.Thermo

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.OperatorThermoBridge

Thin sign-convention bridge between the operatorial Onsager surface and the
scalar Legendre/Massieu thermodynamic layer.

This file is translator-only. It does not upgrade the scalar layer to owner
status: the noncommutative primitive remains the operatorial second-variation /
probe-read lane, while the canonical free-energy and entropy-production names
here are exported scalar shadows.
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

@[rep_depth transport]
noncomputable def operatorMassieuReadout
    (ω : EndH →L[ℝ] ℝ) (X A : EndH) (t : ℝ) : ℝ :=
  operatorFreeEnergyReadout (E := E) ω X A t

@[rep_depth transport]
noncomputable def operatorCanonicalFreeEnergyReadout
    (ω : EndH →L[ℝ] ℝ) (X A : EndH) (t : ℝ) : ℝ :=
  operatorMassieuReadout (E := E) ω X A t

@[rep_depth transport]
noncomputable def operatorCanonicalEntropyProduction
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E)) (X A : EndH) : ℝ :=
  entropyProduction P X A

@[rep_depth transport]
theorem operatorCanonicalFreeEnergyReadout_eq_massieu
    (ω : EndH →L[ℝ] ℝ) (X A : EndH) (t : ℝ) :
    operatorCanonicalFreeEnergyReadout (E := E) ω X A t =
    operatorMassieuReadout (E := E) ω X A t := by
  rfl

@[rep_depth transport]
theorem operatorCanonicalEntropyProduction_eq_probe_hessian
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E)) (X A : EndH) :
    operatorCanonicalEntropyProduction (E := E) P X A =
    P.probe (operatorFisherDiagonal (E := E) X A) := by
  exact entropyProduction_eq_probe_hessian P X A

@[rep_depth transport]
theorem operatorCanonicalEntropyProduction_nonneg_of_probe_hessian_nonneg
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E))
    (hP : ∀ X A : EndH, 0 ≤ P.probe (operatorFisherDiagonal (E := E) X A))
    (X A : EndH) :
    0 ≤ operatorCanonicalEntropyProduction (E := E) P X A := by
  exact entropyProduction_nonneg_of_probe_hessian_nonneg P hP X A

@[rep_depth transport]
theorem scalarCanonicalFreeEnergy_sign
    (M : LegendreModel) (ε θ : ℝ) :
    M.canonicalFreeEnergy ε θ = -ε * M.massieu θ := by
  simp

@[rep_depth transport]
theorem scalarCanonicalEntropy_sign
    (M : LegendreModel) (θ : ℝ) :
    M.canonicalEntropy θ = M.massieu θ - θ * M.dualCoord θ := by
  simp

@[rep_depth transport]
theorem scalarCanonicalEnergy_sign
    (M : LegendreModel) (θ : ℝ) :
    M.canonicalEnergy θ = -M.dualCoord θ := by
  simp

end Bridge

end InfoGeometry.Canonical.OperatorThermoBridge
