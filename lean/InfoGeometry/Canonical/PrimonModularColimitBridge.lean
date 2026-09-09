import InfoGeometry.Canonical.AlgebraicKMSStateColimit
import InfoGeometry.Canonical.CuntzMatrixTraceModularInvariance

/-!
# Modular readout on the algebraic Primon colimit

This is a small application-facing bridge.  The finite Hamiltonian family and
its density transport are owned by `CuntzMatrixCompatibleStateNet`; the
delta-first modular automorphism and its KMS identity are owned by
`AlgebraicKMSStateColimit`.  This file only instantiates those owners for the
propagated Gibbs family.

No identification is made between an `AlgebraEnd H` generator and the
algebraic colimit carrier: those are different native types in the repository.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.PrimonModularColimitBridge

open InfoGeometry.Canonical.AlgebraicKMSStateColimit
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional
open InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceModularInvariance

abbrev Carrier := AlgebraicKMSStateColimit.Carrier

/-- Finite-stage delta-first modular conjugation. -/
def finiteDeltaImaginaryTimeAlgEquiv (n : ℕ) (δ : (MatrixStage n)ˣ) :
    MatrixStage n ≃ₐ[ℂ] MatrixStage n :=
  MulSemiringAction.toAlgEquiv ℂ (MatrixStage n) (ConjAct.toConjAct δ)

@[simp]
theorem finiteDeltaImaginaryTimeAlgEquiv_apply
    (n : ℕ) (δ : (MatrixStage n)ˣ) (A : MatrixStage n) :
    finiteDeltaImaginaryTimeAlgEquiv n δ A =
      (δ : MatrixStage n) * A * ((δ⁻¹ : (MatrixStage n)ˣ) : MatrixStage n) :=
  rfl

@[simp]
theorem finiteDeltaImaginaryTimeAlgEquiv_inverse
    (n : ℕ) (δ : (MatrixStage n)ˣ) (A : MatrixStage n) :
    finiteDeltaImaginaryTimeAlgEquiv n δ⁻¹
        (finiteDeltaImaginaryTimeAlgEquiv n δ A) = A := by
  rw [finiteDeltaImaginaryTimeAlgEquiv_apply,
    finiteDeltaImaginaryTimeAlgEquiv_apply]
  simp [mul_assoc]

@[simp]
theorem finiteDeltaImaginaryTimeAlgEquiv_mul
    (n : ℕ) (δ₁ δ₂ : (MatrixStage n)ˣ) (A : MatrixStage n) :
    finiteDeltaImaginaryTimeAlgEquiv n (δ₁ * δ₂) A =
      finiteDeltaImaginaryTimeAlgEquiv n δ₁
        (finiteDeltaImaginaryTimeAlgEquiv n δ₂ A) := by
  rw [finiteDeltaImaginaryTimeAlgEquiv_apply,
    finiteDeltaImaginaryTimeAlgEquiv_apply,
    finiteDeltaImaginaryTimeAlgEquiv_apply]
  simp [mul_assoc]

/-- The finite normalized matrix trace is invariant under the modular
    conjugation. -/
theorem matrixTraceState_finiteDelta_invariant
    (n : ℕ) (δ : (MatrixStage n)ˣ) (A : MatrixStage n) :
    matrixTraceState n (finiteDeltaImaginaryTimeAlgEquiv n δ A) =
      matrixTraceState n A := by
  rw [finiteDeltaImaginaryTimeAlgEquiv_apply, matrixTraceState_mul_comm]
  rw [← mul_assoc]
  rw [show ((δ⁻¹ : (MatrixStage n)ˣ) : MatrixStage n) * (δ : MatrixStage n) = 1 by
    exact Units.inv_mul δ]
  simp

/-- The propagated Gibbs density at the colimit, viewed as a unit. -/
def propagatedGibbsColimitUnit
    (H₀ : MatrixStage 0) (h₀ : H₀.IsHermitian) (β : ℝ) : Carrierˣ :=
  densityColimitUnit
    (propagatedGibbsDensity H₀ h₀ β)
    (propagatedGibbsDensity_unit_zero H₀ h₀ β)

@[simp]
theorem propagatedGibbsColimitUnit_coe
    (H₀ : MatrixStage 0) (h₀ : H₀.IsHermitian) (β : ℝ) :
    (propagatedGibbsColimitUnit H₀ h₀ β : Carrier) =
      stageInjection 0 (propagatedGibbsDensity H₀ h₀ β 0) := by
  exact densityColimitUnit_coe
    (propagatedGibbsDensity H₀ h₀ β)
    (propagatedGibbsDensity_unit_zero H₀ h₀ β)

/-- The colimit modular automorphism attached to the propagated density. -/
def propagatedGibbsModularAutomorphism
    (H₀ : MatrixStage 0) (h₀ : H₀.IsHermitian) (β : ℝ) :
    Carrier ≃ₐ[ℂ] Carrier :=
  deltaImaginaryTimeAlgEquiv (propagatedGibbsColimitUnit H₀ h₀ β)

@[simp]
theorem propagatedGibbsModularAutomorphism_apply
    (H₀ : MatrixStage 0) (h₀ : H₀.IsHermitian) (β : ℝ) (x : Carrier) :
    propagatedGibbsModularAutomorphism H₀ h₀ β x =
      (propagatedGibbsColimitUnit H₀ h₀ β : Carrier) * x *
        (((propagatedGibbsColimitUnit H₀ h₀ β)⁻¹ : Carrierˣ) : Carrier) := by
  exact deltaImaginaryTimeAlgEquiv_apply
    (propagatedGibbsColimitUnit H₀ h₀ β) x

@[simp]
theorem deltaImaginaryTimeAlgEquiv_inverse
    (δ : Carrierˣ) (x : Carrier) :
    deltaImaginaryTimeAlgEquiv δ⁻¹
        (deltaImaginaryTimeAlgEquiv δ x) = x := by
  rw [deltaImaginaryTimeAlgEquiv_apply,
    deltaImaginaryTimeAlgEquiv_apply]
  simp [mul_assoc]

@[simp]
theorem deltaImaginaryTimeAlgEquiv_mul
    (δ₁ δ₂ : Carrierˣ) (x : Carrier) :
    deltaImaginaryTimeAlgEquiv (δ₁ * δ₂) x =
      deltaImaginaryTimeAlgEquiv δ₁
        (deltaImaginaryTimeAlgEquiv δ₂ x) := by
  rw [deltaImaginaryTimeAlgEquiv_apply,
    deltaImaginaryTimeAlgEquiv_apply,
    deltaImaginaryTimeAlgEquiv_apply]
  simp [mul_assoc]

/-- The finite conjugation action is transported by the canonical stage
    injection to the corresponding colimit conjugation action. -/
theorem finiteDelta_action_lifts_to_colimit
    (n : ℕ) (δ : (MatrixStage n)ˣ) (A : MatrixStage n) :
    deltaImaginaryTimeAlgEquiv (stageUnitToColimit n δ)
        (stageInjection n A) =
      stageInjection n (finiteDeltaImaginaryTimeAlgEquiv n δ A) := by
  rw [deltaImaginaryTimeAlgEquiv_apply,
    finiteDeltaImaginaryTimeAlgEquiv_apply,
    stageUnitToColimit_coe]
  have hinv :
      (((stageUnitToColimit n δ)⁻¹ : Carrierˣ) : Carrier) =
        stageInjection n ((δ⁻¹ : (MatrixStage n)ˣ) : MatrixStage n) := by
    exact stageUnitToColimit_coe n (δ⁻¹ : (MatrixStage n)ˣ)
  rw [hinv, ← stageInjection_mul, ← stageInjection_mul]

/-- Colimit trace readback of the lifted finite modular action. -/
theorem lifted_finiteDelta_trace_readback
    (n : ℕ) (δ : (MatrixStage n)ˣ) (A : MatrixStage n) :
    traceFunctional
        (deltaImaginaryTimeAlgEquiv (stageUnitToColimit n δ)
          (stageInjection n A)) =
      matrixTraceState n (finiteDeltaImaginaryTimeAlgEquiv n δ A) := by
  rw [finiteDelta_action_lifts_to_colimit, traceFunctional_stage]

/-- The normalized colimit trace is invariant under the delta modular
    automorphism.  The conjugation calculation is supplied by the existing
    `CuntzMatrixTraceModularInvariance` owner. -/
theorem traceFunctional_deltaImaginaryTimeAlgEquiv
    (δ : Carrierˣ) (x : Carrier) :
    traceFunctional (deltaImaginaryTimeAlgEquiv δ x) = traceFunctional x := by
  simpa [deltaImaginaryTimeAlgEquiv_apply, unitConjugation] using
    (traceFunctional_unitConjugation δ x)

theorem propagatedGibbsModularAutomorphism_trace_invariant
    (H₀ : MatrixStage 0) (h₀ : H₀.IsHermitian) (β : ℝ) (x : Carrier) :
    traceFunctional
        (propagatedGibbsModularAutomorphism H₀ h₀ β x) = traceFunctional x := by
  exact traceFunctional_deltaImaginaryTimeAlgEquiv
    (propagatedGibbsColimitUnit H₀ h₀ β) x

/-- Stage readback of the propagated modular KMS functional. -/
theorem propagatedGibbsModularFunctional_stage
    (H₀ : MatrixStage 0) (h₀ : H₀.IsHermitian) (β : ℝ)
    (n : ℕ) (x : MatrixStage n) :
    deltaWeightedFunctional (propagatedGibbsColimitUnit H₀ h₀ β)
        (stageInjection n x) =
      matrixTraceFunctional n
        (x * propagatedGibbsDensity H₀ h₀ β n) := by
  change deltaWeightedFunctional
      (densityColimitUnit
        (propagatedGibbsDensity H₀ h₀ β)
        (propagatedGibbsDensity_unit_zero H₀ h₀ β))
      (stageInjection n x) = _
  rw [← weightedColimitFunctional_eq_deltaWeighted
    (propagatedGibbsDensity H₀ h₀ β)
    (propagatedGibbsDensity_compatible H₀ h₀ β)
    (propagatedGibbsDensity_unit_zero H₀ h₀ β)]
  exact weightedColimitFunctional_stage
    (propagatedGibbsDensity H₀ h₀ β)
    (weightedStageFunctional_compatible_of_density_compatible
      (propagatedGibbsDensity H₀ h₀ β)
      (propagatedGibbsDensity_compatible H₀ h₀ β)) n x

theorem propagatedGibbsModularFunctional_normalized
    (H₀ : MatrixStage 0) (h₀ : H₀.IsHermitian) (β : ℝ) :
    normalizedDeltaWeightedFunctional
        (propagatedGibbsColimitUnit H₀ h₀ β) (1 : Carrier) = 1 := by
  exact normalizedDeltaWeightedFunctional_one
    (propagatedGibbsColimitUnit H₀ h₀ β)
    (propagatedGibbsDensity_colimit_trace_ne_zero H₀ h₀ β)

/-- The propagated Gibbs readout satisfies the algebraic modular KMS identity. -/
theorem propagatedGibbsModularFunctional_kms
    (H₀ : MatrixStage 0) (h₀ : H₀.IsHermitian) (β : ℝ)
    (x y : Carrier) :
    normalizedDeltaWeightedFunctional
        (propagatedGibbsColimitUnit H₀ h₀ β) (x * y) =
      normalizedDeltaWeightedFunctional
        (propagatedGibbsColimitUnit H₀ h₀ β)
          (y * propagatedGibbsModularAutomorphism H₀ h₀ β x) := by
  exact normalizedDeltaWeightedFunctional_kms
    (propagatedGibbsColimitUnit H₀ h₀ β) x y

end InfoGeometry.Canonical.PrimonModularColimitBridge
