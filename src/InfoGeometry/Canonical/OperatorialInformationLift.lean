import InfoGeometry.Canonical.JaynesRNModularBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.InformationPartitionCore
import InfoGeometry.Canonical.KreinDiracWeightFunctionalLift

/-!
# Operatorial Information Lift

Thin canonical layer making explicit the analytic syntax shared by the scalar
RN/modular lane and the transported Dirac/thermal operator lane.

This file does not claim a global functor theorem. It only packages the owner
facts already proved in the repo:

- scalar modular potential is the scalar coefficient of the modular Hamiltonian,
- scalar exponential recovery is the scalar coefficient of the modular operator,
- normalized log-partition calculus applies to the modular Hamiltonian,
- the same normalized log-partition syntax applies to transported Dirac and
  transported thermal generators on the doubled Dirac--Clifford--Krein carrier.
-/

namespace InfoGeometry.Canonical.OperatorialInformationLift

open InfoGeometry.Canonical.YangMillsContinuum
open InfoGeometry.Canonical.InformationCalculus.ModularRadonNikodymData
open InfoGeometry.Canonical.RelativePotentialScalarBridge
open InfoGeometry.Canonical.KreinDiracPolarizationBridge
open InfoGeometry.Canonical.KreinDiracWeightFunctionalLift
open InfoGeometry.Canonical.SpectralInference
open InfoGeometry.Canonical.SplitCliffordThermalBridge
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Quantum.RealMajorana
open InfoGeometry.Krein

section Modular

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable local instance : NormedRing (EndH E) := inferInstance
noncomputable local instance : NormedAlgebra ℝ (EndH E) := inferInstance
noncomputable local instance : NormedSpace ℝ (EndH E) := inferInstance
local instance : IsTopologicalRing (EndH E) := inferInstance
local instance : CompleteSpace (EndH E) := inferInstance

/-- The modular Hamiltonian is the scalar modular potential lifted to `Id`. -/
theorem modularHamiltonian_eq_scalarModularPotential_smul_id
    (M : ModularRadonNikodymData E) :
    M.modularHamiltonian =
      scalarModularPotential M.rnDerivative M.rnDerivative_pos • idEndH E := by
  rw [InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.modularHamiltonian_eq_neg_log_rn
    (M := M)]
  simp [InfoGeometry.Canonical.RelativePotentialScalarBridge.scalarModularPotential_eq_neg_log]

/-- The modular operator is the exponential recovery of the scalar modular potential. -/
theorem modularOperator_eq_exp_neg_scalarModularPotential_smul_id
    (M : ModularRadonNikodymData E) :
    M.modularOperator =
      Real.exp (-(scalarModularPotential M.rnDerivative M.rnDerivative_pos)) • idEndH E := by
  rw [InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.modularOperator_eq_rn
    (M := M)]
  rw [InfoGeometry.Canonical.RelativePotentialScalarBridge.scalarModularPotential_eq_neg_log
    (r := M.rnDerivative) (hr := M.rnDerivative_pos)]
  simp [Real.exp_log M.rnDerivative_pos]

/-- Normalized log-partition lift for the modular Hamiltonian. -/
theorem normalized_logOperatorialInformationLift_modularHamiltonian
    (ω : EndH E →L[ℝ] ℝ)
    (hω1 : ω (1 : EndH E) = 1)
    (M : ModularRadonNikodymData E) :
    HasDerivAt
      (fun τ : ℝ => logInformationPartitionFunction ω M.modularHamiltonian τ)
      (ω (scalarModularPotential M.rnDerivative M.rnDerivative_pos • idEndH E)) 0 := by
  have hmod := modularHamiltonian_eq_scalarModularPotential_smul_id (M := M)
  simpa [hmod] using
    hasDerivAt_logInformationPartitionFunction_zero_modularHamiltonian_of_normalized
      (ω := ω) (M := M) hω1

/--
Canonical scalar-to-operator information lift on the RN/modular lane.
This records the scalar coefficient identities together with the normalized
log-partition derivative on the operator side.
-/
theorem operatorialInformationLift_of_normalized
    (ω : EndH E →L[ℝ] ℝ)
    (hω1 : ω (1 : EndH E) = 1)
    (M : ModularRadonNikodymData E) :
    InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.TypeIIIModularInterface M ∧
    M.modularHamiltonian =
      scalarModularPotential M.rnDerivative M.rnDerivative_pos • idEndH E ∧
    M.modularOperator =
      Real.exp (-(scalarModularPotential M.rnDerivative M.rnDerivative_pos)) • idEndH E ∧
    HasDerivAt
      (fun τ : ℝ => logInformationPartitionFunction ω M.modularHamiltonian τ)
      (ω (scalarModularPotential M.rnDerivative M.rnDerivative_pos • idEndH E)) 0 := by
  refine ⟨?_,
    modularHamiltonian_eq_scalarModularPotential_smul_id (M := M),
    modularOperator_eq_exp_neg_scalarModularPotential_smul_id (M := M),
    normalized_logOperatorialInformationLift_modularHamiltonian
      (ω := ω) (hω1 := hω1) (M := M)⟩
  exact InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.typeIIIModularInterface
    (E := E) (M := M)

end Modular

section Doubled

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {M : RealMajoranaDatum (S := DoubledSpace E)}

local notation "H₂" => DoubledSpace E
local notation "EndHD" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndHD := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndHD := inferInstance
noncomputable local instance : NormedSpace ℝ EndHD := inferInstance
local instance : IsTopologicalRing EndHD := inferInstance
local instance : CompleteSpace EndHD := inferInstance

/-- Transported Weyl weight data for the Dirac lift. -/
noncomputable def transportedDiracOperatorialWeightData_of_strictSymmetry
    (IST : InfoSpectralTriple H₂)
    {X Y : PolarizedMajorana (S := H₂) M} (h : X ⟶ Y) :
    (M.weylPlus ≃ₗ[ℝ] (h.toBogoliubovTransform).transportWeylPlus) ×
    (M.weylMinus ≃ₗ[ℝ] (h.toBogoliubovTransform).transportWeylMinus) := by
  let _ := IST
  exact transportWeylWeightEquivs_of_strictSymmetry (M := M) h

/-- Normalized log-partition lift for the transported Dirac generator. -/
theorem normalized_logTransportedDiracOperatorialInformationLift_of_strictSymmetry
    (ω : EndHD →L[ℝ] ℝ)
    (hω1 : ω (1 : EndHD) = 1)
    (IST : InfoSpectralTriple H₂)
    {X Y : PolarizedMajorana (S := H₂) M} (h : X ⟶ Y) :
    HasDerivAt
      (fun τ : ℝ =>
        logInformationPartitionFunction ω
          (transportDirac IST h.toBogoliubovTransform) τ)
      (ω (transportDirac IST h.toBogoliubovTransform)) 0 :=
  normalized_logKreinDiracWeightLift_of_strictSymmetry
    (ω := ω) (hω1 := hω1) (IST := IST) h

/-- Combined operatorial information lift for the transported Dirac generator. -/
theorem transportedDiracOperatorialInformationLift_of_strictSymmetry
    (ω : EndHD →L[ℝ] ℝ)
    (hω1 : ω (1 : EndHD) = 1)
    (IST : InfoSpectralTriple H₂)
    {X Y : PolarizedMajorana (S := H₂) M} (h : X ⟶ Y) :
    Nonempty
      ((M.weylPlus ≃ₗ[ℝ] (h.toBogoliubovTransform).transportWeylPlus) ×
        (M.weylMinus ≃ₗ[ℝ] (h.toBogoliubovTransform).transportWeylMinus)) ∧
    HasDerivAt
      (fun τ : ℝ =>
        logInformationPartitionFunction ω
          (transportDirac IST h.toBogoliubovTransform) τ)
      (ω (transportDirac IST h.toBogoliubovTransform)) 0 := by
  refine ⟨?_, normalized_logTransportedDiracOperatorialInformationLift_of_strictSymmetry
    (ω := ω) (hω1 := hω1) (IST := IST) h⟩
  exact ⟨transportWeylWeightEquivs_of_strictSymmetry (M := M) h⟩

/-- Transported Weyl weight data for the thermal lift. -/
noncomputable def transportedThermalOperatorialWeightData_of_strictSymmetry
    (B : HyperbolicMixingParams)
    (μ : ℝ)
    (IST : InfoSpectralTriple H₂)
    {X Y : PolarizedMajorana (S := H₂) M} (h : X ⟶ Y) :
    (M.weylPlus ≃ₗ[ℝ] (h.toBogoliubovTransform).transportWeylPlus) ×
    (M.weylMinus ≃ₗ[ℝ] (h.toBogoliubovTransform).transportWeylMinus) := by
  let _ := B
  let _ := μ
  let _ := IST
  exact transportWeylWeightEquivs_of_strictSymmetry (M := M) h

/-- Normalized log-partition lift for the transported thermal generator. -/
theorem normalized_logTransportedThermalOperatorialInformationLift_of_strictSymmetry
    (ω : EndHD →L[ℝ] ℝ)
    (hω1 : ω (1 : EndHD) = 1)
    (B : HyperbolicMixingParams)
    (μ : ℝ)
    (IST : InfoSpectralTriple H₂)
    {X Y : PolarizedMajorana (S := H₂) M} (h : X ⟶ Y) :
    HasDerivAt
      (fun τ : ℝ =>
        logInformationPartitionFunction ω
          (transportedThermalGenerator (E := E) B IST h.toBogoliubovTransform μ) τ)
      (ω (transportedThermalGenerator (E := E) B IST h.toBogoliubovTransform μ)) 0 :=
  normalized_logSplitCliffordThermalWeightLift_of_strictSymmetry
    (ω := ω) (hω1 := hω1) (B := B) (μ := μ) (IST := IST) h

/-- Combined operatorial information lift for the transported thermal generator. -/
theorem transportedThermalOperatorialInformationLift_of_strictSymmetry
    (ω : EndHD →L[ℝ] ℝ)
    (hω1 : ω (1 : EndHD) = 1)
    (B : HyperbolicMixingParams)
    (μ : ℝ)
    (IST : InfoSpectralTriple H₂)
    {X Y : PolarizedMajorana (S := H₂) M} (h : X ⟶ Y) :
    Nonempty
      ((M.weylPlus ≃ₗ[ℝ] (h.toBogoliubovTransform).transportWeylPlus) ×
        (M.weylMinus ≃ₗ[ℝ] (h.toBogoliubovTransform).transportWeylMinus)) ∧
    HasDerivAt
      (fun τ : ℝ =>
        logInformationPartitionFunction ω
          (transportedThermalGenerator (E := E) B IST h.toBogoliubovTransform μ) τ)
      (ω (transportedThermalGenerator (E := E) B IST h.toBogoliubovTransform μ)) 0 := by
  refine ⟨?_, normalized_logTransportedThermalOperatorialInformationLift_of_strictSymmetry
    (ω := ω) (hω1 := hω1) (B := B) (μ := μ) (IST := IST) h⟩
  exact ⟨transportWeylWeightEquivs_of_strictSymmetry (M := M) h⟩

/--
Under vacuum-transported Einstein closure, the transported thermal lift reduces
back to the transported Dirac lift on the same carrier.
-/
theorem normalized_logTransportedThermalOperatorialInformationLift_of_vacuumTransported
    (ω : EndHD →L[ℝ] ℝ)
    (hω1 : ω (1 : EndHD) = 1)
    (B : HyperbolicMixingParams)
    (IST : InfoSpectralTriple H₂)
    (R : RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (x : E) (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R K x scalar Λ V Γ)
    {X Y : PolarizedMajorana (S := H₂) M} (h : X ⟶ Y) :
    HasDerivAt
      (fun τ : ℝ =>
        logInformationPartitionFunction ω
          (transportedThermalGenerator (E := E) B IST h.toBogoliubovTransform
            (einsteinInducedChemicalPotential R K x scalar Λ V Γ)) τ)
      (ω (transportDirac IST h.toBogoliubovTransform)) 0 :=
  normalized_logSplitCliffordThermalWeightFunctionalLift_of_vacuumTransported
    (ω := ω) (hω1 := hω1) (B := B) (IST := IST)
    (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ)
    (V := V) (Γ := Γ) hVacSplit h

end Doubled

end InfoGeometry.Canonical.OperatorialInformationLift
