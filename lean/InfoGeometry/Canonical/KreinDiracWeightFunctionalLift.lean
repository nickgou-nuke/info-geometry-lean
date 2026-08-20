import InfoGeometry.Canonical.SplitCliffordThermalBridge
import InfoGeometry.Canonical.InformationPartitionCore

/-!
# Krein Dirac Weight Functional Lift

Thin canonical layer packaging the weight-transport and analytic-lift facts
already present on the transported Dirac--Clifford--Krein carrier.

This file does not claim a full spectral theorem or invariant-subspace theory
for the transported generators. It only records the currently proved owner
surface:

- strict symmetry yields explicit linear equivalences on the Weyl weight sectors,
- the transported Dirac and thermal generators carry additive exponential flows,
- normalized log-partition calculus applies to those generators,
- vacuum-transported Einstein gauge terms collapse the thermal generator back to
  the transported Dirac generator.
-/

namespace InfoGeometry.Canonical.KreinDiracWeightFunctionalLift

open InfoGeometry.Quantum.RealMajorana
open InfoGeometry.Canonical.KreinDiracPolarizationBridge
open InfoGeometry.Canonical.KreinDiracSpectralLift
open InfoGeometry.Canonical.SplitCliffordThermalBridge
open InfoGeometry.Canonical.SpectralInference
open InfoGeometry.Canonical.InformationCalculus.ModularRadonNikodymData
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Krein

section Doubled

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {M : RealMajoranaDatum (S := DoubledSpace E)}

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedSpace ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- Strict symmetry induces the explicit Weyl-plus weight equivalence. -/
noncomputable def transportWeylPlusEquiv_of_strictSymmetry
    {X Y : PolarizedMajorana (S := H₂) M} (h : X ⟶ Y) :
    M.weylPlus ≃ₗ[ℝ] (h.toBogoliubovTransform).transportWeylPlus :=
  h.toBogoliubovTransform.weylPlusEquiv

/-- Strict symmetry induces the explicit Weyl-minus weight equivalence. -/
noncomputable def transportWeylMinusEquiv_of_strictSymmetry
    {X Y : PolarizedMajorana (S := H₂) M} (h : X ⟶ Y) :
    M.weylMinus ≃ₗ[ℝ] (h.toBogoliubovTransform).transportWeylMinus :=
  h.toBogoliubovTransform.weylMinusEquiv

/-- Pair of transported Weyl weight equivalences under strict symmetry. -/
noncomputable def transportWeylWeightEquivs_of_strictSymmetry
    {X Y : PolarizedMajorana (S := H₂) M} (h : X ⟶ Y) :
    (M.weylPlus ≃ₗ[ℝ] (h.toBogoliubovTransform).transportWeylPlus) ×
    (M.weylMinus ≃ₗ[ℝ] (h.toBogoliubovTransform).transportWeylMinus) :=
  ⟨transportWeylPlusEquiv_of_strictSymmetry (M := M) h,
    transportWeylMinusEquiv_of_strictSymmetry (M := M) h⟩

/-- Strict symmetry keeps the transported Dirac exponential flow additive in time. -/
theorem transportDiracFlow_add_of_strictSymmetry
    (IST : InfoSpectralTriple H₂)
    {X Y : PolarizedMajorana (S := H₂) M} (h : X ⟶ Y)
    (s t : ℝ) :
    transportDiracFlow IST h.toBogoliubovTransform (s + t)
      = transportDiracFlow IST h.toBogoliubovTransform s
          * transportDiracFlow IST h.toBogoliubovTransform t :=
  transportDiracFlow_add (IST := IST) (T := h.toBogoliubovTransform) s t

/-- Normalized log-partition lift for the transported Dirac generator. -/
theorem normalized_logKreinDiracWeightLift_of_strictSymmetry
    (ω : EndH →L[ℝ] ℝ)
    (hω1 : ω (1 : EndH) = 1)
    (IST : InfoSpectralTriple H₂)
    {X Y : PolarizedMajorana (S := H₂) M} (h : X ⟶ Y) :
    HasDerivAt
      (fun τ : ℝ =>
        logInformationPartitionFunction ω
          (transportDirac IST h.toBogoliubovTransform) τ)
      (ω (transportDirac IST h.toBogoliubovTransform)) 0 :=
  normalized_logKreinDiracSpectralLift_of_strictSymmetry
    (ω := ω) (hω1 := hω1) (IST := IST) h

/-- Strict symmetry keeps the transported thermal flow additive in time. -/
theorem transportedThermalFlow_add_of_strictSymmetry
    (B : HyperbolicMixingParams)
    (μ : ℝ)
    (IST : InfoSpectralTriple H₂)
    {X Y : PolarizedMajorana (S := H₂) M} (h : X ⟶ Y)
    (s t : ℝ) :
    transportedThermalFlow (E := E) B IST h.toBogoliubovTransform μ (s + t)
      = transportedThermalFlow (E := E) B IST h.toBogoliubovTransform μ s
          * transportedThermalFlow (E := E) B IST h.toBogoliubovTransform μ t :=
  transportedThermalFlow_add (E := E) (B := B) (IST := IST)
    (T := h.toBogoliubovTransform) (μ := μ) s t

/-- Normalized log-partition lift for the transported thermal generator. -/
theorem normalized_logSplitCliffordThermalWeightLift_of_strictSymmetry
    (ω : EndH →L[ℝ] ℝ)
    (hω1 : ω (1 : EndH) = 1)
    (B : HyperbolicMixingParams)
    (μ : ℝ)
    (IST : InfoSpectralTriple H₂)
    {X Y : PolarizedMajorana (S := H₂) M} (h : X ⟶ Y) :
    HasDerivAt
      (fun τ : ℝ =>
        logInformationPartitionFunction ω
          (transportedThermalGenerator (E := E) B IST h.toBogoliubovTransform μ) τ)
      (ω (transportedThermalGenerator (E := E) B IST h.toBogoliubovTransform μ)) 0 :=
  normalized_logSplitCliffordThermalBridge_of_strictSymmetry
    (ω := ω) (hω1 := hω1) (B := B) (μ := μ) (IST := IST) h

/--
Vacuum-transported Einstein gauge terms collapse the transported thermal
generator back to the transported Dirac generator, so the normalized
log-partition lift reduces to the spectral one on the same carrier.
-/
theorem normalized_logSplitCliffordThermalWeightFunctionalLift_of_vacuumTransported
    (ω : EndH →L[ℝ] ℝ)
    (hω1 : ω (1 : EndH) = 1)
    (B : HyperbolicMixingParams)
    (IST : InfoSpectralTriple H₂)
    (R : RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (x : E) (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : RicciMongeAmpere.SpinConnection K x V)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R K x scalar Λ V Γ)
    {X Y : PolarizedMajorana (S := H₂) M} (h : X ⟶ Y) :
    HasDerivAt
      (fun τ : ℝ =>
        logInformationPartitionFunction ω
          (transportedThermalGenerator (E := E) B IST h.toBogoliubovTransform
            (einsteinInducedChemicalPotential R K x scalar Λ V Γ)) τ)
      (ω (transportDirac IST h.toBogoliubovTransform)) 0 := by
  have hgen :
      transportedThermalGenerator (E := E) B IST h.toBogoliubovTransform
        (einsteinInducedChemicalPotential R K x scalar Λ V Γ)
        = transportDirac IST h.toBogoliubovTransform := by
    exact transportedThermalGenerator_eq_transportDirac_of_vacuumTransported
      (E := E) (B := B) (IST := IST) (T := h.toBogoliubovTransform)
      (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ)
      (V := V) (Γ := Γ) hVacSplit
  simpa [hgen] using
    normalized_logKreinDiracSpectralLift_of_strictSymmetry
      (ω := ω) (hω1 := hω1) (IST := IST) h

end Doubled

end InfoGeometry.Canonical.KreinDiracWeightFunctionalLift
