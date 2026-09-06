import InfoGeometry.Canonical.EPDefectAlgebra
import InfoGeometry.Canonical.InverseKernelCartanCore
import Mathlib.Tactic.NoncommRing

namespace InfoGeometry.Canonical

/-!
# Drazin Penrose Dilation Algebra

Owner surface for the repo-native Drazin–Penrose–dilation Cartan slice carried
by a `CertifiedInverseKernel`.

The canonical generators are:

- `P_D`: Drazin core projector.
- `P_L`, `P_R`: Moore-Penrose left/right projectors.
- `Γ_S`: spectral Cartan grading.
- `Γ_G`: geometric Cartan grading (`P_R - P_L`).
- `G`: half-gap dilation generator.
- `Δ`: projector mismatch (`P_D - P_L`).
- `χ_L`, `χ_R`: left/right anomaly commutators.
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

namespace CertifiedInverseKernel

variable (CIK : CertifiedInverseKernel E)

/-- Spectral Cartan grading `Γ_S`. -/
noncomputable abbrev spectralCartanGenerator : EndH :=
  CIK.GammaS

/-- Geometric Cartan grading `Γ_G = P_R - P_L`. -/
abbrev geometricCartanGenerator : EndH :=
  CIK.mpChiralGap

/-- Dilation generator `G = (1/2) • (P_R - P_L)`. -/
noncomputable abbrev dilationGenerator : EndH :=
  CIK.dilationGap

/-- Drazin projector `P_D`. -/
abbrev drazinProjector : EndH :=
  CIK.drazinCoreProj

/-- Moore-Penrose left projector `P_L`. -/
abbrev mpLeftProjector : EndH :=
  CIK.mpLeftProj

/-- Moore-Penrose right projector `P_R`. -/
abbrev mpRightProjector : EndH :=
  CIK.mpRightProj

/-- Projector mismatch `Δ = P_D - P_L`. -/
abbrev projectorMismatchGenerator : EndH :=
  CIK.projectorMismatch

/-- Left anomaly commutator `χ_L = [P_D, P_L]`. -/
abbrev leftAnomalyGenerator : EndH :=
  CIK.chiralAnomaly

/-- Right anomaly commutator `χ_R = [P_D, P_R]`. -/
abbrev rightAnomalyGenerator : EndH :=
  CIK.rightChiralAnomaly

/-- Canonical geometric/dilation identity `Γ_G = 2G`. -/
theorem geometricCartanGenerator_eq_two_smul_dilationGenerator :
    CIK.geometricCartanGenerator = (2 : ℝ) • CIK.dilationGenerator := by
  exact CIK.mpChiralGap_eq_two_smul_dilationGap

/-- Canonical bracket identity `[P_D, Γ_G] = χ_R - χ_L`. -/
theorem drazinProjector_commutator_geometricCartanGenerator_eq_sub_anomalies :
    CIK.drazinProjector * CIK.geometricCartanGenerator
      - CIK.geometricCartanGenerator * CIK.drazinProjector
      =
    CIK.rightAnomalyGenerator - CIK.leftAnomalyGenerator := by
  calc
    CIK.drazinProjector * CIK.geometricCartanGenerator
        - CIK.geometricCartanGenerator * CIK.drazinProjector
      = CIK.drazinProjector * ((2 : ℝ) • CIK.dilationGenerator)
          - ((2 : ℝ) • CIK.dilationGenerator) * CIK.drazinProjector := by
            rw [CIK.geometricCartanGenerator_eq_two_smul_dilationGenerator]
    _ = (2 : ℝ) •
          (CIK.drazinProjector * CIK.dilationGenerator
            - CIK.dilationGenerator * CIK.drazinProjector) := by
          simp [smul_sub]
    _ = (2 : ℝ) • (((2 : ℝ)⁻¹) •
          (CIK.rightAnomalyGenerator - CIK.leftAnomalyGenerator)) := by
          rw [show CIK.drazinProjector * CIK.dilationGenerator
                - CIK.dilationGenerator * CIK.drazinProjector
                = ((2 : ℝ)⁻¹) •
                    (CIK.rightAnomalyGenerator - CIK.leftAnomalyGenerator) by
                simpa [CertifiedInverseKernel.drazinProjector,
                  CertifiedInverseKernel.dilationGenerator,
                  CertifiedInverseKernel.rightAnomalyGenerator,
                  CertifiedInverseKernel.leftAnomalyGenerator] using
                CIK.spectralProjector_commutator_dilationGap_eq_half_sub_anomalies]
    _ = CIK.rightAnomalyGenerator - CIK.leftAnomalyGenerator := by
          simp [smul_smul]

end CertifiedInverseKernel

end InfoGeometry.Canonical
