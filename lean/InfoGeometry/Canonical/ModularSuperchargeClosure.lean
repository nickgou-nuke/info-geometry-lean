import InfoGeometry.Canonical.DrazinSupercharge
import InfoGeometry.Canonical.DrazinModularSingularityBridge
import InfoGeometry.Canonical.BogoliubovClosedForms
import InfoGeometry.Canonical.RealTomitaCore
import InfoGeometry.Canonical.WedgeBoostModularBridge
import InfoGeometry.Canonical.ModularSpectralConjugationBridge
import InfoGeometry.Canonical.GlobalChiralDecomposition
import InfoGeometry.Canonical.RelativeModularBlockDiagonalCore
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace Topology

/-!
# InfoGeometry.Canonical.ModularSuperchargeClosure

Closure bridge for the projected Drazin even lane to modular transport.

This version is constructive: it defines a canonical modular seed from `H_D`
and derives `H_D = modularTransportGenerator(seed)` internally.

From that identification it derives:
1. modular adjoint-flow fixedness of `H_D`,
2. wedge-parameter fixedness,
3. transport of the internal canonical split `H_D = H + Z` to the modular lane.
-/

namespace InfoGeometry.Canonical.ModularSuperchargeClosure

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.DrazinSupercharge
open InfoGeometry.Canonical.DrazinModularSingularityBridge
open InfoGeometry.Canonical.RealTomitaCore
open InfoGeometry.Canonical.WedgeBoostModularBridge
open InfoGeometry.Canonical.TomitaTakesaki

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/--
Canonical modular seed extracted from the projected even generator:
`h_mod := -(H_D ∘ K)`.
-/
@[rep_depth transport]
noncomputable def canonicalModularSeed
    (CIK : CertifiedInverseKernel H₂) : EndH :=
  -(DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK).comp
    (modularComplexI (E := E))

/--
Comparison theorem to the active spectral-wedge lane:
after multiplying by the bridged wedge sign, the canonical modular seed factors
through `J * P_D` on the certified regular Drazin block.
-/
@[rep_depth transport]
theorem canonicalModularSeed_mul_owned_epsilon_eq_neg_superHamiltonian_mul_modular_j_mul_spectralProjector
    (CIK : CertifiedInverseKernel H₂)
    {W : InfoGeometry.Canonical.ModularSpectralWedge.HasModularSpectralWedge E}
    (owned_epsilon : EndH)
    (comp :
      InfoGeometry.Canonical.ModularSpectralWedgeBridge.IsCompatibleWedge
        W owned_epsilon CIK.spectralComplementaryProjector)
    (hActivePhase :
      modularComplexI (E := E) = (modular_j (E := E)) * owned_epsilon) :
    canonicalModularSeed (E := E) CIK * owned_epsilon
      =
    -(
      DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
        * ((modular_j (E := E)) * CIK.spectralProjector)
      ) := by
  have hActive :
      InfoGeometry.Canonical.ModularSpectralConjugationBridge.activeModularConjugation
          (E := E) owned_epsilon CIK.spectralComplementaryProjector
        =
      (modular_j (E := E)) * CIK.spectralProjector :=
    InfoGeometry.Canonical.ModularSpectralConjugationBridge.Compatibility.activeModularConjugation_eq_modular_j_mul_spectralProjector
      (E := E) (W := W) CIK owned_epsilon comp hActivePhase
  calc
    canonicalModularSeed (E := E) CIK * owned_epsilon
        =
      -(
        DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
          * InfoGeometry.Canonical.ModularSpectralConjugationBridge.activeModularConjugation
              (E := E) owned_epsilon CIK.spectralComplementaryProjector
      ) := by
        ext x <;> rfl
    _ =
      -(
        DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
          * ((modular_j (E := E)) * CIK.spectralProjector)
      ) := by rw [hActive]

/--
Projector-first specialization of the canonical-seed comparison theorem:
using the owned sign operator `Σ = P₊ - P₋`, the canonical seed factors through
`J * P_D` on the certified regular Drazin block.
-/
@[rep_depth transport]
theorem canonicalModularSeed_mul_modularSign_eq_neg_superHamiltonian_mul_modular_j_mul_spectralProjector
    (CIK : CertifiedInverseKernel H₂)
    {W : InfoGeometry.Canonical.ModularSpectralWedge.HasModularSpectralWedge E}
    (comp :
      InfoGeometry.Canonical.ModularSpectralWedgeBridge.IsCompatibleWedge
        W (InfoGeometry.Canonical.ProjectorEquivariance.modularSign (E := E))
          CIK.spectralComplementaryProjector) :
    canonicalModularSeed (E := E) CIK
      * InfoGeometry.Canonical.ProjectorEquivariance.modularSign (E := E)
      =
    -(
      DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
        * ((modular_j (E := E)) * CIK.spectralProjector)
      ) := by
  exact canonicalModularSeed_mul_owned_epsilon_eq_neg_superHamiltonian_mul_modular_j_mul_spectralProjector
    (E := E) (CIK := CIK)
    (W := W)
    (owned_epsilon := InfoGeometry.Canonical.ProjectorEquivariance.modularSign (E := E))
    comp
    (InfoGeometry.Canonical.ModularSpectralConjugationBridge.Compatibility.modularComplexI_eq_modular_j_mul_modularSign
      (E := E))

/--
Projector-first DPD split specialization on the modular lane:
`Q_D = [P_D, Σ] + [P_D, Γ_G - Σ]` with `Σ = P₊ - P₋`.
-/
@[rep_depth krein]
theorem supercharge_eq_commutator_spectralProjector_modularSign_add_commutator_spectralProjector_GammaG_sub_modularSign
    (CIK : CertifiedInverseKernel H₂) :
    DrazinSupercharge.CertifiedInverseKernel.supercharge CIK
      =
    DrazinSupercharge.commutator CIK.spectralProjector
      (InfoGeometry.Canonical.ProjectorEquivariance.modularSign (E := E))
      +
    DrazinSupercharge.commutator CIK.spectralProjector
      (CIK.GammaG - InfoGeometry.Canonical.ProjectorEquivariance.modularSign (E := E)) := by
  simpa [DrazinSupercharge.CertifiedInverseKernel.geometricMismatch] using
    (DrazinSupercharge.CertifiedInverseKernel.supercharge_eq_commutator_spectralProjector_sigma_add_commutator_spectralProjector_geometricMismatch
      (CIK := CIK)
      (sigma := InfoGeometry.Canonical.ProjectorEquivariance.modularSign (E := E)))

/--
Equivalent `ε`-form of the DPD split specialization:
`Q_D = [P_D, ε] + [P_D, Γ_G - ε]`.
-/
@[rep_depth krein]
theorem supercharge_eq_commutator_spectralProjector_spectral_epsilon_add_commutator_spectralProjector_GammaG_sub_spectral_epsilon
    (CIK : CertifiedInverseKernel H₂) :
    DrazinSupercharge.CertifiedInverseKernel.supercharge CIK
      =
    DrazinSupercharge.commutator CIK.spectralProjector (spectral_epsilon (E := E))
      +
    DrazinSupercharge.commutator CIK.spectralProjector
      (CIK.GammaG - spectral_epsilon (E := E)) := by
  simpa [InfoGeometry.Canonical.ProjectorEquivariance.modularSign_eq_spectral_epsilon] using
    supercharge_eq_commutator_spectralProjector_modularSign_add_commutator_spectralProjector_GammaG_sub_modularSign
      (E := E) (CIK := CIK)

/--
CP-003 downstream consumer on the modular lane:
reuse the singular projector/anomaly surrogate closure directly from the
global-chiral owner surface.
-/
@[rep_depth transport, capstone]
theorem cp003_singular_surrogate_commutator_closure
    (CIK : CertifiedInverseKernel H₂) :
    let K : InfoGeometry.Canonical.DrazinPenroseDilationKKT.DPDKKT H₂ := ⟨CIK⟩
    InfoGeometry.Canonical.DrazinPenroseDilationKKT.commutator K.P_D K.GammaG
      = K.rightSupercharge - K.leftSupercharge := by
  intro K
  exact InfoGeometry.Canonical.GlobalChiralDecomposition.singular_polar_surrogate_closure
    (E := E) K

/--
The canonical seed realizes the projected even generator as a true modular
transport generator:
`H_D = modularTransportGenerator(canonicalModularSeed)`.
-/
@[rep_depth transport]
theorem superHamiltonian_eq_modularTransportGenerator_canonicalSeed
    (CIK : CertifiedInverseKernel H₂) :
    DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
      =
    modularTransportGenerator (E := E) (canonicalModularSeed (E := E) CIK) := by
  set SH : EndH := DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
  set K : EndH := modularComplexI (E := E)
  have hK2 : K.comp K = -(ContinuousLinearMap.id ℝ H₂) := by
    simpa [K] using modularComplexI_sq (E := E)
  have hEq :
      modularTransportGenerator (E := E) (canonicalModularSeed (E := E) CIK) = SH := by
    calc
      modularTransportGenerator (E := E) (canonicalModularSeed (E := E) CIK)
          = (-(SH.comp K)).comp K := by
              simp [canonicalModularSeed, modularTransportGenerator, SH, K]
      _ = -((SH.comp K).comp K) := by simp
      _ = -(SH.comp (K.comp K)) := by simp [ContinuousLinearMap.comp_assoc]
      _ = -(SH.comp (-(ContinuousLinearMap.id ℝ H₂))) := by rw [hK2]
      _ = -(-(SH.comp (ContinuousLinearMap.id ℝ H₂))) := by simp
      _ = SH := by simp
  simpa [SH] using hEq.symm

/--
Compatibility witness for the modular capstone on the projected Drazin lane.

This is now assumption-free on the even/generator equality:
the modular seed is fixed canonically from `H_D`.
-/
@[rep_depth transport]
structure ModularSuperchargeCompatibility where
  CIK : CertifiedInverseKernel H₂

namespace ModularSuperchargeCompatibility

variable (M : ModularSuperchargeCompatibility (E := E))

/-- Local alias for the projected Drazin even generator `H_D`. -/
@[rep_depth transport]
noncomputable def HD : EndH :=
  DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK M.CIK

/-- Local alias for the modular transport generator `A_mod`. -/
@[rep_depth transport]
noncomputable def AMod : EndH :=
  modularTransportGenerator (E := E)
    (canonicalModularSeed (E := E) M.CIK)

/-- The compatibility identity in alias form (derived from the canonical seed). -/
@[rep_depth transport]
theorem hHD_eq_AMod : M.HD = M.AMod := by
  simpa [HD, AMod] using
    (superHamiltonian_eq_modularTransportGenerator_canonicalSeed
      (E := E) (CIK := M.CIK))

/--
Under compatibility, the projected even generator `H_D` is fixed by modular
adjoint transport.
-/
@[rep_depth transport]
theorem hD_fixed_under_modularAdjointFlow (t : ℝ) :
    DrazinModularSingularityBridge.modularAdjointFlow
      (E := E)
      (canonicalModularSeed (E := E) M.CIK)
      t M.HD = M.HD := by
  have hCommGen :
      Commute M.HD
        (modularTransportGenerator (E := E)
          (canonicalModularSeed (E := E) M.CIK)) := by
    rw [M.hHD_eq_AMod]
    exact Commute.refl _
  exact
    DrazinModularSingularityBridge.modularAdjointFlow_eq_self_of_commute_generator
      (E := E)
      (canonicalModularSeed (E := E) M.CIK)
      M.HD t hCommGen

/--
Wedge-normalized version of modular fixedness using `τ_mod = τ_wedge / (2π)`.
-/
@[rep_depth transport]
theorem hD_fixed_under_wedgeAdjointFlow (τwedge : ℝ) :
    DrazinModularSingularityBridge.modularAdjointFlow
      (E := E)
      (canonicalModularSeed (E := E) M.CIK)
      (RealTomitaCore.modularTimeOfWedgeBoost τwedge)
      M.HD
      = M.HD := by
  exact M.hD_fixed_under_modularAdjointFlow
    (RealTomitaCore.modularTimeOfWedgeBoost τwedge)

/--
Compatibility transports the internal canonical split onto the modular lane.
-/
@[rep_depth transport]
theorem modularGenerator_eq_canonicalKinetic_plus_canonicalDefectCentral :
    modularTransportGenerator (E := E)
      (canonicalModularSeed (E := E) M.CIK)
      =
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalKineticPartK (CIK := M.CIK)
      +
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK M.CIK := by
  calc
    modularTransportGenerator (E := E)
      (canonicalModularSeed (E := E) M.CIK)
        = InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK M.CIK := by
            simpa [HD, AMod] using M.hHD_eq_AMod.symm
    _ = InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalKineticPartK (CIK := M.CIK)
          + InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK M.CIK := by
          exact
            InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK_eq_canonicalKineticPartK_plus_canonicalDefectCentralK
                (CIK := M.CIK)

/--
Existence form on the modular lane:
`A_mod = H + Z` with the same Drazin-lane centrality witness for `Z`.
-/
@[rep_depth transport]
theorem exists_modularGenerator_split_with_drazin_lane_centrality :
    ∃ H Z : EndH,
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentralK M.CIK Z
        ∧ InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDefectSupportedK M.CIK Z
        ∧ InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.HasVanishingDefectBlockK M.CIK H
        ∧ modularTransportGenerator (E := E)
            (canonicalModularSeed (E := E) M.CIK) = H + Z := by
  rcases
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.exists_superHamiltonian_canonical_split_with_drazin_lane_centralityK
        (CIK := M.CIK)
    with ⟨H, Z, hCentral, hDef, hVan, hSplit⟩
  refine ⟨H, Z, hCentral, hDef, hVan, ?_⟩
  calc
    modularTransportGenerator (E := E)
      (canonicalModularSeed (E := E) M.CIK)
        = InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK M.CIK := by
            simpa [HD, AMod] using M.hHD_eq_AMod.symm
    _ = H + Z := hSplit

/--
Canonical-seed wedge flow bridge from the single lower-owner theorem target:
`FlowEqUnruh(canonicalModularSeed)`.
-/
@[rep_depth transport]
theorem flow_at_wedgeParameter_of_flowEqUnruh
    (hFlowEqUnruh :
      WedgeBoostModularBridge.FlowEqUnruh (E := E)
        (canonicalModularSeed (E := E) M.CIK))
    (τwedge : ℝ) :
    modularTransportFlow (E := E)
      (canonicalModularSeed (E := E) M.CIK)
      (RealTomitaCore.modularTimeOfWedgeBoost τwedge)
      =
    InfoGeometry.Dynamics.unruhFlow (E := E) τwedge := by
  exact WedgeBoostModularBridge.flow_at_wedgeParameter_of_flowEqUnruh
    (E := E)
    (modularSeed := canonicalModularSeed (E := E) M.CIK)
    hFlowEqUnruh
    τwedge

/--
Canonical-seed modular polynomial bridge from the same single lower-owner
theorem target.
-/
@[rep_depth transport]
theorem flow_eq_unruh_modular_polynomial_of_flowEqUnruh
    (hFlowEqUnruh :
      WedgeBoostModularBridge.FlowEqUnruh (E := E)
        (canonicalModularSeed (E := E) M.CIK))
    (τmod : ℝ) :
    modularTransportFlow (E := E)
      (canonicalModularSeed (E := E) M.CIK) τmod
      =
    (Real.cosh (RealTomitaCore.wedgeBoostParameter τmod))
      • (ContinuousLinearMap.id ℝ H₂)
      +
    (Real.sinh (RealTomitaCore.wedgeBoostParameter τmod))
      • InfoGeometry.Dynamics.modularHamiltonian (E := E) := by
  calc
    modularTransportFlow (E := E)
      (canonicalModularSeed (E := E) M.CIK) τmod
        = WedgeBoostModularBridge.unruhFlowOfModularTime (E := E) τmod := by
            simpa [WedgeBoostModularBridge.FlowEqUnruh] using hFlowEqUnruh τmod
    _ =
      (Real.cosh (RealTomitaCore.wedgeBoostParameter τmod))
        • (ContinuousLinearMap.id ℝ H₂)
        +
      (Real.sinh (RealTomitaCore.wedgeBoostParameter τmod))
        • InfoGeometry.Dynamics.modularHamiltonian (E := E) := by
          simpa using
            WedgeBoostModularBridge.unruhFlowOfModularTime_eq_modular_polynomial
              (E := E) τmod

/--
Backward-compatible alias for the old `_of_wedgeCompatibility` API name.
-/
@[rep_depth transport]
theorem flow_at_wedgeParameter_of_wedgeCompatibility
    (W : WedgeBoostModularBridge.WedgeBoostModularCompatibility (E := E))
    (hSeed : W.modularSeed = canonicalModularSeed (E := E) M.CIK)
    (τwedge : ℝ) :
    modularTransportFlow (E := E)
      (canonicalModularSeed (E := E) M.CIK)
      (RealTomitaCore.modularTimeOfWedgeBoost τwedge)
      =
    InfoGeometry.Dynamics.unruhFlow (E := E) τwedge := by
  have hFlowEqUnruh :
      WedgeBoostModularBridge.FlowEqUnruh (E := E)
        (canonicalModularSeed (E := E) M.CIK) := by
    intro τmod
    simpa [hSeed] using W.hFlowEqUnruh τmod
  simpa using flow_at_wedgeParameter_of_flowEqUnruh
    (E := E) (M := M) hFlowEqUnruh τwedge

/--
Backward-compatible alias for the old `_of_wedgeCompatibility` API name.
-/
@[rep_depth transport]
theorem flow_eq_unruh_modular_polynomial_of_wedgeCompatibility
    (W : WedgeBoostModularBridge.WedgeBoostModularCompatibility (E := E))
    (hSeed : W.modularSeed = canonicalModularSeed (E := E) M.CIK)
    (τmod : ℝ) :
    modularTransportFlow (E := E)
      (canonicalModularSeed (E := E) M.CIK) τmod
      =
    (Real.cosh (RealTomitaCore.wedgeBoostParameter τmod))
      • (ContinuousLinearMap.id ℝ H₂)
      +
    (Real.sinh (RealTomitaCore.wedgeBoostParameter τmod))
      • InfoGeometry.Dynamics.modularHamiltonian (E := E) := by
  have hFlowEqUnruh :
      WedgeBoostModularBridge.FlowEqUnruh (E := E)
        (canonicalModularSeed (E := E) M.CIK) := by
    intro t
    simpa [hSeed] using W.hFlowEqUnruh t
  simpa using flow_eq_unruh_modular_polynomial_of_flowEqUnruh
    (E := E) (M := M) hFlowEqUnruh τmod

end ModularSuperchargeCompatibility

/--
Compatibility witness identifying the canonical projected Drazin seed with an
owned real-Tomita `δ = log Δ` package.

This is the missing bridge from canonical-seed closure to the explicit
`RealTomitaCore` owner lane.
-/
@[rep_depth transport]
structure CanonicalSeedTomitaCompatibility where
  CIK : CertifiedInverseKernel H₂
  T : RealTomitaCore.RealModularLogData (E := E)
  hDeltaLog : T.deltaLog = canonicalModularSeed (E := E) CIK

namespace CanonicalSeedTomitaCompatibility

variable (M : CanonicalSeedTomitaCompatibility (E := E))

/--
Tomita generator identification:
`H_D = T.generator` once `T.deltaLog` is identified with the canonical seed.
-/
@[rep_depth transport]
theorem superHamiltonian_eq_tomitaGenerator :
    DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK M.CIK
      = M.T.generator := by
  calc
    DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK M.CIK
        = modularTransportGenerator (E := E)
            (canonicalModularSeed (E := E) M.CIK) := by
            simpa using
              (superHamiltonian_eq_modularTransportGenerator_canonicalSeed
                (E := E) (CIK := M.CIK))
    _ = modularTransportGenerator (E := E) M.T.deltaLog := by
          simpa [M.hDeltaLog]
    _ = M.T.generator := by
          rfl

/--
Flow identification:
the canonical-seed modular flow is exactly the real-Tomita flow of `T`.
-/
@[rep_depth transport]
theorem canonicalSeed_flow_eq_tomitaFlow (t : ℝ) :
    modularTransportFlow (E := E)
      (canonicalModularSeed (E := E) M.CIK) t
      = M.T.flow t := by
  simpa [RealTomitaCore.RealModularLogData.flow, M.hDeltaLog]

/--
Adjoint-flow identification:
the canonical modular adjoint flow is exactly `T.adjointFlow`.
-/
@[rep_depth transport]
theorem canonicalSeed_adjointFlow_eq_tomitaAdjointFlow
    (t : ℝ) (A : EndH) :
    DrazinModularSingularityBridge.modularAdjointFlow
      (E := E)
      (canonicalModularSeed (E := E) M.CIK) t A
      = M.T.adjointFlow t A := by
  unfold DrazinModularSingularityBridge.modularAdjointFlow
  unfold RealTomitaCore.RealModularLogData.adjointFlow
  rw [← M.canonicalSeed_flow_eq_tomitaFlow t, ← M.canonicalSeed_flow_eq_tomitaFlow (-t)]

/--
Tomita-side fixedness of `H_D` under the real-Tomita adjoint flow.
-/
@[rep_depth transport]
theorem superHamiltonian_fixed_under_tomitaAdjointFlow (t : ℝ) :
    M.T.adjointFlow t
      (DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK M.CIK)
      =
    DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK M.CIK := by
  set SH : EndH := DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK M.CIK
  have hGen :
      modularTransportGenerator (E := E)
        (canonicalModularSeed (E := E) M.CIK) = SH := by
    simpa [SH] using
      (superHamiltonian_eq_modularTransportGenerator_canonicalSeed
        (E := E) (CIK := M.CIK)).symm
  have hCommGen :
      Commute SH
        (modularTransportGenerator (E := E)
          (canonicalModularSeed (E := E) M.CIK)) := by
    simpa [hGen] using (Commute.refl SH)
  have hFix :
      DrazinModularSingularityBridge.modularAdjointFlow
        (E := E)
        (canonicalModularSeed (E := E) M.CIK) t
        SH = SH := by
    exact
      DrazinModularSingularityBridge.modularAdjointFlow_eq_self_of_commute_generator
        (E := E)
        (canonicalModularSeed (E := E) M.CIK)
        SH t hCommGen
  calc
    M.T.adjointFlow t
      SH
        =
      DrazinModularSingularityBridge.modularAdjointFlow
        (E := E)
        (canonicalModularSeed (E := E) M.CIK) t
        SH := by
          symm
          exact M.canonicalSeed_adjointFlow_eq_tomitaAdjointFlow
            t SH
    _ = SH := hFix
    _ = DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK M.CIK := by
          rfl

/--
Tomita-side wedge bridge:
if a wedge compatibility witness is provided on `T.deltaLog`, then Tomita flow
at wedge-normalized time equals Unruh flow.
-/
@[rep_depth transport]
theorem tomitaFlow_at_wedgeParameter
    (W : WedgeBoostModularBridge.WedgeBoostModularCompatibility (E := E))
    (hW : W.modularSeed = M.T.deltaLog)
    (τwedge : ℝ) :
    M.T.flow (RealTomitaCore.modularTimeOfWedgeBoost τwedge)
      =
    InfoGeometry.Dynamics.unruhFlow (E := E) τwedge := by
  calc
    M.T.flow (RealTomitaCore.modularTimeOfWedgeBoost τwedge)
        =
      modularTransportFlow (E := E) M.T.deltaLog
        (RealTomitaCore.modularTimeOfWedgeBoost τwedge) := by
          rfl
    _ =
      modularTransportFlow (E := E) W.modularSeed
        (RealTomitaCore.modularTimeOfWedgeBoost τwedge) := by
          simpa [hW]
    _ = InfoGeometry.Dynamics.unruhFlow (E := E) τwedge := by
          simpa using
            WedgeBoostModularBridge.WedgeBoostModularCompatibility.flow_at_wedgeParameter
              (E := E) (W := W) τwedge

end CanonicalSeedTomitaCompatibility

/--
Canonical real-Tomita `δ = log Δ` package induced directly by the canonical
modular seed of the projected Drazin even lane.
-/
@[rep_depth transport]
noncomputable def canonicalTomitaLogData
    (CIK : CertifiedInverseKernel H₂) :
    RealTomitaCore.RealModularLogData (E := E) where
  Delta := NormedSpace.exp (canonicalModularSeed (E := E) CIK)
  deltaLog := canonicalModularSeed (E := E) CIK
  exp_deltaLog := rfl

/--
The canonical real-Tomita package is definitionally aligned with the canonical
modular seed.
-/
@[rep_depth transport]
theorem canonicalTomitaLogData_deltaLog
    (CIK : CertifiedInverseKernel H₂) :
    (canonicalTomitaLogData (E := E) CIK).deltaLog
      = canonicalModularSeed (E := E) CIK := rfl

/--
Canonical compatibility witness from the canonical projected seed to the
canonical real-Tomita package.
-/
@[rep_depth transport]
noncomputable def canonicalSeedTomitaCompatibility
    (CIK : CertifiedInverseKernel H₂) :
    CanonicalSeedTomitaCompatibility (E := E) where
  CIK := CIK
  T := canonicalTomitaLogData (E := E) CIK
  hDeltaLog := rfl

/--
Unconditional Tomita-generator identification on the canonical seed lane.
-/
@[rep_depth transport]
theorem superHamiltonian_eq_canonicalTomitaGenerator
    (CIK : CertifiedInverseKernel H₂) :
    DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
      = (canonicalTomitaLogData (E := E) CIK).generator := by
  let M : CanonicalSeedTomitaCompatibility (E := E) :=
    canonicalSeedTomitaCompatibility (E := E) CIK
  simpa [M, canonicalSeedTomitaCompatibility, canonicalTomitaLogData] using
    (CanonicalSeedTomitaCompatibility.superHamiltonian_eq_tomitaGenerator
      (E := E) (M := M))

/--
Unconditional flow identification between canonical-seed modular flow and the
canonical real-Tomita flow.
-/
@[rep_depth transport]
theorem canonicalSeed_flow_eq_canonicalTomitaFlow
    (CIK : CertifiedInverseKernel H₂) (t : ℝ) :
    modularTransportFlow (E := E)
      (canonicalModularSeed (E := E) CIK) t
      = (canonicalTomitaLogData (E := E) CIK).flow t := by
  let M : CanonicalSeedTomitaCompatibility (E := E) :=
    canonicalSeedTomitaCompatibility (E := E) CIK
  simpa [M, canonicalSeedTomitaCompatibility, canonicalTomitaLogData] using
    (CanonicalSeedTomitaCompatibility.canonicalSeed_flow_eq_tomitaFlow
      (E := E) (M := M) t)

/--
Unconditional fixedness of `H_D` under the canonical real-Tomita adjoint flow.
-/
@[rep_depth transport]
theorem superHamiltonian_fixed_under_canonicalTomitaAdjointFlow
    (CIK : CertifiedInverseKernel H₂) (t : ℝ) :
    (canonicalTomitaLogData (E := E) CIK).adjointFlow t
      (DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK)
      =
    DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK := by
  let M : CanonicalSeedTomitaCompatibility (E := E) :=
    canonicalSeedTomitaCompatibility (E := E) CIK
  simpa [M, canonicalSeedTomitaCompatibility, canonicalTomitaLogData] using
    (CanonicalSeedTomitaCompatibility.superHamiltonian_fixed_under_tomitaAdjointFlow
      (E := E) (M := M) t)

/--
Wedge-calibrated closure (kernel lane):
if canonical Tomita flow is calibrated to a compatible wedge packet, then it
commutes with the certified complementary Drazin projector `Q_D`.
-/
@[rep_depth transport]
theorem canonicalTomitaFlow_commutes_spectralComplementaryProjector_of_wedgeCalibrated
    (CIK : CertifiedInverseKernel H₂)
    {W : InfoGeometry.Canonical.ModularSpectralWedge.HasModularSpectralWedge E}
    (C :
      InfoGeometry.Canonical.ModularSpectralWedgeBridge.WedgeCalibrated
        (E := E)
        (T := canonicalTomitaLogData (E := E) CIK)
        (W := W)
        (owned_epsilon := spectral_epsilon (E := E))
        (owned_P_D := CIK.spectralComplementaryProjector))
    (τ : ℝ) :
    (canonicalTomitaLogData (E := E) CIK).flow τ * CIK.spectralComplementaryProjector
      =
    CIK.spectralComplementaryProjector * (canonicalTomitaLogData (E := E) CIK).flow τ := by
  exact (C.flow_commutes_owned_P_D τ).eq

/--
Wedge-calibrated closure (active lane):
if canonical Tomita flow is calibrated to a compatible wedge packet, then it
commutes with the active projector `1 - Q_D`.
-/
@[rep_depth transport]
theorem canonicalTomitaFlow_commutes_activeProjector_of_wedgeCalibrated
    (CIK : CertifiedInverseKernel H₂)
    {W : InfoGeometry.Canonical.ModularSpectralWedge.HasModularSpectralWedge E}
    (C :
      InfoGeometry.Canonical.ModularSpectralWedgeBridge.WedgeCalibrated
        (E := E)
        (T := canonicalTomitaLogData (E := E) CIK)
        (W := W)
        (owned_epsilon := spectral_epsilon (E := E))
        (owned_P_D := CIK.spectralComplementaryProjector))
    (τ : ℝ) :
    (canonicalTomitaLogData (E := E) CIK).flow τ
        * ((1 : EndH) - CIK.spectralComplementaryProjector)
      =
    ((1 : EndH) - CIK.spectralComplementaryProjector)
        * (canonicalTomitaLogData (E := E) CIK).flow τ := by
  exact
    InfoGeometry.Canonical.ModularSpectralWedgeBridge.WedgeCalibrated.flow_mul_activeProjector_eq_activeProjector_mul_flow
        (E := E)
        (T := canonicalTomitaLogData (E := E) CIK)
        (W := W)
        (owned_epsilon := spectral_epsilon (E := E))
        (owned_PD := CIK.spectralComplementaryProjector)
        C τ

/--
Bounded operator-level canonical relative modular representative on the modular
closure lane: the canonical Tomita flow at time `τ`.
-/
@[rep_depth transport]
noncomputable def canonicalRelativeModularOperator
    (CIK : CertifiedInverseKernel H₂) (τ : ℝ) : EndH :=
  (canonicalTomitaLogData (E := E) CIK).flow τ

/--
Wedge-calibrated commutation witness on the active projector lane:
the canonical bounded relative modular representative commutes with `P_D`.
-/
@[rep_depth transport]
theorem canonicalRelativeModularOperator_commutes_spectralProjector_of_wedgeCalibrated
    (CIK : CertifiedInverseKernel H₂)
    {W : InfoGeometry.Canonical.ModularSpectralWedge.HasModularSpectralWedge E}
    (C :
      InfoGeometry.Canonical.ModularSpectralWedgeBridge.WedgeCalibrated
        (E := E)
        (T := canonicalTomitaLogData (E := E) CIK)
        (W := W)
        (owned_epsilon := spectral_epsilon (E := E))
        (owned_P_D := CIK.spectralComplementaryProjector))
    (τ : ℝ) :
    Commute
      (canonicalRelativeModularOperator (E := E) CIK τ)
      CIK.spectralProjector := by
  have hActive :
      (canonicalTomitaLogData (E := E) CIK).flow τ
          * ((1 : EndH) - CIK.spectralComplementaryProjector)
        =
      ((1 : EndH) - CIK.spectralComplementaryProjector)
          * (canonicalTomitaLogData (E := E) CIK).flow τ :=
    canonicalTomitaFlow_commutes_activeProjector_of_wedgeCalibrated
      (E := E) (CIK := CIK) (W := W) C τ
  have hProj :
      ((1 : EndH) - CIK.spectralComplementaryProjector) = CIK.spectralProjector := by
    rw [CertifiedInverseKernel.spectralComplementaryProjector,
      CertifiedInverseKernel.toInverseKernel', InverseKernel.spectralComplementaryProjector]
    simp
  simpa [Commute, canonicalRelativeModularOperator, hProj] using hActive

/--
Wedge-calibrated mixed-block vanishing for the canonical bounded relative
modular representative on the certified active/apex split.
-/
@[rep_depth transport]
theorem canonicalRelativeModularOperator_mixed_blocks_zero_of_wedgeCalibrated
    (CIK : CertifiedInverseKernel H₂)
    {W : InfoGeometry.Canonical.ModularSpectralWedge.HasModularSpectralWedge E}
    (C :
      InfoGeometry.Canonical.ModularSpectralWedgeBridge.WedgeCalibrated
        (E := E)
        (T := canonicalTomitaLogData (E := E) CIK)
        (W := W)
        (owned_epsilon := spectral_epsilon (E := E))
        (owned_P_D := CIK.spectralComplementaryProjector))
    (τ : ℝ) :
    CIK.spectralComplementaryProjector
      * canonicalRelativeModularOperator (E := E) CIK τ
      * CIK.spectralProjector = 0
      ∧
    CIK.spectralProjector
      * canonicalRelativeModularOperator (E := E) CIK τ
      * CIK.spectralComplementaryProjector = 0 := by
  have hComm :
      Commute
        CIK.spectralProjector
        (canonicalRelativeModularOperator (E := E) CIK τ) :=
    (canonicalRelativeModularOperator_commutes_spectralProjector_of_wedgeCalibrated
      (E := E) (CIK := CIK) (W := W) C τ).symm
  have hCore :=
    InfoGeometry.Canonical.RelativeModularBlockDiagonalCore.block_diagonal_of_commute_idempotent
      (E := E)
      (P := CIK.spectralProjector)
      (R := canonicalRelativeModularOperator (E := E) CIK τ)
      CIK.spectralProjector_idempotent
      hComm
  constructor
  · calc
      CIK.spectralComplementaryProjector
          * canonicalRelativeModularOperator (E := E) CIK τ
          * CIK.spectralProjector
          =
        ((1 : EndH) - CIK.spectralProjector)
          * canonicalRelativeModularOperator (E := E) CIK τ
          * CIK.spectralProjector := by
            rw [CertifiedInverseKernel.spectralComplementaryProjector,
              CertifiedInverseKernel.toInverseKernel', InverseKernel.spectralComplementaryProjector]
      _ = 0 := hCore.1
  · calc
      CIK.spectralProjector
          * canonicalRelativeModularOperator (E := E) CIK τ
          * CIK.spectralComplementaryProjector
          =
        CIK.spectralProjector
          * canonicalRelativeModularOperator (E := E) CIK τ
          * ((1 : EndH) - CIK.spectralProjector) := by
            rw [CertifiedInverseKernel.spectralComplementaryProjector,
              CertifiedInverseKernel.toInverseKernel', InverseKernel.spectralComplementaryProjector]
      _ = 0 := hCore.2

/--
Wedge-calibrated active/apex split for the canonical bounded relative modular
representative.
-/
@[rep_depth transport, capstone]
theorem canonicalRelativeModularOperator_activeApex_split_of_wedgeCalibrated
    (CIK : CertifiedInverseKernel H₂)
    {W : InfoGeometry.Canonical.ModularSpectralWedge.HasModularSpectralWedge E}
    (C :
      InfoGeometry.Canonical.ModularSpectralWedgeBridge.WedgeCalibrated
        (E := E)
        (T := canonicalTomitaLogData (E := E) CIK)
        (W := W)
        (owned_epsilon := spectral_epsilon (E := E))
        (owned_P_D := CIK.spectralComplementaryProjector))
    (τ : ℝ) :
    canonicalRelativeModularOperator (E := E) CIK τ
      =
    CIK.spectralComplementaryProjector
        * canonicalRelativeModularOperator (E := E) CIK τ
        * CIK.spectralComplementaryProjector
      +
    CIK.spectralProjector
        * canonicalRelativeModularOperator (E := E) CIK τ
        * CIK.spectralProjector := by
  have hComm :
      Commute
        CIK.spectralProjector
        (canonicalRelativeModularOperator (E := E) CIK τ) :=
    (canonicalRelativeModularOperator_commutes_spectralProjector_of_wedgeCalibrated
      (E := E) (CIK := CIK) (W := W) C τ).symm
  exact
    InfoGeometry.Canonical.GlobalChiralDecomposition.global_active_apex_decomposition
      (E := E)
      (CIK := CIK)
      (R := canonicalRelativeModularOperator (E := E) CIK τ)
      hComm

/--
Canonical internal modular Hamiltonian extracted from the projected even
generator:
`K_int := (2π)⁻¹ • H_D`.
-/
@[rep_depth transport]
noncomputable def canonicalInternalModularHamiltonian
    (CIK : CertifiedInverseKernel H₂) : EndH :=
  (2 * Real.pi)⁻¹ • DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK

/--
Exact normalization identity on the canonical internal lane:
`H_D = (2π) • K_int`.
-/
@[rep_depth transport]
theorem superHamiltonian_eq_two_pi_smul_canonicalInternalModularHamiltonian
    (CIK : CertifiedInverseKernel H₂) :
    DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
      =
    (2 * Real.pi) • canonicalInternalModularHamiltonian (E := E) CIK := by
  let SH : EndH := DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
  have hTwoPi : (2 * Real.pi : ℝ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hNorm :
      (2 * Real.pi) • canonicalInternalModularHamiltonian (E := E) CIK = SH := by
    unfold canonicalInternalModularHamiltonian
    calc
      (2 * Real.pi) • ((2 * Real.pi)⁻¹ • SH)
          = ((2 * Real.pi) * (2 * Real.pi)⁻¹) • SH := by
              rw [smul_smul]
      _ = SH := by
            rw [mul_inv_cancel₀ hTwoPi]
            simpa using (one_smul ℝ SH)
  simpa [SH] using hNorm.symm

/--
Internal Unruh target on the projected lane, defined directly from `H_D`.

This target is fully operator-internal and assumption-free.
-/
@[rep_depth transport]
noncomputable def internalUnruhFlowOfModularTime
    (CIK : CertifiedInverseKernel H₂) (τmod : ℝ) : EndH :=
  NormedSpace.exp
    (τmod • DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK)

/--
Assumption-free canonical closure: canonical-seed transport equals the internal
Unruh target exactly.
-/
@[rep_depth transport]
theorem canonicalSeedFlow_eq_internalUnruhFlowOfModularTime
    (CIK : CertifiedInverseKernel H₂) :
    ∀ τmod : ℝ,
      modularTransportFlow (E := E)
        (canonicalModularSeed (E := E) CIK) τmod
        =
      internalUnruhFlowOfModularTime (E := E) CIK τmod := by
  intro τmod
  have hGen :
      modularTransportGenerator (E := E)
        (canonicalModularSeed (E := E) CIK)
          =
      DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK := by
    simpa using
      (superHamiltonian_eq_modularTransportGenerator_canonicalSeed
        (E := E) (CIK := CIK)).symm
  simpa [internalUnruhFlowOfModularTime, BogoliubovTransport.modularTransportFlow, hGen]

/--
Canonical-seed wedge bridge with a single hypothesis:
if the canonical-seed modular flow matches the Unruh modular-time flow, then
at wedge-normalized time it matches the wedge-rapidity Unruh flow.
-/
@[rep_depth transport]
def canonicalSeedFlowEqUnruhTarget
    (CIK : CertifiedInverseKernel H₂) : Prop :=
  WedgeBoostModularBridge.FlowEqUnruh (E := E)
    (canonicalModularSeed (E := E) CIK)

/--
Exact closure normal form for the canonical single-gap target:
the target is equivalent to one exponential-flow identity on `H_D`.
-/
@[rep_depth transport]
theorem canonicalSeedFlowEqUnruhTarget_iff_superHamiltonian_exponential
    (CIK : CertifiedInverseKernel H₂) :
    canonicalSeedFlowEqUnruhTarget (E := E) CIK
      ↔
    (∀ τmod : ℝ,
      NormedSpace.exp
        (τmod • DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK)
        =
      WedgeBoostModularBridge.unruhFlowOfModularTime (E := E) τmod) := by
  have hGen :
      modularTransportGenerator (E := E)
        (canonicalModularSeed (E := E) CIK)
          =
      DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK := by
    simpa using
      (superHamiltonian_eq_modularTransportGenerator_canonicalSeed
        (E := E) (CIK := CIK)).symm
  constructor
  · intro h τmod
    calc
      NormedSpace.exp
        (τmod • DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK)
          =
      NormedSpace.exp
        (τmod • modularTransportGenerator (E := E)
          (canonicalModularSeed (E := E) CIK)) := by
            simp [hGen]
      _ = WedgeBoostModularBridge.unruhFlowOfModularTime (E := E) τmod := by
            simpa [canonicalSeedFlowEqUnruhTarget, WedgeBoostModularBridge.FlowEqUnruh,
              BogoliubovTransport.modularTransportFlow] using h τmod
  · intro h τmod
    calc
      modularTransportFlow (E := E) (canonicalModularSeed (E := E) CIK) τmod
          =
      NormedSpace.exp
        (τmod • modularTransportGenerator (E := E)
          (canonicalModularSeed (E := E) CIK)) := by
            rfl
      _ =
      NormedSpace.exp
        (τmod • DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK) := by
            simp [hGen]
      _ = WedgeBoostModularBridge.unruhFlowOfModularTime (E := E) τmod := h τmod

/--
Generator-identification route for the canonical-seed flow target.

If the canonical modular transport generator is identified with the wedge-scaled
Unruh generator and the corresponding exponential lane is identified with the
Unruh modular-time flow, then the canonical seed satisfies `FlowEqUnruh`.
-/
@[rep_depth transport]
theorem canonicalSeedFlowEqUnruhTarget_of_generator_identification
    (CIK : CertifiedInverseKernel H₂)
    (hGen :
      modularTransportGenerator (E := E) (canonicalModularSeed (E := E) CIK)
        =
      (2 * Real.pi) • InfoGeometry.Dynamics.modularHamiltonian (E := E))
    (hExp :
      ∀ τmod : ℝ,
        NormedSpace.exp
            (τmod • ((2 * Real.pi) • InfoGeometry.Dynamics.modularHamiltonian (E := E)))
          =
        WedgeBoostModularBridge.unruhFlowOfModularTime (E := E) τmod) :
    canonicalSeedFlowEqUnruhTarget (E := E) CIK := by
  intro τmod
  change
    NormedSpace.exp
        (τmod • modularTransportGenerator (E := E) (canonicalModularSeed (E := E) CIK))
      =
    WedgeBoostModularBridge.unruhFlowOfModularTime (E := E) τmod
  calc
    NormedSpace.exp
        (τmod • modularTransportGenerator (E := E) (canonicalModularSeed (E := E) CIK))
      =
    NormedSpace.exp
        (τmod • ((2 * Real.pi) • InfoGeometry.Dynamics.modularHamiltonian (E := E))) := by
          rw [hGen]
    _ = WedgeBoostModularBridge.unruhFlowOfModularTime (E := E) τmod := hExp τmod

/--
Canonical generator-identification route specialized from `H_D`.

This packages the single algebraic generator identification
`H_D = (2π)·K_unruh` with the exponential-flow identification witness into
`FlowEqUnruh(canonicalModularSeed)`.
-/
@[rep_depth transport]
theorem canonicalSeedFlowEqUnruhTarget_of_superHamiltonian_identification
    (CIK : CertifiedInverseKernel H₂)
    (hHD :
      DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
        =
      (2 * Real.pi) • InfoGeometry.Dynamics.modularHamiltonian (E := E))
    (hExp :
      ∀ τmod : ℝ,
        NormedSpace.exp
            (τmod • ((2 * Real.pi) • InfoGeometry.Dynamics.modularHamiltonian (E := E)))
          =
        WedgeBoostModularBridge.unruhFlowOfModularTime (E := E) τmod) :
    canonicalSeedFlowEqUnruhTarget (E := E) CIK := by
  have hGen :
      modularTransportGenerator (E := E) (canonicalModularSeed (E := E) CIK)
        =
      (2 * Real.pi) • InfoGeometry.Dynamics.modularHamiltonian (E := E) := by
    calc
      modularTransportGenerator (E := E) (canonicalModularSeed (E := E) CIK)
        = DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK := by
            simpa using
              (superHamiltonian_eq_modularTransportGenerator_canonicalSeed
                (E := E) (CIK := CIK)).symm
      _ = (2 * Real.pi) • InfoGeometry.Dynamics.modularHamiltonian (E := E) := hHD
  exact canonicalSeedFlowEqUnruhTarget_of_generator_identification
    (E := E) CIK hGen hExp

/--
Hyperbolic exponential witness for the wedge/Unruh modular-time lane.

If the chosen modular Hamiltonian squares to `Id`, the exponential transport law
matches the owned Unruh modular-time polynomial exactly.
-/
@[rep_depth transport]
theorem unruh_exponential_witness_of_modularHamiltonian_sq_one
    :
    ∀ τmod : ℝ,
      NormedSpace.exp
        (τmod • ((2 * Real.pi) • InfoGeometry.Dynamics.modularHamiltonian (E := E)))
        =
      WedgeBoostModularBridge.unruhFlowOfModularTime (E := E) τmod := by
  intro τmod
  have hSq :
      (InfoGeometry.Dynamics.modularHamiltonian (E := E)
        : EndH) * InfoGeometry.Dynamics.modularHamiltonian (E := E) = (1 : EndH) := by
    simpa using (InfoGeometry.Dynamics.modularHamiltonian_sq_one (E := E))
  calc
    NormedSpace.exp
      (τmod • ((2 * Real.pi) • InfoGeometry.Dynamics.modularHamiltonian (E := E)))
        =
    NormedSpace.exp
      ((τmod * (2 * Real.pi)) • InfoGeometry.Dynamics.modularHamiltonian (E := E)) := by
        rw [smul_smul]
    _ =
      (Real.cosh (τmod * (2 * Real.pi))) • (1 : EndH)
        + (Real.sinh (τmod * (2 * Real.pi)))
            • InfoGeometry.Dynamics.modularHamiltonian (E := E) := by
          simpa using
            BogoliubovClosedForms.exp_eq_cosh_add_sinh_of_sq_eq_one
              (E := E) (G := InfoGeometry.Dynamics.modularHamiltonian (E := E))
              hSq
              (τmod * (2 * Real.pi))
    _ =
      (Real.cosh (RealTomitaCore.wedgeBoostParameter τmod))
        • (ContinuousLinearMap.id ℝ H₂)
        + (Real.sinh (RealTomitaCore.wedgeBoostParameter τmod))
            • InfoGeometry.Dynamics.modularHamiltonian (E := E) := by
          have hOne : (1 : EndH) = (ContinuousLinearMap.id ℝ H₂) := by
            ext x <;> rfl
          rw [hOne]
          simp [RealTomitaCore.wedgeBoostParameter, mul_comm]
    _ = WedgeBoostModularBridge.unruhFlowOfModularTime (E := E) τmod := by
          simpa using
            (WedgeBoostModularBridge.unruhFlowOfModularTime_eq_modular_polynomial
              (E := E) τmod).symm

/--
Canonical-seed discharge route specialized to the hyperbolic square law.

This removes the separate exponential witness hypothesis by deriving it from
`modularHamiltonian^2 = Id`.
-/
@[rep_depth transport]
theorem canonicalSeedFlowEqUnruhTarget_of_superHamiltonian_identification_of_modularHamiltonian_sq_one
    (CIK : CertifiedInverseKernel H₂)
    (hHD :
      DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
        =
      (2 * Real.pi) • InfoGeometry.Dynamics.modularHamiltonian (E := E)) :
    canonicalSeedFlowEqUnruhTarget (E := E) CIK := by
  exact canonicalSeedFlowEqUnruhTarget_of_superHamiltonian_identification
    (E := E) CIK hHD
    unruh_exponential_witness_of_modularHamiltonian_sq_one

/--
Owner-level calibration contract for the wedge-normalized closure lane.

This packages the remaining generator-identification obligation as a single
named compatibility surface, avoiding ad-hoc hypothesis threading.
-/
@[rep_depth transport]
structure SuperHamiltonianWedgeCalibration where
  CIK : CertifiedInverseKernel H₂
  hTwoPi :
    DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
      =
    (2 * Real.pi) • InfoGeometry.Dynamics.modularHamiltonian (E := E)

/--
Canonical-seed closure from the packaged wedge calibration contract.
-/
@[rep_depth transport]
theorem canonicalSeedFlowEqUnruhTarget_of_wedgeCalibration
    (C : SuperHamiltonianWedgeCalibration (E := E)) :
    canonicalSeedFlowEqUnruhTarget (E := E) C.CIK := by
  exact
    canonicalSeedFlowEqUnruhTarget_of_superHamiltonian_identification_of_modularHamiltonian_sq_one
      (E := E) C.CIK C.hTwoPi

/--
Infinitesimal generator of the Unruh modular-time flow at the origin:
`d/dτ|₀ unruhFlowOfModularTime = (2π) · modularHamiltonian`.
-/
@[rep_depth transport]
theorem hasDerivAt_unruhFlowOfModularTime_zero :
    HasDerivAt
      (fun τmod : ℝ => WedgeBoostModularBridge.unruhFlowOfModularTime (E := E) τmod)
      ((2 * Real.pi) • InfoGeometry.Dynamics.modularHamiltonian (E := E))
      0 := by
  have hWB :
      HasDerivAt
        (fun τmod : ℝ => RealTomitaCore.wedgeBoostParameter τmod)
        (2 * Real.pi) 0 := by
    simpa [RealTomitaCore.wedgeBoostParameter] using
      (hasDerivAt_const_mul (x := (0 : ℝ)) (c := (2 * Real.pi)))
  have hCosh :
      HasDerivAt
        (fun τmod : ℝ => Real.cosh (RealTomitaCore.wedgeBoostParameter τmod))
        ((Real.sinh (RealTomitaCore.wedgeBoostParameter 0)) * (2 * Real.pi))
        0 := by
    simpa using (Real.hasDerivAt_cosh (RealTomitaCore.wedgeBoostParameter 0)).comp 0 hWB
  have hSinh :
      HasDerivAt
        (fun τmod : ℝ => Real.sinh (RealTomitaCore.wedgeBoostParameter τmod))
        ((Real.cosh (RealTomitaCore.wedgeBoostParameter 0)) * (2 * Real.pi))
        0 := by
    simpa using (Real.hasDerivAt_sinh (RealTomitaCore.wedgeBoostParameter 0)).comp 0 hWB
  have hPoly :
      HasDerivAt
        (fun τmod : ℝ =>
          (Real.cosh (RealTomitaCore.wedgeBoostParameter τmod))
            • (ContinuousLinearMap.id ℝ H₂)
          +
          (Real.sinh (RealTomitaCore.wedgeBoostParameter τmod))
            • InfoGeometry.Dynamics.modularHamiltonian (E := E))
        (((Real.sinh (RealTomitaCore.wedgeBoostParameter 0)) * (2 * Real.pi))
            • (ContinuousLinearMap.id ℝ H₂)
          +
          ((Real.cosh (RealTomitaCore.wedgeBoostParameter 0)) * (2 * Real.pi))
            • InfoGeometry.Dynamics.modularHamiltonian (E := E))
        0 := by
    exact (hCosh.smul_const (ContinuousLinearMap.id ℝ H₂)).add
      (hSinh.smul_const (InfoGeometry.Dynamics.modularHamiltonian (E := E)))
  have hEqFun :
      (fun τmod : ℝ => WedgeBoostModularBridge.unruhFlowOfModularTime (E := E) τmod)
        =
      (fun τmod : ℝ =>
        (Real.cosh (RealTomitaCore.wedgeBoostParameter τmod))
          • (ContinuousLinearMap.id ℝ H₂)
        +
        (Real.sinh (RealTomitaCore.wedgeBoostParameter τmod))
          • InfoGeometry.Dynamics.modularHamiltonian (E := E)) := by
    funext τmod
    simpa using
      (WedgeBoostModularBridge.unruhFlowOfModularTime_eq_modular_polynomial
        (E := E) τmod)
  have hUnruhPoly :
      HasDerivAt
        (fun τmod : ℝ => WedgeBoostModularBridge.unruhFlowOfModularTime (E := E) τmod)
        (((Real.sinh (RealTomitaCore.wedgeBoostParameter 0)) * (2 * Real.pi))
            • (ContinuousLinearMap.id ℝ H₂)
          +
          ((Real.cosh (RealTomitaCore.wedgeBoostParameter 0)) * (2 * Real.pi))
            • InfoGeometry.Dynamics.modularHamiltonian (E := E))
        0 := by
    simpa [hEqFun] using hPoly
  have hCoeff :
      (((Real.sinh (RealTomitaCore.wedgeBoostParameter 0)) * (2 * Real.pi))
          • (ContinuousLinearMap.id ℝ H₂)
        +
        ((Real.cosh (RealTomitaCore.wedgeBoostParameter 0)) * (2 * Real.pi))
          • InfoGeometry.Dynamics.modularHamiltonian (E := E))
        =
      ((2 * Real.pi) • InfoGeometry.Dynamics.modularHamiltonian (E := E)) := by
    simp [RealTomitaCore.wedgeBoostParameter]
  exact hCoeff ▸ hUnruhPoly

/--
Reverse generator-identification route:
if the canonical-seed modular flow equals the Unruh modular-time flow, then
the projected even generator is exactly `(2π) · modularHamiltonian`.
-/
@[rep_depth transport]
theorem superHamiltonian_eq_two_pi_modularHamiltonian_of_canonicalSeedFlowEqUnruhTarget
    (CIK : CertifiedInverseKernel H₂)
    (hFlowEqUnruh : canonicalSeedFlowEqUnruhTarget (E := E) CIK) :
    DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
      =
    (2 * Real.pi) • InfoGeometry.Dynamics.modularHamiltonian (E := E) := by
  have hDerivCanonical :
      HasDerivAt
        (fun τmod : ℝ =>
          modularTransportFlow (E := E) (canonicalModularSeed (E := E) CIK) τmod)
        (DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK)
        0 := by
    have hExp :
        HasDerivAt
          (fun τmod : ℝ =>
            NormedSpace.exp
              (τmod •
                modularTransportGenerator (E := E)
                  (canonicalModularSeed (E := E) CIK)))
          (modularTransportGenerator (E := E)
            (canonicalModularSeed (E := E) CIK))
          0 := by
      simpa [zero_smul, NormedSpace.exp_zero] using
        (hasDerivAt_exp_smul_const
          (modularTransportGenerator (E := E)
            (canonicalModularSeed (E := E) CIK))
          (0 : ℝ))
    simpa [BogoliubovTransport.modularTransportFlow] using
      (superHamiltonian_eq_modularTransportGenerator_canonicalSeed
        (E := E) (CIK := CIK)) ▸ hExp
  have hFlowEq :
      (fun τmod : ℝ =>
        modularTransportFlow (E := E) (canonicalModularSeed (E := E) CIK) τmod)
        =
      (fun τmod : ℝ =>
        WedgeBoostModularBridge.unruhFlowOfModularTime (E := E) τmod) := by
    funext τmod
    exact hFlowEqUnruh τmod
  have hDerivOnUnruh :
      HasDerivAt
        (fun τmod : ℝ =>
          WedgeBoostModularBridge.unruhFlowOfModularTime (E := E) τmod)
        (DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK)
        0 := by
    simpa [hFlowEq] using hDerivCanonical
  exact hDerivOnUnruh.unique (hasDerivAt_unruhFlowOfModularTime_zero (E := E))

/--
Hyperbolic closure equivalence package:
`FlowEqUnruh(canonicalModularSeed)` is equivalent to
`H_D = (2π)·modularHamiltonian`.
-/
@[rep_depth transport]
theorem canonicalSeedFlowEqUnruhTarget_iff_superHamiltonian_eq_two_pi_modularHamiltonian
    (CIK : CertifiedInverseKernel H₂) :
    canonicalSeedFlowEqUnruhTarget (E := E) CIK
      ↔
    (DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
      = (2 * Real.pi) • InfoGeometry.Dynamics.modularHamiltonian (E := E)) := by
  constructor
  · intro hFlow
    exact
      superHamiltonian_eq_two_pi_modularHamiltonian_of_canonicalSeedFlowEqUnruhTarget
        (E := E) CIK hFlow
  · intro hHD
    exact
      canonicalSeedFlowEqUnruhTarget_of_superHamiltonian_identification_of_modularHamiltonian_sq_one
        (E := E) CIK hHD

/--
Projector-first closure equivalence package:
`FlowEqUnruh(canonicalModularSeed)` is equivalent to
`H_D = (2π)·(P₊ - P₋)`.
-/
@[rep_depth transport]
theorem canonicalSeedFlowEqUnruhTarget_iff_superHamiltonian_eq_two_pi_modularSign
    (CIK : CertifiedInverseKernel H₂) :
    canonicalSeedFlowEqUnruhTarget (E := E) CIK
      ↔
    (DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
      = (2 * Real.pi)
          • InfoGeometry.Canonical.ProjectorEquivariance.modularSign (E := E)) := by
  constructor
  · intro hFlow
    have hHD :
        DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
          = (2 * Real.pi) • InfoGeometry.Dynamics.modularHamiltonian (E := E) :=
      (canonicalSeedFlowEqUnruhTarget_iff_superHamiltonian_eq_two_pi_modularHamiltonian
        (E := E) CIK).1 hFlow
    calc
      DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
          = (2 * Real.pi) • InfoGeometry.Dynamics.modularHamiltonian (E := E) := hHD
      _ =
        (2 * Real.pi) • InfoGeometry.Canonical.ProjectorEquivariance.modularSign (E := E) := by
          simp [InfoGeometry.Dynamics.modularHamiltonian_eq_modularSign]
  · intro hHDsign
    have hHD :
        DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
          = (2 * Real.pi) • InfoGeometry.Dynamics.modularHamiltonian (E := E) := by
      calc
        DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
            = (2 * Real.pi)
                • InfoGeometry.Canonical.ProjectorEquivariance.modularSign (E := E) := hHDsign
        _ =
          (2 * Real.pi) • InfoGeometry.Dynamics.modularHamiltonian (E := E) := by
            simp [InfoGeometry.Dynamics.modularHamiltonian_eq_modularSign]
    exact
      (canonicalSeedFlowEqUnruhTarget_iff_superHamiltonian_eq_two_pi_modularHamiltonian
        (E := E) CIK).2 hHD

/--
Canonical single-gap target:
`FlowEqUnruh(canonicalModularSeed)`.
-/
@[rep_depth transport]
theorem canonicalSeed_flow_at_wedgeParameter_of_flowEqUnruh
    (CIK : CertifiedInverseKernel H₂)
    (hFlowEqUnruh : canonicalSeedFlowEqUnruhTarget (E := E) CIK)
    (τwedge : ℝ) :
    modularTransportFlow (E := E)
      (canonicalModularSeed (E := E) CIK)
      (RealTomitaCore.modularTimeOfWedgeBoost τwedge)
      =
    InfoGeometry.Dynamics.unruhFlow (E := E) τwedge := by
  calc
    modularTransportFlow (E := E)
      (canonicalModularSeed (E := E) CIK)
      (RealTomitaCore.modularTimeOfWedgeBoost τwedge)
        =
      WedgeBoostModularBridge.unruhFlowOfModularTime (E := E)
        (RealTomitaCore.modularTimeOfWedgeBoost τwedge) := by
          simpa using hFlowEqUnruh (RealTomitaCore.modularTimeOfWedgeBoost τwedge)
    _ =
      InfoGeometry.Dynamics.unruhFlow (E := E)
        (RealTomitaCore.wedgeBoostParameter
          (RealTomitaCore.modularTimeOfWedgeBoost τwedge)) := by
            rfl
    _ = InfoGeometry.Dynamics.unruhFlow (E := E) τwedge := by
          have hRound :
              RealTomitaCore.wedgeBoostParameter
                (RealTomitaCore.modularTimeOfWedgeBoost τwedge) = τwedge := by
            simpa using WedgeBoostModularBridge.wedgeBoost_roundtrip τwedge
          simpa [hRound]

/--
Canonical real-Tomita wedge bridge with the same single canonical-seed
flow-equality hypothesis.
-/
@[rep_depth transport]
theorem canonicalTomitaFlow_at_wedgeParameter_of_flowEqUnruh
    (CIK : CertifiedInverseKernel H₂)
    (hFlowEqUnruh : canonicalSeedFlowEqUnruhTarget (E := E) CIK)
    (τwedge : ℝ) :
    (canonicalTomitaLogData (E := E) CIK).flow
      (RealTomitaCore.modularTimeOfWedgeBoost τwedge)
      =
    InfoGeometry.Dynamics.unruhFlow (E := E) τwedge := by
  have hSeedFlow :
      modularTransportFlow (E := E)
        (canonicalModularSeed (E := E) CIK)
        (RealTomitaCore.modularTimeOfWedgeBoost τwedge)
        =
      InfoGeometry.Dynamics.unruhFlow (E := E) τwedge :=
    canonicalSeed_flow_at_wedgeParameter_of_flowEqUnruh
      (E := E) CIK hFlowEqUnruh τwedge
  have hTomitaSeed :
      (canonicalTomitaLogData (E := E) CIK).flow
        (RealTomitaCore.modularTimeOfWedgeBoost τwedge)
        =
      modularTransportFlow (E := E)
        (canonicalModularSeed (E := E) CIK)
        (RealTomitaCore.modularTimeOfWedgeBoost τwedge) := by
    symm
    exact canonicalSeed_flow_eq_canonicalTomitaFlow (E := E) CIK
      (RealTomitaCore.modularTimeOfWedgeBoost τwedge)
  calc
    (canonicalTomitaLogData (E := E) CIK).flow
      (RealTomitaCore.modularTimeOfWedgeBoost τwedge)
        =
      modularTransportFlow (E := E)
        (canonicalModularSeed (E := E) CIK)
        (RealTomitaCore.modularTimeOfWedgeBoost τwedge) := hTomitaSeed
    _ = InfoGeometry.Dynamics.unruhFlow (E := E) τwedge := hSeedFlow

/--
Single-hypothesis canonical-seed compatibility interface for wedge/Unruh flow.

This isolates the remaining modular capstone gap to one theorem field:
`FlowEqUnruh(canonicalModularSeed)`.
-/
@[rep_depth transport]
structure CanonicalSeedUnruhCompatibility where
  CIK : CertifiedInverseKernel H₂
  hFlowEqUnruh : canonicalSeedFlowEqUnruhTarget (E := E) CIK

namespace CanonicalSeedUnruhCompatibility

variable (U : CanonicalSeedUnruhCompatibility (E := E))

/--
Export the canonical-seed compatibility as the generic wedge/modular witness.
-/
@[rep_depth transport]
noncomputable def toWedgeBoostModularCompatibility :
    WedgeBoostModularBridge.WedgeBoostModularCompatibility (E := E) where
  modularSeed := canonicalModularSeed (E := E) U.CIK
  hFlowEqUnruh := U.hFlowEqUnruh

/--
Wedge-parameter bridge on the canonical seed from the single-hypothesis
compatibility interface.
-/
@[rep_depth transport]
theorem flow_at_wedgeParameter (τwedge : ℝ) :
    modularTransportFlow (E := E)
      (canonicalModularSeed (E := E) U.CIK)
      (RealTomitaCore.modularTimeOfWedgeBoost τwedge)
      =
    InfoGeometry.Dynamics.unruhFlow (E := E) τwedge := by
  have hFlow :
      modularTransportFlow (E := E)
        (canonicalModularSeed (E := E) U.CIK)
        (RealTomitaCore.modularTimeOfWedgeBoost τwedge)
        =
      InfoGeometry.Dynamics.unruhFlow (E := E) τwedge :=
    canonicalSeed_flow_at_wedgeParameter_of_flowEqUnruh
      (E := E) U.CIK U.hFlowEqUnruh τwedge
  exact hFlow

/--
Tomita-flow wedge bridge on the canonical seed from the same interface.
-/
@[rep_depth transport]
theorem tomitaFlow_at_wedgeParameter (τwedge : ℝ) :
    (canonicalTomitaLogData (E := E) U.CIK).flow
      (RealTomitaCore.modularTimeOfWedgeBoost τwedge)
      =
    InfoGeometry.Dynamics.unruhFlow (E := E) τwedge := by
  have hTomita :
      (canonicalTomitaLogData (E := E) U.CIK).flow
        (RealTomitaCore.modularTimeOfWedgeBoost τwedge)
        =
      InfoGeometry.Dynamics.unruhFlow (E := E) τwedge :=
    canonicalTomitaFlow_at_wedgeParameter_of_flowEqUnruh
      (E := E) U.CIK U.hFlowEqUnruh τwedge
  exact hTomita

/--
Polynomial modular-time form of the canonical-seed flow under the same single
compatibility hypothesis.
-/
@[rep_depth transport]
theorem flow_eq_unruh_modular_polynomial (τmod : ℝ) :
    modularTransportFlow (E := E)
      (canonicalModularSeed (E := E) U.CIK) τmod
      =
    (Real.cosh (RealTomitaCore.wedgeBoostParameter τmod))
      • (ContinuousLinearMap.id ℝ H₂)
      +
    (Real.sinh (RealTomitaCore.wedgeBoostParameter τmod))
      • InfoGeometry.Dynamics.modularHamiltonian (E := E) := by
  have hUnruhEq :
      modularTransportFlow (E := E)
        (canonicalModularSeed (E := E) U.CIK) τmod
        = WedgeBoostModularBridge.unruhFlowOfModularTime (E := E) τmod :=
    U.hFlowEqUnruh τmod
  have hPoly :
      WedgeBoostModularBridge.unruhFlowOfModularTime (E := E) τmod
        =
      (Real.cosh (RealTomitaCore.wedgeBoostParameter τmod))
        • (ContinuousLinearMap.id ℝ H₂)
        +
      (Real.sinh (RealTomitaCore.wedgeBoostParameter τmod))
        • InfoGeometry.Dynamics.modularHamiltonian (E := E) :=
    WedgeBoostModularBridge.unruhFlowOfModularTime_eq_modular_polynomial
      (E := E) τmod
  calc
    modularTransportFlow (E := E)
      (canonicalModularSeed (E := E) U.CIK) τmod
        = WedgeBoostModularBridge.unruhFlowOfModularTime (E := E) τmod := hUnruhEq
    _ =
      (Real.cosh (RealTomitaCore.wedgeBoostParameter τmod))
        • (ContinuousLinearMap.id ℝ H₂)
        +
      (Real.sinh (RealTomitaCore.wedgeBoostParameter τmod))
        • InfoGeometry.Dynamics.modularHamiltonian (E := E) := hPoly

/--
Lower-owner extraction of the calibration identity from the canonical-seed
Unruh compatibility witness.
-/
@[rep_depth transport]
theorem superHamiltonian_eq_two_pi_modularHamiltonian :
    DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK U.CIK
      =
    (2 * Real.pi) • InfoGeometry.Dynamics.modularHamiltonian (E := E) := by
  have hTwoPi :
      DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK U.CIK
        =
      (2 * Real.pi) • InfoGeometry.Dynamics.modularHamiltonian (E := E) :=
    superHamiltonian_eq_two_pi_modularHamiltonian_of_canonicalSeedFlowEqUnruhTarget
      (E := E) U.CIK U.hFlowEqUnruh
  exact hTwoPi

/--
Canonical-seed/Unruh compatibility induces the packaged wedge-calibration
object without extra hypotheses.
-/
@[rep_depth transport]
noncomputable def toSuperHamiltonianWedgeCalibration :
    SuperHamiltonianWedgeCalibration (E := E) where
  CIK := U.CIK
  hTwoPi := U.superHamiltonian_eq_two_pi_modularHamiltonian

end CanonicalSeedUnruhCompatibility

namespace SuperHamiltonianWedgeCalibration

variable (C : SuperHamiltonianWedgeCalibration (E := E))

/--
The packaged wedge calibration implies the canonical-seed/Unruh flow witness.
-/
@[rep_depth transport]
theorem hFlowEqUnruh :
    canonicalSeedFlowEqUnruhTarget (E := E) C.CIK := by
  have hFlow : canonicalSeedFlowEqUnruhTarget (E := E) C.CIK :=
    canonicalSeedFlowEqUnruhTarget_of_wedgeCalibration (E := E) C
  exact hFlow

/--
Packaged wedge calibration converted to canonical-seed/Unruh compatibility.
-/
@[rep_depth transport]
noncomputable def toCanonicalSeedUnruhCompatibility :
    CanonicalSeedUnruhCompatibility (E := E) where
  CIK := C.CIK
  hFlowEqUnruh := C.hFlowEqUnruh

end SuperHamiltonianWedgeCalibration

/--
Unconditional capstone: the projected even generator is fixed by canonical-seed
modular adjoint flow, with no external compatibility hypothesis.
-/
@[rep_depth transport]
theorem superHamiltonian_fixed_under_modularAdjointFlow_canonicalSeed
    (CIK : CertifiedInverseKernel H₂) (t : ℝ) :
    DrazinModularSingularityBridge.modularAdjointFlow
      (E := E)
      (canonicalModularSeed (E := E) CIK)
      t
      (DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK)
      =
    DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK := by
  let M : ModularSuperchargeCompatibility (E := E) := { CIK := CIK }
  have hFixed :
      DrazinModularSingularityBridge.modularAdjointFlow
        (E := E)
        (canonicalModularSeed (E := E) M.CIK)
        t
        (ModularSuperchargeCompatibility.HD (E := E) M)
        =
      ModularSuperchargeCompatibility.HD (E := E) M :=
    ModularSuperchargeCompatibility.hD_fixed_under_modularAdjointFlow
      (E := E) (M := M) t
  simpa [M, ModularSuperchargeCompatibility.HD] using hFixed

/--
Wedge-normalized unconditional capstone: `H_D` fixedness at
`τ_mod = τ_wedge / (2π)`.
-/
@[rep_depth transport]
theorem superHamiltonian_fixed_under_wedgeAdjointFlow_canonicalSeed
    (CIK : CertifiedInverseKernel H₂) (τwedge : ℝ) :
    DrazinModularSingularityBridge.modularAdjointFlow
      (E := E)
      (canonicalModularSeed (E := E) CIK)
      (RealTomitaCore.modularTimeOfWedgeBoost τwedge)
      (DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK)
      =
    DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK := by
  let M : ModularSuperchargeCompatibility (E := E) := { CIK := CIK }
  have hFixed :
      DrazinModularSingularityBridge.modularAdjointFlow
        (E := E)
        (canonicalModularSeed (E := E) M.CIK)
        (RealTomitaCore.modularTimeOfWedgeBoost τwedge)
        (ModularSuperchargeCompatibility.HD (E := E) M)
        =
      ModularSuperchargeCompatibility.HD (E := E) M :=
    ModularSuperchargeCompatibility.hD_fixed_under_wedgeAdjointFlow
      (E := E) (M := M) τwedge
  simpa [M, ModularSuperchargeCompatibility.HD] using hFixed

/--
Unconditional modular-lane transport of the internal canonical split.
-/
@[rep_depth transport]
theorem modularGenerator_eq_canonicalKinetic_plus_canonicalDefectCentral_canonicalSeed
    (CIK : CertifiedInverseKernel H₂) :
    modularTransportGenerator (E := E)
      (canonicalModularSeed (E := E) CIK)
      =
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalKineticPartK (CIK := CIK)
      +
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK CIK := by
  let M : ModularSuperchargeCompatibility (E := E) := { CIK := CIK }
  simpa [M] using
    (ModularSuperchargeCompatibility.modularGenerator_eq_canonicalKinetic_plus_canonicalDefectCentral
      (E := E) (M := M))

/--
Unconditional existence form on the canonical-seed modular lane:
`A_mod = H + Z` with the same Drazin-lane centrality witness for `Z`.
-/
@[rep_depth transport]
theorem exists_modularGenerator_split_with_drazin_lane_centrality_canonicalSeed
    (CIK : CertifiedInverseKernel H₂) :
    ∃ H Z : EndH,
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentralK CIK Z
        ∧ InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDefectSupportedK CIK Z
        ∧ InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.HasVanishingDefectBlockK CIK H
        ∧ modularTransportGenerator (E := E)
            (canonicalModularSeed (E := E) CIK) = H + Z := by
  let M : ModularSuperchargeCompatibility (E := E) := { CIK := CIK }
  simpa [M] using
    (ModularSuperchargeCompatibility.exists_modularGenerator_split_with_drazin_lane_centrality
      (E := E) (M := M))

/--
Canonical identity-kernel witness on the doubled carrier.

This gives a concrete certified inverse-kernel instance where all projector
mismatch/anomaly lanes vanish exactly.
-/
@[rep_depth operator]
noncomputable def idCertifiedInverseKernel : CertifiedInverseKernel H₂ where
  A := (1 : EndH)
  A_D := (1 : EndH)
  A_MP := (1 : EndH)
  drazinIndex := 0
  hDrazin := by
    refine ⟨?_, ?_, ?_⟩ <;> simp
  hMoorePenrose := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

/-- On the identity certified kernel, the projected odd supercharge vanishes. -/
@[rep_depth operator]
theorem supercharge_idCertifiedInverseKernel_eq_zero :
    DrazinSupercharge.CertifiedInverseKernel.supercharge
      (idCertifiedInverseKernel (E := E))
      = 0 := by
  let CIK : CertifiedInverseKernel H₂ := idCertifiedInverseKernel (E := E)
  have hDil : CIK.dilationGap = 0 := by
    simp [CIK, idCertifiedInverseKernel, CertifiedInverseKernel.dilationGap,
      CertifiedInverseKernel.toInverseKernel', InverseKernel.dilationGap,
      CertifiedInverseKernel.mpRangeProjector, CertifiedInverseKernel.metricProjector,
      InverseKernel.mpRangeProjector, InverseKernel.metricProjector,
      MoorePenrose.IsMoorePenroseInverse.rightProjector,
      MoorePenrose.IsMoorePenroseInverse.leftProjector]
  calc
    DrazinSupercharge.CertifiedInverseKernel.supercharge CIK
        = (2 : ℝ) • DrazinSupercharge.commutator CIK.spectralProjector CIK.dilationGap := by
            simpa using
              (DrazinSupercharge.CertifiedInverseKernel.supercharge_eq_two_smul_commutator_spectralProjector_dilationGap
                (CIK := CIK))
    _ = 0 := by
      simp [DrazinSupercharge.commutator, hDil]

/-- On the identity certified kernel, the projected even generator `Q_D²` vanishes. -/
@[rep_depth krein]
theorem superHamiltonianK_idCertifiedInverseKernel_eq_zero :
    DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK
      (idCertifiedInverseKernel (E := E))
      = 0 := by
  let CIK : CertifiedInverseKernel H₂ := idCertifiedInverseKernel (E := E)
  have hQ :
      DrazinSupercharge.CertifiedInverseKernel.supercharge CIK = 0 :=
    supercharge_idCertifiedInverseKernel_eq_zero (E := E)
  unfold DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK
  unfold DrazinSupercharge.CertifiedInverseKernel.superHamiltonian
  simpa [CIK, hQ]

/--
Counterexample theorem: the equation
`H_D = (2π) • modularHamiltonian` is not derivable uniformly for all certified
inverse kernels from the current lower-owner assumptions alone.
-/
@[rep_depth transport, capstone]
theorem not_forall_superHamiltonian_eq_two_pi_modularHamiltonian
    (hModNonzero : InfoGeometry.Dynamics.modularHamiltonian (E := E) ≠ 0) :
    ∃ CIK : CertifiedInverseKernel H₂,
      DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
        ≠ (2 * Real.pi) • InfoGeometry.Dynamics.modularHamiltonian (E := E) := by
  refine ⟨idCertifiedInverseKernel (E := E), ?_⟩
  intro hEq
  have hSmulZero :
      (2 * Real.pi) • InfoGeometry.Dynamics.modularHamiltonian (E := E) = 0 := by
    have hH0 :
        DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK
          (idCertifiedInverseKernel (E := E))
          = 0 :=
      superHamiltonianK_idCertifiedInverseKernel_eq_zero (E := E)
    simpa [hH0] using hEq.symm
  rcases smul_eq_zero.mp hSmulZero with hScale | hModZero
  · have hPi : (2 * Real.pi : ℝ) ≠ 0 := by
      have h2 : (2 : ℝ) ≠ 0 := by norm_num
      exact mul_ne_zero h2 Real.pi_ne_zero
    exact hPi hScale
  · exact hModNonzero hModZero

end Core

end InfoGeometry.Canonical.ModularSuperchargeClosure
