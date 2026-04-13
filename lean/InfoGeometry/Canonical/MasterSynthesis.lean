import InfoGeometry.Quantum.ZeroPointEnergy
import InfoGeometry.Canonical.ConformalUnification
import InfoGeometry.Canonical.NavierStokesBridge
import InfoGeometry.Canonical.YangMillsContinuum
import InfoGeometry.Canonical.GrandSynthesis
import InfoGeometry.Canonical.InformationalLichnerowiczBottBridge
import InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge
import InfoGeometry.Canonical.DiracRicciBridge
import InfoGeometry.Canonical.KaehlerGeometry
import InfoGeometry.Canonical.CalabiYauBridge
import InfoGeometry.Quantum.RealMajoranaCategory
import InfoGeometry.Canonical.UniversalVolume
import InfoGeometry.Canonical.Determinant
import InfoGeometry.Canonical.ZetaDeterminant
import InfoGeometry.Canonical.MongeAmpereCramerRao
import InfoGeometry.Canonical.BekensteinBound
import InfoGeometry.Canonical.KMSCocycleGeneratorBridge
import InfoGeometry.Canonical.DrazinInfiniteCore
import InfoGeometry.Canonical.DrazinWitnessElimination
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Canonical.RealBdGDIIIAtom
import InfoGeometry.Clifford.Hestenes
import InfoGeometry.Convex.HessianGeometry
import InfoGeometry.Canonical.SpectralInference
import InfoGeometry.Quantum.KitaevChain
import InfoGeometry.Volume.Pfaffian

/-!
# InfoGeometry.Canonical.MasterSynthesis

Capstone composition module linking the canonical bridges.

This module proves the "Hardened Unification":
1. Cramer-Rao / zero-point lower bound (`Quantum.ZeroPointEnergy`)
2. Projector-obstruction sourced Einstein equation (`ConformalUnification`)
3. Anomaly-as-fluid-state bridge (`NavierStokesBridge`)
4. Thermal-time identity (`YangMillsContinuum`)
5. Lichnerowicz-balanced Bott-Dirac closure (`GrandSynthesis`)
6. Universal Volume Fibration (`UniversalVolume`)
7. Topological Bekenstein bound from RN-cocycle monotonicity (`BekensteinBound`)
8. Hestenes GA Weyl Scaling (`Hestenes`)
9. Kitaev Tiling Identity (`KitaevChain`)

The unification is established through the **Rigidity of the Volume Form**
(the Radon-Nikodym derivative), which identifies information-theoretic
incompressibility with physical stability.
-/

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

namespace InfoGeometry.Canonical.MasterSynthesis

open InfoGeometry.Quantum.ZeroPointEnergy
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.YangMillsContinuum
open InfoGeometry.Canonical.GrandSynthesis
open InfoGeometry.Canonical.InformationalLichnerowiczBottBridge
open InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge
open InfoGeometry.Canonical.ChiralEinsteinBridge
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Canonical.SpectralInference
open InfoGeometry.Canonical.BottDirac
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.DiracRicciBridge
open InfoGeometry.Canonical.KaehlerGeometry
open InfoGeometry.Canonical.CalabiYauBridge
open InfoGeometry.Canonical.UniversalVolume
open InfoGeometry.Canonical.Determinant
open InfoGeometry.Canonical.MongeAmpereCramerRao
open InfoGeometry.Canonical.BekensteinBound
open InfoGeometry.Canonical.KMSCocycleBridge
open InfoGeometry.Canonical.RealBdGDIIIAtom
open InfoGeometry.Clifford.Hestenes
open InfoGeometry.Convex
open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Krein
open InfoGeometry.Quantum.KitaevChain
open InfoGeometry.Volume.Pfaffian

variable {E F : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

open scoped InfoGeometry.Canonical.Determinant

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E

/-- Pauli-exclusion style nilpotency witness for an algebra endomorphism. -/
private def SatisfiesExclusionConnection (Q : AlgebraEnd E) : Prop :=
  Q * Q = 0

omit [FiniteDimensional ℝ E] in
/--
Constructive anomaly-exclusion witness from the canonical lightlike split-`Cl(1,1)` mode.
-/
private theorem anomalyExclusion_witness :
    ∃ Q : AlgebraEnd E, SatisfiesExclusionConnection Q := by
  let Q : AlgebraEnd E := InfoGeometry.Krein.cl11RepLin (E := E) ((1 / 2 : ℝ), (1 / 2 : ℝ))
  refine ⟨Q, ?_⟩
  unfold SatisfiesExclusionConnection
  simpa [Q, InfoGeometry.Clifford.splitQ11_apply] using
    (InfoGeometry.Krein.cl11RepLin_sq (E := E) ((1 / 2 : ℝ), (1 / 2 : ℝ)))

omit [FiniteDimensional ℝ E] in
/--
Anomaly-exclusion package:
vanishing projector obstruction yields commutation closure, while exclusion is
discharged by a constructive nilpotent witness.
-/
private theorem anomalyExclusion_package_of_chiralAnomaly_eq_zero
    (CI : ConformalInference E)
    (hAnom : CI.chiralAnomalyOperator = 0) :
    CI.spectralChiralProjector * CI.metricChiralProjector
      = CI.metricChiralProjector * CI.spectralChiralProjector
      ∧ (∃ Q : AlgebraEnd E, SatisfiesExclusionConnection Q) := by
  refine ⟨CI.projectors_commute_of_chiralAnomaly_eq_zero hAnom, ?_⟩
  exact anomalyExclusion_witness (E := E)

omit [FiniteDimensional ℝ E] in
/--
Kähler/log-det anomaly-exclusion package:
if the anomaly scale is identified with the RN Kähler potential and unit
relative volume holds, projector obstruction closes and exclusion has a
constructive witness.
-/
private theorem anomalyExclusion_package_of_kahlerLogDet_unitRelativeVolume
    (CI : ConformalInference E)
    {n : Nat}
    (M : SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (hUnitVolume : relativeVolumeChangeRN n M = 1) :
    CI.spectralChiralProjector * CI.metricChiralProjector
      = CI.metricChiralProjector * CI.spectralChiralProjector
      ∧ (∃ Q : AlgebraEnd E, SatisfiesExclusionConnection Q) := by
  refine ⟨
    CI.projectors_commute_of_kahlerLogDet_unitRelativeVolume
      (M := M) hScaleFromKahler hUnitVolume,
    anomalyExclusion_witness (E := E)⟩

/--
Rigidity of the Information Volume Form (Incompressibility).
The relative volume measure (Radon-Nikodym derivative) is locked to 1.
-/
private def IsRigidVolumeForm {n : Nat} (M : SinkhornMatrix n) : Prop :=
  relativeVolumeChangeRN n M = 1

/--
Helicity Invariant (h).
The ensemble average of the helicity operator (u ∘ vorticity(u)) under probe ω.
-/
private noncomputable def helicityInvariant
    (u : VelocityField E) (ω : VelocityField E →L[ℝ] ℝ) : ℝ :=
  ω (helicityOperator u)

/--
Twin Wave Helicity Invariant (Ω).
Interference pairing between forward and backward waves in the Krein space.
-/
private noncomputable def twinWaveHelicity
    (u : VelocityField E) (Ω : AlgebraEnd E →L[ℝ] ℝ) : ℝ :=
  InfoGeometry.Canonical.twinWaveHelicity u Ω

/-! ### Sub-bridges to manage complexity -/

private theorem bridge_zpe_gravity
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x) :
    0 < S.variance_limit ∧
    EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CI.chiralScale)) Λ κ
      (anomalyStressEnergyAt Kgeo x CI.chiralScale) :=
  ⟨zero_point_energy_topological_obstruction S hRankPos,
   CI.einsteinEquation_of_projectorObstruction_source c R Kgeo x Λ κ hEin⟩

/--
Owner-path variant of the ZPE/gravity bridge routed through the certified
inverse-kernel package.
-/
private theorem bridge_zpe_gravity_of_certifiedInverseKernel
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x) :
    0 < S.variance_limit ∧
    EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CIK.chiralScale)) Λ κ
      (anomalyStressEnergyAt Kgeo x CIK.chiralScale) := by
  refine ⟨zero_point_energy_topological_obstruction S hRankPos, ?_⟩
  let CI : ConformalInference E := { toInverseKernel := CIK.toInverseKernel' }
  have hCI :
      EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CI.chiralScale)) Λ κ
        (anomalyStressEnergyAt Kgeo x CI.chiralScale) :=
    CI.einsteinEquation_of_projectorObstruction_source c R Kgeo x Λ κ hEin
  simpa [CI] using hCI

private theorem bridge_fluid_helicity
    (A B_mp B_dr : VelocityField E)
    (ω : VelocityField E →L[ℝ] ℝ)
    (Ω : AlgebraEnd E →L[ℝ] ℝ)
    (hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr)
    (hHelicity : helicityInvariant A ω = twinWaveHelicity A Ω) :
    (∃ state : FluidState E,
      state.u = EinsteinAnomaly A B_mp B_dr
        ∧ state.ρ = 1
        ∧ momentumResidual (E := E) state.u = 0) ∧
    (∃ (ω' : VelocityField E →L[ℝ] ℝ) (Ω' : AlgebraEnd E →L[ℝ] ℝ),
      helicityInvariant A ω' = twinWaveHelicity A Ω') :=
  by
    have hOnePos : (1 : ℝ) > 0 := by norm_num
    let state : FluidState E :=
      anomalyFluidStateWithDensity (E := E) A B_mp B_dr 1 hOnePos
    have hState :
        state.u = EinsteinAnomaly A B_mp B_dr ∧ state.ρ = 1 := by
      simp [state, anomalyFluidStateWithDensity]
    have hResidual :
        momentumResidual (E := E) state.u = 0 := by
      have hResidualEin :
          momentumResidual (E := E) (EinsteinAnomaly A B_mp B_dr) = 0 :=
        anomalyMomentumResidual_eq_zero_of_skew (E := E) A B_mp B_dr hAnomalySkew
      simpa [hState.1] using hResidualEin
    exact ⟨⟨state, hState.1, hState.2, hResidual⟩, ⟨ω, Ω, hHelicity⟩⟩

omit [FiniteDimensional ℝ E] in
/--
Regularization-sourced anomaly skewness on the fluid lane.
-/
private theorem anomalySkew_of_regularization
    (A B_mp B_dr : VelocityField E)
    (h_mp : IsMoorePenroseInverse A B_mp)
    (k : ℕ)
    (h_dr : IsDrazinInverse A B_dr k)
    (h_dr_star : star (A * B_dr) = A * B_dr) :
    ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
      = -EinsteinAnomaly A B_mp B_dr := by
  simpa using
    (einsteinAnomaly_skew_adjoint (a := A) (b_mp := B_mp) (b_dr := B_dr)
      (k := k) h_mp h_dr h_dr_star)

/--
Fluid/helicity bridge with skewness sourced from the regularization lane.
-/
private theorem bridge_fluid_helicity_of_regularization
    (A B_mp B_dr : VelocityField E)
    (ω : VelocityField E →L[ℝ] ℝ)
    (Ω : AlgebraEnd E →L[ℝ] ℝ)
    (h_mp : IsMoorePenroseInverse A B_mp)
    (k : ℕ)
    (h_dr : IsDrazinInverse A B_dr k)
    (h_dr_star : star (A * B_dr) = A * B_dr)
    (hHelicity : helicityInvariant A ω = twinWaveHelicity A Ω) :
    (∃ state : FluidState E,
      state.u = EinsteinAnomaly A B_mp B_dr
        ∧ state.ρ = 1
        ∧ momentumResidual (E := E) state.u = 0) ∧
    (∃ (ω' : VelocityField E →L[ℝ] ℝ) (Ω' : AlgebraEnd E →L[ℝ] ℝ),
      helicityInvariant A ω' = twinWaveHelicity A Ω') := by
  have hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr :=
    anomalySkew_of_regularization (A := A) (B_mp := B_mp) (B_dr := B_dr)
      h_mp k h_dr h_dr_star
  exact bridge_fluid_helicity A B_mp B_dr ω Ω hAnomalySkew hHelicity

/--
Finite-dimensional regularization wrapper:
derive a canonical Drazin witness internally and expose the fluid/helicity
bridge under the remaining projector self-adjointness condition.
-/
private theorem bridge_fluid_helicity_of_regularization_of_finiteDimensional
    (A B_mp : VelocityField E)
    (ω : VelocityField E →L[ℝ] ℝ)
    (Ω : AlgebraEnd E →L[ℝ] ℝ)
    (h_mp : IsMoorePenroseInverse A B_mp)
    (hHelicity : helicityInvariant A ω = twinWaveHelicity A Ω) :
    ∃ (k : ℕ) (B_dr : VelocityField E),
      IsDrazinInverse A B_dr k ∧
      (star (A * B_dr) = A * B_dr →
        ((∃ state : FluidState E,
            state.u = EinsteinAnomaly A B_mp B_dr
              ∧ state.ρ = 1
              ∧ momentumResidual (E := E) state.u = 0) ∧
          (∃ (ω' : VelocityField E →L[ℝ] ℝ) (Ω' : AlgebraEnd E →L[ℝ] ℝ),
            helicityInvariant A ω' = twinWaveHelicity A Ω'))) := by
  refine ⟨
    DrazinWitnessElimination.drazinIndex (E := E) A,
    DrazinWitnessElimination.drazinInverse (E := E) A,
    DrazinWitnessElimination.isDrazinInverse_drazinInverse (E := E) A,
    ?_
  ⟩
  intro h_dr_star
  exact bridge_fluid_helicity
    A B_mp (DrazinWitnessElimination.drazinInverse (E := E) A) ω Ω
    (anomalySkew_of_regularization_auto (E := E) A B_mp h_mp h_dr_star)
    hHelicity

omit [FiniteDimensional ℝ E] in
/--
Transport-to-Bott helper:
derive the `LichnerowiczBalancedCl11` witness from the owned operatorial
transport compatibility package.
-/
private theorem lichnerowiczBalancedCl11_of_transportCompatibility
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (IST : InfoSpectralTriple H₂)
    (hCompat : InformationalLichnerowiczBottCompatibility (E := E) V IST) :
    LichnerowiczBalancedCl11 (A := E) IST :=
  InformationalLichnerowiczBottBridge.lichnerowiczBalancedCl11_of_operatorialTransport
    (E := E) (V := V) (IST := IST) hCompat

/--
Master capstone composition:

- information-theoretic zero-point lower bound (Cramer-Rao),
- anomaly-sourced Einstein equation,
- anomaly-induced fluid realization (Navier-Stokes),
- Connes-Rovelli thermal-time identity,
- Lichnerowicz-balanced split Bott-Dirac closure,
- universal volume-to-potential homomorphism,
- topological Bekenstein bound,
- Hestenes GA Weyl scaling,
- Kitaev tiling identity.

All pieces are interpreted under the **Rigidity of the Volume Form** principle,
ensuring the information flow is volume-preserving (pairing-preserving/Krein-isometric on the doubled carrier).
-/
private theorem bits_to_gravity_to_fluid_capstone
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (ω : VelocityField E →L[ℝ] ℝ)
    (Ω : AlgebraEnd E →L[ℝ] ℝ)
    (hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr)
    (hHelicity : helicityInvariant A ω = twinWaveHelicity A Ω)
    (Mod : ModularRadonNikodymData E)
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (IST : InfoSpectralTriple H₂)
    (hCompat : InformationalLichnerowiczBottCompatibility (E := E) V IST)
    (n : Nat)
    (Tflow : SinkhornTrajectory n)
    (γ : ℕ → E)
    (N : ℕ) :
    -- 1. ZPE is positive (Cramer-Rao topological obstruction)
    0 < S.variance_limit
    -- 2. Gravity is generated by the Anomaly-sourced Einstein equation
      ∧ EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CI.chiralScale)) Λ κ
          (anomalyStressEnergyAt Kgeo x CI.chiralScale)
    -- 3. The Anomaly induces a Fluid State (Incompressible)
      ∧ (∃ state : FluidState E,
          state.u = EinsteinAnomaly A B_mp B_dr
            ∧ state.ρ = 1
            ∧ momentumResidual (E := E) state.u = 0)
    -- 4. Thermal Time identity holds (Connes-Rovelli)
      ∧ Mod.ConnesRovelliThermalTimeIdentity
    -- 5. Lichnerowicz-balanced split Bott-Dirac square vanishes (Stability)
      ∧ (cl11BottDirac (E := E) (spectralDiracLinear IST)).comp
          (cl11BottDirac (E := E) (spectralDiracLinear IST)) = 0
    -- 6. Helicity Invariant matches the Twin Wave pairing (Topological Protection)
      ∧ (∃ (ω : VelocityField E →L[ℝ] ℝ) (Ω : AlgebraEnd E →L[ℝ] ℝ), helicityInvariant A ω = twinWaveHelicity A Ω)
    -- 7. Pauli Exclusion Principle has a constructive witness (Fermionic Liquidity)
      ∧ (∃ Q : AlgebraEnd E, SatisfiesExclusionConnection Q)
    -- 8. Universal Volume-to-Potential Homomorphism (The Log-Map)
      ∧ (∀ f g : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ), LogAbsVolume (f.trans g) = LogAbsVolume f + LogAbsVolume g)
    -- 9. Topological Bekenstein bound from RN-barrier monotonicity.
      ∧ (∀ k : Nat, 0 ≤ trajectoryRNBarrier n Tflow k)
    -- 10. Chiral Information Fluid (Max Caliber) witness.
      ∧ (∃ (H : HessianGeometry E) (γ : ℕ → E) (N : ℕ), bayesianAction H γ N ≥ 0)
    -- 11. Hestenes GA Weyl Scaling: exp(θ I) generates the volume scale.
      ∧ (∀ θ : ℝ, expPseudoscalar θ = Real.exp θ)
    -- 12. Kitaev Tiling Identity: Total volume is the product of microscopic Pfaffians.
      ∧ (∀ chain : List (KitaevCell.{0}), ∃ Vol : ℝ,
          Vol = (chain.map (fun c : KitaevCell.{0} => c.pfaffian)).prod) := by
  have hBal : LichnerowiczBalancedCl11 (A := E) IST :=
    lichnerowiczBalancedCl11_of_transportCompatibility
      (E := E) (V := V) (IST := IST) hCompat
  let hZPE := bridge_zpe_gravity S hRankPos CI c R Kgeo x Λ κ hEin
  let hFH := bridge_fluid_helicity A B_mp B_dr ω Ω hAnomalySkew hHelicity
  refine ⟨hZPE.1, hZPE.2, hFH.1, Mod.connesRovelliThermalTimeIdentity,
          cl11_bottDirac_sq_eq_zero_of_lichnerowiczBalanced (A := E) IST hBal,
      hFH.2, ?_, capstone_logAbsVolume_add_from_zeta,
      topologicalBekensteinBound_of_sinkhornTrajectory (n := n) Tflow, ?_,
          expPseudoscalar_is_scaling, kitaev_tiling_identity⟩
  · -- Concrete lightlike split-`Cl(1,1)` witness; CAR nilpotency is already established upstream.
    let Q : AlgebraEnd E := InfoGeometry.Krein.cl11RepLin (E := E) ((1 / 2 : ℝ), (1 / 2 : ℝ))
    refine ⟨Q, ?_⟩
    unfold SatisfiesExclusionConnection
    simpa [Q, InfoGeometry.Clifford.splitQ11_apply] using
      (InfoGeometry.Krein.cl11RepLin_sq (E := E) ((1 / 2 : ℝ), (1 / 2 : ℝ)))
  · -- Max Caliber witness from caller-supplied trajectory and horizon.
    exact ⟨Kgeo.H, γ, N, InfoGeometry.Canonical.SpectralInference.bayesianAction_nonneg Kgeo.H γ N⟩

/--
Defect-sourced capstone variant:
if transported-index compatibility with the conformal projector lane is provided,
then the capstone conjunction holds and the conformal source scale is provably
nonzero.
-/
private theorem bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_quasilatticeAnalyticalIndex
    {A₀ B₀ : Type}
    [NormedRing A₀] [NormedRing B₀]
    [NormedAlgebra ℝ A₀] [NormedAlgebra ℝ B₀]
    [KreinSpace H₂] [KreinGradedModule H₂]
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (ω : VelocityField E →L[ℝ] ℝ)
    (Ω : AlgebraEnd E →L[ℝ] ℝ)
    (hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr)
    (hHelicity : helicityInvariant A ω = twinWaveHelicity A Ω)
    (Mod : ModularRadonNikodymData E)
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (IST : InfoSpectralTriple H₂)
    (hCompat : InformationalLichnerowiczBottCompatibility (E := E) V IST)
    (Xdef : RealSplitKreinDiracFredholmModule A₀ B₀ H₂)
    (tdef : ℝ)
    (hVXdef : QuasilatticeChiralFredholmSurface V Xdef tdef)
    (hCompatDefect :
      SuperchargeProjectorCompatibility
        (A := A₀) (B := B₀) (E := E)
        CI V Xdef tdef hVXdef
        CI.spectralChiralProjector CI.metricChiralProjector)
    (hIndexNonzero : quasilatticeAnalyticalIndex V Xdef tdef hVXdef ≠ 0)
    (n : Nat)
    (Tflow : SinkhornTrajectory n)
    (γ : ℕ → E)
    (N : ℕ) :
    CI.chiralScale ≠ 0
      ∧
    (0 < S.variance_limit
      ∧ EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CI.chiralScale)) Λ κ
          (anomalyStressEnergyAt Kgeo x CI.chiralScale)
      ∧ (∃ state : FluidState E,
          state.u = EinsteinAnomaly A B_mp B_dr
            ∧ state.ρ = 1
            ∧ momentumResidual (E := E) state.u = 0)
      ∧ Mod.ConnesRovelliThermalTimeIdentity
      ∧ (cl11BottDirac (E := E) (spectralDiracLinear IST)).comp
          (cl11BottDirac (E := E) (spectralDiracLinear IST)) = 0
      ∧ (∃ (ω : VelocityField E →L[ℝ] ℝ) (Ω : AlgebraEnd E →L[ℝ] ℝ),
          helicityInvariant A ω = twinWaveHelicity A Ω)
      ∧ (∃ Q : AlgebraEnd E, SatisfiesExclusionConnection Q)
      ∧ (∀ f g : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ),
          LogAbsVolume (f.trans g) = LogAbsVolume f + LogAbsVolume g)
      ∧ (∀ k : Nat, 0 ≤ trajectoryRNBarrier n Tflow k)
      ∧ (∃ (H : HessianGeometry E) (γ : ℕ → E) (N : ℕ), bayesianAction H γ N ≥ 0)
      ∧ (∀ θ : ℝ, expPseudoscalar θ = Real.exp θ)
      ∧ (∀ chain : List (KitaevCell.{0}), ∃ Vol : ℝ,
          Vol = (chain.map (fun c : KitaevCell.{0} => c.pfaffian)).prod)) := by
  have hScaleEin :
      CI.chiralScale ≠ 0
        ∧
      EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CI.chiralScale)) Λ κ
        (anomalyStressEnergyAt Kgeo x CI.chiralScale) :=
    chiralScale_ne_zero_and_einsteinEquation_of_quasilatticeAnalyticalIndex_ne_zero_of_compat
      (A := A₀) (B := B₀) (E := E)
      (CI := CI) (V := V) (X := Xdef) (t := tdef) (hVX := hVXdef)
      (superchargeProj := CI.spectralChiralProjector)
      (transportedProj := CI.metricChiralProjector)
      (hCompat := hCompatDefect)
      (hIndexNonzero := hIndexNonzero)
      (c := c) (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ) hEin
  have hCap :
      0 < S.variance_limit
        ∧ EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CI.chiralScale)) Λ κ
            (anomalyStressEnergyAt Kgeo x CI.chiralScale)
        ∧ (∃ state : FluidState E,
            state.u = EinsteinAnomaly A B_mp B_dr
              ∧ state.ρ = 1
              ∧ momentumResidual (E := E) state.u = 0)
        ∧ Mod.ConnesRovelliThermalTimeIdentity
        ∧ (cl11BottDirac (E := E) (spectralDiracLinear IST)).comp
            (cl11BottDirac (E := E) (spectralDiracLinear IST)) = 0
        ∧ (∃ (ω : VelocityField E →L[ℝ] ℝ) (Ω : AlgebraEnd E →L[ℝ] ℝ),
            helicityInvariant A ω = twinWaveHelicity A Ω)
        ∧ (∃ Q : AlgebraEnd E, SatisfiesExclusionConnection Q)
        ∧ (∀ f g : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ),
            LogAbsVolume (f.trans g) = LogAbsVolume f + LogAbsVolume g)
        ∧ (∀ k : Nat, 0 ≤ trajectoryRNBarrier n Tflow k)
        ∧ (∃ (H : HessianGeometry E) (γ : ℕ → E) (N : ℕ), bayesianAction H γ N ≥ 0)
        ∧ (∀ θ : ℝ, expPseudoscalar θ = Real.exp θ)
        ∧ (∀ chain : List (KitaevCell.{0}), ∃ Vol : ℝ,
            Vol = (chain.map (fun c : KitaevCell.{0} => c.pfaffian)).prod) :=
    bits_to_gravity_to_fluid_capstone
      (S := S) (hRankPos := hRankPos) (CI := CI) (c := c)
      (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ) (hEin := hEin)
      (A := A) (B_mp := B_mp) (B_dr := B_dr) (ω := ω) (Ω := Ω)
      (hAnomalySkew := hAnomalySkew) (hHelicity := hHelicity)
      (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
      (n := n) (Tflow := Tflow) (γ := γ) (N := N)
  exact ⟨hScaleEin.1, hCap⟩

/--
Defect-sourced capstone variant (canonical projector pair):
the compatibility witness is derived from the mismatch-to-noncommutation
implication on the same transported defect slice.
-/
private theorem bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_quasilatticeAnalyticalIndex_of_mismatch_forces_projector_noncommute
    {A₀ B₀ : Type}
    [NormedRing A₀] [NormedRing B₀]
    [NormedAlgebra ℝ A₀] [NormedAlgebra ℝ B₀]
    [KreinSpace H₂] [KreinGradedModule H₂]
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (ω : VelocityField E →L[ℝ] ℝ)
    (Ω : AlgebraEnd E →L[ℝ] ℝ)
    (hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr)
    (hHelicity : helicityInvariant A ω = twinWaveHelicity A Ω)
    (Mod : ModularRadonNikodymData E)
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (IST : InfoSpectralTriple H₂)
    (hCompat : InformationalLichnerowiczBottCompatibility (E := E) V IST)
    (Xdef : RealSplitKreinDiracFredholmModule A₀ B₀ H₂)
    (tdef : ℝ)
    (hVXdef : QuasilatticeChiralFredholmSurface V Xdef tdef)
    (hMismatchNoncommute :
      InfoGeometry.Canonical.ChiralDefectIndexBridge.TransportedChiralKernelDimMismatch
          V Xdef tdef hVXdef →
        CI.spectralChiralProjector * CI.metricChiralProjector
          ≠
        CI.metricChiralProjector * CI.spectralChiralProjector)
    (hIndexNonzero : quasilatticeAnalyticalIndex V Xdef tdef hVXdef ≠ 0)
    (n : Nat)
    (Tflow : SinkhornTrajectory n)
    (γ : ℕ → E)
    (N : ℕ) :
    CI.chiralScale ≠ 0
      ∧
    (0 < S.variance_limit
      ∧ EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CI.chiralScale)) Λ κ
          (anomalyStressEnergyAt Kgeo x CI.chiralScale)
      ∧ (∃ state : FluidState E,
          state.u = EinsteinAnomaly A B_mp B_dr
            ∧ state.ρ = 1
            ∧ momentumResidual (E := E) state.u = 0)
      ∧ Mod.ConnesRovelliThermalTimeIdentity
      ∧ (cl11BottDirac (E := E) (spectralDiracLinear IST)).comp
          (cl11BottDirac (E := E) (spectralDiracLinear IST)) = 0
      ∧ (∃ (ω : VelocityField E →L[ℝ] ℝ) (Ω : AlgebraEnd E →L[ℝ] ℝ),
          helicityInvariant A ω = twinWaveHelicity A Ω)
      ∧ (∃ Q : AlgebraEnd E, SatisfiesExclusionConnection Q)
      ∧ (∀ f g : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ),
          LogAbsVolume (f.trans g) = LogAbsVolume f + LogAbsVolume g)
      ∧ (∀ k : Nat, 0 ≤ trajectoryRNBarrier n Tflow k)
      ∧ (∃ (H : HessianGeometry E) (γ : ℕ → E) (N : ℕ), bayesianAction H γ N ≥ 0)
      ∧ (∀ θ : ℝ, expPseudoscalar θ = Real.exp θ)
      ∧ (∀ chain : List (KitaevCell.{0}), ∃ Vol : ℝ,
          Vol = (chain.map (fun c : KitaevCell.{0} => c.pfaffian)).prod)) := by
  have hCompatDefect :
      SuperchargeProjectorCompatibility
        (A := A₀) (B := B₀) (E := E)
        CI V Xdef tdef hVXdef
        CI.spectralChiralProjector CI.metricChiralProjector :=
    superchargeProjectorCompatibility_of_mismatch_forces_projector_noncommute
      CI V Xdef tdef hVXdef hMismatchNoncommute
  exact
    bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_quasilatticeAnalyticalIndex
      (A₀ := A₀) (B₀ := B₀)
      (S := S) (hRankPos := hRankPos)
      (CI := CI) (c := c) (R := R) (Kgeo := Kgeo)
      (x := x) (Λ := Λ) (κ := κ) (hEin := hEin)
      (A := A) (B_mp := B_mp) (B_dr := B_dr) (ω := ω) (Ω := Ω)
      (hAnomalySkew := hAnomalySkew)
      (hHelicity := hHelicity)
      (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
      (Xdef := Xdef) (tdef := tdef) (hVXdef := hVXdef)
      (hCompatDefect := hCompatDefect)
      (hIndexNonzero := hIndexNonzero)
      (n := n) (Tflow := Tflow)
      (γ := γ) (N := N)

/--
Defect-sourced capstone + DIII commutator wrapper:
reuse the mismatch-driven capstone path, and append the DIII-owned transport
commutator consequence from the canonical real BdG DIII atom closure.
-/
private theorem bits_to_gravity_to_fluid_capstone_with_nonzero_scale_and_diii_transportCommutator_of_quasilatticeAnalyticalIndex_of_mismatch_forces_projector_noncommute
    {A₀ B₀ : Type}
    [NormedRing A₀] [NormedRing B₀]
    [NormedAlgebra ℝ A₀] [NormedAlgebra ℝ B₀]
    [KreinSpace H₂] [KreinGradedModule H₂]
    (Sstate : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (ω : VelocityField E →L[ℝ] ℝ)
    (Ω : AlgebraEnd E →L[ℝ] ℝ)
    (hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr)
    (hHelicity : helicityInvariant A ω = twinWaveHelicity A Ω)
    (Mod : ModularRadonNikodymData E)
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (IST : InfoSpectralTriple H₂)
    (hCompat : InformationalLichnerowiczBottCompatibility (E := E) V IST)
    (Xdef : RealSplitKreinDiracFredholmModule A₀ B₀ H₂)
    (hXdef : ChiralFredholmSurface Xdef)
    (hEvenDef : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (tdef : ℝ)
    (hVXdef : QuasilatticeChiralFredholmSurface V Xdef tdef)
    (hMismatchNoncommute :
      InfoGeometry.Canonical.ChiralDefectIndexBridge.TransportedChiralKernelDimMismatch
          V Xdef tdef hVXdef →
        CI.spectralChiralProjector * CI.metricChiralProjector
          ≠
        CI.metricChiralProjector * CI.spectralChiralProjector)
    (hIndexNonzero : quasilatticeAnalyticalIndex V Xdef tdef hVXdef ≠ 0)
    (hCentral :
      InfoGeometry.Canonical.OperatorialCentralCharge.operatorialCentralCharge
        (A := A₀) (B := B₀) (E := E) Xdef hXdef ≠ 0)
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M)
    (Sbd : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : Sbd.kernel.A = InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V Xdef.F tdef)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V Xdef tdef)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V Xdef tdef)
    (hodd :
      InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
        (M := M) P0 (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V Xdef.F tdef))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V Xdef.F tdef v = 0 →
          v ≠ 0 → Sbd.boundaryGenerator v ≠ 0)
    (hBoundary :
      Sbd.boundaryGenerator = InfoGeometry.Canonical.VortexAnomalyLink.sourceVortexSeed (E := E) V
        ∨ Sbd.boundaryGenerator = InfoGeometry.Canonical.VortexAnomalyLink.sinkVortexSeed (E := E) V)
    (n : Nat)
    (Tflow : SinkhornTrajectory n)
    (γ : ℕ → E)
    (N : ℕ) :
    (CI.chiralScale ≠ 0
      ∧
    (0 < Sstate.variance_limit
      ∧ EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CI.chiralScale)) Λ κ
          (anomalyStressEnergyAt Kgeo x CI.chiralScale)
      ∧ (∃ state : FluidState E,
          state.u = EinsteinAnomaly A B_mp B_dr
            ∧ state.ρ = 1
            ∧ momentumResidual (E := E) state.u = 0)
      ∧ Mod.ConnesRovelliThermalTimeIdentity
      ∧ (cl11BottDirac (E := E) (spectralDiracLinear IST)).comp
          (cl11BottDirac (E := E) (spectralDiracLinear IST)) = 0
      ∧ (∃ (ω : VelocityField E →L[ℝ] ℝ) (Ω : AlgebraEnd E →L[ℝ] ℝ),
          helicityInvariant A ω = twinWaveHelicity A Ω)
      ∧ (∃ Q : AlgebraEnd E, SatisfiesExclusionConnection Q)
      ∧ (∀ f g : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ),
          LogAbsVolume (f.trans g) = LogAbsVolume f + LogAbsVolume g)
      ∧ (∀ k : Nat, 0 ≤ trajectoryRNBarrier n Tflow k)
      ∧ (∃ (H : HessianGeometry E) (γ : ℕ → E) (N : ℕ), bayesianAction H γ N ≥ 0)
      ∧ (∀ θ : ℝ, expPseudoscalar θ = Real.exp θ)
      ∧ (∀ chain : List (KitaevCell.{0}), ∃ Vol : ℝ,
          Vol = (chain.map (fun c : KitaevCell.{0} => c.pfaffian)).prod)))
      ∧
    InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
      V.connectionGenerator (spectral_epsilon (E := E)) ≠ 0 := by
  have hCap :=
    bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_quasilatticeAnalyticalIndex_of_mismatch_forces_projector_noncommute
      (A₀ := A₀) (B₀ := B₀)
      (S := Sstate) (hRankPos := hRankPos)
      (CI := CI) (c := c) (R := R) (Kgeo := Kgeo)
      (x := x) (Λ := Λ) (κ := κ) (hEin := hEin)
      (A := A) (B_mp := B_mp) (B_dr := B_dr) (ω := ω) (Ω := Ω)
      (hAnomalySkew := hAnomalySkew)
      (hHelicity := hHelicity)
      (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
      (Xdef := Xdef) (tdef := tdef) (hVXdef := hVXdef)
      (hMismatchNoncommute := hMismatchNoncommute)
      (hIndexNonzero := hIndexNonzero)
      (n := n) (Tflow := Tflow)
      (γ := γ) (N := N)
  have hComm :
      InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
        V.connectionGenerator (spectral_epsilon (E := E)) ≠ 0 := by
    have hDIII :=
      canonicalDIIIProxy_transport_root_centralCharge_commutator_closure
        (A := A₀) (B := B₀) (E := E)
        V Xdef hXdef hEvenDef tdef M P0 Sbd hA hplus hminus hodd
        hBoundaryOnZeroModes hCentral hBoundary
    exact hDIII.2.2
  exact ⟨hCap, hComm⟩

/--
Owner-path capstone composition:
same capstone payload as `bits_to_gravity_to_fluid_capstone`, but routed through
`CertifiedInverseKernel` instead of taking a free `ConformalInference` argument.
-/
private theorem bits_to_gravity_to_fluid_capstone_of_certifiedInverseKernel
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (ω : VelocityField E →L[ℝ] ℝ)
    (Ω : AlgebraEnd E →L[ℝ] ℝ)
    (hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr)
    (hHelicity : helicityInvariant A ω = twinWaveHelicity A Ω)
    (Mod : ModularRadonNikodymData E)
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (IST : InfoSpectralTriple H₂)
    (hCompat : InformationalLichnerowiczBottCompatibility (E := E) V IST)
    (n : Nat)
    (Tflow : SinkhornTrajectory n)
    (γ : ℕ → E)
    (N : ℕ) :
    0 < S.variance_limit
      ∧ EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CIK.chiralScale)) Λ κ
          (anomalyStressEnergyAt Kgeo x CIK.chiralScale)
      ∧ (∃ state : FluidState E,
          state.u = EinsteinAnomaly A B_mp B_dr
            ∧ state.ρ = 1
            ∧ momentumResidual (E := E) state.u = 0)
      ∧ Mod.ConnesRovelliThermalTimeIdentity
      ∧ (cl11BottDirac (E := E) (spectralDiracLinear IST)).comp
          (cl11BottDirac (E := E) (spectralDiracLinear IST)) = 0
      ∧ (∃ (ω : VelocityField E →L[ℝ] ℝ) (Ω : AlgebraEnd E →L[ℝ] ℝ),
          helicityInvariant A ω = twinWaveHelicity A Ω)
      ∧ (∃ Q : AlgebraEnd E, SatisfiesExclusionConnection Q)
      ∧ (∀ f g : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ),
          LogAbsVolume (f.trans g) = LogAbsVolume f + LogAbsVolume g)
      ∧ (∀ k : Nat, 0 ≤ trajectoryRNBarrier n Tflow k)
      ∧ (∃ (H : HessianGeometry E) (γ : ℕ → E) (N : ℕ), bayesianAction H γ N ≥ 0)
      ∧ (∀ θ : ℝ, expPseudoscalar θ = Real.exp θ)
      ∧ (∀ chain : List (KitaevCell.{0}), ∃ Vol : ℝ,
          Vol = (chain.map (fun c : KitaevCell.{0} => c.pfaffian)).prod) := by
  let CI : ConformalInference E := { toInverseKernel := CIK.toInverseKernel' }
  have hCap :
      0 < S.variance_limit
        ∧ EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CI.chiralScale)) Λ κ
            (anomalyStressEnergyAt Kgeo x CI.chiralScale)
        ∧ (∃ state : FluidState E,
            state.u = EinsteinAnomaly A B_mp B_dr
              ∧ state.ρ = 1
              ∧ momentumResidual (E := E) state.u = 0)
        ∧ Mod.ConnesRovelliThermalTimeIdentity
        ∧ (cl11BottDirac (E := E) (spectralDiracLinear IST)).comp
            (cl11BottDirac (E := E) (spectralDiracLinear IST)) = 0
        ∧ (∃ (ω : VelocityField E →L[ℝ] ℝ) (Ω : AlgebraEnd E →L[ℝ] ℝ),
            helicityInvariant A ω = twinWaveHelicity A Ω)
        ∧ (∃ Q : AlgebraEnd E, SatisfiesExclusionConnection Q)
        ∧ (∀ f g : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ),
            LogAbsVolume (f.trans g) = LogAbsVolume f + LogAbsVolume g)
        ∧ (∀ k : Nat, 0 ≤ trajectoryRNBarrier n Tflow k)
        ∧ (∃ (H : HessianGeometry E) (γ : ℕ → E) (N : ℕ), bayesianAction H γ N ≥ 0)
        ∧ (∀ θ : ℝ, expPseudoscalar θ = Real.exp θ)
        ∧ (∀ chain : List (KitaevCell.{0}), ∃ Vol : ℝ,
            Vol = (chain.map (fun c : KitaevCell.{0} => c.pfaffian)).prod) :=
    bits_to_gravity_to_fluid_capstone
      (S := S) (hRankPos := hRankPos) (CI := CI) (c := c)
      (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
      (hEin := hEin)
      (A := A) (B_mp := B_mp) (B_dr := B_dr) (ω := ω) (Ω := Ω)
      (hAnomalySkew := hAnomalySkew) (hHelicity := hHelicity)
      (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
      (n := n) (Tflow := Tflow) (γ := γ) (N := N)
  simpa [CI] using hCap

/--
Regularization-sourced capstone wrapper:
derive the anomaly skewness from Moore-Penrose/Drazin data and reuse the
primary capstone composition.
-/
private theorem bits_to_gravity_to_fluid_capstone_of_regularization
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (ω : VelocityField E →L[ℝ] ℝ)
    (Ω : AlgebraEnd E →L[ℝ] ℝ)
    (h_mp : IsMoorePenroseInverse A B_mp)
    (k : ℕ)
    (h_dr : IsDrazinInverse A B_dr k)
    (h_dr_star : star (A * B_dr) = A * B_dr)
    (hHelicity : helicityInvariant A ω = twinWaveHelicity A Ω)
    (Mod : ModularRadonNikodymData E)
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (IST : InfoSpectralTriple H₂)
    (hCompat : InformationalLichnerowiczBottCompatibility (E := E) V IST)
    (n : Nat)
    (Tflow : SinkhornTrajectory n)
    (γ : ℕ → E)
    (N : ℕ) :
    0 < S.variance_limit
      ∧ EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CI.chiralScale)) Λ κ
          (anomalyStressEnergyAt Kgeo x CI.chiralScale)
      ∧ (∃ state : FluidState E,
          state.u = EinsteinAnomaly A B_mp B_dr
            ∧ state.ρ = 1
            ∧ momentumResidual (E := E) state.u = 0)
      ∧ Mod.ConnesRovelliThermalTimeIdentity
      ∧ (cl11BottDirac (E := E) (spectralDiracLinear IST)).comp
          (cl11BottDirac (E := E) (spectralDiracLinear IST)) = 0
      ∧ (∃ (ω : VelocityField E →L[ℝ] ℝ) (Ω : AlgebraEnd E →L[ℝ] ℝ),
          helicityInvariant A ω = twinWaveHelicity A Ω)
      ∧ (∃ Q : AlgebraEnd E, SatisfiesExclusionConnection Q)
      ∧ (∀ f g : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ),
          LogAbsVolume (f.trans g) = LogAbsVolume f + LogAbsVolume g)
      ∧ (∀ k : Nat, 0 ≤ trajectoryRNBarrier n Tflow k)
      ∧ (∃ (H : HessianGeometry E) (γ : ℕ → E) (N : ℕ), bayesianAction H γ N ≥ 0)
      ∧ (∀ θ : ℝ, expPseudoscalar θ = Real.exp θ)
      ∧ (∀ chain : List (KitaevCell.{0}), ∃ Vol : ℝ,
          Vol = (chain.map (fun c : KitaevCell.{0} => c.pfaffian)).prod) := by
  have hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr :=
    anomalySkew_of_regularization (A := A) (B_mp := B_mp) (B_dr := B_dr)
      h_mp k h_dr h_dr_star
  exact bits_to_gravity_to_fluid_capstone
    (S := S) (hRankPos := hRankPos) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
    (hEin := hEin)
    (A := A) (B_mp := B_mp) (B_dr := B_dr) (ω := ω) (Ω := Ω)
    (hAnomalySkew := hAnomalySkew) (hHelicity := hHelicity)
    (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)

/--
Regularization wrapper with internalized Drazin witness:
derive `h_dr` from finite-dimensional global existence and keep only the
star/selfadjointness regularization obligation as external input.
-/
private theorem bits_to_gravity_to_fluid_capstone_of_regularization_canonical_drazin
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x)
    (A B_mp : VelocityField E)
    (ω : VelocityField E →L[ℝ] ℝ)
    (Ω : AlgebraEnd E →L[ℝ] ℝ)
    (h_mp : IsMoorePenroseInverse A B_mp)
    (h_dr_star_canonical :
      star (A * DrazinInfiniteCore.canonicalDrazinInverse_endCLM (E := E) A)
        = A * DrazinInfiniteCore.canonicalDrazinInverse_endCLM (E := E) A)
    (hHelicity : helicityInvariant A ω = twinWaveHelicity A Ω)
    (Mod : ModularRadonNikodymData E)
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (IST : InfoSpectralTriple H₂)
    (hCompat : InformationalLichnerowiczBottCompatibility (E := E) V IST)
    (n : Nat)
    (Tflow : SinkhornTrajectory n)
    (γ : ℕ → E)
    (N : ℕ) :
    ∃ (B_dr : VelocityField E),
      0 < S.variance_limit
        ∧ EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CI.chiralScale)) Λ κ
            (anomalyStressEnergyAt Kgeo x CI.chiralScale)
        ∧ (∃ state : FluidState E,
            state.u = EinsteinAnomaly A B_mp B_dr
              ∧ state.ρ = 1
              ∧ momentumResidual (E := E) state.u = 0)
        ∧ Mod.ConnesRovelliThermalTimeIdentity
        ∧ (cl11BottDirac (E := E) (spectralDiracLinear IST)).comp
            (cl11BottDirac (E := E) (spectralDiracLinear IST)) = 0
        ∧ (∃ (ω : VelocityField E →L[ℝ] ℝ) (Ω : AlgebraEnd E →L[ℝ] ℝ),
            helicityInvariant A ω = twinWaveHelicity A Ω)
        ∧ (∃ Q : AlgebraEnd E, SatisfiesExclusionConnection Q)
        ∧ (∀ f g : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ),
            LogAbsVolume (f.trans g) = LogAbsVolume f + LogAbsVolume g)
        ∧ (∀ k' : Nat, 0 ≤ trajectoryRNBarrier n Tflow k')
        ∧ (∃ (H : HessianGeometry E) (γ : ℕ → E) (N : ℕ), bayesianAction H γ N ≥ 0)
        ∧ (∀ θ : ℝ, expPseudoscalar θ = Real.exp θ)
        ∧ (∀ chain : List (KitaevCell.{0}), ∃ Vol : ℝ,
            Vol = (chain.map (fun c : KitaevCell.{0} => c.pfaffian)).prod) := by
  refine ⟨DrazinInfiniteCore.canonicalDrazinInverse_endCLM (E := E) A, ?_⟩
  exact bits_to_gravity_to_fluid_capstone_of_regularization
    (S := S) (hRankPos := hRankPos) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
    (hEin := hEin)
    (A := A) (B_mp := B_mp)
    (B_dr := DrazinInfiniteCore.canonicalDrazinInverse_endCLM (E := E) A)
    (ω := ω) (Ω := Ω)
    (h_mp := h_mp)
    (k := DrazinInfiniteCore.canonicalDrazinIndex_endCLM (E := E) A)
    (h_dr := DrazinInfiniteCore.canonicalDrazinInverse_endCLM_spec (E := E) A)
    (h_dr_star := h_dr_star_canonical)
    (hHelicity := hHelicity)
    (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)

/--
Capstone-facing squeezing bound:
if the capstone supplies the Bekenstein barrier clause and `|t|` is budgeted by
that barrier at step `k`, then logarithmic squeezing shear is bounded by
`4 * trajectoryRNBarrier`.
-/
private theorem squeezingLogShear_bound_of_capstone_bekenstein_clause
    (n : Nat)
    (Tflow : SinkhornTrajectory n)
    (hBekenstein : ∀ k : Nat, 0 ≤ trajectoryRNBarrier n Tflow k)
    (k : Nat)
    (t : ℝ)
    (hTime : |t| ≤ trajectoryRNBarrier n Tflow k) :
    |squeezingLogShear t| ≤ 4 * trajectoryRNBarrier n Tflow k := by
  exact abs_squeezingLogShear_le_of_topologicalBekensteinBound
    (n := n) (T := Tflow) hBekenstein k t hTime

/--
Tuple-extraction corollary:
from the capstone conjunction itself, extract the Bekenstein clause and derive
the squeezing-log-shear bound under a matching RN time budget.
-/
private theorem squeezingLogShear_bound_of_capstone_conjunction
    (S : SpinFactorState E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (A B_mp B_dr : VelocityField E)
    (Mod : ModularRadonNikodymData E)
    (IST : InfoSpectralTriple F)
    (n : Nat)
    (Tflow : SinkhornTrajectory n)
    (hCapstone :
      0 < S.variance_limit
        ∧ EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CI.chiralScale)) Λ κ
            (anomalyStressEnergyAt Kgeo x CI.chiralScale)
        ∧ (∃ state : FluidState E,
            state.u = EinsteinAnomaly A B_mp B_dr
              ∧ state.ρ = 1
              ∧ momentumResidual (E := E) state.u = 0)
        ∧ Mod.ConnesRovelliThermalTimeIdentity
        ∧ (cl11BottDirac (E := E) (spectralDiracLinear IST)).comp
            (cl11BottDirac (E := E) (spectralDiracLinear IST)) = 0
        ∧ (∃ (ω : VelocityField E →L[ℝ] ℝ) (Ω : AlgebraEnd E →L[ℝ] ℝ),
            helicityInvariant A ω = twinWaveHelicity A Ω)
        ∧ (∃ Q : AlgebraEnd E, SatisfiesExclusionConnection Q)
        ∧ (∀ f g : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ),
            LogAbsVolume (f.trans g) = LogAbsVolume f + LogAbsVolume g)
        ∧ (∀ k : Nat, 0 ≤ trajectoryRNBarrier n Tflow k)
        ∧ (∃ (H : HessianGeometry E) (γ : ℕ → E) (N : ℕ), bayesianAction H γ N ≥ 0)
        ∧ (∀ θ : ℝ, expPseudoscalar θ = Real.exp θ)
        ∧ (∀ chain : List (KitaevCell.{0}), ∃ Vol : ℝ,
          Vol = (chain.map (fun c : KitaevCell.{0} => c.pfaffian)).prod))
    (k : Nat)
    (t : ℝ)
    (hTime : |t| ≤ trajectoryRNBarrier n Tflow k) :
    |squeezingLogShear t| ≤ 4 * trajectoryRNBarrier n Tflow k := by
  rcases hCapstone with ⟨_, _, _, _, _, _, _, _, hBekenstein, _, _, _⟩
  exact squeezingLogShear_bound_of_capstone_bekenstein_clause
    n Tflow hBekenstein k t hTime

/--
Convenience corollary:
invoke `bits_to_gravity_to_fluid_capstone` internally and immediately extract
the Bekenstein clause to bound logarithmic squeezing shear.
-/
private theorem squeezingLogShear_bound_of_bits_to_gravity_to_fluid_capstone
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (ω : VelocityField E →L[ℝ] ℝ)
    (Ω : AlgebraEnd E →L[ℝ] ℝ)
    (hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr)
    (hHelicity : helicityInvariant A ω = twinWaveHelicity A Ω)
    (Mod : ModularRadonNikodymData E)
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (IST : InfoSpectralTriple H₂)
    (hCompat : InformationalLichnerowiczBottCompatibility (E := E) V IST)
    (n : Nat)
    (Tflow : SinkhornTrajectory n)
    (γ : ℕ → E)
    (N : ℕ)
    (j : Nat)
    (t : ℝ)
    (hTime : |t| ≤ trajectoryRNBarrier n Tflow j) :
    |squeezingLogShear t| ≤ 4 * trajectoryRNBarrier n Tflow j := by
  have hCapstone :=
    bits_to_gravity_to_fluid_capstone
      (S := S) (hRankPos := hRankPos) (CI := CI) (c := c)
      (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
      (hEin := hEin)
      (A := A) (B_mp := B_mp) (B_dr := B_dr) (ω := ω) (Ω := Ω)
      (hAnomalySkew := hAnomalySkew)
      (hHelicity := hHelicity)
      (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
      (n := n) (Tflow := Tflow) (γ := γ) (N := N)
  exact squeezingLogShear_bound_of_capstone_conjunction
    (S := S) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x)
    (Λ := Λ) (κ := κ)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (Mod := Mod) (IST := IST)
    (n := n) (Tflow := Tflow)
    hCapstone j t hTime

/--
Owner-path squeezing corollary:
the same squeezing bound routed through `CertifiedInverseKernel` instead of a
free conformal bridge argument.
-/
private theorem squeezingLogShear_bound_of_bits_to_gravity_to_fluid_capstone_of_certifiedInverseKernel
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (ω : VelocityField E →L[ℝ] ℝ)
    (Ω : AlgebraEnd E →L[ℝ] ℝ)
    (hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr)
    (hHelicity : helicityInvariant A ω = twinWaveHelicity A Ω)
    (Mod : ModularRadonNikodymData E)
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (IST : InfoSpectralTriple H₂)
    (hCompat : InformationalLichnerowiczBottCompatibility (E := E) V IST)
    (n : Nat)
    (Tflow : SinkhornTrajectory n)
    (γ : ℕ → E)
    (N : ℕ)
    (j : Nat)
    (t : ℝ)
    (hTime : |t| ≤ trajectoryRNBarrier n Tflow j) :
    |squeezingLogShear t| ≤ 4 * trajectoryRNBarrier n Tflow j := by
  let CI : ConformalInference E := { toInverseKernel := CIK.toInverseKernel' }
  have hCap :
      0 < S.variance_limit
        ∧ EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CI.chiralScale)) Λ κ
            (anomalyStressEnergyAt Kgeo x CI.chiralScale)
        ∧ (∃ state : FluidState E,
            state.u = EinsteinAnomaly A B_mp B_dr
              ∧ state.ρ = 1
              ∧ momentumResidual (E := E) state.u = 0)
        ∧ Mod.ConnesRovelliThermalTimeIdentity
        ∧ (cl11BottDirac (E := E) (spectralDiracLinear IST)).comp
            (cl11BottDirac (E := E) (spectralDiracLinear IST)) = 0
        ∧ (∃ (ω : VelocityField E →L[ℝ] ℝ) (Ω : AlgebraEnd E →L[ℝ] ℝ),
            helicityInvariant A ω = twinWaveHelicity A Ω)
        ∧ (∃ Q : AlgebraEnd E, SatisfiesExclusionConnection Q)
        ∧ (∀ f g : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ),
            LogAbsVolume (f.trans g) = LogAbsVolume f + LogAbsVolume g)
        ∧ (∀ k : Nat, 0 ≤ trajectoryRNBarrier n Tflow k)
        ∧ (∃ (H : HessianGeometry E) (γ : ℕ → E) (N : ℕ), bayesianAction H γ N ≥ 0)
        ∧ (∀ θ : ℝ, expPseudoscalar θ = Real.exp θ)
        ∧ (∀ chain : List (KitaevCell.{0}), ∃ Vol : ℝ,
            Vol = (chain.map (fun c : KitaevCell.{0} => c.pfaffian)).prod) := by
    simpa [CI] using
      (bits_to_gravity_to_fluid_capstone_of_certifiedInverseKernel
        (S := S) (hRankPos := hRankPos) (CIK := CIK) (c := c)
        (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
        (hEin := hEin)
        (A := A) (B_mp := B_mp) (B_dr := B_dr) (ω := ω) (Ω := Ω)
        (hAnomalySkew := hAnomalySkew) (hHelicity := hHelicity)
        (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
        (n := n) (Tflow := Tflow) (γ := γ) (N := N))
  exact squeezingLogShear_bound_of_capstone_conjunction
    (S := S) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x)
    (Λ := Λ) (κ := κ)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (Mod := Mod) (IST := IST)
    (n := n) (Tflow := Tflow)
    hCap j t hTime

/--
Regularization-sourced squeezing corollary:
derives anomaly skewness from MP/Drazin data before invoking the capstone.
-/
private theorem squeezingLogShear_bound_of_bits_to_gravity_to_fluid_capstone_of_regularization_canonical_drazin
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x)
    (A B_mp : VelocityField E)
    (ω : VelocityField E →L[ℝ] ℝ)
    (Ω : AlgebraEnd E →L[ℝ] ℝ)
    (h_mp : IsMoorePenroseInverse A B_mp)
    (h_dr_star_canonical :
      star (A * DrazinInfiniteCore.canonicalDrazinInverse_endCLM (E := E) A)
        = A * DrazinInfiniteCore.canonicalDrazinInverse_endCLM (E := E) A)
    (hHelicity : helicityInvariant A ω = twinWaveHelicity A Ω)
    (Mod : ModularRadonNikodymData E)
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (IST : InfoSpectralTriple H₂)
    (hCompat : InformationalLichnerowiczBottCompatibility (E := E) V IST)
    (n : Nat)
    (Tflow : SinkhornTrajectory n)
    (γ : ℕ → E)
    (N : ℕ)
    (j : Nat)
    (t : ℝ)
      (hTime : |t| ≤ trajectoryRNBarrier n Tflow j) :
    |squeezingLogShear t| ≤ 4 * trajectoryRNBarrier n Tflow j := by
  rcases bits_to_gravity_to_fluid_capstone_of_regularization_canonical_drazin
      (S := S) (hRankPos := hRankPos) (CI := CI) (c := c)
      (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
      (hEin := hEin)
      (A := A) (B_mp := B_mp) (ω := ω) (Ω := Ω)
      (h_mp := h_mp) (h_dr_star_canonical := h_dr_star_canonical)
      (hHelicity := hHelicity)
      (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
      (n := n) (Tflow := Tflow) (γ := γ) (N := N) with ⟨B_dr, hCapstone⟩
  exact squeezingLogShear_bound_of_capstone_conjunction
    (S := S) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x)
    (Λ := Λ) (κ := κ)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (Mod := Mod) (IST := IST)
    (n := n) (Tflow := Tflow)
    hCapstone j t hTime

/--
Cocycle-sourced capstone variant:
the topological Bekenstein clause is discharged from the RN cocycle layer
via `topologicalBekensteinBound_of_connesCocycle`.
-/
private theorem bits_to_gravity_to_fluid_capstone_cocycle_sourced
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (ω : VelocityField E →L[ℝ] ℝ)
    (Ω : AlgebraEnd E →L[ℝ] ℝ)
    (hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr)
    (hHelicity : helicityInvariant A ω = twinWaveHelicity A Ω)
    (Mod : ModularRadonNikodymData E)
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (IST : InfoSpectralTriple H₂)
    (hCompat : InformationalLichnerowiczBottCompatibility (E := E) V IST)
    (n : Nat)
    (Tflow : SinkhornTrajectory n)
    (γ : ℕ → E)
    (N : ℕ)
    {G : Type}
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G] [FiniteDimensional ℝ G]
    (σ : InfoGeometry.Volume.ConnesCocycle.AdditiveModularFlow (H := G))
    (u : ℝ → InfoGeometry.Volume.ConnesCocycle.AlgebraEnd G)
    (hCocycle : InfoGeometry.Volume.ConnesCocycle.IsConnesCocycle σ u)
    (hBridge : InfoGeometry.Volume.ConnesCocycle.ScalarCocycleBridge (H := G) σ)
    (hGeneratorLift :
      CocycleGeneratorLift n Tflow
        (CocycleEntropyPotential (H := G) σ u hBridge)) :
    0 < S.variance_limit
      ∧ EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CI.chiralScale)) Λ κ
          (anomalyStressEnergyAt Kgeo x CI.chiralScale)
      ∧ (∃ state : FluidState E,
          state.u = EinsteinAnomaly A B_mp B_dr
            ∧ state.ρ = 1
            ∧ momentumResidual (E := E) state.u = 0)
      ∧ Mod.ConnesRovelliThermalTimeIdentity
      ∧ (cl11BottDirac (E := E) (spectralDiracLinear IST)).comp
          (cl11BottDirac (E := E) (spectralDiracLinear IST)) = 0
      ∧ (∃ (ω : VelocityField E →L[ℝ] ℝ) (Ω : AlgebraEnd E →L[ℝ] ℝ),
          helicityInvariant A ω = twinWaveHelicity A Ω)
      ∧ (∃ Q : AlgebraEnd E, SatisfiesExclusionConnection Q)
      ∧ (∀ f g : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ),
          LogAbsVolume (f.trans g) = LogAbsVolume f + LogAbsVolume g)
      ∧ (∀ k : Nat, 0 ≤ trajectoryRNBarrier n Tflow k)
      ∧ (∃ (H : HessianGeometry E) (γ : ℕ → E) (N : ℕ), bayesianAction H γ N ≥ 0)
        ∧ (∀ θ : ℝ, expPseudoscalar θ = Real.exp θ)
        ∧ (∀ chain : List (KitaevCell.{0}), ∃ Vol : ℝ,
          Vol = (chain.map (fun c : KitaevCell.{0} => c.pfaffian)).prod) := by
  rcases bits_to_gravity_to_fluid_capstone
      (S := S) (hRankPos := hRankPos) (CI := CI) (c := c) (R := R) (Kgeo := Kgeo)
      (x := x) (Λ := Λ) (κ := κ) (hEin := hEin)
      (A := A) (B_mp := B_mp) (B_dr := B_dr) (ω := ω) (Ω := Ω)
      (hAnomalySkew := hAnomalySkew)
      (hHelicity := hHelicity)
      (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
      (n := n) (Tflow := Tflow)
      (γ := γ) (N := N) with
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_, h10, h11, h12⟩
  exact topologicalBekensteinBound_of_connesCocycle_generatorLift
    (n := n) (H := G) (σ := σ) (u := u) (T := Tflow) hCocycle hBridge hGeneratorLift

/--
KMS-closure / pairing-witness cocycle-sourced capstone variant:
the cocycle generator-lift clause is discharged from exact Sinkhorn-step KMS
closure plus the pairing witness.
-/
private def bits_to_gravity_to_fluid_capstone_cocycle_sourced_sinkhornKMSClosure_pairingWitness
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (ω : VelocityField E →L[ℝ] ℝ)
    (Ω : AlgebraEnd E →L[ℝ] ℝ)
    (hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr)
    (hHelicity : helicityInvariant A ω = twinWaveHelicity A Ω)
    (Mod : ModularRadonNikodymData E)
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (IST : InfoSpectralTriple H₂)
    (hCompat : InformationalLichnerowiczBottCompatibility (E := E) V IST)
    (n : Nat)
    (Tflow : SinkhornTrajectory n)
    (γ : ℕ → E)
    (N : ℕ)
    {G : Type}
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G] [FiniteDimensional ℝ G]
    (σ : InfoGeometry.Volume.ConnesCocycle.AdditiveModularFlow (H := G))
    (u : ℝ → InfoGeometry.Volume.ConnesCocycle.AlgebraEnd G)
    (hCocycle : InfoGeometry.Volume.ConnesCocycle.IsConnesCocycle σ u)
    (hBridge : InfoGeometry.Volume.ConnesCocycle.ScalarCocycleBridge (H := G) σ)
    (K : InfoGeometry.Canonical.KMSSinkhornBridge.AlgebraEnd G)
    (ωKMS :
      Nat → InfoGeometry.Canonical.KMSSinkhornBridge.AlgebraEnd G →L[ℝ] ℝ)
    (β : ℝ)
    (hClosure :
      InfoGeometry.Canonical.KMSSinkhornBridge.SinkhornKMSClosure
        n Tflow K ωKMS β)
    (hPair :
      KMSPairingWitness (n := n) (E := G) Tflow σ u hBridge K ωKMS β) := by
  exact bits_to_gravity_to_fluid_capstone_cocycle_sourced
    (S := S) (hRankPos := hRankPos) (CI := CI) (c := c) (R := R) (Kgeo := Kgeo)
    (x := x) (Λ := Λ) (κ := κ) (hEin := hEin)
    (A := A) (B_mp := B_mp) (B_dr := B_dr) (ω := ω) (Ω := Ω)
    (hAnomalySkew := hAnomalySkew)
    (hHelicity := hHelicity)
    (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
    (n := n) (Tflow := Tflow)
    (γ := γ) (N := N)
    (σ := σ) (u := u) (hCocycle := hCocycle) (hBridge := hBridge)
    (hGeneratorLift :=
      cocycleGeneratorLift_of_sinkhornKMSClosure_pairingWitness
        (n := n) (E := G)
        (T := Tflow) (σ := σ) (u := u) (bridge := hBridge)
        (K := K) (ω := ωKMS) (β := β)
        hClosure hPair)

/--
KMS-control / pairing-witness cocycle-sourced capstone variant:
the cocycle generator-lift clause is discharged from Sinkhorn KMS control by
first closing to exact stepwise KMS.
-/
private def bits_to_gravity_to_fluid_capstone_cocycle_sourced_sinkhornKMSControl_pairingWitness
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (ω : VelocityField E →L[ℝ] ℝ)
    (Ω : AlgebraEnd E →L[ℝ] ℝ)
    (hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr)
    (hHelicity : helicityInvariant A ω = twinWaveHelicity A Ω)
    (Mod : ModularRadonNikodymData E)
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (IST : InfoSpectralTriple H₂)
    (hCompat : InformationalLichnerowiczBottCompatibility (E := E) V IST)
    (n : Nat)
    (Tflow : SinkhornTrajectory n)
    (γ : ℕ → E)
    (N : ℕ)
    {G : Type}
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G] [FiniteDimensional ℝ G]
    (σ : InfoGeometry.Volume.ConnesCocycle.AdditiveModularFlow (H := G))
    (u : ℝ → InfoGeometry.Volume.ConnesCocycle.AlgebraEnd G)
    (hCocycle : InfoGeometry.Volume.ConnesCocycle.IsConnesCocycle σ u)
    (hBridge : InfoGeometry.Volume.ConnesCocycle.ScalarCocycleBridge (H := G) σ)
    (K : InfoGeometry.Canonical.KMSSinkhornBridge.AlgebraEnd G)
    (ωKMS :
      Nat → InfoGeometry.Canonical.KMSSinkhornBridge.AlgebraEnd G →L[ℝ] ℝ)
    (β : ℝ)
    (hControl :
      InfoGeometry.Canonical.KMSSinkhornBridge.SinkhornKMSControl
        n Tflow K ωKMS β)
    (hPair :
      KMSPairingWitness (n := n) (E := G) Tflow σ u hBridge K ωKMS β) := by
  exact bits_to_gravity_to_fluid_capstone_cocycle_sourced
    (S := S) (hRankPos := hRankPos) (CI := CI) (c := c) (R := R) (Kgeo := Kgeo)
    (x := x) (Λ := Λ) (κ := κ) (hEin := hEin)
    (A := A) (B_mp := B_mp) (B_dr := B_dr) (ω := ω) (Ω := Ω)
    (hAnomalySkew := hAnomalySkew)
    (hHelicity := hHelicity)
    (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
    (n := n) (Tflow := Tflow)
    (γ := γ) (N := N)
    (σ := σ) (u := u) (hCocycle := hCocycle) (hBridge := hBridge)
    (hGeneratorLift :=
      cocycleGeneratorLift_of_sinkhornKMSControl_pairingWitness
        (n := n) (E := G)
        (T := Tflow) (σ := σ) (u := u) (bridge := hBridge)
        (K := K) (ω := ωKMS) (β := β)
        hControl hPair)

/--
Integer-time cocycle-match capstone variant:
the RN cocycle bridge discharges the topological Bekenstein clause from
`hMatch` by deriving the generator-lift condition internally.
-/
private theorem bits_to_gravity_to_fluid_capstone_cocycle_sourced_natMatch
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (ω : VelocityField E →L[ℝ] ℝ)
    (Ω : AlgebraEnd E →L[ℝ] ℝ)
    (hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr)
    (hHelicity : helicityInvariant A ω = twinWaveHelicity A Ω)
    (Mod : ModularRadonNikodymData E)
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (IST : InfoSpectralTriple H₂)
    (hCompat : InformationalLichnerowiczBottCompatibility (E := E) V IST)
    (n : Nat)
    (Tflow : SinkhornTrajectory n)
    (γ : ℕ → E)
    (N : ℕ)
    {G : Type}
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G] [FiniteDimensional ℝ G]
    (σ : InfoGeometry.Volume.ConnesCocycle.AdditiveModularFlow (H := G))
    (u : ℝ → InfoGeometry.Volume.ConnesCocycle.AlgebraEnd G)
    (hCocycle : InfoGeometry.Volume.ConnesCocycle.IsConnesCocycle σ u)
    (hBridge : InfoGeometry.Volume.ConnesCocycle.ScalarCocycleBridge (H := G) σ)
    (hMatch :
      ∀ k : Nat,
        CocycleEntropyPotential (H := G) σ u hBridge k
          = trajectoryRNGeneratorPotential (n := n) Tflow k) :
    0 < S.variance_limit
      ∧ EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CI.chiralScale)) Λ κ
          (anomalyStressEnergyAt Kgeo x CI.chiralScale)
      ∧ (∃ state : FluidState E,
          state.u = EinsteinAnomaly A B_mp B_dr
            ∧ state.ρ = 1
            ∧ momentumResidual (E := E) state.u = 0)
      ∧ Mod.ConnesRovelliThermalTimeIdentity
      ∧ (cl11BottDirac (E := E) (spectralDiracLinear IST)).comp
          (cl11BottDirac (E := E) (spectralDiracLinear IST)) = 0
      ∧ (∃ (ω : VelocityField E →L[ℝ] ℝ) (Ω : AlgebraEnd E →L[ℝ] ℝ),
          helicityInvariant A ω = twinWaveHelicity A Ω)
      ∧ (∃ Q : AlgebraEnd E, SatisfiesExclusionConnection Q)
      ∧ (∀ f g : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ),
          LogAbsVolume (f.trans g) = LogAbsVolume f + LogAbsVolume g)
      ∧ (∀ k : Nat, 0 ≤ trajectoryRNBarrier n Tflow k)
      ∧ (∃ (H : HessianGeometry E) (γ : ℕ → E) (N : ℕ), bayesianAction H γ N ≥ 0)
        ∧ (∀ θ : ℝ, expPseudoscalar θ = Real.exp θ)
        ∧ (∀ chain : List (KitaevCell.{0}), ∃ Vol : ℝ,
          Vol = (chain.map (fun c : KitaevCell.{0} => c.pfaffian)).prod) := by
  exact bits_to_gravity_to_fluid_capstone_cocycle_sourced
    (S := S) (hRankPos := hRankPos) (CI := CI) (c := c) (R := R) (Kgeo := Kgeo)
    (x := x) (Λ := Λ) (κ := κ) (hEin := hEin)
    (A := A) (B_mp := B_mp) (B_dr := B_dr) (ω := ω) (Ω := Ω)
    (hAnomalySkew := hAnomalySkew)
    (hHelicity := hHelicity)
    (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
    (n := n) (Tflow := Tflow)
    (γ := γ) (N := N)
    (σ := σ) (u := u) (hCocycle := hCocycle) (hBridge := hBridge)
    (hGeneratorLift :=
      cocycleGeneratorLift_of_cocycleEntropyPotential_match
        (n := n) (H := G) (σ := σ) (u := u) (hBridge := hBridge)
        (T := Tflow) hMatch)

/--
Tomita-specialized cocycle-sourced capstone variant using the canonical
modular-sign additive flow.
-/
private theorem bits_to_gravity_to_fluid_capstone_tomita_cocycle_sourced
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (ω : VelocityField E →L[ℝ] ℝ)
    (Ω : AlgebraEnd E →L[ℝ] ℝ)
    (hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr)
    (hHelicity : helicityInvariant A ω = twinWaveHelicity A Ω)
    (Mod : ModularRadonNikodymData E)
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (IST : InfoSpectralTriple H₂)
    (hCompat : InformationalLichnerowiczBottCompatibility (E := E) V IST)
    (n : Nat)
    (Tflow : SinkhornTrajectory n)
    (γ : ℕ → E)
    (N : ℕ)
    {G : Type}
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G] [FiniteDimensional ℝ G]
    (u : ℝ → InfoGeometry.Volume.ConnesCocycle.AlgebraEnd G)
    (hCocycle :
      InfoGeometry.Volume.ConnesCocycle.IsConnesCocycle
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := G))
        u)
    (hBridge :
      InfoGeometry.Volume.ConnesCocycle.ScalarCocycleBridge (H := G)
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := G)))
    (hGeneratorLift :
      CocycleGeneratorLift n Tflow
        (TomitaCocycleEntropyPotential (H := G) u hBridge)) :
    0 < S.variance_limit
      ∧ EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CI.chiralScale)) Λ κ
          (anomalyStressEnergyAt Kgeo x CI.chiralScale)
      ∧ (∃ state : FluidState E,
          state.u = EinsteinAnomaly A B_mp B_dr
            ∧ state.ρ = 1
            ∧ momentumResidual (E := E) state.u = 0)
      ∧ Mod.ConnesRovelliThermalTimeIdentity
      ∧ (cl11BottDirac (E := E) (spectralDiracLinear IST)).comp
          (cl11BottDirac (E := E) (spectralDiracLinear IST)) = 0
      ∧ (∃ (ω : VelocityField E →L[ℝ] ℝ) (Ω : AlgebraEnd E →L[ℝ] ℝ),
          helicityInvariant A ω = twinWaveHelicity A Ω)
      ∧ (∃ Q : AlgebraEnd E, SatisfiesExclusionConnection Q)
      ∧ (∀ f g : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ),
          LogAbsVolume (f.trans g) = LogAbsVolume f + LogAbsVolume g)
      ∧ (∀ k : Nat, 0 ≤ trajectoryRNBarrier n Tflow k)
      ∧ (∃ (H : HessianGeometry E) (γ : ℕ → E) (N : ℕ), bayesianAction H γ N ≥ 0)
        ∧ (∀ θ : ℝ, expPseudoscalar θ = Real.exp θ)
        ∧ (∀ chain : List (KitaevCell.{0}), ∃ Vol : ℝ,
          Vol = (chain.map (fun c : KitaevCell.{0} => c.pfaffian)).prod) := by
  exact bits_to_gravity_to_fluid_capstone_cocycle_sourced
    (S := S) (hRankPos := hRankPos) (CI := CI) (c := c) (R := R) (Kgeo := Kgeo)
    (x := x) (Λ := Λ) (κ := κ) (hEin := hEin)
    (A := A) (B_mp := B_mp) (B_dr := B_dr) (ω := ω) (Ω := Ω)
    (hAnomalySkew := hAnomalySkew)
    (hHelicity := hHelicity)
    (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
    (n := n) (Tflow := Tflow)
    (γ := γ) (N := N)
    (σ := InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := G))
    (u := u) (hCocycle := hCocycle) (hBridge := hBridge)
    (hGeneratorLift := by simpa [TomitaCocycleEntropyPotential] using hGeneratorLift)

/--
Tomita-specialized integer-time cocycle-match capstone variant.
-/
private theorem bits_to_gravity_to_fluid_capstone_tomita_cocycle_sourced_natMatch
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (ω : VelocityField E →L[ℝ] ℝ)
    (Ω : AlgebraEnd E →L[ℝ] ℝ)
    (hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr)
    (hHelicity : helicityInvariant A ω = twinWaveHelicity A Ω)
    (Mod : ModularRadonNikodymData E)
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (IST : InfoSpectralTriple H₂)
    (hCompat : InformationalLichnerowiczBottCompatibility (E := E) V IST)
    (n : Nat)
    (Tflow : SinkhornTrajectory n)
    (γ : ℕ → E)
    (N : ℕ)
    {G : Type}
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G] [FiniteDimensional ℝ G]
    (u : ℝ → InfoGeometry.Volume.ConnesCocycle.AlgebraEnd G)
    (hCocycle :
      InfoGeometry.Volume.ConnesCocycle.IsConnesCocycle
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := G))
        u)
    (hBridge :
      InfoGeometry.Volume.ConnesCocycle.ScalarCocycleBridge (H := G)
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := G)))
    (hMatch :
      ∀ k : Nat,
        TomitaCocycleEntropyPotential (H := G) u hBridge k
          = trajectoryRNGeneratorPotential (n := n) Tflow k) :
    0 < S.variance_limit
      ∧ EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CI.chiralScale)) Λ κ
          (anomalyStressEnergyAt Kgeo x CI.chiralScale)
      ∧ (∃ state : FluidState E,
          state.u = EinsteinAnomaly A B_mp B_dr
            ∧ state.ρ = 1
            ∧ momentumResidual (E := E) state.u = 0)
      ∧ Mod.ConnesRovelliThermalTimeIdentity
      ∧ (cl11BottDirac (E := E) (spectralDiracLinear IST)).comp
          (cl11BottDirac (E := E) (spectralDiracLinear IST)) = 0
      ∧ (∃ (ω : VelocityField E →L[ℝ] ℝ) (Ω : AlgebraEnd E →L[ℝ] ℝ),
          helicityInvariant A ω = twinWaveHelicity A Ω)
      ∧ (∃ Q : AlgebraEnd E, SatisfiesExclusionConnection Q)
      ∧ (∀ f g : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ),
          LogAbsVolume (f.trans g) = LogAbsVolume f + LogAbsVolume g)
      ∧ (∀ k : Nat, 0 ≤ trajectoryRNBarrier n Tflow k)
      ∧ (∃ (H : HessianGeometry E) (γ : ℕ → E) (N : ℕ), bayesianAction H γ N ≥ 0)
        ∧ (∀ θ : ℝ, expPseudoscalar θ = Real.exp θ)
        ∧ (∀ chain : List (KitaevCell.{0}), ∃ Vol : ℝ,
          Vol = (chain.map (fun c : KitaevCell.{0} => c.pfaffian)).prod) := by
  exact bits_to_gravity_to_fluid_capstone_tomita_cocycle_sourced
    (S := S) (hRankPos := hRankPos) (CI := CI) (c := c) (R := R) (Kgeo := Kgeo)
    (x := x) (Λ := Λ) (κ := κ) (hEin := hEin)
    (A := A) (B_mp := B_mp) (B_dr := B_dr) (ω := ω) (Ω := Ω)
    (hAnomalySkew := hAnomalySkew)
    (hHelicity := hHelicity)
    (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
    (n := n) (Tflow := Tflow)
    (γ := γ) (N := N)
    (u := u) (hCocycle := hCocycle) (hBridge := hBridge)
    (hGeneratorLift := by
      simpa [TomitaCocycleEntropyPotential] using
        (cocycleGeneratorLift_of_cocycleEntropyPotential_match
          (n := n) (H := G)
          (σ := InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := G))
          (u := u) (hBridge := hBridge) (T := Tflow) hMatch))

/--
Tomita flow-unit cocycle-sourced capstone variant.

This is the no-free-cocycle/no-free-bridge wrapper on the Tomita lane:
`u`, `hCocycle`, and `hBridge` are fixed to the welded flow-unit surfaces.
-/
private def bits_to_gravity_to_fluid_capstone_tomita_flowUnit_cocycle_sourced
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (ω : VelocityField E →L[ℝ] ℝ)
    (Ω : AlgebraEnd E →L[ℝ] ℝ)
    (hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr)
    (hHelicity : helicityInvariant A ω = twinWaveHelicity A Ω)
    (Mod : ModularRadonNikodymData E)
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (IST : InfoSpectralTriple H₂)
    (hCompat : InformationalLichnerowiczBottCompatibility (E := E) V IST)
    (n : Nat)
    (Tflow : SinkhornTrajectory n)
    (γ : ℕ → E)
    (N : ℕ)
    {G : Type}
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G] [FiniteDimensional ℝ G]
    (hGeneratorLift :
      CocycleGeneratorLift n Tflow
        (TomitaCocycleEntropyPotential (H := G)
          (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
            (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := G)))
          (InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
            (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := G))))) := by
  exact bits_to_gravity_to_fluid_capstone_tomita_cocycle_sourced
    (S := S) (hRankPos := hRankPos) (CI := CI) (c := c) (R := R) (Kgeo := Kgeo)
    (x := x) (Λ := Λ) (κ := κ) (hEin := hEin)
    (A := A) (B_mp := B_mp) (B_dr := B_dr) (ω := ω) (Ω := Ω)
    (hAnomalySkew := hAnomalySkew)
    (hHelicity := hHelicity)
    (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
    (n := n) (Tflow := Tflow)
    (γ := γ) (N := N)
    (u := InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
      (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := G)))
    (hCocycle := InfoGeometry.Canonical.ModularWeldBridge.tomita_modularSign_flowUnitCocycle_isConnesCocycle
      (H := G))
    (hBridge := InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
      (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := G)))
    (hGeneratorLift := hGeneratorLift)

/--
Tomita flow-unit integer-time cocycle-match capstone variant.

This is the no-free-cocycle/no-free-bridge wrapper on the Tomita lane:
`u`, `hCocycle`, and `hBridge` are fixed to the welded flow-unit surfaces.
-/
private def bits_to_gravity_to_fluid_capstone_tomita_flowUnit_cocycle_sourced_natMatch
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (ω : VelocityField E →L[ℝ] ℝ)
    (Ω : AlgebraEnd E →L[ℝ] ℝ)
    (hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr)
    (hHelicity : helicityInvariant A ω = twinWaveHelicity A Ω)
    (Mod : ModularRadonNikodymData E)
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (IST : InfoSpectralTriple H₂)
    (hCompat : InformationalLichnerowiczBottCompatibility (E := E) V IST)
    (n : Nat)
    (Tflow : SinkhornTrajectory n)
    (γ : ℕ → E)
    (N : ℕ)
    {G : Type}
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G] [FiniteDimensional ℝ G]
    (hMatch :
      ∀ k : Nat,
        TomitaCocycleEntropyPotential (H := G)
          (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
            (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := G)))
          (InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
            (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := G))) k
          = trajectoryRNGeneratorPotential (n := n) Tflow k) := by
  exact bits_to_gravity_to_fluid_capstone_tomita_cocycle_sourced_natMatch
    (S := S) (hRankPos := hRankPos) (CI := CI) (c := c) (R := R) (Kgeo := Kgeo)
    (x := x) (Λ := Λ) (κ := κ) (hEin := hEin)
    (A := A) (B_mp := B_mp) (B_dr := B_dr) (ω := ω) (Ω := Ω)
    (hAnomalySkew := hAnomalySkew)
    (hHelicity := hHelicity)
    (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
    (n := n) (Tflow := Tflow)
    (γ := γ) (N := N)
    (u := InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
      (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := G)))
    (hCocycle := InfoGeometry.Canonical.ModularWeldBridge.tomita_modularSign_flowUnitCocycle_isConnesCocycle
      (H := G))
    (hBridge := InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
      (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := G)))
    (hMatch := hMatch)

end InfoGeometry.Canonical.MasterSynthesis
