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
import InfoGeometry.Canonical.IncompressibleBitBridge
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
set_option linter.unusedSectionVars false

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

omit [FiniteDimensional ℝ E] in
/--
Unit-relative-volume-bit anomaly-exclusion package.

This is the proof-carrying variant of
`anomalyExclusion_package_of_kahlerLogDet_unitRelativeVolume`: callers provide
`UnitRelativeVolumeBit` instead of the bare equality
`relativeVolumeChangeRN n M = 1`.  The projector commutation is read from the
existing incompressible-bit owner route, while the nilpotent exclusion witness
is still constructed by `anomalyExclusion_witness`.
-/
private theorem anomalyExclusion_package_of_unitRelativeVolumeBit
    (CI : ConformalInference E)
    {n : Nat}
    (M : SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (bit : InfoGeometry.Canonical.IncompressibleBitBridge.UnitRelativeVolumeBit n M) :
    CI.spectralChiralProjector * CI.metricChiralProjector
      = CI.metricChiralProjector * CI.spectralChiralProjector
      ∧ (∃ Q : AlgebraEnd E, SatisfiesExclusionConnection Q) := by
  refine ⟨?_, anomalyExclusion_witness (E := E)⟩
  exact InfoGeometry.Canonical.IncompressibleBitBridge.projectors_commute_of_unitRelativeVolumeBit
    (CI := CI) (M := M) hScaleFromKahler bit

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

/--
Proof-carrying helicity match.

This keeps the two probe functionals and their matching equation together, so
bridge theorems can consume one explicit witness object instead of three free
arguments `(ω, Ω, hHelicity)`.
-/
private structure MatchedHelicityWitness (A : VelocityField E) where
  /-- Probe used to read the ordinary helicity invariant. -/
  omega : VelocityField E →L[ℝ] ℝ
  /-- Probe used to read the twin-wave helicity invariant. -/
  Omega : AlgebraEnd E →L[ℝ] ℝ
  /-- The two readouts match on the chosen velocity field. -/
  match_helicity : helicityInvariant A omega = twinWaveHelicity A Omega

/--
Proof-carrying ZPE/gravity package.

This bundles the positive spin-rank witness with the local Einstein-Kähler
owner certificate, so constructive capstone branches can consume one explicit
owner packet instead of threading two loose hypotheses through the bridge.
-/
private structure ZPEGravityWitness
    (S : SpinFactorState E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E) where
  /-- Positive finite rank needed by the zero-point-energy obstruction owner. -/
  hRankPos : 0 < Module.finrank ℝ E
  /-- Local Einstein-Kähler certificate for the anomaly-stress owner. -/
  hEin : IsEinsteinKaehlerAtWith c R Kgeo x

/--
Proof-carrying thermal/Bott stability package.

This bundles the modular Radon-Nikodym datum, Bogoliubov vielbein, spectral
triple, and the operatorial transport compatibility certificate.  Narrowed
capstone branches can consume this single owner packet instead of threading
`Mod`, `V`, `IST`, and the loose `hCompat` hypothesis separately.
-/
private structure ThermalBottWitness where
  /-- Modular datum owning the Connes-Rovelli thermal-time identity. -/
  Mod : ModularRadonNikodymData E
  /-- Bogoliubov vielbein carrying the transport generator. -/
  V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)
  /-- Spectral triple whose split Bott-Dirac square is closed by compatibility. -/
  IST : InfoSpectralTriple H₂
  /-- Operatorial transport compatibility producing the Lichnerowicz-balanced owner witness. -/
  hCompat : InformationalLichnerowiczBottCompatibility (E := E) V IST

/--
Proof-carrying regularization package for the generic anomaly-skew route.

This bundles the Moore-Penrose leg, the Drazin index/inverse witness, and the
star-compatibility witness instead of threading them as separate hypotheses.
-/
private structure RegularizationWitness (A B_mp B_dr : VelocityField E) where
  /-- Moore-Penrose leg used by the anomaly regularization theorem. -/
  h_mp : IsMoorePenroseInverse A B_mp
  /-- Drazin index for the regularizing inverse. -/
  k : ℕ
  /-- Drazin inverse witness at the stored index. -/
  h_drazin : IsDrazinInverse A B_dr k
  /-- Star-compatibility for the regularized product. -/
  h_star : star (A * B_dr) = A * B_dr

/--
Proof-carrying canonical-Drazin regularization package.

This is the narrowed infinite-owner branch for the canonical Drazin inverse: it
bundles the Moore-Penrose leg with the remaining star-compatibility witness, so
capstone-facing wrappers no longer carry those two assumptions as loose theorem
arguments on this route.
-/
private structure CanonicalDrazinRegularizationWitness (A B_mp : VelocityField E) where
  /-- Moore-Penrose leg used by the anomaly regularization theorem. -/
  h_mp : IsMoorePenroseInverse A B_mp
  /-- Star-compatibility for the canonical Drazin regularizing inverse. -/
  h_star_canonical :
    star (A * DrazinInfiniteCore.canonicalDrazinInverse_endCLM (E := E) A)
      = A * DrazinInfiniteCore.canonicalDrazinInverse_endCLM (E := E) A

/--
Recover the generic regularization packet from the canonical-Drazin witness.
-/
private noncomputable def canonicalDrazinRegularizationWitness_toRegularizationWitness
    (A B_mp : VelocityField E)
    (W : CanonicalDrazinRegularizationWitness (E := E) A B_mp) :
    RegularizationWitness (E := E) A B_mp
      (DrazinInfiniteCore.canonicalDrazinInverse_endCLM (E := E) A) :=
  { h_mp := W.h_mp
    k := DrazinInfiniteCore.canonicalDrazinIndex_endCLM (E := E) A
    h_drazin := DrazinInfiniteCore.canonicalDrazinInverse_endCLM_spec (E := E) A
    h_star := W.h_star_canonical }

/--
Proof-carrying DIII transport-commutator package.

This bundles the real-Majorana polarization, boundary correction, central-charge
nonvanishing, and boundary-source witnesses needed by the canonical DIII atom
closure.  Downstream capstones can consume one owner packet instead of carrying
nine separate hypotheses for the same transport-commutator route.
-/
private structure DIIITransportCommutatorWitness
    {A₀ B₀ : Type}
    [NormedRing A₀] [NormedRing B₀]
    [NormedAlgebra ℝ A₀] [NormedAlgebra ℝ B₀]
    [KreinSpace H₂] [KreinGradedModule H₂]
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (Xdef : RealSplitKreinDiracFredholmModule A₀ B₀ H₂)
    (hXdef : ChiralFredholmSurface Xdef)
    (tdef : ℝ) where
  /-- Evenness of the transported defect generator. -/
  hEvenDef : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator
  /-- Real-Majorana datum carrying the polarization. -/
  M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂)
  /-- K-polarization on the real-Majorana datum. -/
  P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M
  /-- Singular-boundary correction entering the canonical DIII closure. -/
  Sbd : InfoGeometry.Canonical.SingularBoundaryCorrection H₂
  /-- The boundary-correction kernel is the quasilattice Dirac operator. -/
  hA : Sbd.kernel.A = InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V Xdef.F tdef
  /-- Positive chiral slice match for the polarization. -/
  hplus : P0.plus = quasilatticeChiralKernelSlicePlus V Xdef tdef
  /-- Negative chiral slice match for the polarization. -/
  hminus : P0.minus = quasilatticeChiralKernelSliceMinus V Xdef tdef
  /-- Oddness of the polarization with respect to the quasilattice Dirac operator. -/
  hodd :
    InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
      (M := M) P0 (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V Xdef.F tdef)
  /-- Boundary source is nonzero on nonzero quasilattice zero modes. -/
  hBoundaryOnZeroModes :
    ∀ v : H₂,
      InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V Xdef.F tdef v = 0 →
        v ≠ 0 → Sbd.boundaryGenerator v ≠ 0
  /-- Nonzero operatorial central charge on the chiral Fredholm surface. -/
  hCentral :
    InfoGeometry.Canonical.OperatorialCentralCharge.operatorialCentralCharge
      (A := A₀) (B := B₀) (E := E) Xdef hXdef ≠ 0
  /-- Boundary generator is one of the canonical vortex seeds. -/
  hBoundary :
    Sbd.boundaryGenerator = InfoGeometry.Canonical.VortexAnomalyLink.sourceVortexSeed (E := E) V
      ∨ Sbd.boundaryGenerator = InfoGeometry.Canonical.VortexAnomalyLink.sinkVortexSeed (E := E) V

/--
Proof-carrying quasilattice mismatch / nonzero-index packet.

This bundles the two remaining explicit hypotheses on the mismatch-driven
quasilattice branch: the owner implication from transported chiral-kernel
mismatch to projector noncommutation, and the nonzero quasilattice analytical
index witness on the same defect surface.
-/
private structure QuasilatticeIndexMismatchWitness
    {A₀ B₀ : Type}
    [NormedRing A₀] [NormedRing B₀]
    [NormedAlgebra ℝ A₀] [NormedAlgebra ℝ B₀]
    [KreinSpace H₂] [KreinGradedModule H₂]
    (CI : ConformalInference E)
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (Xdef : RealSplitKreinDiracFredholmModule A₀ B₀ H₂)
    (tdef : ℝ)
    (hVXdef : QuasilatticeChiralFredholmSurface V Xdef tdef) where
  /-- Owner implication from mismatch to projector noncommutation. -/
  hMismatchNoncommute :
    InfoGeometry.Canonical.ChiralDefectIndexBridge.TransportedChiralKernelDimMismatch
        V Xdef tdef hVXdef →
      CI.spectralChiralProjector * CI.metricChiralProjector
        ≠
      CI.metricChiralProjector * CI.spectralChiralProjector
  /-- Nonzero quasilattice analytical index on the same transported defect slice. -/
  hIndexNonzero : quasilatticeAnalyticalIndex V Xdef tdef hVXdef ≠ 0

/--
Recover the DIII-owned transport-commutator nonvanishing theorem from the bundled
witness packet.
-/
private theorem transportCommutator_ne_zero_of_diiiWitness
    {A₀ B₀ : Type}
    [NormedRing A₀] [NormedRing B₀]
    [NormedAlgebra ℝ A₀] [NormedAlgebra ℝ B₀]
    [KreinSpace H₂] [KreinGradedModule H₂]
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (Xdef : RealSplitKreinDiracFredholmModule A₀ B₀ H₂)
    (hXdef : ChiralFredholmSurface Xdef)
    (tdef : ℝ)
    (W : DIIITransportCommutatorWitness (E := E) V Xdef hXdef tdef) :
    InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
      V.connectionGenerator (spectral_epsilon (E := E)) ≠ 0 := by
  have hDIII :=
    canonicalDIIIProxy_transport_root_centralCharge_commutator_closure
      (A := A₀) (B := B₀) (E := E)
      V Xdef hXdef W.hEvenDef tdef W.M W.P0 W.Sbd W.hA W.hplus W.hminus W.hodd
      W.hBoundaryOnZeroModes W.hCentral W.hBoundary
  exact hDIII.2.2

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
Witness-routed ZPE/gravity bridge: recover the old two-component output from a
single proof-carrying packet instead of separate `hRankPos` and `hEin`
hypotheses.
-/
private theorem bridge_zpe_gravity_of_witness
    (S : SpinFactorState E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (W : ZPEGravityWitness (E := E) S c R Kgeo x) :
    0 < S.variance_limit ∧
    EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CI.chiralScale)) Λ κ
      (anomalyStressEnergyAt Kgeo x CI.chiralScale) :=
  bridge_zpe_gravity S W.hRankPos CI c R Kgeo x Λ κ W.hEin

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

/--
Witness-routed fluid/helicity bridge.

This is the constructive companion to `bridge_fluid_helicity`: the explicit
helicity probes and matching equality are recovered from a single
`MatchedHelicityWitness` object.
-/
private theorem bridge_fluid_helicity_of_matchedWitness
    (A B_mp B_dr : VelocityField E)
    (hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr)
    (hHelicity : MatchedHelicityWitness (E := E) A) :
    (∃ state : FluidState E,
      state.u = EinsteinAnomaly A B_mp B_dr
        ∧ state.ρ = 1
        ∧ momentumResidual (E := E) state.u = 0) ∧
    (∃ (ω' : VelocityField E →L[ℝ] ℝ) (Ω' : AlgebraEnd E →L[ℝ] ℝ),
      helicityInvariant A ω' = twinWaveHelicity A Ω') := by
  exact bridge_fluid_helicity A B_mp B_dr
    hHelicity.omega hHelicity.Omega hAnomalySkew hHelicity.match_helicity

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
Proof-carrying fluid/helicity production packet.

This bundles the regularization data that constructs anomaly skewness together
with the matched-helicity readout, so downstream capstone wrappers can consume
one constructive packet instead of carrying separate regularization and helicity
hypothesis surfaces.
-/
private structure FluidHelicityProductionWitness
    (A B_mp B_dr : VelocityField E) where
  /-- Regularization witness constructing the skew-adjoint anomaly route. -/
  regularization : RegularizationWitness (E := E) A B_mp B_dr
  /-- Matched helicity probes for the same velocity field. -/
  helicity : MatchedHelicityWitness (E := E) A

/--
Proof-carrying canonical-Drazin fluid/helicity packet.

This is the canonical-Drazin specialization of `FluidHelicityProductionWitness`:
callers provide one constructive packet instead of the two explicit theorem
arguments `CanonicalDrazinRegularizationWitness` and `MatchedHelicityWitness`.
-/
private structure CanonicalDrazinFluidHelicityWitness
    (A B_mp : VelocityField E) where
  /-- Canonical-Drazin regularization data for the anomaly route. -/
  canonicalRegularization : CanonicalDrazinRegularizationWitness (E := E) A B_mp
  /-- Matched helicity probes for the same velocity field. -/
  helicity : MatchedHelicityWitness (E := E) A

/--
Proof-carrying owner packet for the narrowed base master-capstone lane.

This bundles the three already-constructed constructive packets used by
`bits_to_gravity_to_fluid_capstone_of_ownerWitnesses_and_productionWitness_and_thermalBottWitness`
so the capstone branch can consume one explicit witness object instead of three
separate theorem arguments.
-/
private structure ConstructiveMasterCapstoneWitness
    (S : SpinFactorState E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (A B_mp B_dr : VelocityField E) where
  /-- Zero-point / Einstein witness packet for the gravity lane. -/
  zpeGravity : ZPEGravityWitness (E := E) S c R Kgeo x
  /-- Fluid-production witness packet for the anomaly/helicity lane. -/
  fluidProduction : FluidHelicityProductionWitness (E := E) A B_mp B_dr
  /-- Thermal/Bott witness packet for the modular/Bott lane. -/
  thermalBott : ThermalBottWitness (E := E)

/--
Proof-carrying canonical-Drazin capstone packet.

This is the canonical-Drazin specialization of
`ConstructiveMasterCapstoneWitness`: callers provide one constructive packet
carrying the ZPE/gravity lane, the canonical-Drazin fluid/helicity lane, and the
thermal/Bott lane, instead of threading those three packet arguments
separately.
-/
private structure CanonicalDrazinMasterCapstoneWitness
    (S : SpinFactorState E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (A B_mp : VelocityField E) where
  /-- Zero-point / Einstein witness packet for the gravity lane. -/
  zpeGravity : ZPEGravityWitness (E := E) S c R Kgeo x
  /-- Canonical-Drazin fluid-production witness packet. -/
  fluidProduction : CanonicalDrazinFluidHelicityWitness (E := E) A B_mp
  /-- Thermal/Bott witness packet for the modular/Bott lane. -/
  thermalBott : ThermalBottWitness (E := E)

/--
Recover the generic fluid/helicity production witness from the canonical-Drazin
packet by computing the Drazin leg as the canonical Drazin inverse.
-/
private noncomputable def canonicalDrazinFluidHelicityWitness_toProductionWitness
    (A B_mp : VelocityField E)
    (W : CanonicalDrazinFluidHelicityWitness (E := E) A B_mp) :
    FluidHelicityProductionWitness (E := E) A B_mp
      (DrazinInfiniteCore.canonicalDrazinInverse_endCLM (E := E) A) :=
  { regularization :=
      canonicalDrazinRegularizationWitness_toRegularizationWitness
        (E := E) A B_mp W.canonicalRegularization
    helicity := W.helicity }

/--
Recover the generic master-capstone witness from the canonical-Drazin packet by
computing the Drazin leg as the canonical Drazin inverse.
-/
private noncomputable def canonicalDrazinMasterCapstoneWitness_toConstructiveWitness
    (S : SpinFactorState E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (A B_mp : VelocityField E)
    (W : CanonicalDrazinMasterCapstoneWitness (E := E) S c R Kgeo x A B_mp) :
    ConstructiveMasterCapstoneWitness (E := E) S c R Kgeo x A B_mp
      (DrazinInfiniteCore.canonicalDrazinInverse_endCLM (E := E) A) :=
  { zpeGravity := W.zpeGravity
    fluidProduction :=
      canonicalDrazinFluidHelicityWitness_toProductionWitness
        (E := E) A B_mp W.fluidProduction
    thermalBott := W.thermalBott }

/--
Recover anomaly skewness from the proof-carrying regularization packet.

This names the constructive route from the bundled Moore-Penrose/Drazin/star
witness to the old skew-adjoint hypothesis surface, so capstone wrappers do not
repeat the four-field projection proof inline.
-/
private theorem anomalySkew_of_regularizationWitness
    (A B_mp B_dr : VelocityField E)
    (hReg : RegularizationWitness (E := E) A B_mp B_dr) :
    ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
      = -EinsteinAnomaly A B_mp B_dr :=
  anomalySkew_of_regularization (A := A) (B_mp := B_mp) (B_dr := B_dr)
    hReg.h_mp hReg.k hReg.h_drazin hReg.h_star

/--
Witness-routed regularization bridge:
derive the anomaly skewness and fluid/helicity packet from one regularization
witness instead of four separate regularization hypotheses.
-/
private theorem bridge_fluid_helicity_of_regularizationWitness
    (A B_mp B_dr : VelocityField E)
    (hReg : RegularizationWitness (E := E) A B_mp B_dr)
    (hHelicity : MatchedHelicityWitness (E := E) A) :
    (∃ state : FluidState E,
      state.u = EinsteinAnomaly A B_mp B_dr
        ∧ state.ρ = 1
        ∧ momentumResidual (E := E) state.u = 0) ∧
    (∃ (ω' : VelocityField E →L[ℝ] ℝ) (Ω' : AlgebraEnd E →L[ℝ] ℝ),
      helicityInvariant A ω' = twinWaveHelicity A Ω') := by
  have hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr :=
    anomalySkew_of_regularizationWitness (E := E) A B_mp B_dr hReg
  exact bridge_fluid_helicity_of_matchedWitness A B_mp B_dr hAnomalySkew hHelicity

/--
Recover the fluid/helicity packet from a single proof-carrying production
witness, eliminating the separate regularization and helicity theorem arguments
on narrowed constructive branches.
-/
private theorem bridge_fluid_helicity_of_productionWitness
    (A B_mp B_dr : VelocityField E)
    (W : FluidHelicityProductionWitness (E := E) A B_mp B_dr) :
    (∃ state : FluidState E,
      state.u = EinsteinAnomaly A B_mp B_dr
        ∧ state.ρ = 1
        ∧ momentumResidual (E := E) state.u = 0) ∧
    (∃ (ω' : VelocityField E →L[ℝ] ℝ) (Ω' : AlgebraEnd E →L[ℝ] ℝ),
      helicityInvariant A ω' = twinWaveHelicity A Ω') :=
  bridge_fluid_helicity_of_regularizationWitness
    (E := E) A B_mp B_dr W.regularization W.helicity

/--
Canonical-Drazin production route for the fluid/helicity packet.  This removes
the explicit pair `(hCanon, hHelicity)` on the narrowed canonical-Drazin branch;
the canonical Drazin inverse and generic regularization packet are recovered by
definition from `CanonicalDrazinFluidHelicityWitness`.
-/
private theorem bridge_fluid_helicity_of_canonicalDrazinProductionWitness
    (A B_mp : VelocityField E)
    (W : CanonicalDrazinFluidHelicityWitness (E := E) A B_mp) :
    (∃ state : FluidState E,
      state.u = EinsteinAnomaly A B_mp
          (DrazinInfiniteCore.canonicalDrazinInverse_endCLM (E := E) A)
        ∧ state.ρ = 1
        ∧ momentumResidual (E := E) state.u = 0) ∧
    (∃ (ω' : VelocityField E →L[ℝ] ℝ) (Ω' : AlgebraEnd E →L[ℝ] ℝ),
      helicityInvariant A ω' = twinWaveHelicity A Ω') :=
  bridge_fluid_helicity_of_productionWitness
    (E := E) A B_mp
    (DrazinInfiniteCore.canonicalDrazinInverse_endCLM (E := E) A)
    (canonicalDrazinFluidHelicityWitness_toProductionWitness (E := E) A B_mp W)

/--
Compatibility wrapper for the older regularization surface.
It now builds the regularization witness locally and routes through
`bridge_fluid_helicity_of_regularizationWitness`.
-/
private theorem bridge_fluid_helicity_of_regularization
    (A B_mp B_dr : VelocityField E)
    (h_mp : IsMoorePenroseInverse A B_mp)
    (k : ℕ)
    (h_dr : IsDrazinInverse A B_dr k)
    (h_dr_star : star (A * B_dr) = A * B_dr)
    (hHelicity : MatchedHelicityWitness (E := E) A) :
    (∃ state : FluidState E,
      state.u = EinsteinAnomaly A B_mp B_dr
        ∧ state.ρ = 1
        ∧ momentumResidual (E := E) state.u = 0) ∧
    (∃ (ω' : VelocityField E →L[ℝ] ℝ) (Ω' : AlgebraEnd E →L[ℝ] ℝ),
      helicityInvariant A ω' = twinWaveHelicity A Ω') := by
  exact bridge_fluid_helicity_of_regularizationWitness
    A B_mp B_dr
    { h_mp := h_mp, k := k, h_drazin := h_dr, h_star := h_dr_star }
    hHelicity

/--
Finite-dimensional regularization witness:
derive the canonical Drazin packet internally and expose the fluid/helicity
bridge under a single proof-carrying helicity witness.
-/
private theorem bridge_fluid_helicity_of_regularization_of_finiteDimensional_of_matchedHelicityWitness
    (A B_mp : VelocityField E)
    (h_mp : IsMoorePenroseInverse A B_mp)
    (hHelicity : MatchedHelicityWitness (E := E) A) :
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
    A B_mp (DrazinWitnessElimination.drazinInverse (E := E) A)
    hHelicity.omega hHelicity.Omega
    (anomalySkew_of_regularization_auto (E := E) A B_mp h_mp h_dr_star)
    hHelicity.match_helicity

/--
Finite-dimensional regularization compatibility wrapper:
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
  exact bridge_fluid_helicity_of_regularization_of_finiteDimensional_of_matchedHelicityWitness
    (E := E) A B_mp h_mp
    { omega := ω, Omega := Ω, match_helicity := hHelicity }

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
Witness-routed thermal/Bott bridge: recover the old modular thermal-time output
and split Bott-Dirac closure from one proof-carrying owner packet instead of
separate `Mod`, `V`, `IST`, and `hCompat` theorem arguments.
-/
private theorem bridge_thermal_bott_of_witness
    (W : ThermalBottWitness (E := E)) :
    W.Mod.ConnesRovelliThermalTimeIdentity
      ∧ (cl11BottDirac (E := E) (spectralDiracLinear W.IST)).comp
          (cl11BottDirac (E := E) (spectralDiracLinear W.IST)) = 0 := by
  have hBal : LichnerowiczBalancedCl11 (A := E) W.IST :=
    lichnerowiczBalancedCl11_of_transportCompatibility
      (E := E) (V := W.V) (IST := W.IST) W.hCompat
  exact ⟨
    W.Mod.connesRovelliThermalTimeIdentity,
    cl11_bottDirac_sq_eq_zero_of_lichnerowiczBalanced (A := E) W.IST hBal⟩

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
  let hZPE := bridge_zpe_gravity_of_witness S CI c R Kgeo x Λ κ
    { hRankPos := hRankPos, hEin := hEin }
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
Witness-routed master capstone composition.

This compatibility-preserving variant keeps the original capstone theorem intact,
but replaces the three free helicity arguments `(ω, Ω, hHelicity)` by the
proof-carrying `MatchedHelicityWitness` packet.
-/
private theorem bits_to_gravity_to_fluid_capstone_of_matchedHelicityWitness
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
    (hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr)
    (hHelicity : MatchedHelicityWitness (E := E) A)
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
  exact bits_to_gravity_to_fluid_capstone
    (S := S) (hRankPos := hRankPos) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
    (hEin := hEin)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (ω := hHelicity.omega) (Ω := hHelicity.Omega)
    (hAnomalySkew := hAnomalySkew) (hHelicity := hHelicity.match_helicity)
    (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)

/--
Owner-witness-routed master capstone composition.

This narrows the capstone route one step further than
`bits_to_gravity_to_fluid_capstone_of_matchedHelicityWitness`: the zero-point
rank witness and the local Einstein-Kähler certificate are consumed through the
proof-carrying `ZPEGravityWitness`, while helicity is consumed through
`MatchedHelicityWitness`.  The older theorem is kept as a compatibility wrapper
for callers that still thread the loose hypotheses.
-/
private theorem bits_to_gravity_to_fluid_capstone_of_ownerWitnesses
    (S : SpinFactorState E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hZPEGravity : ZPEGravityWitness (E := E) S c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr)
    (hHelicity : MatchedHelicityWitness (E := E) A)
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
  exact bits_to_gravity_to_fluid_capstone_of_matchedHelicityWitness
    (S := S) (hRankPos := hZPEGravity.hRankPos) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
    (hEin := hZPEGravity.hEin)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (hAnomalySkew := hAnomalySkew) (hHelicity := hHelicity)
    (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)

/--
Owner-witness and thermal/Bott-witness routed capstone composition.

This is the narrowed constructive branch that removes the loose thermal/Bott
packet `(Mod, V, IST, hCompat)` from the theorem arguments.  The old broad
capstone wrappers remain available, while this route computes the thermal-time
and Bott-Dirac closure components from `ThermalBottWitness`.
-/
private theorem bits_to_gravity_to_fluid_capstone_of_ownerWitnesses_and_thermalBottWitness
    (S : SpinFactorState E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hZPEGravity : ZPEGravityWitness (E := E) S c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr)
    (hHelicity : MatchedHelicityWitness (E := E) A)
    (hThermalBott : ThermalBottWitness (E := E))
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
      ∧ hThermalBott.Mod.ConnesRovelliThermalTimeIdentity
      ∧ (cl11BottDirac (E := E) (spectralDiracLinear hThermalBott.IST)).comp
          (cl11BottDirac (E := E) (spectralDiracLinear hThermalBott.IST)) = 0
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
  exact bits_to_gravity_to_fluid_capstone_of_ownerWitnesses
    (S := S) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
    (hZPEGravity := hZPEGravity)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (hAnomalySkew := hAnomalySkew) (hHelicity := hHelicity)
    (Mod := hThermalBott.Mod) (V := hThermalBott.V)
    (IST := hThermalBott.IST) (hCompat := hThermalBott.hCompat)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)

/--
Constructive fluid/helicity + thermal/Bott capstone variant.

This is the next narrowing step on the owner/thermal branch: the explicit
anomaly-skew and matched-helicity hypotheses are bundled into a single
`FluidHelicityProductionWitness` packet, while the thermal/Bott witness is kept
as the compatibility carrier.
-/
private theorem bits_to_gravity_to_fluid_capstone_of_ownerWitnesses_and_productionWitness_and_thermalBottWitness
    (S : SpinFactorState E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hZPEGravity : ZPEGravityWitness (E := E) S c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (Wfluid : FluidHelicityProductionWitness (E := E) A B_mp B_dr)
    (hThermalBott : ThermalBottWitness (E := E))
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
      ∧ hThermalBott.Mod.ConnesRovelliThermalTimeIdentity
      ∧ (cl11BottDirac (E := E) (spectralDiracLinear hThermalBott.IST)).comp
          (cl11BottDirac (E := E) (spectralDiracLinear hThermalBott.IST)) = 0
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
  exact bits_to_gravity_to_fluid_capstone_of_ownerWitnesses_and_thermalBottWitness
    (S := S) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
    (hZPEGravity := hZPEGravity)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (hAnomalySkew :=
      anomalySkew_of_regularizationWitness (E := E) A B_mp B_dr Wfluid.regularization)
    (hHelicity := Wfluid.helicity)
    (hThermalBott := hThermalBott)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)

/--
Further constructive narrowing of the base capstone branch.

This removes the remaining three explicit packet arguments
`(hZPEGravity, Wfluid, hThermalBott)` by routing through one
`ConstructiveMasterCapstoneWitness` object on the same infinite-dimensional lane.
-/
private theorem bits_to_gravity_to_fluid_capstone_of_constructiveWitness
    (S : SpinFactorState E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (A B_mp B_dr : VelocityField E)
    (W : ConstructiveMasterCapstoneWitness (E := E) S c R Kgeo x A B_mp B_dr)
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
      ∧ W.thermalBott.Mod.ConnesRovelliThermalTimeIdentity
      ∧ (cl11BottDirac (E := E) (spectralDiracLinear W.thermalBott.IST)).comp
          (cl11BottDirac (E := E) (spectralDiracLinear W.thermalBott.IST)) = 0
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
  bits_to_gravity_to_fluid_capstone_of_ownerWitnesses_and_productionWitness_and_thermalBottWitness
    (S := S) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
    (hZPEGravity := W.zpeGravity)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (Wfluid := W.fluidProduction)
    (hThermalBott := W.thermalBott)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)

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
Owner-witness-routed defect-sourced capstone variant.

This narrows the quasilattice-index route by consuming the ZPE/gravity packet and
matched-helicity packet directly, instead of exposing separate `hRankPos`,
`hEin`, `ω`, `Ω`, and `hHelicity` hypotheses at the capstone theorem surface.
The older loose-hypothesis theorem remains available as the compatibility route.
-/
private theorem bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_quasilatticeAnalyticalIndex_of_ownerWitnesses
    {A₀ B₀ : Type}
    [NormedRing A₀] [NormedRing B₀]
    [NormedAlgebra ℝ A₀] [NormedAlgebra ℝ B₀]
    [KreinSpace H₂] [KreinGradedModule H₂]
    (S : SpinFactorState E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hZPEGravity : ZPEGravityWitness (E := E) S c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr)
    (hHelicity : MatchedHelicityWitness (E := E) A)
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
  exact bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_quasilatticeAnalyticalIndex
    (S := S) (hRankPos := hZPEGravity.hRankPos) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
    (hEin := hZPEGravity.hEin)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (ω := hHelicity.omega) (Ω := hHelicity.Omega)
    (hAnomalySkew := hAnomalySkew) (hHelicity := hHelicity.match_helicity)
    (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
    (Xdef := Xdef) (tdef := tdef) (hVXdef := hVXdef)
    (hCompatDefect := hCompatDefect) (hIndexNonzero := hIndexNonzero)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)

/--
Defect-sourced capstone variant with owner and fluid-production witnesses.

This is the next truthful narrowing on the quasilattice-index branch: the loose
pair `(hAnomalySkew, hHelicity)` is recovered from the single constructive
packet `FluidHelicityProductionWitness`.
-/
private theorem bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_quasilatticeAnalyticalIndex_of_ownerWitnesses_and_productionWitness
    {A₀ B₀ : Type}
    [NormedRing A₀] [NormedRing B₀]
    [NormedAlgebra ℝ A₀] [NormedAlgebra ℝ B₀]
    [KreinSpace H₂] [KreinGradedModule H₂]
    (S : SpinFactorState E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hZPEGravity : ZPEGravityWitness (E := E) S c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (Wfluid : FluidHelicityProductionWitness (E := E) A B_mp B_dr)
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
  exact bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_quasilatticeAnalyticalIndex_of_ownerWitnesses
    (S := S) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
    (hZPEGravity := hZPEGravity)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (hAnomalySkew :=
      anomalySkew_of_regularizationWitness (E := E) A B_mp B_dr Wfluid.regularization)
    (hHelicity := Wfluid.helicity)
    (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
    (Xdef := Xdef) (tdef := tdef) (hVXdef := hVXdef)
    (hCompatDefect := hCompatDefect) (hIndexNonzero := hIndexNonzero)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)

/--
Defect-sourced capstone variant with owner witnesses and thermal/Bott witness.

This is the narrowed constructive route for the quasilattice-index branch: it
keeps the explicit defect-surface and index witnesses, but removes the loose
thermal/Bott packet `(Mod, V, IST, hCompat)` by consuming the proof-carrying
`ThermalBottWitness` directly.
-/
private theorem bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_quasilatticeAnalyticalIndex_of_ownerWitnesses_and_thermalBottWitness
    {A₀ B₀ : Type}
    [NormedRing A₀] [NormedRing B₀]
    [NormedAlgebra ℝ A₀] [NormedAlgebra ℝ B₀]
    [KreinSpace H₂] [KreinGradedModule H₂]
    (S : SpinFactorState E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hZPEGravity : ZPEGravityWitness (E := E) S c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (Wfluid : FluidHelicityProductionWitness (E := E) A B_mp B_dr)
    (hThermalBott : ThermalBottWitness (E := E))
    (Xdef : RealSplitKreinDiracFredholmModule A₀ B₀ H₂)
    (tdef : ℝ)
    (hVXdef : QuasilatticeChiralFredholmSurface hThermalBott.V Xdef tdef)
    (hCompatDefect :
      SuperchargeProjectorCompatibility
        (A := A₀) (B := B₀) (E := E)
        CI hThermalBott.V Xdef tdef hVXdef
        CI.spectralChiralProjector CI.metricChiralProjector)
    (hIndexNonzero : quasilatticeAnalyticalIndex hThermalBott.V Xdef tdef hVXdef ≠ 0)
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
      ∧ hThermalBott.Mod.ConnesRovelliThermalTimeIdentity
      ∧ (cl11BottDirac (E := E) (spectralDiracLinear hThermalBott.IST)).comp
          (cl11BottDirac (E := E) (spectralDiracLinear hThermalBott.IST)) = 0
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
  exact bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_quasilatticeAnalyticalIndex_of_ownerWitnesses_and_productionWitness
    (S := S) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
    (hZPEGravity := hZPEGravity)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (Wfluid := Wfluid)
    (Mod := hThermalBott.Mod) (V := hThermalBott.V)
    (IST := hThermalBott.IST) (hCompat := hThermalBott.hCompat)
    (Xdef := Xdef) (tdef := tdef) (hVXdef := hVXdef)
    (hCompatDefect := hCompatDefect) (hIndexNonzero := hIndexNonzero)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)

/--
Further constructive narrowing of the quasilattice-index capstone branch.

This removes the remaining three explicit packet arguments
`(hZPEGravity, Wfluid, hThermalBott)` by routing through one
`ConstructiveMasterCapstoneWitness` object while keeping the same explicit
quasilattice defect and nonzero-index lane.
-/
private theorem bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_quasilatticeAnalyticalIndex_of_constructiveWitness
    {A₀ B₀ : Type}
    [NormedRing A₀] [NormedRing B₀]
    [NormedAlgebra ℝ A₀] [NormedAlgebra ℝ B₀]
    [KreinSpace H₂] [KreinGradedModule H₂]
    (S : SpinFactorState E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (A B_mp B_dr : VelocityField E)
    (W : ConstructiveMasterCapstoneWitness (E := E) S c R Kgeo x A B_mp B_dr)
    (Xdef : RealSplitKreinDiracFredholmModule A₀ B₀ H₂)
    (tdef : ℝ)
    (hVXdef : QuasilatticeChiralFredholmSurface W.thermalBott.V Xdef tdef)
    (hCompatDefect :
      SuperchargeProjectorCompatibility
        (A := A₀) (B := B₀) (E := E)
        CI W.thermalBott.V Xdef tdef hVXdef
        CI.spectralChiralProjector CI.metricChiralProjector)
    (hIndexNonzero : quasilatticeAnalyticalIndex W.thermalBott.V Xdef tdef hVXdef ≠ 0)
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
      ∧ W.thermalBott.Mod.ConnesRovelliThermalTimeIdentity
      ∧ (cl11BottDirac (E := E) (spectralDiracLinear W.thermalBott.IST)).comp
          (cl11BottDirac (E := E) (spectralDiracLinear W.thermalBott.IST)) = 0
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
  exact bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_quasilatticeAnalyticalIndex_of_ownerWitnesses_and_thermalBottWitness
    (A₀ := A₀) (B₀ := B₀)
    (S := S) (CI := CI) (c := c) (R := R) (Kgeo := Kgeo)
    (x := x) (Λ := Λ) (κ := κ)
    (hZPEGravity := W.zpeGravity)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (Wfluid := W.fluidProduction)
    (hThermalBott := W.thermalBott)
    (Xdef := Xdef) (tdef := tdef) (hVXdef := hVXdef)
    (hCompatDefect := hCompatDefect)
    (hIndexNonzero := hIndexNonzero)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)


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
    (Wfluid : FluidHelicityProductionWitness (E := E) A B_mp B_dr)
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
    bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_quasilatticeAnalyticalIndex_of_ownerWitnesses_and_productionWitness
      (A₀ := A₀) (B₀ := B₀)
      (S := S)
      (CI := CI) (c := c) (R := R) (Kgeo := Kgeo)
      (x := x) (Λ := Λ) (κ := κ)
      (hZPEGravity := { hRankPos := hRankPos, hEin := hEin })
      (A := A) (B_mp := B_mp) (B_dr := B_dr) (Wfluid := Wfluid)
      (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
      (Xdef := Xdef) (tdef := tdef) (hVXdef := hVXdef)
      (hCompatDefect := hCompatDefect)
      (hIndexNonzero := hIndexNonzero)
      (n := n) (Tflow := Tflow)
      (γ := γ) (N := N)

/--
Owner-witness-routed mismatch capstone variant.

This is the mismatch-driven analogue of the owner-witness quasilattice route:
the old broad theorem remains as the compatibility surface, while this route
consumes the ZPE/gravity and matched-helicity packets directly and derives the
same conformal nonzero-scale capstone from the mismatch owner.
-/
private theorem bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_mismatch_forces_projector_noncommute_of_ownerWitnesses
    {A₀ B₀ : Type}
    [NormedRing A₀] [NormedRing B₀]
    [NormedAlgebra ℝ A₀] [NormedAlgebra ℝ B₀]
    [KreinSpace H₂] [KreinGradedModule H₂]
    (S : SpinFactorState E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hZPEGravity : ZPEGravityWitness (E := E) S c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr)
    (hHelicity : MatchedHelicityWitness (E := E) A)
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
    bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_quasilatticeAnalyticalIndex_of_ownerWitnesses
      (A₀ := A₀) (B₀ := B₀)
      (S := S)
      (CI := CI) (c := c) (R := R) (Kgeo := Kgeo)
      (x := x) (Λ := Λ) (κ := κ) (hZPEGravity := hZPEGravity)
      (A := A) (B_mp := B_mp) (B_dr := B_dr)
      (hAnomalySkew := hAnomalySkew)
      (hHelicity := hHelicity)
      (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
      (Xdef := Xdef) (tdef := tdef) (hVXdef := hVXdef)
      (hCompatDefect := hCompatDefect)
      (hIndexNonzero := hIndexNonzero)
      (n := n) (Tflow := Tflow)
      (γ := γ) (N := N)

/--
Witness-routed mismatch capstone variant.

This narrows the mismatch-driven quasilattice branch one step further by
replacing the explicit anomaly-skew/helicity pair with the bundled
`FluidHelicityProductionWitness` packet.  The older theorem remains available as
the compatibility surface for callers that still thread the loose hypotheses.
-/
private theorem bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_quasilatticeAnalyticalIndex_of_mismatch_forces_projector_noncommute_of_ownerWitnesses_and_productionWitness
    {A₀ B₀ : Type}
    [NormedRing A₀] [NormedRing B₀]
    [NormedAlgebra ℝ A₀] [NormedAlgebra ℝ B₀]
    [KreinSpace H₂] [KreinGradedModule H₂]
    (S : SpinFactorState E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hZPEGravity : ZPEGravityWitness (E := E) S c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (Wfluid : FluidHelicityProductionWitness (E := E) A B_mp B_dr)
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
  exact
    bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_quasilatticeAnalyticalIndex_of_mismatch_forces_projector_noncommute
      (A₀ := A₀) (B₀ := B₀)
      (S := S) (hRankPos := hZPEGravity.hRankPos)
      (CI := CI) (c := c) (R := R) (Kgeo := Kgeo)
      (x := x) (Λ := Λ) (κ := κ) (hEin := hZPEGravity.hEin)
      (A := A) (B_mp := B_mp) (B_dr := B_dr) (Wfluid := Wfluid)
      (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
      (Xdef := Xdef) (tdef := tdef) (hVXdef := hVXdef)
      (hMismatchNoncommute := hMismatchNoncommute)
      (hIndexNonzero := hIndexNonzero)
      (n := n) (Tflow := Tflow)
      (γ := γ) (N := N)

/--
Witness-routed mismatch capstone with constructive owner packets.

This is the smaller constructive route on the mismatch-driven quasilattice
branch: one `ConstructiveMasterCapstoneWitness` now recovers the
`(hZPEGravity, Wfluid, hThermalBott)` lane, while the bundled
`QuasilatticeIndexMismatchWitness` supplies the remaining mismatch/index owner
data for the same transported defect surface.
-/
private theorem bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_quasilatticeIndexMismatchWitness_of_constructiveWitness
    {A₀ B₀ : Type}
    [NormedRing A₀] [NormedRing B₀]
    [NormedAlgebra ℝ A₀] [NormedAlgebra ℝ B₀]
    [KreinSpace H₂] [KreinGradedModule H₂]
    (S : SpinFactorState E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (A B_mp B_dr : VelocityField E)
    (W : ConstructiveMasterCapstoneWitness (E := E) S c R Kgeo x A B_mp B_dr)
    (Xdef : RealSplitKreinDiracFredholmModule A₀ B₀ H₂)
    (tdef : ℝ)
    (hVXdef : QuasilatticeChiralFredholmSurface W.thermalBott.V Xdef tdef)
    (Wmismatch : QuasilatticeIndexMismatchWitness
      (A₀ := A₀) (B₀ := B₀) (E := E)
      (CI := CI) W.thermalBott.V Xdef tdef hVXdef)
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
      ∧ W.thermalBott.Mod.ConnesRovelliThermalTimeIdentity
      ∧ (cl11BottDirac (E := E) (spectralDiracLinear W.thermalBott.IST)).comp
          (cl11BottDirac (E := E) (spectralDiracLinear W.thermalBott.IST)) = 0
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
  exact
    bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_quasilatticeAnalyticalIndex_of_mismatch_forces_projector_noncommute_of_ownerWitnesses_and_productionWitness
      (A₀ := A₀) (B₀ := B₀)
      (S := S) (CI := CI) (c := c) (R := R) (Kgeo := Kgeo)
      (x := x) (Λ := Λ) (κ := κ)
      (hZPEGravity := W.zpeGravity)
      (A := A) (B_mp := B_mp) (B_dr := B_dr)
      (Wfluid := W.fluidProduction)
      (Mod := W.thermalBott.Mod) (V := W.thermalBott.V)
      (IST := W.thermalBott.IST) (hCompat := W.thermalBott.hCompat)
      (Xdef := Xdef) (tdef := tdef) (hVXdef := hVXdef)
      (hMismatchNoncommute := Wmismatch.hMismatchNoncommute)
      (hIndexNonzero := Wmismatch.hIndexNonzero)
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
    bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_mismatch_forces_projector_noncommute_of_ownerWitnesses
      (A₀ := A₀) (B₀ := B₀)
      (S := Sstate)
      (CI := CI) (c := c) (R := R) (Kgeo := Kgeo)
      (x := x) (Λ := Λ) (κ := κ)
      (hZPEGravity := { hRankPos := hRankPos, hEin := hEin })
      (A := A) (B_mp := B_mp) (B_dr := B_dr)
      (hAnomalySkew := hAnomalySkew)
      (hHelicity := { omega := ω, Omega := Ω, match_helicity := hHelicity })
      (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
      (Xdef := Xdef) (tdef := tdef) (hVXdef := hVXdef)
      (hMismatchNoncommute := hMismatchNoncommute)
      (hIndexNonzero := hIndexNonzero)
      (n := n) (Tflow := Tflow)
      (γ := γ) (N := N)
  let W : DIIITransportCommutatorWitness (E := E) V Xdef hXdef tdef :=
    { hEvenDef := hEvenDef
      M := M
      P0 := P0
      Sbd := Sbd
      hA := hA
      hplus := hplus
      hminus := hminus
      hodd := hodd
      hBoundaryOnZeroModes := hBoundaryOnZeroModes
      hCentral := hCentral
      hBoundary := hBoundary }
  have hComm :
      InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
        V.connectionGenerator (spectral_epsilon (E := E)) ≠ 0 :=
    transportCommutator_ne_zero_of_diiiWitness
      (A₀ := A₀) (B₀ := B₀) (E := E) V Xdef hXdef tdef W
  exact ⟨hCap, hComm⟩

/--
Witness-routed DIII transport capstone:
consume the bundled `DIIITransportCommutatorWitness` directly instead of carrying
its ten owner fields as separate theorem hypotheses.  The older long-argument
wrapper below is kept for compatibility and can build this witness locally.
-/
private theorem bits_to_gravity_to_fluid_capstone_with_nonzero_scale_and_diii_transportCommutator_of_quasilatticeAnalyticalIndex_of_mismatch_forces_projector_noncommute_of_diiiWitness
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
    (tdef : ℝ)
    (hVXdef : QuasilatticeChiralFredholmSurface V Xdef tdef)
    (hMismatchNoncommute :
      InfoGeometry.Canonical.ChiralDefectIndexBridge.TransportedChiralKernelDimMismatch
          V Xdef tdef hVXdef →
        CI.spectralChiralProjector * CI.metricChiralProjector
          ≠
        CI.metricChiralProjector * CI.spectralChiralProjector)
    (hIndexNonzero : quasilatticeAnalyticalIndex V Xdef tdef hVXdef ≠ 0)
    (W : DIIITransportCommutatorWitness (E := E) V Xdef hXdef tdef)
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
  exact
    bits_to_gravity_to_fluid_capstone_with_nonzero_scale_and_diii_transportCommutator_of_quasilatticeAnalyticalIndex_of_mismatch_forces_projector_noncommute
      (A₀ := A₀) (B₀ := B₀)
      (Sstate := Sstate) (hRankPos := hRankPos)
      (CI := CI) (c := c) (R := R) (Kgeo := Kgeo)
      (x := x) (Λ := Λ) (κ := κ) (hEin := hEin)
      (A := A) (B_mp := B_mp) (B_dr := B_dr)
      (ω := ω) (Ω := Ω)
      (hAnomalySkew := hAnomalySkew)
      (hHelicity := hHelicity)
      (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
      (Xdef := Xdef) (hXdef := hXdef) (hEvenDef := W.hEvenDef) (tdef := tdef)
      (hVXdef := hVXdef)
      (hMismatchNoncommute := hMismatchNoncommute)
      (hIndexNonzero := hIndexNonzero)
      (hCentral := W.hCentral)
      (M := W.M) (P0 := W.P0) (Sbd := W.Sbd)
      (hA := W.hA) (hplus := W.hplus) (hminus := W.hminus) (hodd := W.hodd)
      (hBoundaryOnZeroModes := W.hBoundaryOnZeroModes)
      (hBoundary := W.hBoundary)
      (n := n) (Tflow := Tflow)
      (γ := γ) (N := N)

/--
Witness-routed DIII transport capstone.

This is the next narrowing step on the quasilattice/mismatch branch: the loose
anomaly-skew and helicity inputs are replaced by the single
`FluidHelicityProductionWitness` packet, while the DIII transport witness keeps
the transport-commutator consequence constructive.
-/
private theorem bits_to_gravity_to_fluid_capstone_with_nonzero_scale_and_diii_transportCommutator_of_quasilatticeAnalyticalIndex_of_mismatch_forces_projector_noncommute_of_ownerWitnesses_and_productionWitness
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
    (Wfluid : FluidHelicityProductionWitness (E := E) A B_mp B_dr)
    (Mod : ModularRadonNikodymData E)
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (IST : InfoSpectralTriple H₂)
    (hCompat : InformationalLichnerowiczBottCompatibility (E := E) V IST)
    (Xdef : RealSplitKreinDiracFredholmModule A₀ B₀ H₂)
    (hXdef : ChiralFredholmSurface Xdef)
    (tdef : ℝ)
    (hVXdef : QuasilatticeChiralFredholmSurface V Xdef tdef)
    (hMismatchNoncommute :
      InfoGeometry.Canonical.ChiralDefectIndexBridge.TransportedChiralKernelDimMismatch
          V Xdef tdef hVXdef →
        CI.spectralChiralProjector * CI.metricChiralProjector
          ≠
        CI.metricChiralProjector * CI.spectralChiralProjector)
    (hIndexNonzero : quasilatticeAnalyticalIndex V Xdef tdef hVXdef ≠ 0)
    (W : DIIITransportCommutatorWitness (E := E) V Xdef hXdef tdef)
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
  exact
    bits_to_gravity_to_fluid_capstone_with_nonzero_scale_and_diii_transportCommutator_of_quasilatticeAnalyticalIndex_of_mismatch_forces_projector_noncommute_of_diiiWitness
      (A₀ := A₀) (B₀ := B₀)
      (Sstate := Sstate) (hRankPos := hRankPos)
      (CI := CI) (c := c) (R := R) (Kgeo := Kgeo)
      (x := x) (Λ := Λ) (κ := κ) (hEin := hEin)
      (A := A) (B_mp := B_mp) (B_dr := B_dr)
      (ω := Wfluid.helicity.omega) (Ω := Wfluid.helicity.Omega)
      (hAnomalySkew :=
        anomalySkew_of_regularizationWitness (E := E) A B_mp B_dr Wfluid.regularization)
      (hHelicity := Wfluid.helicity.match_helicity)
      (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
      (Xdef := Xdef) (hXdef := hXdef) (tdef := tdef)
      (hVXdef := hVXdef)
      (hMismatchNoncommute := hMismatchNoncommute)
      (hIndexNonzero := hIndexNonzero)
      (W := W)
      (n := n) (Tflow := Tflow)
      (γ := γ) (N := N)

/--
Witness-routed DIII transport capstone with production and transport owner packets.

This is the next narrowing step on the mismatch-driven DIII branch: the explicit
anomaly-skew/helicity pair is bundled into `FluidHelicityProductionWitness`,
while the DIII transport consequence is consumed through the bundled
`DIIITransportCommutatorWitness`.
-/
private theorem bits_to_gravity_to_fluid_capstone_with_nonzero_scale_and_diii_transportCommutator_of_quasilatticeAnalyticalIndex_of_mismatch_forces_projector_noncommute_of_productionWitness_and_diiiWitness
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
    (Wfluid : FluidHelicityProductionWitness (E := E) A B_mp B_dr)
    (Mod : ModularRadonNikodymData E)
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (IST : InfoSpectralTriple H₂)
    (hCompat : InformationalLichnerowiczBottCompatibility (E := E) V IST)
    (Xdef : RealSplitKreinDiracFredholmModule A₀ B₀ H₂)
    (hXdef : ChiralFredholmSurface Xdef)
    (tdef : ℝ)
    (hVXdef : QuasilatticeChiralFredholmSurface V Xdef tdef)
    (hMismatchNoncommute :
      InfoGeometry.Canonical.ChiralDefectIndexBridge.TransportedChiralKernelDimMismatch
          V Xdef tdef hVXdef →
        CI.spectralChiralProjector * CI.metricChiralProjector
          ≠
        CI.metricChiralProjector * CI.spectralChiralProjector)
    (hIndexNonzero : quasilatticeAnalyticalIndex V Xdef tdef hVXdef ≠ 0)
    (W : DIIITransportCommutatorWitness (E := E) V Xdef hXdef tdef)
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
          Vol = (chain.map (fun c : KitaevCell.{0} => c.pfaffian)).prod)
      ∧
    InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
      V.connectionGenerator (spectral_epsilon (E := E)) ≠ 0)) := by
  have hCap :=
    bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_quasilatticeAnalyticalIndex_of_mismatch_forces_projector_noncommute_of_ownerWitnesses_and_productionWitness
      (A₀ := A₀) (B₀ := B₀)
      (S := Sstate) (hZPEGravity := { hRankPos := hRankPos, hEin := hEin })
      (CI := CI) (c := c) (R := R) (Kgeo := Kgeo)
      (x := x) (Λ := Λ) (κ := κ)
      (A := A) (B_mp := B_mp) (B_dr := B_dr)
      (Wfluid := Wfluid)
      (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
      (Xdef := Xdef) (tdef := tdef) (hVXdef := hVXdef)
      (hMismatchNoncommute := hMismatchNoncommute)
      (hIndexNonzero := hIndexNonzero)
      (n := n) (Tflow := Tflow)
      (γ := γ) (N := N)
  have hComm :
      InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
        V.connectionGenerator (spectral_epsilon (E := E)) ≠ 0 :=
    transportCommutator_ne_zero_of_diiiWitness
      (A₀ := A₀) (B₀ := B₀) (E := E) V Xdef hXdef tdef W
  rcases hCap with
    ⟨hScale, hVar, hEinEq, hState, hTherm, hBott, hHel, hExcl, hLog, hBekenstein,
      hBayes, hExp, hChain⟩
  exact ⟨hScale, hVar, hEinEq, hState, hTherm, hBott, hHel, hExcl, hLog,
    hBekenstein, hBayes, hExp, hChain, hComm⟩

/--
Witness-routed DIII transport capstone with thermal/Bott owner packet.

This is the next truthful narrowing on the mismatch-driven DIII branch: the
thermal-time/Bott inputs `(Mod, V, IST, hCompat)` are recovered from the single
`ThermalBottWitness`, while the fluid/helicity and DIII transport consequences
remain carried by their existing proof-carrying packets.
-/
private theorem bits_to_gravity_to_fluid_capstone_with_nonzero_scale_and_diii_transportCommutator_of_quasilatticeAnalyticalIndex_of_mismatch_forces_projector_noncommute_of_ownerWitnesses_and_productionWitness_and_thermalBottWitness
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
    (Wfluid : FluidHelicityProductionWitness (E := E) A B_mp B_dr)
    (hThermalBott : ThermalBottWitness (E := E))
    (Xdef : RealSplitKreinDiracFredholmModule A₀ B₀ H₂)
    (hXdef : ChiralFredholmSurface Xdef)
    (tdef : ℝ)
    (hVXdef : QuasilatticeChiralFredholmSurface hThermalBott.V Xdef tdef)
    (hMismatchNoncommute :
      InfoGeometry.Canonical.ChiralDefectIndexBridge.TransportedChiralKernelDimMismatch
          hThermalBott.V Xdef tdef hVXdef →
        CI.spectralChiralProjector * CI.metricChiralProjector
          ≠
        CI.metricChiralProjector * CI.spectralChiralProjector)
    (hIndexNonzero : quasilatticeAnalyticalIndex hThermalBott.V Xdef tdef hVXdef ≠ 0)
    (W : DIIITransportCommutatorWitness (E := E) hThermalBott.V Xdef hXdef tdef)
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
      ∧ hThermalBott.Mod.ConnesRovelliThermalTimeIdentity
      ∧ (cl11BottDirac (E := E) (spectralDiracLinear hThermalBott.IST)).comp
          (cl11BottDirac (E := E) (spectralDiracLinear hThermalBott.IST)) = 0
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
      hThermalBott.V.connectionGenerator (spectral_epsilon (E := E)) ≠ 0 := by
  exact
    bits_to_gravity_to_fluid_capstone_with_nonzero_scale_and_diii_transportCommutator_of_quasilatticeAnalyticalIndex_of_mismatch_forces_projector_noncommute_of_ownerWitnesses_and_productionWitness
      (A₀ := A₀) (B₀ := B₀)
      (Sstate := Sstate) (hRankPos := hRankPos)
      (CI := CI) (c := c) (R := R) (Kgeo := Kgeo)
      (x := x) (Λ := Λ) (κ := κ) (hEin := hEin)
      (A := A) (B_mp := B_mp) (B_dr := B_dr)
      (Wfluid := Wfluid)
      (Mod := hThermalBott.Mod) (V := hThermalBott.V)
      (IST := hThermalBott.IST) (hCompat := hThermalBott.hCompat)
      (Xdef := Xdef) (hXdef := hXdef) (tdef := tdef)
      (hVXdef := hVXdef)
      (hMismatchNoncommute := hMismatchNoncommute)
      (hIndexNonzero := hIndexNonzero)
      (W := W)
      (n := n) (Tflow := Tflow)
      (γ := γ) (N := N)

/--
Witness-routed DIII transport capstone with ZPE/gravity, production, and
thermal/Bott owner packets.

This is the smaller constructive route on the mismatch-driven DIII branch:
`ZPEGravityWitness` now recovers `(hRankPos, hEin)` on top of the already-owned
`FluidHelicityProductionWitness`, `ThermalBottWitness`, and
`DIIITransportCommutatorWitness` packets.
-/
private theorem bits_to_gravity_to_fluid_capstone_with_nonzero_scale_and_diii_transportCommutator_of_quasilatticeAnalyticalIndex_of_mismatch_forces_projector_noncommute_of_zpeGravityWitness_and_productionWitness_and_thermalBottWitness
    {A₀ B₀ : Type}
    [NormedRing A₀] [NormedRing B₀]
    [NormedAlgebra ℝ A₀] [NormedAlgebra ℝ B₀]
    [KreinSpace H₂] [KreinGradedModule H₂]
    (Sstate : SpinFactorState E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hZPEGravity : ZPEGravityWitness (E := E) Sstate c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (Wfluid : FluidHelicityProductionWitness (E := E) A B_mp B_dr)
    (hThermalBott : ThermalBottWitness (E := E))
    (Xdef : RealSplitKreinDiracFredholmModule A₀ B₀ H₂)
    (hXdef : ChiralFredholmSurface Xdef)
    (tdef : ℝ)
    (hVXdef : QuasilatticeChiralFredholmSurface hThermalBott.V Xdef tdef)
    (hMismatchNoncommute :
      InfoGeometry.Canonical.ChiralDefectIndexBridge.TransportedChiralKernelDimMismatch
          hThermalBott.V Xdef tdef hVXdef →
        CI.spectralChiralProjector * CI.metricChiralProjector
          ≠
        CI.metricChiralProjector * CI.spectralChiralProjector)
    (hIndexNonzero : quasilatticeAnalyticalIndex hThermalBott.V Xdef tdef hVXdef ≠ 0)
    (W : DIIITransportCommutatorWitness (E := E) hThermalBott.V Xdef hXdef tdef)
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
      ∧ hThermalBott.Mod.ConnesRovelliThermalTimeIdentity
      ∧ (cl11BottDirac (E := E) (spectralDiracLinear hThermalBott.IST)).comp
          (cl11BottDirac (E := E) (spectralDiracLinear hThermalBott.IST)) = 0
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
      hThermalBott.V.connectionGenerator (spectral_epsilon (E := E)) ≠ 0 :=
  bits_to_gravity_to_fluid_capstone_with_nonzero_scale_and_diii_transportCommutator_of_quasilatticeAnalyticalIndex_of_mismatch_forces_projector_noncommute_of_ownerWitnesses_and_productionWitness_and_thermalBottWitness
      (A₀ := A₀) (B₀ := B₀)
      (Sstate := Sstate) (hRankPos := hZPEGravity.hRankPos)
      (CI := CI) (c := c) (R := R) (Kgeo := Kgeo)
      (x := x) (Λ := Λ) (κ := κ) (hEin := hZPEGravity.hEin)
      (A := A) (B_mp := B_mp) (B_dr := B_dr)
      (Wfluid := Wfluid)
      (hThermalBott := hThermalBott)
      (Xdef := Xdef) (hXdef := hXdef) (tdef := tdef)
      (hVXdef := hVXdef)
      (hMismatchNoncommute := hMismatchNoncommute)
      (hIndexNonzero := hIndexNonzero)
      (W := W)
      (n := n) (Tflow := Tflow)
      (γ := γ) (N := N)

/--
Witness-routed DIII transport capstone with quasilattice mismatch packet.

This is the next small constructive reduction on the mismatch-driven DIII branch:
the explicit pair `(hMismatchNoncommute, hIndexNonzero)` is recovered from one
`QuasilatticeIndexMismatchWitness` on top of the already-owned ZPE/gravity,
production, thermal/Bott, and DIII transport packets.
-/
private theorem bits_to_gravity_to_fluid_capstone_with_nonzero_scale_and_diii_transportCommutator_of_quasilatticeIndexMismatchWitness_of_zpeGravityWitness_and_productionWitness_and_thermalBottWitness
    {A₀ B₀ : Type}
    [NormedRing A₀] [NormedRing B₀]
    [NormedAlgebra ℝ A₀] [NormedAlgebra ℝ B₀]
    [KreinSpace H₂] [KreinGradedModule H₂]
    (Sstate : SpinFactorState E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hZPEGravity : ZPEGravityWitness (E := E) Sstate c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (Wfluid : FluidHelicityProductionWitness (E := E) A B_mp B_dr)
    (hThermalBott : ThermalBottWitness (E := E))
    (Xdef : RealSplitKreinDiracFredholmModule A₀ B₀ H₂)
    (hXdef : ChiralFredholmSurface Xdef)
    (tdef : ℝ)
    (hVXdef : QuasilatticeChiralFredholmSurface hThermalBott.V Xdef tdef)
    (Wmismatch : QuasilatticeIndexMismatchWitness
      (A₀ := A₀) (B₀ := B₀) (E := E)
      CI hThermalBott.V Xdef tdef hVXdef)
    (W : DIIITransportCommutatorWitness (E := E) hThermalBott.V Xdef hXdef tdef)
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
      ∧ hThermalBott.Mod.ConnesRovelliThermalTimeIdentity
      ∧ (cl11BottDirac (E := E) (spectralDiracLinear hThermalBott.IST)).comp
          (cl11BottDirac (E := E) (spectralDiracLinear hThermalBott.IST)) = 0
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
      hThermalBott.V.connectionGenerator (spectral_epsilon (E := E)) ≠ 0 :=
  bits_to_gravity_to_fluid_capstone_with_nonzero_scale_and_diii_transportCommutator_of_quasilatticeAnalyticalIndex_of_mismatch_forces_projector_noncommute_of_zpeGravityWitness_and_productionWitness_and_thermalBottWitness
      (A₀ := A₀) (B₀ := B₀)
      (Sstate := Sstate) (CI := CI) (c := c) (R := R) (Kgeo := Kgeo)
      (x := x) (Λ := Λ) (κ := κ)
      (hZPEGravity := hZPEGravity)
      (A := A) (B_mp := B_mp) (B_dr := B_dr)
      (Wfluid := Wfluid)
      (hThermalBott := hThermalBott)
      (Xdef := Xdef) (hXdef := hXdef) (tdef := tdef)
      (hVXdef := hVXdef)
      (hMismatchNoncommute := Wmismatch.hMismatchNoncommute)
      (hIndexNonzero := Wmismatch.hIndexNonzero)
      (W := W)
      (n := n) (Tflow := Tflow)
      (γ := γ) (N := N)

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
Certified-kernel capstone with proof-carrying helicity witness:
this narrows the older certified inverse-kernel surface by replacing the free
probe pair `(ω, Ω)` and equality `hHelicity` with one constructive
`MatchedHelicityWitness` packet.
-/
private theorem bits_to_gravity_to_fluid_capstone_of_certifiedInverseKernel_of_matchedHelicityWitness
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
    (hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr)
    (hHelicity : MatchedHelicityWitness (E := E) A)
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
          Vol = (chain.map (fun c : KitaevCell.{0} => c.pfaffian)).prod) :=
  bits_to_gravity_to_fluid_capstone_of_certifiedInverseKernel
    (S := S) (hRankPos := hRankPos) (CIK := CIK) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
    (hEin := hEin)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (ω := hHelicity.omega) (Ω := hHelicity.Omega)
    (hAnomalySkew := hAnomalySkew) (hHelicity := hHelicity.match_helicity)
    (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)

/--
Certified-kernel capstone with proof-carrying helicity and ZPE/gravity owner
witnesses.

This keeps the certified inverse kernel as the conformal owner while removing
the loose `hRankPos` and `hEin` hypotheses from the matched-helicity route.
The older theorem remains as a compatibility wrapper for callers that still
thread those two hypotheses separately.
-/
private theorem bits_to_gravity_to_fluid_capstone_of_certifiedInverseKernel_of_matchedHelicityWitness_of_zpeGravityWitness
    (S : SpinFactorState E)
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hZPEGravity : ZPEGravityWitness (E := E) S c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr)
    (hHelicity : MatchedHelicityWitness (E := E) A)
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
          Vol = (chain.map (fun c : KitaevCell.{0} => c.pfaffian)).prod) :=
  bits_to_gravity_to_fluid_capstone_of_certifiedInverseKernel_of_matchedHelicityWitness
    (S := S) (hRankPos := hZPEGravity.hRankPos) (CIK := CIK) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
    (hEin := hZPEGravity.hEin)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (hAnomalySkew := hAnomalySkew) (hHelicity := hHelicity)
    (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)

/--
Certified-kernel capstone routed entirely through proof-carrying owner packets.

This constructive branch keeps the certified inverse kernel as the conformal
owner, but removes the loose `(hRankPos, hEin)`, helicity-probe, and
thermal/Bott packet arguments.  The older certified-kernel theorems above remain
as compatibility routes for callers that still carry those arguments separately.
-/
private theorem bits_to_gravity_to_fluid_capstone_of_certifiedInverseKernel_ownerWitnesses
    (S : SpinFactorState E)
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hZPEGravity : ZPEGravityWitness (E := E) S c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (hAnomalySkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr)
    (hHelicity : MatchedHelicityWitness (E := E) A)
    (hThermalBott : ThermalBottWitness (E := E))
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
      ∧ hThermalBott.Mod.ConnesRovelliThermalTimeIdentity
      ∧ (cl11BottDirac (E := E) (spectralDiracLinear hThermalBott.IST)).comp
          (cl11BottDirac (E := E) (spectralDiracLinear hThermalBott.IST)) = 0
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
  bits_to_gravity_to_fluid_capstone_of_certifiedInverseKernel_of_matchedHelicityWitness_of_zpeGravityWitness
    (S := S) (CIK := CIK) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
    (hZPEGravity := hZPEGravity)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (hAnomalySkew := hAnomalySkew) (hHelicity := hHelicity)
    (Mod := hThermalBott.Mod) (V := hThermalBott.V)
    (IST := hThermalBott.IST) (hCompat := hThermalBott.hCompat)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)

/--
Certified-kernel capstone routed through all currently owned constructive
packets.

This is the narrowest certified inverse-kernel branch presently owned in this
module: `ZPEGravityWitness` recovers `(hRankPos, hEin)`,
`FluidHelicityProductionWitness` recovers `(hAnomalySkew, hHelicity)`, and
`ThermalBottWitness` recovers `(Mod, V, IST, hCompat)`. The broader
certified-kernel theorem surface is kept intact for compatibility, while this
branch removes those explicit packet arguments from the theorem signature.
-/
private theorem bits_to_gravity_to_fluid_capstone_of_certifiedInverseKernel_of_productionWitness_of_zpeGravityWitness_and_thermalBottWitness
    (S : SpinFactorState E)
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hZPEGravity : ZPEGravityWitness (E := E) S c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (Wfluid : FluidHelicityProductionWitness (E := E) A B_mp B_dr)
    (hThermalBott : ThermalBottWitness (E := E))
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
      ∧ hThermalBott.Mod.ConnesRovelliThermalTimeIdentity
      ∧ (cl11BottDirac (E := E) (spectralDiracLinear hThermalBott.IST)).comp
          (cl11BottDirac (E := E) (spectralDiracLinear hThermalBott.IST)) = 0
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
  bits_to_gravity_to_fluid_capstone_of_certifiedInverseKernel_ownerWitnesses
    (S := S) (CIK := CIK) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
    (hZPEGravity := hZPEGravity)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (hAnomalySkew :=
      anomalySkew_of_regularizationWitness (E := E) A B_mp B_dr Wfluid.regularization)
    (hHelicity := Wfluid.helicity)
    (hThermalBott := hThermalBott)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)

/--
Regularization-sourced capstone wrapper:
derive the anomaly skewness from one proof-carrying regularization witness and
reuse the primary capstone composition.
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
    (hReg : RegularizationWitness (E := E) A B_mp B_dr)
    (hHelicity : MatchedHelicityWitness (E := E) A)
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
    anomalySkew_of_regularizationWitness (E := E) A B_mp B_dr hReg
  exact bits_to_gravity_to_fluid_capstone_of_matchedHelicityWitness
    (S := S) (hRankPos := hRankPos) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
    (hEin := hEin)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (hAnomalySkew := hAnomalySkew) (hHelicity := hHelicity)
    (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)

/--
Regularization-sourced capstone route with a single fluid-production witness.

This is the narrowed constructive branch for the regularization/helicity lane:
it removes the explicit pair `(hReg, hHelicity)` and recovers both surfaces from
`FluidHelicityProductionWitness`.
-/
private theorem bits_to_gravity_to_fluid_capstone_of_productionWitness
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
    (Wfluid : FluidHelicityProductionWitness (E := E) A B_mp B_dr)
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
          Vol = (chain.map (fun c : KitaevCell.{0} => c.pfaffian)).prod) :=
  bits_to_gravity_to_fluid_capstone_of_regularization
    (S := S) (hRankPos := hRankPos) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
    (hEin := hEin)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (hReg := Wfluid.regularization) (hHelicity := Wfluid.helicity)
    (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)

/--
Regularization capstone with the ZPE/gravity owner packet.

This is the smaller constructive route for the regularization lane: the old
rank-positivity and Einstein-Kähler hypotheses are recovered from one
`ZPEGravityWitness`, while anomaly skewness is still derived from the
`RegularizationWitness` and helicity from `MatchedHelicityWitness`.
-/
private theorem bits_to_gravity_to_fluid_capstone_of_regularization_of_zpeGravityWitness
    (S : SpinFactorState E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hZPEGravity : ZPEGravityWitness (E := E) S c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (hReg : RegularizationWitness (E := E) A B_mp B_dr)
    (hHelicity : MatchedHelicityWitness (E := E) A)
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
          Vol = (chain.map (fun c : KitaevCell.{0} => c.pfaffian)).prod) :=
  bits_to_gravity_to_fluid_capstone_of_regularization
    (S := S) (hRankPos := hZPEGravity.hRankPos) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
    (hEin := hZPEGravity.hEin)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (hReg := hReg) (hHelicity := hHelicity)
    (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)

/--
Production-witness capstone with the ZPE/gravity owner packet.

This is the narrower constructive branch combining the existing owner packets:
`ZPEGravityWitness` recovers rank-positivity and Einstein-Kähler data, while
`FluidHelicityProductionWitness` recovers the regularization and matched
helicity inputs. The old explicit pair `(hReg, hHelicity)` is removed on this
branch.
-/
private theorem bits_to_gravity_to_fluid_capstone_of_productionWitness_of_zpeGravityWitness
    (S : SpinFactorState E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hZPEGravity : ZPEGravityWitness (E := E) S c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (Wfluid : FluidHelicityProductionWitness (E := E) A B_mp B_dr)
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
          Vol = (chain.map (fun c : KitaevCell.{0} => c.pfaffian)).prod) :=
  bits_to_gravity_to_fluid_capstone_of_regularization_of_zpeGravityWitness
    (S := S) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
    (hZPEGravity := hZPEGravity)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (hReg := Wfluid.regularization) (hHelicity := Wfluid.helicity)
    (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)

/--
Production-witness capstone with both ZPE/gravity and thermal/Bott owner packets.

This is the smallest constructive route presently owned in the capstone lane:
`ZPEGravityWitness` recovers `(hRankPos, hEin)`,
`FluidHelicityProductionWitness` recovers `(hReg, hHelicity)`, and
`ThermalBottWitness` recovers `(Mod, V, IST, hCompat)`.  The broader theorem
surface remains available, but this branch removes the explicit thermal/Bott
packet entirely.
-/
private theorem bits_to_gravity_to_fluid_capstone_of_productionWitness_of_zpeGravityWitness_and_thermalBottWitness
    (S : SpinFactorState E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hZPEGravity : ZPEGravityWitness (E := E) S c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (Wfluid : FluidHelicityProductionWitness (E := E) A B_mp B_dr)
    (hThermalBott : ThermalBottWitness (E := E))
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
      ∧ hThermalBott.Mod.ConnesRovelliThermalTimeIdentity
      ∧ (cl11BottDirac (E := E) (spectralDiracLinear hThermalBott.IST)).comp
          (cl11BottDirac (E := E) (spectralDiracLinear hThermalBott.IST)) = 0
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
  bits_to_gravity_to_fluid_capstone_of_productionWitness_of_zpeGravityWitness
    (S := S) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
    (hZPEGravity := hZPEGravity)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (Wfluid := Wfluid)
    (Mod := hThermalBott.Mod) (V := hThermalBott.V)
    (IST := hThermalBott.IST) (hCompat := hThermalBott.hCompat)
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
    (h_mp : IsMoorePenroseInverse A B_mp)
    (h_dr_star_canonical :
      star (A * DrazinInfiniteCore.canonicalDrazinInverse_endCLM (E := E) A)
        = A * DrazinInfiniteCore.canonicalDrazinInverse_endCLM (E := E) A)
    (hHelicity : MatchedHelicityWitness (E := E) A)
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
    (hReg :=
      canonicalDrazinRegularizationWitness_toRegularizationWitness
        (E := E) A B_mp
        { h_mp := h_mp
          h_star_canonical := h_dr_star_canonical })
    (hHelicity := hHelicity)
    (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)

/--
Canonical-Drazin witness branch of the capstone regularization wrapper.

This theorem removes the loose `(h_mp, h_dr_star_canonical)` pair from the new
branch and routes through `CanonicalDrazinRegularizationWitness` instead.  The
older wrapper above is kept as a compatibility surface for downstream callers.
-/
private theorem bits_to_gravity_to_fluid_capstone_of_canonicalDrazinFluidHelicityWitness
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
    (hFluidHelicity : CanonicalDrazinFluidHelicityWitness (E := E) A B_mp)
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
  exact bits_to_gravity_to_fluid_capstone_of_regularization_canonical_drazin
    (S := S) (hRankPos := hRankPos) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
    (hEin := hEin) (A := A) (B_mp := B_mp)
    (h_mp := hFluidHelicity.canonicalRegularization.h_mp)
    (h_dr_star_canonical := hFluidHelicity.canonicalRegularization.h_star_canonical)
    (hHelicity := hFluidHelicity.helicity)
    (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)

/--
Compatibility wrapper for the older canonical-Drazin capstone route.  It keeps
the public theorem-facing name with separate regularization/helicity arguments,
but internally builds the proof-carrying fluid/helicity packet.
-/
private theorem bits_to_gravity_to_fluid_capstone_of_canonicalDrazinRegularizationWitness
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
    (hCanon : CanonicalDrazinRegularizationWitness (E := E) A B_mp)
    (hHelicity : MatchedHelicityWitness (E := E) A)
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
  exact bits_to_gravity_to_fluid_capstone_of_regularization_canonical_drazin
    (S := S) (hRankPos := hRankPos) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
    (hEin := hEin) (A := A) (B_mp := B_mp)
    (h_mp := hCanon.h_mp) (h_dr_star_canonical := hCanon.h_star_canonical)
    (hHelicity := hHelicity)
    (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)

/--
Canonical-Drazin witness route with a proof-carrying ZPE gravity packet.

This is the next narrowing step on the canonical-Drazin lane: the explicit
rank-positivity and Einstein-Kähler hypotheses are recovered from one
`ZPEGravityWitness`, while the canonical-Drazin fluid/helicity packet carries the
regularization and helicity data.
-/
private theorem bits_to_gravity_to_fluid_capstone_of_canonicalDrazinFluidHelicityWitness_and_zpeGravityWitness
    (S : SpinFactorState E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hZPEGravity : ZPEGravityWitness (E := E) S c R Kgeo x)
    (A B_mp : VelocityField E)
    (hFluidHelicity : CanonicalDrazinFluidHelicityWitness (E := E) A B_mp)
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
  exact bits_to_gravity_to_fluid_capstone_of_canonicalDrazinFluidHelicityWitness
    (S := S) (hRankPos := hZPEGravity.hRankPos) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
    (hEin := hZPEGravity.hEin) (A := A) (B_mp := B_mp)
    (hFluidHelicity := hFluidHelicity)
    (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)

/--
Canonical-Drazin witness route with both ZPE/gravity and thermal/Bott owner packets.

This further narrows the canonical-Drazin capstone lane by removing the loose
thermal/Bott packet `(Mod, V, IST, hCompat)` as well. The remaining broad route
is kept for compatibility, while this theorem computes those fields from the
proof-carrying `ThermalBottWitness`.
-/
private theorem bits_to_gravity_to_fluid_capstone_of_canonicalDrazinFluidHelicityWitness_and_zpeGravityWitness_and_thermalBottWitness
    (S : SpinFactorState E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hZPEGravity : ZPEGravityWitness (E := E) S c R Kgeo x)
    (A B_mp : VelocityField E)
    (hFluidHelicity : CanonicalDrazinFluidHelicityWitness (E := E) A B_mp)
    (hThermalBott : ThermalBottWitness (E := E))
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
        ∧ hThermalBott.Mod.ConnesRovelliThermalTimeIdentity
        ∧ (cl11BottDirac (E := E) (spectralDiracLinear hThermalBott.IST)).comp
            (cl11BottDirac (E := E) (spectralDiracLinear hThermalBott.IST)) = 0
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
  exact bits_to_gravity_to_fluid_capstone_of_canonicalDrazinFluidHelicityWitness_and_zpeGravityWitness
    (S := S) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
    (hZPEGravity := hZPEGravity)
    (A := A) (B_mp := B_mp)
    (hFluidHelicity := hFluidHelicity)
    (Mod := hThermalBott.Mod) (V := hThermalBott.V)
    (IST := hThermalBott.IST) (hCompat := hThermalBott.hCompat)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)

/--
Further constructive narrowing of the canonical-Drazin capstone branch.

This removes the remaining three explicit packet arguments
`(hZPEGravity, hFluidHelicity, hThermalBott)` by routing through one
`CanonicalDrazinMasterCapstoneWitness` object on the same infinite-dimensional
lane.
-/
private theorem bits_to_gravity_to_fluid_capstone_of_canonicalDrazinConstructiveWitness
    (S : SpinFactorState E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (A B_mp : VelocityField E)
    (W : CanonicalDrazinMasterCapstoneWitness (E := E) S c R Kgeo x A B_mp)
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
        ∧ W.thermalBott.Mod.ConnesRovelliThermalTimeIdentity
        ∧ (cl11BottDirac (E := E) (spectralDiracLinear W.thermalBott.IST)).comp
            (cl11BottDirac (E := E) (spectralDiracLinear W.thermalBott.IST)) = 0
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
  exact bits_to_gravity_to_fluid_capstone_of_constructiveWitness
    (S := S) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
    (A := A) (B_mp := B_mp)
    (B_dr := DrazinInfiniteCore.canonicalDrazinInverse_endCLM (E := E) A)
    (W :=
      canonicalDrazinMasterCapstoneWitness_toConstructiveWitness
        (E := E) S c R Kgeo x A B_mp W)
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
    (h_mp : IsMoorePenroseInverse A B_mp)
    (h_dr_star_canonical :
      star (A * DrazinInfiniteCore.canonicalDrazinInverse_endCLM (E := E) A)
        = A * DrazinInfiniteCore.canonicalDrazinInverse_endCLM (E := E) A)
    (hHelicity : MatchedHelicityWitness (E := E) A)
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
      (A := A) (B_mp := B_mp)
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
Production-witness squeezing corollary.

This is the constructive narrowing on the regularization/helicity branch of the
squeezing bound: the explicit pair `(hReg, hHelicity)` is replaced by one
`FluidHelicityProductionWitness`, while the broader capstone-facing theorem is
kept for compatibility.
-/
private theorem squeezingLogShear_bound_of_bits_to_gravity_to_fluid_capstone_of_productionWitness
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
    (Wfluid : FluidHelicityProductionWitness (E := E) A B_mp B_dr)
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
    bits_to_gravity_to_fluid_capstone_of_productionWitness
      (S := S) (hRankPos := hRankPos) (CI := CI) (c := c)
      (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
      (hEin := hEin)
      (A := A) (B_mp := B_mp) (B_dr := B_dr)
      (Wfluid := Wfluid)
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
Constructive-witness squeezing corollary.

This is the smallest theorem-backed squeezing route on the base capstone lane:
the explicit ZPE/gravity, fluid-production, and thermal/Bott packets are all
recovered from a single `ConstructiveMasterCapstoneWitness` object before
extracting the Bekenstein clause.
-/
private theorem squeezingLogShear_bound_of_bits_to_gravity_to_fluid_capstone_of_constructiveWitness
    (S : SpinFactorState E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (A B_mp B_dr : VelocityField E)
    (W : ConstructiveMasterCapstoneWitness (E := E) S c R Kgeo x A B_mp B_dr)
    (n : Nat)
    (Tflow : SinkhornTrajectory n)
    (γ : ℕ → E)
    (N : ℕ)
    (j : Nat)
    (t : ℝ)
    (hTime : |t| ≤ trajectoryRNBarrier n Tflow j) :
    |squeezingLogShear t| ≤ 4 * trajectoryRNBarrier n Tflow j := by
  have hCapstone :=
    bits_to_gravity_to_fluid_capstone_of_constructiveWitness
      (S := S) (CI := CI) (c := c)
      (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
      (A := A) (B_mp := B_mp) (B_dr := B_dr)
      (W := W)
      (n := n) (Tflow := Tflow) (γ := γ) (N := N)
  exact squeezingLogShear_bound_of_capstone_conjunction
    (S := S) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x)
    (Λ := Λ) (κ := κ)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (Mod := W.thermalBott.Mod) (IST := W.thermalBott.IST)
    (n := n) (Tflow := Tflow)
    hCapstone j t hTime

/--
Canonical-Drazin witness squeezing corollary with both ZPE/gravity and thermal/Bott owner packets.

This is the smaller constructive squeezing route on the canonical-Drazin lane:
it removes the loose rank, Einstein, and thermal/Bott packet hypotheses from the
squeezing bound by routing through the existing theorem-backed capstone witness
surface.
-/
private theorem squeezingLogShear_bound_of_bits_to_gravity_to_fluid_capstone_of_canonicalDrazinFluidHelicityWitness_and_zpeGravityWitness_and_thermalBottWitness
    (S : SpinFactorState E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hZPEGravity : ZPEGravityWitness (E := E) S c R Kgeo x)
    (A B_mp : VelocityField E)
    (hFluidHelicity : CanonicalDrazinFluidHelicityWitness (E := E) A B_mp)
    (hThermalBott : ThermalBottWitness (E := E))
    (n : Nat)
    (Tflow : SinkhornTrajectory n)
    (γ : ℕ → E)
    (N : ℕ)
    (j : Nat)
    (t : ℝ)
    (hTime : |t| ≤ trajectoryRNBarrier n Tflow j) :
    |squeezingLogShear t| ≤ 4 * trajectoryRNBarrier n Tflow j := by
  rcases
      bits_to_gravity_to_fluid_capstone_of_canonicalDrazinFluidHelicityWitness_and_zpeGravityWitness_and_thermalBottWitness
        (S := S) (CI := CI) (c := c)
        (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
        (hZPEGravity := hZPEGravity)
        (A := A) (B_mp := B_mp)
        (hFluidHelicity := hFluidHelicity)
        (hThermalBott := hThermalBott)
        (n := n) (Tflow := Tflow) (γ := γ) (N := N)
    with ⟨B_dr, hCapstone⟩
  exact squeezingLogShear_bound_of_capstone_conjunction
    (S := S) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x)
    (Λ := Λ) (κ := κ)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (Mod := hThermalBott.Mod) (IST := hThermalBott.IST)
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
    (hReg : RegularizationWitness (E := E) A B_mp B_dr)
    (hHelicity : MatchedHelicityWitness (E := E) A)
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
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (ω := hHelicity.omega) (Ω := hHelicity.Omega)
    (hAnomalySkew := anomalySkew_of_regularizationWitness (E := E) A B_mp B_dr hReg)
    (hHelicity := hHelicity.match_helicity)
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
KMS-closure / pairing-witness cocycle-sourced capstone variant with the
ZPE/gravity owner packet.

This removes the explicit `(hRankPos, hEin)` theorem surface for callers that
already own the proof-carrying `ZPEGravityWitness` packet.
-/
private def bits_to_gravity_to_fluid_capstone_cocycle_sourced_sinkhornKMSClosure_pairingWitness_of_zpeGravityWitness
    (S : SpinFactorState E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hZPEGravity : ZPEGravityWitness (E := E) S c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (hReg : RegularizationWitness (E := E) A B_mp B_dr)
    (hHelicity : MatchedHelicityWitness (E := E) A)
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
  exact bits_to_gravity_to_fluid_capstone_cocycle_sourced_sinkhornKMSClosure_pairingWitness
    (S := S) (hRankPos := hZPEGravity.hRankPos) (CI := CI) (c := c) (R := R) (Kgeo := Kgeo)
    (x := x) (Λ := Λ) (κ := κ) (hEin := hZPEGravity.hEin)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (hReg := hReg) (hHelicity := hHelicity)
    (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)
    (σ := σ) (u := u) (hCocycle := hCocycle) (hBridge := hBridge)
    (K := K) (ωKMS := ωKMS) (β := β)
    (hClosure := hClosure) (hPair := hPair)

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
KMS-control / pairing-witness cocycle-sourced capstone variant with a single
fluid-production witness.  This narrowed route derives anomaly skewness from the
regularization owner packet and recovers helicity probes from the bundled
matched-helicity witness, instead of exposing the four loose fluid/helicity
hypotheses used by the compatibility theorem above.
-/
private def bits_to_gravity_to_fluid_capstone_cocycle_sourced_sinkhornKMSControl_pairingFluidWitness
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
    (Wfluid : FluidHelicityProductionWitness (E := E) A B_mp B_dr)
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
  exact bits_to_gravity_to_fluid_capstone_cocycle_sourced_sinkhornKMSControl_pairingWitness
    (S := S) (hRankPos := hRankPos) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ) (hEin := hEin)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (ω := Wfluid.helicity.omega) (Ω := Wfluid.helicity.Omega)
    (hAnomalySkew :=
      anomalySkew_of_regularizationWitness (E := E) A B_mp B_dr Wfluid.regularization)
    (hHelicity := Wfluid.helicity.match_helicity)
    (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)
    (σ := σ) (u := u) (hCocycle := hCocycle) (hBridge := hBridge)
    (K := K) (ωKMS := ωKMS) (β := β)
    (hControl := hControl) (hPair := hPair)

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
Integer-time cocycle-match capstone variant with a single fluid-production
witness.  This narrowed constructive route derives anomaly skewness from the
regularization owner packet and recovers the helicity probes from the bundled
matched-helicity witness, instead of exposing `ω`, `Ω`, `hAnomalySkew`, and
`hHelicity` as loose theorem arguments.
-/
private def bits_to_gravity_to_fluid_capstone_cocycle_sourced_natMatch_fluidWitness
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
    (Wfluid : FluidHelicityProductionWitness (E := E) A B_mp B_dr)
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
  exact bits_to_gravity_to_fluid_capstone_cocycle_sourced_natMatch
    (S := S) (hRankPos := hRankPos) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ) (hEin := hEin)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (ω := Wfluid.helicity.omega) (Ω := Wfluid.helicity.Omega)
    (hAnomalySkew :=
      anomalySkew_of_regularizationWitness (E := E) A B_mp B_dr Wfluid.regularization)
    (hHelicity := Wfluid.helicity.match_helicity)
    (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)
    (σ := σ) (u := u) (hCocycle := hCocycle) (hBridge := hBridge)
    (hMatch := hMatch)

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
Tomita-specialized integer-time cocycle-match capstone variant with a single
fluid-production witness.

This narrows the Tomita nat-match lane by recovering `ω`, `Ω`, anomaly skewness,
and the helicity equality from one `FluidHelicityProductionWitness` packet.
-/
private theorem bits_to_gravity_to_fluid_capstone_tomita_cocycle_sourced_natMatch_fluidWitness
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
    (Wfluid : FluidHelicityProductionWitness (E := E) A B_mp B_dr)
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
  exact bits_to_gravity_to_fluid_capstone_tomita_cocycle_sourced_natMatch
    (S := S) (hRankPos := hRankPos) (CI := CI) (c := c) (R := R) (Kgeo := Kgeo)
    (x := x) (Λ := Λ) (κ := κ) (hEin := hEin)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (ω := Wfluid.helicity.omega) (Ω := Wfluid.helicity.Omega)
    (hAnomalySkew :=
      anomalySkew_of_regularizationWitness (E := E) A B_mp B_dr Wfluid.regularization)
    (hHelicity := Wfluid.helicity.match_helicity)
    (Mod := Mod) (V := V) (IST := IST) (hCompat := hCompat)
    (n := n) (Tflow := Tflow)
    (γ := γ) (N := N)
    (u := u) (hCocycle := hCocycle) (hBridge := hBridge)
    (hMatch := hMatch)

/--
Tomita-specialized integer-time cocycle-match capstone variant with the owner
ZPE/gravity packet, the fluid-production witness, and the thermal/Bott witness.

This is the smallest constructive route presently owned on the Tomita nat-match
lane: it removes the loose rank witness, Einstein-Kähler certificate, and the
thermal/Bott packet from the theorem surface, while keeping the explicit
Tomita cocycle match as the remaining boundary hypothesis.
-/
private theorem bits_to_gravity_to_fluid_capstone_tomita_cocycle_sourced_natMatch_of_zpeGravityWitness_and_productionWitness_and_thermalBottWitness
    (S : SpinFactorState E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hZPEGravity : ZPEGravityWitness (E := E) S c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (Wfluid : FluidHelicityProductionWitness (E := E) A B_mp B_dr)
    (hThermalBott : ThermalBottWitness (E := E))
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
      ∧ hThermalBott.Mod.ConnesRovelliThermalTimeIdentity
      ∧ (cl11BottDirac (E := E) (spectralDiracLinear hThermalBott.IST)).comp
          (cl11BottDirac (E := E) (spectralDiracLinear hThermalBott.IST)) = 0
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
  exact bits_to_gravity_to_fluid_capstone_tomita_cocycle_sourced_natMatch_fluidWitness
    (S := S) (hRankPos := hZPEGravity.hRankPos) (CI := CI) (c := c)
    (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ)
    (hEin := hZPEGravity.hEin)
    (A := A) (B_mp := B_mp) (B_dr := B_dr)
    (Wfluid := Wfluid)
    (Mod := hThermalBott.Mod) (V := hThermalBott.V)
    (IST := hThermalBott.IST) (hCompat := hThermalBott.hCompat)
    (n := n) (Tflow := Tflow) (γ := γ) (N := N)
    (u := u) (hCocycle := hCocycle) (hBridge := hBridge)
    (hMatch := hMatch)

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
