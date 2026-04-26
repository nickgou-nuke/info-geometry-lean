import InfoGeometry.Canonical.DrazinCoreFlow
import InfoGeometry.Canonical.DrazinInfiniteCore
import InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge
import InfoGeometry.Canonical.RindlerWedgeCartanBridge
import InfoGeometry.Canonical.RealBdG
import InfoGeometry.Canonical.DrazinWeylConstructive
import InfoGeometry.Core.MajoranaLiftPacket
import InfoGeometry.Canonical.UnifiedTopologicalGapBridge
import InfoGeometry.Canonical.OperatorialHessianBridge
import InfoGeometry.Canonical.FierzStressProjectionBridge
import InfoGeometry.Canonical.SuperSouriauFermionGasBridge
import InfoGeometry.Canonical.JaynesRNMaxEnt
import InfoGeometry.Canonical.PrimeGasMaxEnt
import InfoGeometry.Canonical.KleinBottleOrientifold
import InfoGeometry.Canonical.PrimeGeodesicEmergence
import InfoGeometry.Canonical.WindingOrbitClosure
import InfoGeometry.Convex.SelfDualCone
import InfoGeometry.Clifford.HestenesDirac
import InfoGeometry.MaxEnt.Core
import Mathlib

/-!
# InfoGeometry.Canonical.OpenProblemFormalization

Lean-side formalization surface extracted from `open_problem.md`.

Design:
- Prove the fully algebraic lemmas that are already kernel-safe.
- Re-export Drazin-core lemmas from owner modules under open-problem names.
- Register theorem-shaped frontier claims as typed axioms.
-/

namespace InfoGeometry.Canonical.OpenProblemFormalization

section PTLane

variable {G : Type*} [Group G]

/-- L1: parity involution law. -/
lemma parity_is_involution (P : G) (hP : P * P = 1) : P ^ 2 = 1 := by
  simpa [pow_two] using hP

/-- L2: time-reversal involution law. -/
lemma time_reversal_is_involution (T : G) (hT : T * T = 1) : T ^ 2 = 1 := by
  simpa [pow_two] using hT

/-- L3: explicit commuting witness for parity and time reversal. -/
lemma parity_time_commute (P T : G) (hPT : P * T = T * P) :
    P * T = T * P := hPT

/-- L4: if `P² = 1`, `T² = 1`, and `PT = TP`, then `(PT)² = 1`. -/
lemma parity_time_product_is_involution
    (P T : G)
    (hP : P * P = 1)
    (hT : T * T = 1)
    (hPT : P * T = T * P) :
    (P * T) ^ 2 = 1 := by
  calc
    (P * T) ^ 2 = (P * T) * (P * T) := by simp [pow_two]
    _ = P * (T * P) * T := by simp [mul_assoc]
    _ = P * (P * T) * T := by rw [hPT]
    _ = (P * P) * (T * T) := by simp [mul_assoc]
    _ = 1 := by simp [hP, hT]

/-- L20: orbits under finite group actions are finite sets. -/
lemma finite_group_orbits_are_finite
    {α : Type*} [MulAction G α] [Finite G] (x : α) :
    (MulAction.orbit G x).Finite := by
  classical
  simpa [MulAction.orbit] using
    (Set.finite_range (fun g : G => g • x))

/-- L22 helper: a period witness quantizes to a unit power constraint. -/
lemma periodic_flow_quantization_helper
    (g : G) (n : ℕ) (hperiod : g ^ n = 1) :
    (g ^ n) ^ 2 = 1 := by
  simp [hperiod]

end PTLane

section DrazinAliases

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse

variable {R : Type*} [Ring R] {a b : R} {k : ℕ}

/-- L8 alias: the Drazin projector `Π = 1 - a*b` is idempotent. -/
lemma drazin_projector_idempotent
    (h : IsDrazinInverse a b k) :
    complementaryProjection a b * complementaryProjection a b =
      complementaryProjection a b :=
  complementaryProjection_is_idempotent (h := h)

end DrazinAliases

section LinearDrazinCoreAliases

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
variable {A D : Module.End K V} {k : ℕ}

/-- L10 alias: projector range equals the generalized-kernel Drazin core. -/
lemma drazin_projector_range_eq_core
    (h : IsDrazinInverse A D k) :
    LinearMap.range (complementaryProjection A D) = drazinCore A k :=
  InfoGeometry.Canonical.Drazin.IsDrazinInverse.drazin_projector_range_eq_core (h := h)

/-- L11 alias: dissipation vanishes on the Drazin core. -/
lemma dissipation_vanishes_on_drazin_core
    {ψ : V} (hψ : ψ ∈ drazinCore A k) :
    (A ^ k) ψ = 0 :=
  InfoGeometry.Canonical.Drazin.IsDrazinInverse.dissipation_vanishes_on_drazinCore (hψ := hψ)

end LinearDrazinCoreAliases

section InfiniteDimensionalAliases

open InfoGeometry.Canonical.DrazinInfiniteCore

variable {𝕂 E : Type*}
variable [NormedField 𝕂]
variable [NormedAddCommGroup E] [NormedSpace 𝕂 E]

/--
Infinite-dimensional Riesz lane: the public classical Riesz package yields a
canonical Drazin witness without any finite-dimensional reduction.
-/
lemma riesz_decomposition_yields_drazin_inverse
    {T : E →L[𝕂] E}
    (hR : HasClassicalRieszDecompositionAtZero (𝕂 := 𝕂) T) :
    ∃ k TD, InfoGeometry.Canonical.Drazin.IsDrazinInverse T TD k :=
  exists_drazinInverse_of_rieszDecomposition (h := hR)

/--
Alias for the infinite-dimensional Riesz-to-Drazin owner theorem on the same
carrier.
-/
lemma classical_riesz_decomposition_yields_drazin_inverse
    {T : E →L[𝕂] E}
    (hR : HasClassicalRieszDecompositionAtZero (𝕂 := 𝕂) T) :
    ∃ k TD, InfoGeometry.Canonical.Drazin.IsDrazinInverse T TD k :=
  riesz_decomposition_yields_drazin_inverse (hR := hR)

end InfiniteDimensionalAliases

section DrazinBPSAliases

open InfoGeometry.Canonical.TopologicalGapShadow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Owner-backed infinite-dimensional Drazin/BPS correspondence packet.

This is the constructive replacement for the frontier hypothesis surface:
on the protected Drazin core, the SUSY hopping operator annihilates the state
and its entropy-production readout vanishes.
-/
theorem drazin_core_bps_correspondence_packet
    (Q : E →L[ℝ] E) :
    (∀ {ψ : E}, ψ ∈ DrazinCore Q → susyHoppingOperator Q ψ = 0)
      ∧
    (∀ ψ : E, ψ ∈ DrazinCore Q → ‖(susyHoppingOperator Q) ψ‖ = 0) := by
  exact topological_gap_shadow_packet (Q := Q)

end DrazinBPSAliases

section SpectralPeriodicity

open scoped InnerProductSpace

variable {H : Type 0} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "EndH" => InfoGeometry.Krein.DoubledSpace H →L[ℝ] InfoGeometry.Krein.DoubledSpace H

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/--
Infinite-dimensional periodicity owner: detailed equilibrium on the modular
transport seed yields exact winding-periodic exponential closure on the doubled
carrier.
-/
lemma periodic_orbit_discrete_generator_spectrum
    (hMod : EndH)
    (N : ℤ)
    (hEq : InfoGeometry.Canonical.WindingOrbitClosure.IsDetailedEquilibriumSeed (H := H) hMod) :
    NormedSpace.exp
      (InfoGeometry.Canonical.WindingOrbitClosure.multiBranchedGenerator
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) N) =
      NormedSpace.exp
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) :=
  InfoGeometry.Canonical.WindingOrbitClosure.winding_orbit_periodicity_of_detailedEquilibrium
    (H := H) hMod N hEq

end SpectralPeriodicity

section SelfDualAliases

open InfoGeometry.Convex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Infinite-dimensional self-dual owner alias: the cone equals its inner dual on
the Hilbert carrier.
-/
lemma self_dual_cone_equals_inner_dual (C : SelfDualCone E) :
    ProperCone.innerDual (C.cone : Set E) = C.cone :=
  C.innerDual_eq

end SelfDualAliases

section RealBdGAliases

open InfoGeometry.Krein
open InfoGeometry.Canonical.RealBdG
open InfoGeometry.Core

variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Owner-backed real BdG root packet.

This is the real-operator formulation of the "bDg" lane: the phase axis is the
real modular `K = J ∘ ε`, and the canonical Majorana lift records the same root
laws on the doubled carrier.
-/
theorem real_bdg_owner_packet_root_laws :
    let P := canonicalMajoranaLiftPacket (E := E)
    P.J = modular_j (E := E)
      ∧ P.eps = spectral_epsilon (E := E)
      ∧ P.K = complex_i (E := E)
      ∧ P.K.comp P.K = -(ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E)) := by
  exact canonicalMajoranaLiftPacket_root_laws (E := E)

/-- The real BdG phase axis is the modular `K` axis, not an abstract scalar `i`. -/
theorem real_bdg_complexI_is_modularK :
    modularK (E := E) = complex_i (E := E) := by
  exact modularK_eq_complex_i (E := E)

end RealBdGAliases

section ConcreteFourByFourAliases

open InfoGeometry.Clifford.HestenesDirac

/-- Concrete biquaternion/Minkowski 4×4 realization packaged for the open-problem lane. -/
def concrete_real_four_by_four_biquaternion_slice
    (c : MinkowskiCoordinates) :
    RealFourByFourBiquaternionSlice RealMatrix4 :=
  concreteBiquaternionSlice c

/-- Concrete Majorana/BdG 4×4 realization packaged for the open-problem lane. -/
def concrete_majorana_bdg_four_by_four
    (a : MajoranaBdGCoordinates) :
    MajoranaBdGFourByFour RealMatrix4 :=
  concreteMajoranaBdGFourByFour a

/-- Concrete Pfaffian bridge between the biquaternion and BdG real slices. -/
def concrete_real_pfaffian_bridge
    (c : MinkowskiCoordinates) (a : MajoranaBdGCoordinates) :
    RealPfaffianBridge RealMatrix4 where
  biquaternionSlice := concreteBiquaternionSlice c
  majoranaBdG := concreteMajoranaBdGFourByFour a
  biquaternionNull := (concreteBiquaternionSlice c).pfaffianSJ = 0
  bdgZeroMode := (concreteMajoranaBdGFourByFour a).pfaffian
    (concreteMajoranaBdGFourByFour a).bdgMatrix = 0
  pfaffian_bridge := by
    rfl

end ConcreteFourByFourAliases

section OwnerBackedInfinitePackets

open InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge
open InfoGeometry.Canonical.RindlerWedgeCartanBridge
open InfoGeometry.Canonical.DrazinWeylConstructive
open InfoGeometry.Canonical.DrazinInfiniteCore
open InfoGeometry.Volume.ConnesCocycle

open scoped InnerProductSpace

variable {H : Type 0} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "Obs" => InfoGeometry.Volume.ConnesCocycle.AlgebraEnd H
local notation "H₂" => InfoGeometry.Krein.DoubledSpace H
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/--
Constructive Souriau/KMS/Fisher packet on the infinite operator-algebraic
branch.  This is the owner-backed replacement for the abstract KMS/Weyl
surface: the cyclic state, identity modular flow, SLD symmetry, and identity
Weyl gauge are all proved from the existing bridge modules.
-/
lemma cyclic_observable_constructive_packet
    {Symmetry : Type}
    {Tangent : Type}
    (C : CyclicCoordinatelessSouriauFisherContext (H := H) Symmetry Tangent)
    (A B : Obs) (X Y : Tangent) :
    C.state.state.eval 1 = 1 ∧
    C.state.state.eval (A * C.sigma C.beta B) = C.state.state.eval (B * A) ∧
    C.souriauMoment.thermalGenerator =
      C.souriauMoment.momentOperator C.souriauMoment.geometricTemperature ∧
    C.fisherMetric.metric X Y = C.fisherMetric.metric Y X ∧
    C.state.state.eval (C.weylGauge.gauge A) = C.state.state.eval A :=
  C.coordinateless_constructive_packet A B X Y

/- Constructive self-dual Rindler wedge packet on the infinite doubled
carrier.  This packages the left-right wedge exchange and the involutive swap
as an explicit proof-carrying structure rather than a bare conjecture. -/
structure SelfDualRindlerWedgeExchangePacket
    (W : InfoGeometry.Canonical.RindlerWedgeCartanBridge.SelfDualRindlerWedge H)
    (A : EndH) where
  left_wedge_mem_iff_right_wedge :
    A ∈ W.standardForm.swapLeftRight.leftAlgebra ↔ A ∈ W.standardForm.rightAlgebra
  right_wedge_mem_iff_left_wedge :
    A ∈ W.standardForm.swapLeftRight.rightAlgebra ↔ A ∈ W.standardForm.leftAlgebra
  swapLeftRight_involutive :
    W.standardForm.swapLeftRight.swapLeftRight = W.standardForm

/-- Constructive witness for the self-dual Rindler wedge exchange packet. -/
def self_dual_rindler_wedge_exchange_packet
    (W : InfoGeometry.Canonical.RindlerWedgeCartanBridge.SelfDualRindlerWedge H)
    (A : EndH) :
    SelfDualRindlerWedgeExchangePacket W A where
  left_wedge_mem_iff_right_wedge := W.left_wedge_mem_iff_right_wedge A
  right_wedge_mem_iff_left_wedge := W.right_wedge_mem_iff_left_wedge A
  swapLeftRight_involutive := W.swapLeftRight_involutive

lemma chiral_cartan_packet
    (C : InfoGeometry.Canonical.RindlerWedgeCartanBridge.ChiralCartanSplit H₂)
    {X Y : EndH}
    (hX : InfoGeometry.Canonical.ChiralOperatorConeClosure.IsInChiralOperatorCone C.CIK X)
    (hY : InfoGeometry.Canonical.ChiralOperatorConeClosure.IsInChiralOperatorCone C.CIK Y) :
    C.CIK.IsSpectralCompact (X * Y) ∧
      C.CIK.IsSpectralCompact
        (InfoGeometry.Canonical.CertifiedInverseKernel.spectralCommutator X Y) :=
  C.cartan_split_packet hX hY

end OwnerBackedInfinitePackets

section PrimeGasJaynesFrontier

open InfoGeometry.MaxEnt

/--
Discrete symmetry packet for the prime-occupation Jaynes problem.

The `V4` field is the primitive Klein-four reflection skeleton.  The tensor
flags record the possibility of independent product copies (`V4 × V4`,
`V4 × V4 × V4`) when the problem is replicated across multiple symmetry axes.
The Möbius/Klein fields record the nonorientable discrete twist separately
from the reflection skeleton.
-/
structure PrimeGasSymmetry where
  V4_Weyl : Prop
  V4_tensor_V4 : Prop
  V4_tensor_V4_tensor_V4 : Prop
  kleinBottleQuotient : Prop
  moebiusDiscreteTwist : Prop
  splitCl11Atom : Prop

/--
Explicit Jaynes problem surface for the prime-fermion gas.

This stays infinite and operatorially honest: the sample space, prior measure,
and linear constraints are all left explicit, while the symmetry data are
carried as hypotheses rather than being collapsed into a finite shadow model.
-/
structure PrimeGasJaynesData where
  Ω : Type*
  instMeasurableSpace : MeasurableSpace Ω
  μ₀ : MeasureTheory.Measure Ω
  energy : LinearConstraint Ω
  particleNumber : LinearConstraint Ω
  symmetry : PrimeGasSymmetry
  idealFermionGas : Prop
  primeOccupationLogEnergy : Prop
  eulerProductPartition : Prop

/--
The prime-gas Jaynes problem: maximize entropy on the explicit prime-occupation
constraint surface, with the discrete Klein/Weyl/Möbius symmetry package kept
as a separate hypothesis block.

The expected mathematical conclusion, not proved here, is the Gibbs/Fermi-Dirac
maximizer together with the Euler-product partition function
`∏ p, (1 + e^{-α} p^{-β})`.  That analytic target remains debt until a countable
or product-measure substrate is owned.
-/
def PrimeGasJaynesConjecture (D : PrimeGasJaynesData) : Prop :=
  by
    letI : MeasurableSpace D.Ω := D.instMeasurableSpace
    let μ₀ : MeasureTheory.Measure D.Ω := D.μ₀
    exact
      ∃ P : ACProbMeasure μ₀,
        IsMaxEntSolution (μ₀ := μ₀)
          ({D.energy, D.particleNumber} : Set (LinearConstraint D.Ω)) P ∧
        D.symmetry.V4_Weyl ∧
        D.symmetry.V4_tensor_V4 ∧
        D.symmetry.V4_tensor_V4_tensor_V4 ∧
        D.symmetry.kleinBottleQuotient ∧
        D.symmetry.moebiusDiscreteTwist ∧
        D.symmetry.splitCl11Atom ∧
        D.idealFermionGas ∧
        D.primeOccupationLogEnergy ∧
        D.eulerProductPartition

end PrimeGasJaynesFrontier

section PrimeGasOperatorialFierzFrontier

open InfoGeometry.Canonical.FierzStressProjectionBridge
open InfoGeometry.Quantum.Fierz
open InfoGeometry.Krein

/--
Prime-gas / operatorial Fierz packet.

This keeps the Jaynes prime-occupation problem and the doubled-carrier Fierz
readout separate, while forcing the bridge to stay explicit: the prime side is
still a conjectural Jaynes packet, and the operatorial side is the owned
Fierz-stress projection context.
-/
structure PrimeGasOperatorialFierzPacket where
  gas : PrimeGasJaynesData
  jaynes : PrimeGasJaynesConjecture gas
  E : Type
  instNormedAddCommGroup : NormedAddCommGroup E
  instInnerProductSpace : InnerProductSpace ℝ E
  instCompleteSpace : CompleteSpace E
  fierz : FierzStressProjectionContext (E := E)
  X : DoubledSpace E →L[ℝ] DoubledSpace E
  A : DoubledSpace E →L[ℝ] DoubledSpace E
  majoranaShadow :
    IsMajoranaBelief
      (fierz.projectedState
        (InfoGeometry.Canonical.OperatorialHessianBridge.operatorInformationHessian
          (E := E) X A))

namespace PrimeGasOperatorialFierzPacket

/--
The precise current bridge theorem: a bundled prime-gas Jaynes packet may be
routed into the operatorial Fierz projection lane only through an explicit
`FierzStressProjectionContext`.  The conclusion is the owned doubled-carrier
Fierz channel identity for the projected operatorial Hessian; it is not a proof
of the analytic Bost--Connes/KMS/RH problem and not a scalar shadow theorem.
-/
theorem projectedStress_fierz_identity
    (P : PrimeGasOperatorialFierzPacket) :
    letI : NormedAddCommGroup P.E := P.instNormedAddCommGroup
    letI : InnerProductSpace ℝ P.E := P.instInnerProductSpace
    letI : CompleteSpace P.E := P.instCompleteSpace
    (P.fierz.projectedStressReadout
        (InfoGeometry.Canonical.OperatorialHessianBridge.operatorInformationHessian
          (E := P.E) P.X P.A)) ^ (2 : ℕ) =
      (infoScalar
        (E := P.E)
        (P.fierz.projectedState
          (InfoGeometry.Canonical.OperatorialHessianBridge.operatorInformationHessian
            (E := P.E) P.X P.A))) ^ (2 : ℕ)
        + (infoSymplectic
          (E := P.E)
          (P.fierz.projectedState
            (InfoGeometry.Canonical.OperatorialHessianBridge.operatorInformationHessian
              (E := P.E) P.X P.A))) ^ (2 : ℕ)
        + 4 *
          infoArea
            (E := P.E)
            (P.fierz.projectedState
              (InfoGeometry.Canonical.OperatorialHessianBridge.operatorInformationHessian
                (E := P.E) P.X P.A)) := by
  letI : NormedAddCommGroup P.E := P.instNormedAddCommGroup
  letI : InnerProductSpace ℝ P.E := P.instInnerProductSpace
  letI : CompleteSpace P.E := P.instCompleteSpace
  exact P.fierz.operatorInformationHessian_projectedStress_fierz_identity P.X P.A

/--
Majorana/zero-area specialization of the same packet.  This is still purely
operatorial: the prime-gas Jaynes conjecture is carried as data, while the
proved equality is the Fierz readout identity on the doubled carrier.
-/
theorem projectedStress_majorana_identity
    (P : PrimeGasOperatorialFierzPacket) :
    letI : NormedAddCommGroup P.E := P.instNormedAddCommGroup
    letI : InnerProductSpace ℝ P.E := P.instInnerProductSpace
    letI : CompleteSpace P.E := P.instCompleteSpace
    (P.fierz.projectedStressReadout
        (InfoGeometry.Canonical.OperatorialHessianBridge.operatorInformationHessian
          (E := P.E) P.X P.A)) ^ (2 : ℕ) =
      (infoScalar
        (E := P.E)
        (P.fierz.projectedState
          (InfoGeometry.Canonical.OperatorialHessianBridge.operatorInformationHessian
            (E := P.E) P.X P.A))) ^ (2 : ℕ)
        + (infoSymplectic
          (E := P.E)
          (P.fierz.projectedState
            (InfoGeometry.Canonical.OperatorialHessianBridge.operatorInformationHessian
              (E := P.E) P.X P.A))) ^ (2 : ℕ) := by
  letI : NormedAddCommGroup P.E := P.instNormedAddCommGroup
  letI : InnerProductSpace ℝ P.E := P.instInnerProductSpace
  letI : CompleteSpace P.E := P.instCompleteSpace
  exact P.fierz.operatorInformationHessian_projectedStress_majorana_identity P.X P.A P.majoranaShadow

end PrimeGasOperatorialFierzPacket

end PrimeGasOperatorialFierzFrontier

section PrimeGasJaynesOnsagerBridge

open scoped BigOperators
open InfoGeometry.Canonical.JaynesRNMaxEnt
open InfoGeometry.Canonical.FierzStressProjectionBridge
open InfoGeometry.Quantum.Fierz
open InfoGeometry.Krein

/--
MaxEnt packet for the prime-gas lane.

This is the strict measure-theoretic owner surface used to route the prime
occupation program through `MaxEnt.Core` while keeping analytic number-theory
claims explicit and quarantined as hypotheses.
-/
structure PrimeGasMaxEntPacket where
  data : PrimeGasJaynesData
  priorIsProbability : by
    letI : MeasurableSpace data.Ω := data.instMeasurableSpace
    exact MeasureTheory.IsProbabilityMeasure data.μ₀
  candidate : by
    letI : MeasurableSpace data.Ω := data.instMeasurableSpace
    exact InfoGeometry.MaxEnt.ACProbMeasure data.μ₀
  maxEnt : by
    letI : MeasurableSpace data.Ω := data.instMeasurableSpace
    exact InfoGeometry.MaxEnt.IsMaxEntSolution (μ₀ := data.μ₀)
      ({data.energy, data.particleNumber} : Set (InfoGeometry.MaxEnt.LinearConstraint data.Ω)) candidate
  primeLogEnergyHypothesis : data.primeOccupationLogEnergy
  eulerProductHypothesis : data.eulerProductPartition

namespace PrimeGasMaxEntPacket

/-- Convert an `ACProbMeasure` witness into a `ProbabilityMeasure` witness. -/
noncomputable def toProbabilityMeasure (M : PrimeGasMaxEntPacket) : by
    letI : MeasurableSpace M.data.Ω := M.data.instMeasurableSpace
    exact MeasureTheory.ProbabilityMeasure M.data.Ω := by
  letI : MeasurableSpace M.data.Ω := M.data.instMeasurableSpace
  exact ⟨M.candidate.μ, ⟨M.candidate.prob⟩⟩

end PrimeGasMaxEntPacket

/--
Bridge predicate from the `MaxEnt.Core` prime packet to the Jaynes RN interface.

The bridge is intentionally conservative: it records the existence of a
finite-observable Jaynes façade (`MomentFamily`) and leaves Euler-product
identities as explicit hypotheses.
-/
def PrimeGasJaynesRNBridge (M : PrimeGasMaxEntPacket) : Prop := by
  letI : MeasurableSpace M.data.Ω := M.data.instMeasurableSpace
  let μ₀ : MeasureTheory.Measure M.data.Ω := M.data.μ₀
  letI : MeasureTheory.IsProbabilityMeasure μ₀ := M.priorIsProbability
  exact
    ∃ (ι : Type*) (_ : Fintype ι)
      (C : MomentFamily (Ω := M.data.Ω) ι)
      (lam : ι → ℝ),
      PartitionIntegrable (μ₀ := μ₀) (C := C) lam ∧
      M.data.primeOccupationLogEnergy ∧
      M.data.eulerProductPartition

/--
Onsager linear-response packet inside the modular-flow lane.

`transportMatrix` is the response operator, `thermodynamicForce` the force lane,
and `thermodynamicFlux` the flux lane. `reciprocal` enforces Onsager symmetry.
-/
structure OnsagerReciprocalFlow (ι : Type*) [Fintype ι] where
  thermodynamicForce : ι → ℝ
  thermodynamicFlux : ι → ℝ
  transportMatrix : ι → ι → ℝ
  flux_linear_response :
    ∀ i, thermodynamicFlux i = ∑ j, transportMatrix i j * thermodynamicForce j
  reciprocal : ∀ i j, transportMatrix i j = transportMatrix j i

/--
Prime-gas bridge packet tying
1. Jaynes MaxEnt prime packet,
2. explicit Jaynes-RN bridge witness,
3. Onsager reciprocal flow,
4. operatorial Fierz projected-stress lane.

The bridge remains theorem-honest: no Euler-product/RH theorem is claimed.
-/
structure PrimeGasOnsagerFierzBridge where
  packet : PrimeGasOperatorialFierzPacket
  maxEntPacket : PrimeGasMaxEntPacket
  jaynesRNBridge : PrimeGasJaynesRNBridge maxEntPacket
  ι : Type
  instFintype : Fintype ι
  onsager : @OnsagerReciprocalFlow ι instFintype
  stressMode : ι
  stressFluxMatchesProjectedHessian : by
    letI : NormedAddCommGroup packet.E := packet.instNormedAddCommGroup
    letI : InnerProductSpace ℝ packet.E := packet.instInnerProductSpace
    letI : CompleteSpace packet.E := packet.instCompleteSpace
    let _ : Fintype ι := instFintype
    exact
      packet.fierz.projectedStressReadout
          (InfoGeometry.Canonical.OperatorialHessianBridge.operatorInformationHessian
            (E := packet.E) packet.X packet.A)
        = onsager.thermodynamicFlux stressMode

namespace PrimeGasOnsagerFierzBridge

/--
Projected-stress Fierz identity routed through the Onsager flux lane.

This is the conservative bridge theorem requested by the prime-gas program:
- the Jaynes/Euler side remains an explicit hypothesis packet;
- the proved equality is exactly the owned operatorial Fierz identity, rewritten
  through the declared Onsager stress-flux readout.
-/
theorem onsager_projectedStress_fierz_identity
    (B : PrimeGasOnsagerFierzBridge) :
    letI : NormedAddCommGroup B.packet.E := B.packet.instNormedAddCommGroup
    letI : InnerProductSpace ℝ B.packet.E := B.packet.instInnerProductSpace
    letI : CompleteSpace B.packet.E := B.packet.instCompleteSpace
    letI : Fintype B.ι := B.instFintype
    (B.onsager.thermodynamicFlux B.stressMode) ^ (2 : ℕ) =
      (infoScalar
        (E := B.packet.E)
        (B.packet.fierz.projectedState
          (InfoGeometry.Canonical.OperatorialHessianBridge.operatorInformationHessian
            (E := B.packet.E) B.packet.X B.packet.A))) ^ (2 : ℕ)
        + (infoSymplectic
          (E := B.packet.E)
          (B.packet.fierz.projectedState
            (InfoGeometry.Canonical.OperatorialHessianBridge.operatorInformationHessian
              (E := B.packet.E) B.packet.X B.packet.A))) ^ (2 : ℕ)
        + 4 *
          infoArea
            (E := B.packet.E)
            (B.packet.fierz.projectedState
              (InfoGeometry.Canonical.OperatorialHessianBridge.operatorInformationHessian
                (E := B.packet.E) B.packet.X B.packet.A)) := by
  letI : NormedAddCommGroup B.packet.E := B.packet.instNormedAddCommGroup
  letI : InnerProductSpace ℝ B.packet.E := B.packet.instInnerProductSpace
  letI : CompleteSpace B.packet.E := B.packet.instCompleteSpace
  let _ : Fintype B.ι := B.instFintype
  simpa [B.stressFluxMatchesProjectedHessian] using
    PrimeGasOperatorialFierzPacket.projectedStress_fierz_identity B.packet

/--
KMS-target packet for routing the Onsager/Jaynes bridge into the
`SuperSouriauFermionGasBridge` temperature lane.

This keeps the odd temperature branch explicit and allows a strict zero-odd
specialization while preserving the already-proved operatorial Fierz identity.
-/
structure PrimeGasKMSTargetBridge where
  bridge : PrimeGasOnsagerFierzBridge
  betaMode : bridge.ι
  betaOdd : ℝ
  betaOdd_eq_zero : betaOdd = 0

/--
Read the Onsager force mode as a `SuperGeometricTemperature` target.
-/
def toSuperGeometricTemperature
    (K : PrimeGasKMSTargetBridge) :
    InfoGeometry.Canonical.SuperSouriauFermionGasBridge.SuperGeometricTemperature := by
  letI : Fintype K.bridge.ι := K.bridge.instFintype
  exact
    { betaEven := K.bridge.onsager.thermodynamicForce K.betaMode
      betaOdd := K.betaOdd }

theorem toSuperGeometricTemperature_zero_odd
    (K : PrimeGasKMSTargetBridge) :
    (toSuperGeometricTemperature K).betaOdd = 0 := by
  simp [toSuperGeometricTemperature, K.betaOdd_eq_zero]

/--
The KMS-target wrapper preserves the Onsager-routed operatorial Fierz identity.
-/
theorem kms_target_projectedStress_fierz_identity
    (K : PrimeGasKMSTargetBridge) :
    letI : NormedAddCommGroup K.bridge.packet.E := K.bridge.packet.instNormedAddCommGroup
    letI : InnerProductSpace ℝ K.bridge.packet.E := K.bridge.packet.instInnerProductSpace
    letI : CompleteSpace K.bridge.packet.E := K.bridge.packet.instCompleteSpace
    letI : Fintype K.bridge.ι := K.bridge.instFintype
    (K.bridge.onsager.thermodynamicFlux K.bridge.stressMode) ^ (2 : ℕ) =
      (infoScalar
        (E := K.bridge.packet.E)
        (K.bridge.packet.fierz.projectedState
          (InfoGeometry.Canonical.OperatorialHessianBridge.operatorInformationHessian
            (E := K.bridge.packet.E) K.bridge.packet.X K.bridge.packet.A))) ^ (2 : ℕ)
        + (infoSymplectic
          (E := K.bridge.packet.E)
          (K.bridge.packet.fierz.projectedState
            (InfoGeometry.Canonical.OperatorialHessianBridge.operatorInformationHessian
              (E := K.bridge.packet.E) K.bridge.packet.X K.bridge.packet.A))) ^ (2 : ℕ)
        + 4 *
          infoArea
            (E := K.bridge.packet.E)
            (K.bridge.packet.fierz.projectedState
              (InfoGeometry.Canonical.OperatorialHessianBridge.operatorInformationHessian
                (E := K.bridge.packet.E) K.bridge.packet.X K.bridge.packet.A)) :=
  PrimeGasOnsagerFierzBridge.onsager_projectedStress_fierz_identity K.bridge

/--
Non-equilibrium Souriau-Lie thermodynamic packet over the Onsager operatorial
bridge. Entropy production is explicit and constrained only by the supplied
nonnegativity witness.
-/
structure NonEquilibriumSouriauLieThermo where
  bridge : PrimeGasOnsagerFierzBridge
  entropyProduction : ℝ
  entropyProduction_eq_flux_force : by
    letI : Fintype bridge.ι := bridge.instFintype
    exact entropyProduction =
      ∑ i : bridge.ι,
        bridge.onsager.thermodynamicFlux i * bridge.onsager.thermodynamicForce i
  entropyProduction_nonneg : 0 ≤ entropyProduction

/--
Tower of modular-operator derivations indexed by order.
-/
structure ModularDerivationTower (Obs : Type*) where
  derivation : ℕ → Obs → Obs

/--
Order-`N` b-operator form packet. The slots are indexed by derivation order.
-/
structure BOperatorFormN (Obs : Type*) where
  order : ℕ
  slot : ℕ → Obs

/--
Compatibility condition: the b-form slots agree with iterated modular
operator derivations up to the declared order.
-/
def isCompatibleWithModularTower
    {Obs : Type*}
    (B : BOperatorFormN Obs)
    (D : ModularDerivationTower Obs) : Prop :=
  ∀ k, k ≤ B.order → D.derivation k (B.slot 0) = B.slot k

/--
Higher-order Onsager operatorial packet extending the first-order response lane.
The higher-order transport tensors are explicit data; first-order recovery is
tracked as a separate compatibility witness.
-/
structure HigherOrderOnsagerOperatorialTheory where
  thermo : NonEquilibriumSouriauLieThermo
  maxOrder : ℕ
  higherOrderTransport : ℕ → thermo.bridge.ι → thermo.bridge.ι → ℝ
  firstOrder_agrees : by
    letI : Fintype thermo.bridge.ι := thermo.bridge.instFintype
    exact
      ∀ i j : thermo.bridge.ι,
        higherOrderTransport 1 i j = thermo.bridge.onsager.transportMatrix i j
  modularTower : by
    letI : NormedAddCommGroup thermo.bridge.packet.E := thermo.bridge.packet.instNormedAddCommGroup
    letI : InnerProductSpace ℝ thermo.bridge.packet.E := thermo.bridge.packet.instInnerProductSpace
    letI : CompleteSpace thermo.bridge.packet.E := thermo.bridge.packet.instCompleteSpace
    exact ModularDerivationTower
      (DoubledSpace thermo.bridge.packet.E →L[ℝ] DoubledSpace thermo.bridge.packet.E)
  bFormN : by
    letI : NormedAddCommGroup thermo.bridge.packet.E := thermo.bridge.packet.instNormedAddCommGroup
    letI : InnerProductSpace ℝ thermo.bridge.packet.E := thermo.bridge.packet.instInnerProductSpace
    letI : CompleteSpace thermo.bridge.packet.E := thermo.bridge.packet.instCompleteSpace
    exact BOperatorFormN
      (DoubledSpace thermo.bridge.packet.E →L[ℝ] DoubledSpace thermo.bridge.packet.E)
  bForm_modular_compatible : by
    letI : NormedAddCommGroup thermo.bridge.packet.E := thermo.bridge.packet.instNormedAddCommGroup
    letI : InnerProductSpace ℝ thermo.bridge.packet.E := thermo.bridge.packet.instInnerProductSpace
    letI : CompleteSpace thermo.bridge.packet.E := thermo.bridge.packet.instCompleteSpace
    exact isCompatibleWithModularTower bFormN modularTower

/--
The higher-order Onsager packet preserves the already-owned Fierz projected
stress identity on the first-order operatorial lane.
-/
theorem higher_order_projectedStress_fierz_identity
    (H : HigherOrderOnsagerOperatorialTheory) :
    letI : NormedAddCommGroup H.thermo.bridge.packet.E :=
      H.thermo.bridge.packet.instNormedAddCommGroup
    letI : InnerProductSpace ℝ H.thermo.bridge.packet.E :=
      H.thermo.bridge.packet.instInnerProductSpace
    letI : CompleteSpace H.thermo.bridge.packet.E :=
      H.thermo.bridge.packet.instCompleteSpace
    letI : Fintype H.thermo.bridge.ι := H.thermo.bridge.instFintype
    (H.thermo.bridge.onsager.thermodynamicFlux H.thermo.bridge.stressMode) ^ (2 : ℕ) =
      (infoScalar
        (E := H.thermo.bridge.packet.E)
        (H.thermo.bridge.packet.fierz.projectedState
          (InfoGeometry.Canonical.OperatorialHessianBridge.operatorInformationHessian
            (E := H.thermo.bridge.packet.E)
            H.thermo.bridge.packet.X
            H.thermo.bridge.packet.A))) ^ (2 : ℕ)
        + (infoSymplectic
          (E := H.thermo.bridge.packet.E)
          (H.thermo.bridge.packet.fierz.projectedState
            (InfoGeometry.Canonical.OperatorialHessianBridge.operatorInformationHessian
              (E := H.thermo.bridge.packet.E)
              H.thermo.bridge.packet.X
              H.thermo.bridge.packet.A))) ^ (2 : ℕ)
        + 4 *
          infoArea
            (E := H.thermo.bridge.packet.E)
            (H.thermo.bridge.packet.fierz.projectedState
              (InfoGeometry.Canonical.OperatorialHessianBridge.operatorInformationHessian
                (E := H.thermo.bridge.packet.E)
                H.thermo.bridge.packet.X
                H.thermo.bridge.packet.A)) :=
  PrimeGasOnsagerFierzBridge.onsager_projectedStress_fierz_identity H.thermo.bridge

end PrimeGasOnsagerFierzBridge

end PrimeGasJaynesOnsagerBridge

section FrontierConjectures

/-- OP3 scaffold: minimal modular-super-torus data package. -/
structure ModularSuperTorus where
  Δ_UV : ℝ
  Λ_IR : ℝ
  h_UV_pos : 0 < Δ_UV
  h_IR_bound : Δ_UV < Λ_IR

/-- OP12 scaffold: boost/rotation/scale readout triple. -/
structure Ternaform where
  boost : ℝ
  rotation : ℝ
  scale : ℝ

/-- A conservative typed universe for the open-problem registry.

The fields are intentionally predicates and readout maps, not fake
constructions.  They give OP1--OP33 a Lean type surface while preserving the
fact that the frontier implications remain open until owner modules provide
proofs.
-/
structure SpireStabilityData where
  SpinorField : Type*
  Operator : SpinorField → Type*
  VectorPart : Type*
  ObservableUniverse : Type*
  Resonance : Type*
  re : Resonance → ℝ
  MellinSpectrum : SpinorField → Set Resonance
  TernaformOf : SpinorField → Ternaform
  V4WeylCompatible : SpinorField → ModularSuperTorus → Prop
  DrazinCoreIsBPS : {Q : SpinorField} → Operator Q → Prop
  SatisfiesSouriauKMS : {Q : SpinorField} → Operator Q → Prop
  FierzVectorPart : SpinorField → VectorPart
  SouriauTemperature : SpinorField → VectorPart
  IsStable : {Q : SpinorField} → Operator Q → Prop
  CriticalSpectrum : SpinorField → Prop
  MaxEntPrimes : Prop
  RiemannHypothesis : Prop
  NoLabelCollision : Prop
  UniqueCosmology : Prop
  HistoryUnique : ObservableUniverse → Prop
  DarkEnergyPositive : ObservableUniverse → Prop
  DarkMatterSector : Type*
  DarkEnergySector : Type*
  moebiusV4Twist : DarkMatterSector → DarkEnergySector

variable (U : SpireStabilityData)

/--
Explicit frontier hypothesis package.

This replaces the previous global axioms with a local research surface.  The
names from `open_problem.md` remain visible, but they no longer inject
unproven facts into the kernel.
-/
structure FrontierHypotheses where
  V4_Weyl_Isomorphism : Prop
  V4_symmetry_forces_compactification : Prop
  microscopic_V4_induces_partition_modularity : Prop
  DrazinCore_BPS_Correspondence : Prop
  DrazinCore_zero_entropy : Prop
  DiracDrazin_well_posedness : Prop
  m_eff_anomaly_lock : Prop
  SouriauDiracDrazin_equivalence : Prop
  Souriau_KMS_BPS_Correspondence : Prop
  souriau_equilibrium_implies_riemann_zeros : Prop
  Ternaform_conformal_closure : Prop
  ConformalClosure_compact : Prop
  ternaform_closure_yields_riemann_resonances : Prop
  Fierz_spacetime_emergence : Prop
  Fierz_vector_equals_Souriau_temperature : Prop
  gravity_as_thermal_viscosity : Prop
  lie_orbit_quantization : Prop
  spinorial_mellin_transform_has_riemann_spectrum : Prop
  modular_inversion_forces_critical_line : Prop
  Riemann_BPS_Correspondence : Prop
  MaxEnt_RH_Equivalence : Prop
  arithmetic_cosmological_stability : Prop
  Spire_Stability_Unification : Prop
  CollisionResistance_RH : Prop
  identity_preserved : Prop
  FTA_RH_topological_equivalence : Prop
  dark_energy_is_modular_remainder : Prop
  dark_energy_density_scaling : Prop
  central_charge_calibration : Prop
  dark_energy_prevents_collision : Prop
  arithmetic_big_bang_is_bayesian_update : Prop
  MoebiusV4_dark_matter_dark_energy_swap : Prop

/--
Consolidated capstone statement from `open_problem.md`, recorded as a theorem
shape rather than asserted globally.
-/
def SpireStabilityConjecture
    (U : SpireStabilityData)
    (Q : U.SpinorField)
    (Torus : ModularSuperTorus)
    (op : U.Operator Q) : Prop :=
  U.V4WeylCompatible Q Torus →
    U.DrazinCoreIsBPS op →
    U.SatisfiesSouriauKMS op →
    ∀ s ∈ U.MellinSpectrum Q, U.re s = (1 : ℝ) / 2

/--
Typed research package for a single Spire-stability instance.
-/
structure SpireStabilityPackage
    (U : SpireStabilityData)
    (Q : U.SpinorField)
    (Torus : ModularSuperTorus)
    (op : U.Operator Q) where
  frontier : FrontierHypotheses
  spire_stability : SpireStabilityConjecture U Q Torus op

/-- The theorem-facing typed capstone wrapper for the open Spire stability problem.

This is not a proof from lower owner lemmas. It is the elimination rule for a
`SpireStabilityPackage`, keeping the conjectural dependence explicit.
-/
theorem Spire_Stability_Conjecture_typed
    (Q : U.SpinorField)
    (Torus : ModularSuperTorus)
    (op : U.Operator Q)
    (pkg : SpireStabilityPackage U Q Torus op)
    (hV4 : U.V4WeylCompatible Q Torus)
    (hBPS : U.DrazinCoreIsBPS op)
    (hKMS : U.SatisfiesSouriauKMS op) :
    ∀ s ∈ U.MellinSpectrum Q, U.re s = (1 : ℝ) / 2 :=
  pkg.spire_stability hV4 hBPS hKMS

/--
Operatorial critical-line readout on the open-problem lane.

This is the theorem-shaped elimination rule attached to the explicit Spire
stability package: once the package is instantiated, every resonance in the
Mellin spectrum lies on the critical line.
-/
lemma self_dual_resonance_lies_on_critical_line
    (Q : U.SpinorField)
    (Torus : ModularSuperTorus)
    (op : U.Operator Q)
    (pkg : SpireStabilityPackage U Q Torus op)
    (hV4 : U.V4WeylCompatible Q Torus)
    (hBPS : U.DrazinCoreIsBPS op)
    (hKMS : U.SatisfiesSouriauKMS op)
    {s : U.Resonance}
    (hs : s ∈ U.MellinSpectrum Q) :
    U.re s = (1 : ℝ) / 2 :=
  pkg.spire_stability hV4 hBPS hKMS s hs

end FrontierConjectures

end InfoGeometry.Canonical.OpenProblemFormalization
