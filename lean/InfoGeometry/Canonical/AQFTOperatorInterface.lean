import InfoGeometry.Canonical.AQFTOperatorSignatures
import InfoGeometry.Canonical.AQFTHilbertCompression
import InfoGeometry.Canonical.AQFTReadiness
import InfoGeometry.Canonical.AQFTOperatorEndpoints

namespace InfoGeometry

/-!
# InfoGeometry.Canonical.AQFTOperatorInterface

Umbrella import for the AQFT operator interface:

- abstract C*-ready signatures
- concrete Hilbert compression realizations
- static readiness packages
- constructive AQFT endpoints
-/

namespace Canonical.AQFTOperatorInterface

open InfoGeometry.Krein
open InfoGeometry.Canonical.KMSSinkhornBridge
open InfoGeometry.Canonical.IB
open InfoGeometry.Canonical.MoE

/--
Integrated AQFT operator-interface package on the concrete real Hilbert lane.
This is a composition surface carrying signatures, realization, and readiness
from the owner modules.
-/
structure ConcreteInterfacePackage
    (F E : Type)
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  readiness : AQFTReadinessPackage F E
  interpretation_eq_canonical :
    readiness.interpretation = realHilbertCompressionInterpretation (E := E)

/--
Canonical concrete AQFT interface package assembled from owner lanes.
-/
def concreteInterfacePackage
    {F E : Type}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    ConcreteInterfacePackage F E where
  readiness := aqftReadinessPackageRealHilbert (F := F) (E := E)
  interpretation_eq_canonical := rfl

/--
The integrated package carries the concrete C*-readiness property.
-/
theorem concreteInterfacePackage_isCStarReady
    {F E : Type}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    IsCStarReady (Obs := RealHilbertObs F) :=
  (concreteInterfacePackage (F := F) (E := E)).readiness.isCStarReadyF

/--
The integrated package carries the concrete complete-C*-readiness property.
-/
theorem concreteInterfacePackage_isCompleteCStarReady
    {F E : Type}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    IsCompleteCStarReady (Obs := RealHilbertObs E) :=
  (concreteInterfacePackage (F := F) (E := E)).readiness.isCompleteCStarReadyE

/--
Endpoint closure exported through the integrated interface surface.
-/
theorem sinkhornEndpointClosure
    {F : Type}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (n : Nat)
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (β : ℝ)
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (prob : IBProblem (X := Xib) (Y := Yib))
    (pTrajectory : Nat → Xib → FinProb Tib)
    (hStep : ∀ k : Nat, pTrajectory (k + 1) = ibBlahutArimotoStep prob (pTrajectory k))
    (x0 : Xib)
    (t0 : Tib)
    (Ω : InfoGeometry.Krein.DoubledSpace F)
    (hΩ : Ω ≠ 0)
    (hJointKernel : JointKernelOnOmega (F := F) K β Ω)
    (hCommOrthogonal : CommutatorOrthogonalOnOmega (F := F) Ω) :
    SinkhornKMSClosure n T K
      (ibInducedObservableWeighted
        (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib)
        pTrajectory x0 t0 (omegaSeed (F := F) Ω)) β := by
  exact ibWeightedKMSClosure_of_jointKernel_commutator
    (n := n) (T := T) (K := K) (β := β)
    (prob := prob) (pTrajectory := pTrajectory)
    hStep (x0 := x0) (t0 := t0)
    (Ω := Ω) hΩ hJointKernel hCommOrthogonal

/--
Trunk-to-canopy closure packet for the concrete AQFT interface lane:
the same assembled package carries both C*-readiness witnesses.
-/
theorem aqft_trunk_to_canopy_closure
    {F E : Type}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    IsCStarReady (Obs := RealHilbertObs F) ∧
      IsCompleteCStarReady (Obs := RealHilbertObs E) := by
  exact ⟨
    concreteInterfacePackage_isCStarReady (F := F) (E := E),
    concreteInterfacePackage_isCompleteCStarReady (F := F) (E := E)
  ⟩

/--
Root-factorization packet: the canonical concrete interface package exists and
exports the two readiness witnesses from a single owner object.
-/
theorem aqft_root_factorization
    {F E : Type}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    ∃ _ : ConcreteInterfacePackage F E,
      IsCStarReady (Obs := RealHilbertObs F) ∧
      IsCompleteCStarReady (Obs := RealHilbertObs E) := by
  refine ⟨concreteInterfacePackage (F := F) (E := E), ?_⟩
  simpa using aqft_trunk_to_canopy_closure (F := F) (E := E)

/--
Interpretation-corridor identification: the interface interpretation equals the
canonical real-Hilbert compression interpretation through the package property.
-/
theorem aqft_isomorphism_corridor
    {F E : Type}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (concreteInterfacePackage (F := F) (E := E)).readiness.interpretation =
      realHilbertCompressionInterpretation (E := E) := by
  exact (concreteInterfacePackage (F := F) (E := E)).interpretation_eq_canonical

end Canonical.AQFTOperatorInterface

end InfoGeometry
