import InfoGeometry.Canonical.AQFTReadiness
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.KMSSinkhornWeightedTransport
import InfoGeometry.Canonical.GrandCanonicalExperts
import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Canonical.RicciMongeAmpere
import InfoGeometry.Canonical.IBTrajectory
import InfoGeometry.Canonical.IBUpdate

/-!
# InfoGeometry.Canonical.AQFTOperatorEndpoints

Constructive AQFT-facing endpoints over the operator interface.
-/

namespace InfoGeometry.Canonical.AQFTOperatorInterface

open InfoGeometry.Krein
open InfoGeometry.Canonical.KMSSinkhornBridge
open InfoGeometry.Canonical.IB
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.RicciMongeAmpere

section CanonicalEndpoint

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Constructive Fock-side payload:
vacuum-transported splitting identifies the grand-canonical Euler step with
the underlying Hamiltonian update.
-/
theorem grandCanonicalEulerStep_eq_of_vacuumSplit
    (η : ℝ)
    (B : BogoliubovMixingParams)
    (Hf : FockEndomorphism E)
    (R : RicciTensor E)
    (Kgeo : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein Kgeo x)
    (Γ : SpinConnection Kgeo x V)
    (ψ : InfoGeometry.Krein.DoubledSpace E)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R Kgeo x scalar Λ V Γ) :
    grandCanonicalFockEulerStep (E := E) η B Hf
      (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
        (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)) ψ
      = ψ + η • Hf ψ := by
  change ψ + η •
      (grandCanonicalFockGenerator (E := E) B Hf
        (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
          (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ))) ψ
    = ψ + η • Hf ψ
  rw [grandCanonicalFockGenerator_eq_hamiltonian_of_vacuumTransported
    (E := E) (B := B) (H := Hf) (R := R) (K := Kgeo) (x := x)
    (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ) hVacSplit]

/--
Constructive thermal payload:
derive weighted Sinkhorn-KMS closure from IB dynamics through the
joint-kernel/commutator route.
-/
theorem ibWeightedKMSClosure_of_jointKernel_commutator
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
  exact sinkhorn_kmsClosure_of_ibDynamics_weighted_from_jointKernel_commutator
    (n := n) (T := T) (K := K) (β := β)
    (prob := prob) (pTrajectory := pTrajectory)
    hStep (x0 := x0) (t0 := t0)
    (Ω := Ω) hΩ hJointKernel hCommOrthogonal

end CanonicalEndpoint

end InfoGeometry.Canonical.AQFTOperatorInterface
