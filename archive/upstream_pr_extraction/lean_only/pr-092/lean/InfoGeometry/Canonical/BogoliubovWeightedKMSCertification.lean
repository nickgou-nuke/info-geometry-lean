import InfoGeometry.Canonical.RealBdG
import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Canonical.ModularSuperchargeClosure
import InfoGeometry.Canonical.KMSSinkhornWeightedTransport

set_option linter.unusedSectionVars false

/-!
# InfoGeometry.Canonical.BogoliubovWeightedKMSCertification

Certification wrappers linking:
- real-BdG `K`-splitting,
- Bogoliubov modular transport on doubled real carriers,
- Lorentz-seeded modular fixedness/KMS surfaces,
- and weighted nonequilibrium Sinkhorn/KMS closure.
-/

namespace InfoGeometry.Canonical.BogoliubovWeightedKMSCertification

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.RealBdG
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.ModularSuperchargeClosure
open InfoGeometry.Canonical.KMSSinkhornBridge
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.IB

section RealBdGBogoliubov

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- `K`-linearity in `RealBdG` is exactly phase-linearity in Bogoliubov transport form. -/
theorem kLinear_iff_isPhaseLinear
    (A : EndH) :
    KLinear (E := E) A ↔ IsPhaseLinear (E := E) A := by
  constructor
  · intro hK
    have hComplex : A.comp (complex_i (E := E)) = (complex_i (E := E)).comp A := by
      simpa [modularK_eq_complex_i (E := E)] using hK
    exact (isPhaseLinear_iff_comp_complex_i (E := E) A).2 hComplex
  · intro hPhase
    have hComplex : A.comp (complex_i (E := E)) = (complex_i (E := E)).comp A :=
      (isPhaseLinear_iff_comp_complex_i (E := E) A).1 hPhase
    simpa [modularK_eq_complex_i (E := E)] using hComplex

/-- `K`-antilinearity in `RealBdG` is exactly phase-antilinearity in Bogoliubov transport form. -/
theorem kAntilinear_iff_isPhaseAntilinear
    (A : EndH) :
    KAntilinear (E := E) A ↔ IsPhaseAntilinear (E := E) A := by
  constructor
  · intro hK
    have hComplex : A.comp (complex_i (E := E)) = -((complex_i (E := E)).comp A) := by
      simpa [modularK_eq_complex_i (E := E)] using hK
    exact (isPhaseAntilinear_iff_comp_complex_i (E := E) A).2 hComplex
  · intro hPhase
    have hComplex : A.comp (complex_i (E := E)) = -((complex_i (E := E)).comp A) :=
      (isPhaseAntilinear_iff_comp_complex_i (E := E) A).1 hPhase
    simpa [modularK_eq_complex_i (E := E)] using hComplex

/-- Conjugation by `K` coincides with conjugation by the canonical phase axis `Jε`. -/
theorem kConjugate_eq_phaseConjugate
    (A : EndH) :
    KConjugate (E := E) A = phaseConjugate (E := E) A := by
  unfold KConjugate phaseConjugate
  simp [clockAxis_eq_complex_i]

/-- The `RealBdG` linear split equals the Bogoliubov phase-linear split. -/
theorem kLinearPart_eq_phaseLinearPart
    (A : EndH) :
    KLinearPart (E := E) A = phaseLinearPart (E := E) A := by
  unfold KLinearPart phaseLinearPart
  rw [kConjugate_eq_phaseConjugate (E := E) A]

/-- The `RealBdG` antilinear split equals the Bogoliubov phase-antilinear split. -/
theorem kAntilinearPart_eq_phaseAntilinearPart
    (A : EndH) :
    KAntilinearPart (E := E) A = phaseAntilinearPart (E := E) A := by
  unfold KAntilinearPart phaseAntilinearPart
  rw [kConjugate_eq_phaseConjugate (E := E) A]

/-- The reconstructed `RealBdG` split is identical to the reconstructed Bogoliubov split. -/
theorem kSplit_reconstruction_eq_phaseSplit
    (A : EndH) :
    KLinearPart (E := E) A + KAntilinearPart (E := E) A
      =
    phaseLinearPart (E := E) A + phaseAntilinearPart (E := E) A := by
  simp [kLinearPart_eq_phaseLinearPart, kAntilinearPart_eq_phaseAntilinearPart]

/--
Intertwiner property for neural/operator encoders:
if an operator commutes with the relative-modular `K`-generator, its relative-modular
derivation vanishes.
-/
theorem neuralEncoding_intertwiner_of_commute_relativeModularGenerator
    (hMod N : EndH)
    (hComm : Commute N (relativeModularKGenerator (E := E) hMod)) :
    relativeModularDeriv (E := E) hMod N = 0 := by
  exact relativeModularDeriv_eq_zero_of_commute_generator (E := E) hMod N hComm

end RealBdGBogoliubov

section LorentzKMS

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Transport-covariant fixedness of the projected-even generator on the Lorentz orbit. -/
theorem projectedEvenGenerator_lorentzTransportFixed
    (CIK : CertifiedInverseKernel H₂) (τ : ℝ) :
    lorentzChiralConeOrbit (E := E) CIK τ
      (DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK)
      =
    DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK := by
  exact projectedEvenGenerator_fixed_under_lorentzChiralConeOrbit (E := E) CIK τ

/-- Wedge-parametrized form of the Lorentz-transport fixedness property. -/
theorem projectedEvenGenerator_lorentzWedgeTransportFixed
    (CIK : CertifiedInverseKernel H₂) (τwedge : ℝ) :
    lorentzChiralConeOrbit (E := E) CIK
        (RealTomitaCore.modularTimeOfWedgeBoost τwedge)
        (DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK)
      =
    DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK := by
  exact projectedEvenGenerator_fixed_under_lorentzWedgeOrbit (E := E) CIK τwedge

/--
Operatorial KMS compatibility on the Lorentz-bivector seeded modular lane,
directly from the structural joint-kernel and commutator-orthogonality hypotheses.
-/
theorem lorentzBivectorSeed_operatorialKMS_of_structural
    (CIK : CertifiedInverseKernel H₂)
    (β : ℝ)
    (Ω : H₂)
    (hJointKernel :
      JointKernelOnOmega
        (F := E)
        (modularTransportGenerator
          (InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalBivectorSeed
            (E := E) CIK))
        β Ω)
    (hCommOrthogonal :
      CommutatorOrthogonalOnOmega
        (F := E) Ω) :
    ∀ A B : EndH,
      omegaSeed (F := E) Ω
        (A
          * modular_shift
              (E := E)
              (modularTransportGenerator
                (InfoGeometry.Canonical.ModularSuperchargeClosure.lorentzBivectorSeed
                  (E := E) CIK))
              β
              B)
        =
      omegaSeed (F := E) Ω (B * A) := by
  exact InfoGeometry.Canonical.ModularSuperchargeClosure.operatorialKMSCondition_lorentzBivectorSeed_of_structural
    (E := E) CIK β Ω hJointKernel hCommOrthogonal

end LorentzKMS

section WeightedNonequilibrium

variable (n : Nat)
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Positivity of the explicit RN-potential barrier budget at every weighted IB step. -/
theorem weightedNonequilibrium_rnBudget_pos
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (prob : IBProblem (X := Xib) (Y := Yib))
    (pTrajectory : Nat → Xib → FinProb Tib)
    (x0 : Xib) (t0 : Tib) (k : Nat) :
    0 < ibRNPotentialBarrierBudget
      (Xib := Xib) (Yib := Yib) (Tib := Tib) prob pTrajectory x0 t0 k := by
  exact ibRNPotentialBarrierBudget_pos
    (Xib := Xib) (Yib := Yib) (Tib := Tib)
    prob pTrajectory x0 t0 k

/--
Weighted nonequilibrium residual domination by the explicit positive RN budget.
This is the stepwise property used before Sinkhorn/KMS closure promotion.
-/
theorem weightedNonequilibrium_residual_le_rnBudget
    (K : AlgebraEnd F) (β : ℝ)
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (prob : IBProblem (X := Xib) (Y := Yib))
    (pTrajectory : Nat → Xib → FinProb Tib)
    (x0 : Xib) (t0 : Tib)
    (ωSeed : AlgebraEnd F →L[ℝ] ℝ)
    (hSeedKMS : SatisfiesKMSLike (E := F) K ωSeed β)
    (k : Nat) (A B : AlgebraEnd F) :
    kmsResidual K ((ibInducedObservableWeighted
      (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 ωSeed) (k + 1)) β A B
      ≤
    ibRNPotentialBarrierBudget
      (Xib := Xib) (Yib := Yib) (Tib := Tib) prob pTrajectory x0 t0 k := by
  exact hResidualLeRNPotentialBudget_of_ibInducedObservableWeighted
    (K := K) (β := β)
    (Xib := Xib) (Yib := Yib) (Tib := Tib)
    (prob := prob)
    (pTrajectory := pTrajectory)
    (x0 := x0) (t0 := t0)
    (ωSeed := ωSeed)
    hSeedKMS k A B

/--
End-to-end weighted nonequilibrium Sinkhorn KMS closure from structural
joint-kernel and commutator-orthogonality hypotheses.
-/
theorem weightedNonequilibrium_sinkhornKMSClosure_of_structural
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
    (x0 : Xib) (t0 : Tib)
    (Ω : DoubledSpace F)
    (hΩ : Ω ≠ 0)
    (hJointKernel : JointKernelOnOmega (F := F) K β Ω)
    (hCommOrthogonal : CommutatorOrthogonalOnOmega (F := F) Ω) :
    SinkhornKMSClosure n T K
      (ibInducedObservableWeighted
        (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib)
        pTrajectory x0 t0 (omegaSeed (F := F) Ω)) β := by
  exact sinkhorn_kmsClosure_of_ibDynamics_weighted_from_jointKernel_commutator
    (n := n)
    (T := T) (K := K) (β := β)
    (Xib := Xib) (Yib := Yib) (Tib := Tib)
    (prob := prob)
    (pTrajectory := pTrajectory)
    hStep
    (x0 := x0) (t0 := t0)
    (Ω := Ω) hΩ hJointKernel hCommOrthogonal

end WeightedNonequilibrium

end InfoGeometry.Canonical.BogoliubovWeightedKMSCertification
