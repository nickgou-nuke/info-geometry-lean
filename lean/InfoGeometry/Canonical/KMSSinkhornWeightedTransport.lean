import InfoGeometry.Canonical.KMSSinkhornSeedState
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.KMSSinkhornScalarPotential
import InfoGeometry.Canonical.IBFrozenDescent
import InfoGeometry.Canonical.IBTrajectory
import InfoGeometry.Canonical.IBUpdate

set_option linter.unnecessarySeqFocus false

namespace InfoGeometry.Canonical.KMSSinkhornBridge

open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.IB
open InfoGeometry.Krein

/-!
# InfoGeometry.Canonical.KMSSinkhornWeightedTransport

Weighted observable transport and closure layer for the Sinkhorn/KMS corridor.
-/

section SinkhornBridge

variable (n : Nat)
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/--
IB-driven constructive control law:
if KMS residuals are bounded by the frozen-target BA gap along an IB iterate
sequence, then Sinkhorn KMS control follows.
-/
theorem sinkhorn_kmsControl_of_ibDynamics
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (prob : IBProblem (X := Xib) (Y := Yib))
    (pTrajectory : Nat → Xib → FinProb Tib)
    (hStep : ∀ k : Nat, pTrajectory (k + 1) = ibBlahutArimotoStep prob (pTrajectory k))
    (hResidualLeGap :
      ∀ k : Nat, ∀ A B : AlgebraEnd F,
        kmsResidual K (ω (k + 1)) β A B
          ≤ baFrozenTargetGap prob (pTrajectory k) (pTrajectory (k + 1))) :
    SinkhornKMSControl n T K ω β := by
  intro k A B
  have hgap0 : baFrozenTargetGap prob (pTrajectory k) (pTrajectory (k + 1)) = 0 := by
    rw [hStep k]
    exact baFrozenTargetGap_step_eq_zero (prob := prob) (pOld := pTrajectory k)
  have hres0 : kmsResidual K (ω (k + 1)) β A B ≤ 0 := by
    simpa [hgap0] using hResidualLeGap k A B
  have hbar0 : trajectoryRNBarrierNext n T k = 0 :=
    trajectoryRNBarrierNext_eq_zero (n := n) T k
  simpa [hbar0] using hres0

lemma ibObservableWeight_ne_zero
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (pTrajectory : Nat → Xib → FinProb Tib)
    (x0 : Xib) (t0 : Tib) (k : Nat) :
    ibObservableWeight (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 k ≠ 0 :=
  Real.exp_ne_zero _

/--
Explicit IB-side RN-potential barrier budget:
frozen BA-gap plus a strictly positive RN-potential weight term.
-/
noncomputable def ibRNPotentialBarrierBudget
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (prob : IBProblem (X := Xib) (Y := Yib))
    (pTrajectory : Nat → Xib → FinProb Tib)
    (x0 : Xib) (t0 : Tib) (k : Nat) : ℝ :=
  baFrozenTargetGap prob (pTrajectory k) (pTrajectory (k + 1))
    + ibObservableWeight (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 (k + 1)

lemma ibRNPotentialBarrierBudget_pos
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
  unfold ibRNPotentialBarrierBudget
  exact add_pos_of_nonneg_of_pos
    (baFrozenTargetGap_nonneg (prob := prob) (pAnchor := pTrajectory k) (p := pTrajectory (k + 1)))
    (ibObservableWeight_pos
      (Xib := Xib) (Yib := Yib) (Tib := Tib)
      (pTrajectory := pTrajectory) (x0 := x0) (t0 := t0) (k := k + 1))

/--
IB-driven KMS control with explicit RN-potential barrier budget.
-/
def IBRNPotentialKMSControl
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (prob : IBProblem (X := Xib) (Y := Yib))
    (pTrajectory : Nat → Xib → FinProb Tib)
    (x0 : Xib) (t0 : Tib) : Prop :=
  ∀ k : Nat, ∀ A B : AlgebraEnd F,
    kmsResidual K (ω (k + 1)) β A B
      ≤ ibRNPotentialBarrierBudget
          (Xib := Xib) (Yib := Yib) (Tib := Tib) prob pTrajectory x0 t0 k

/--
IB-driven approximate KMS closure tracked by the explicit RN-potential budget.
-/
def IBRNPotentialApproxKMSClosure
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (prob : IBProblem (X := Xib) (Y := Yib))
    (pTrajectory : Nat → Xib → FinProb Tib)
    (x0 : Xib) (t0 : Tib) : Prop :=
  ∀ k : Nat,
    SatisfiesApproxKMSLike K (ω (k + 1)) β
      (ibRNPotentialBarrierBudget
        (Xib := Xib) (Yib := Yib) (Tib := Tib) prob pTrajectory x0 t0 k)

/-- Budgeted control immediately yields budgeted approximate KMS closure. -/
theorem ibRNPotentialApproxKMSClosure_of_control
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (prob : IBProblem (X := Xib) (Y := Yib))
    (pTrajectory : Nat → Xib → FinProb Tib)
    (x0 : Xib) (t0 : Tib)
    (hControl : IBRNPotentialKMSControl
      (F := F) (K := K) (ω := ω) (β := β)
      (Xib := Xib) (Yib := Yib) (Tib := Tib)
      prob pTrajectory x0 t0) :
    IBRNPotentialApproxKMSClosure
      (F := F) (K := K) (ω := ω) (β := β)
      (Xib := Xib) (Yib := Yib) (Tib := Tib)
      prob pTrajectory x0 t0 := by
  intro k A B
  exact hControl k A B

/--
Nonzero IB-induced observable family:
scale a seed observable state by an RN-potential-induced positive weight.
-/
noncomputable def ibInducedObservableWeighted
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (pTrajectory : Nat → Xib → FinProb Tib)
    (x0 : Xib) (t0 : Tib)
    (ωSeed : AlgebraEnd F →L[ℝ] ℝ) :
    Nat → AlgebraEnd F →L[ℝ] ℝ :=
  fun k => (ibObservableWeight (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 k) • ωSeed

lemma ibInducedObservableWeighted_nonzero
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (pTrajectory : Nat → Xib → FinProb Tib)
    (x0 : Xib) (t0 : Tib)
    (ωSeed : AlgebraEnd F →L[ℝ] ℝ)
    (hωSeed : ωSeed ≠ 0) :
    ∀ k : Nat, ibInducedObservableWeighted
      (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 ωSeed k ≠ 0 := by
  intro k hk
  have hw : ibObservableWeight (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 k ≠ 0 :=
    ibObservableWeight_ne_zero
      (Xib := Xib) (Yib := Yib) (Tib := Tib)
      (pTrajectory := pTrajectory) (x0 := x0) (t0 := t0) (k := k)
  have hk' := congrArg
      (fun ψ : AlgebraEnd F →L[ℝ] ℝ =>
        (ibObservableWeight (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 k)⁻¹ • ψ) hk
  have hmul :
      (ibObservableWeight (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 k)⁻¹ *
        ibObservableWeight (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 k = 1 := by
    exact inv_mul_cancel₀ hw
  have hω : ωSeed = 0 := by
    simpa [ibInducedObservableWeighted, smul_smul, hmul] using hk'
  exact hωSeed hω

lemma satisfiesKMSLike_smul
    (K : AlgebraEnd F)
    (ωSeed : AlgebraEnd F →L[ℝ] ℝ)
    (β c : ℝ)
    (hSeedKMS : SatisfiesKMSLike (E := F) K ωSeed β) :
    SatisfiesKMSLike (E := F) K (c • ωSeed) β := by
  intro A B
  simpa [smul_eq_mul] using congrArg (fun r : ℝ => c * r) (hSeedKMS A B)

lemma kmsResidual_eq_zero_of_satisfiesKMSLike
    (K : AlgebraEnd F)
    (ω : AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hKMS : SatisfiesKMSLike (E := F) K ω β)
    (A B : AlgebraEnd F) :
    kmsResidual K ω β A B = 0 := by
  simp [kmsResidual, hKMS A B]

/--
Constructive residual domination for a nonzero IB-induced observable family.
The proof is nontrivial: residual vanishing comes from a KMS seed law, not from
the zero functional.
-/
theorem hResidualLeGap_of_ibInducedObservableWeighted
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
    (hSeedKMS : SatisfiesKMSLike (E := F) K ωSeed β) :
    ∀ k : Nat, ∀ A B : AlgebraEnd F,
      kmsResidual K ((ibInducedObservableWeighted
        (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 ωSeed) (k + 1)) β A B
        ≤ baFrozenTargetGap prob (pTrajectory k) (pTrajectory (k + 1)) := by
  intro k A B
  have hKMSk :
      SatisfiesKMSLike (E := F) K
        ((ibInducedObservableWeighted
          (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 ωSeed) (k + 1)) β := by
    exact satisfiesKMSLike_smul (K := K) (ωSeed := ωSeed) (β := β)
      (c := ibObservableWeight (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 (k + 1))
      hSeedKMS
  have hres0 :
      kmsResidual K ((ibInducedObservableWeighted
        (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 ωSeed) (k + 1)) β A B = 0 :=
    kmsResidual_eq_zero_of_satisfiesKMSLike (K := K)
      (ω := ((ibInducedObservableWeighted
        (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 ωSeed) (k + 1)))
      (β := β) hKMSk A B
  rw [hres0]
  exact baFrozenTargetGap_nonneg (prob := prob) (pAnchor := pTrajectory k) (p := pTrajectory (k + 1))

/--
Constructive residual domination by the explicit positive RN-potential budget.

This avoids the degenerate zero-barrier closure by keeping a strictly positive
stepwise budget term derived from RN potential data.
-/
theorem hResidualLeRNPotentialBudget_of_ibInducedObservableWeighted
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
    (hSeedKMS : SatisfiesKMSLike (E := F) K ωSeed β) :
    ∀ k : Nat, ∀ A B : AlgebraEnd F,
      kmsResidual K ((ibInducedObservableWeighted
        (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 ωSeed) (k + 1)) β A B
        ≤ ibRNPotentialBarrierBudget
            (Xib := Xib) (Yib := Yib) (Tib := Tib) prob pTrajectory x0 t0 k := by
  intro k A B
  have hGap :
      kmsResidual K ((ibInducedObservableWeighted
        (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 ωSeed) (k + 1)) β A B
        ≤ baFrozenTargetGap prob (pTrajectory k) (pTrajectory (k + 1)) :=
    hResidualLeGap_of_ibInducedObservableWeighted
      (K := K) (β := β) (prob := prob) (pTrajectory := pTrajectory)
      (x0 := x0) (t0 := t0) (ωSeed := ωSeed) hSeedKMS k A B
  have hGapLeBudget :
      baFrozenTargetGap prob (pTrajectory k) (pTrajectory (k + 1))
        ≤ ibRNPotentialBarrierBudget
            (Xib := Xib) (Yib := Yib) (Tib := Tib) prob pTrajectory x0 t0 k := by
    unfold ibRNPotentialBarrierBudget
    exact le_add_of_nonneg_right
      (ibObservableWeight_pos
        (Xib := Xib) (Yib := Yib) (Tib := Tib)
        (pTrajectory := pTrajectory) (x0 := x0) (t0 := t0) (k := k + 1)).le
  exact le_trans hGap hGapLeBudget

/--
IB-driven control with explicit positive RN-potential barrier budgets.
-/
theorem ibRNPotential_kmsControl_of_ibDynamics_weighted
    (K : AlgebraEnd F)
    (β : ℝ)
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (prob : IBProblem (X := Xib) (Y := Yib))
    (pTrajectory : Nat → Xib → FinProb Tib)
    (_hStep : ∀ k : Nat, pTrajectory (k + 1) = ibBlahutArimotoStep prob (pTrajectory k))
    (x0 : Xib) (t0 : Tib)
    (ωSeed : AlgebraEnd F →L[ℝ] ℝ)
    (hSeedKMS : SatisfiesKMSLike (E := F) K ωSeed β) :
    IBRNPotentialKMSControl
      (F := F)
      (K := K)
      (ω := ibInducedObservableWeighted
        (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 ωSeed)
      (β := β)
      (Xib := Xib) (Yib := Yib) (Tib := Tib)
      prob pTrajectory x0 t0 := by
  intro k A B
  exact hResidualLeRNPotentialBudget_of_ibInducedObservableWeighted
    (K := K) (β := β) (prob := prob) (pTrajectory := pTrajectory)
    (x0 := x0) (t0 := t0) (ωSeed := ωSeed) hSeedKMS k A B

/--
IB-driven approximate KMS closure with explicit RN-potential budget.
-/
theorem ibRNPotential_approxKMSClosure_of_ibDynamics_weighted
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
    (ωSeed : AlgebraEnd F →L[ℝ] ℝ)
    (hSeedKMS : SatisfiesKMSLike (E := F) K ωSeed β) :
    IBRNPotentialApproxKMSClosure
      (F := F)
      (K := K)
      (ω := ibInducedObservableWeighted
        (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 ωSeed)
      (β := β)
      (Xib := Xib) (Yib := Yib) (Tib := Tib)
      prob pTrajectory x0 t0 := by
  exact ibRNPotentialApproxKMSClosure_of_control
    (F := F)
    (K := K)
    (ω := ibInducedObservableWeighted
      (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 ωSeed)
    (β := β)
    (Xib := Xib) (Yib := Yib) (Tib := Tib)
    (prob := prob)
    (pTrajectory := pTrajectory)
    (x0 := x0)
    (t0 := t0)
    (hControl :=
      ibRNPotential_kmsControl_of_ibDynamics_weighted
        (F := F)
        (K := K)
        (β := β)
        (Xib := Xib) (Yib := Yib) (Tib := Tib)
        (prob := prob)
        (pTrajectory := pTrajectory)
        (_hStep := hStep)
        (x0 := x0)
        (t0 := t0)
        (ωSeed := ωSeed)
        hSeedKMS)

/--
IB-to-Sinkhorn control for the nonzero weighted observable family.
-/
theorem sinkhorn_kmsControl_of_ibDynamics_weighted
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
    (ωSeed : AlgebraEnd F →L[ℝ] ℝ)
    (hSeedKMS : SatisfiesKMSLike (E := F) K ωSeed β) :
    SinkhornKMSControl n T K
      (ibInducedObservableWeighted
        (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 ωSeed) β := by
  refine sinkhorn_kmsControl_of_ibDynamics
    (n := n) (T := T) (K := K)
    (ω := ibInducedObservableWeighted
      (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 ωSeed) (β := β)
    (prob := prob) (pTrajectory := pTrajectory)
    hStep ?_
  exact hResidualLeGap_of_ibInducedObservableWeighted
    (K := K) (β := β) (prob := prob) (pTrajectory := pTrajectory)
    (x0 := x0) (t0 := t0) (ωSeed := ωSeed) hSeedKMS

/--
Fully explicit weighted IB-to-Sinkhorn control using derivable seed-KMS inputs:
joint-kernel modular defect and commutator orthogonality on `Ω`.
-/
theorem sinkhorn_kmsControl_of_ibDynamics_weighted_from_jointKernel_commutator
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
    SinkhornKMSControl n T K
      (ibInducedObservableWeighted
        (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib)
        pTrajectory x0 t0 (omegaSeed (F := F) Ω)) β := by
  have hSeedNonzero : omegaSeed (F := F) Ω ≠ 0 :=
    omegaSeed_nonzero (F := F) Ω hΩ
  have hSeedKMS :
      SatisfiesKMSLike (E := F) K (omegaSeed (F := F) Ω) β :=
    omegaSeed_kms_of_jointKernel_commutator
      (F := F) (K := K) (β := β) (Ω := Ω) hJointKernel hCommOrthogonal
  have _hWeightedNonzero :
      ∀ k : Nat,
        ibInducedObservableWeighted
          (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib)
          pTrajectory x0 t0 (omegaSeed (F := F) Ω) k ≠ 0 :=
    ibInducedObservableWeighted_nonzero
      (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib)
      (pTrajectory := pTrajectory) (x0 := x0) (t0 := t0)
      (ωSeed := omegaSeed (F := F) Ω) hSeedNonzero
  refine sinkhorn_kmsControl_of_ibDynamics_weighted
    (n := n) (T := T) (K := K) (β := β)
    (prob := prob) (pTrajectory := pTrajectory)
    hStep (x0 := x0) (t0 := t0)
    (ωSeed := omegaSeed (F := F) Ω) hSeedKMS

/--
Joint-kernel/commutator route to exact weighted Sinkhorn KMS closure.
-/
theorem sinkhorn_kmsClosure_of_ibDynamics_weighted_from_jointKernel_commutator
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
  exact sinkhorn_step_kmsClosure_of_control
    (n := n) (T := T) (K := K)
    (ω := ibInducedObservableWeighted
      (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib)
      pTrajectory x0 t0 (omegaSeed (F := F) Ω))
    (β := β)
    (sinkhorn_kmsControl_of_ibDynamics_weighted_from_jointKernel_commutator
      (n := n) (T := T) (K := K) (β := β)
      (prob := prob) (pTrajectory := pTrajectory)
      hStep (x0 := x0) (t0 := t0)
      (Ω := Ω) hΩ hJointKernel hCommOrthogonal)

/--
Fully explicit weighted IB-driven control with an RN-potential budget,
derived from joint-kernel and commutator-orthogonality hypotheses.
-/
theorem ibRNPotential_kmsControl_of_ibDynamics_weighted_from_jointKernel_commutator
    (K : AlgebraEnd F)
    (β : ℝ)
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (prob : IBProblem (X := Xib) (Y := Yib))
    (pTrajectory : Nat → Xib → FinProb Tib)
    (_hStep : ∀ k : Nat, pTrajectory (k + 1) = ibBlahutArimotoStep prob (pTrajectory k))
    (x0 : Xib) (t0 : Tib)
    (Ω : DoubledSpace F)
    (hΩ : Ω ≠ 0)
    (hJointKernel : JointKernelOnOmega (F := F) K β Ω)
    (hCommOrthogonal : CommutatorOrthogonalOnOmega (F := F) Ω) :
    IBRNPotentialKMSControl
      (F := F)
      (K := K)
      (ω := ibInducedObservableWeighted
        (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib)
        pTrajectory x0 t0 (omegaSeed (F := F) Ω))
      (β := β)
      (Xib := Xib) (Yib := Yib) (Tib := Tib)
      prob pTrajectory x0 t0 := by
  have _hSeedNonzero : omegaSeed (F := F) Ω ≠ 0 :=
    omegaSeed_nonzero (F := F) Ω hΩ
  have hSeedKMS :
      SatisfiesKMSLike (E := F) K (omegaSeed (F := F) Ω) β :=
    omegaSeed_kms_of_jointKernel_commutator
      (F := F) (K := K) (β := β) (Ω := Ω) hJointKernel hCommOrthogonal
  exact ibRNPotential_kmsControl_of_ibDynamics_weighted
    (F := F)
    (K := K)
    (β := β)
    (Xib := Xib) (Yib := Yib) (Tib := Tib)
    (prob := prob)
    (pTrajectory := pTrajectory)
    (_hStep := _hStep)
    (x0 := x0)
    (t0 := t0)
    (ωSeed := omegaSeed (F := F) Ω)
    hSeedKMS

/--
Joint-kernel/commutator route to RN-potential-budgeted approximate KMS closure.
-/
theorem ibRNPotential_approxKMSClosure_of_ibDynamics_weighted_from_jointKernel_commutator
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
    IBRNPotentialApproxKMSClosure
      (F := F)
      (K := K)
      (ω := ibInducedObservableWeighted
        (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib)
        pTrajectory x0 t0 (omegaSeed (F := F) Ω))
      (β := β)
      (Xib := Xib) (Yib := Yib) (Tib := Tib)
      prob pTrajectory x0 t0 := by
  exact ibRNPotentialApproxKMSClosure_of_control
    (F := F)
    (K := K)
    (ω := ibInducedObservableWeighted
      (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib)
      pTrajectory x0 t0 (omegaSeed (F := F) Ω))
    (β := β)
    (Xib := Xib) (Yib := Yib) (Tib := Tib)
    (prob := prob)
    (pTrajectory := pTrajectory)
    (x0 := x0)
    (t0 := t0)
    (hControl :=
      ibRNPotential_kmsControl_of_ibDynamics_weighted_from_jointKernel_commutator
        (F := F)
        (K := K)
        (β := β)
        (Xib := Xib) (Yib := Yib) (Tib := Tib)
        (prob := prob)
        (pTrajectory := pTrajectory)
        (_hStep := hStep)
        (x0 := x0)
        (t0 := t0)
        (Ω := Ω)
        (hΩ := hΩ)
        (hJointKernel := hJointKernel)
        (hCommOrthogonal := hCommOrthogonal))

end SinkhornBridge

end InfoGeometry.Canonical.KMSSinkhornBridge
