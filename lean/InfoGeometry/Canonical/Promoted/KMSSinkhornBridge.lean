import InfoGeometry.Krein.Thermal
import InfoGeometry.Canonical.Promoted.ChiralAnomaly

open scoped BigOperators

namespace InfoGeometry.Research.KMSSinkhornBridge

open InfoGeometry.Research.MoE
open InfoGeometry.Research.ChiralAnomaly

section RouterHamiltonian

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (n : Nat) [Nonempty (Fin n)]

/-- Router-amplitude space over experts. -/
abbrev RouterAmplitude := Fin n → ℝ

/-- Mean router energy over experts for a fixed token index. -/
noncomputable def routerMeanEnergy (x : Fin n → V) (i : Fin n) : ℝ :=
  (n : ℝ)⁻¹ * ∑ e : Fin n, routerEnergy n x i e

/--
Modular Hamiltonian induced by router logits/energies:
a scalar (mean-energy) generator on the doubled router-amplitude space.
-/
noncomputable def routerModularHamiltonian (x : Fin n → V) (i : Fin n) :
    AlgebraEnd (RouterAmplitude n) :=
  routerMeanEnergy n x i •
    ContinuousLinearMap.id ℝ (DoubledSpace (RouterAmplitude n))

omit [NormedSpace ℝ V] [Nonempty (Fin n)] in
@[simp] lemma routerModularHamiltonian_apply
    (x : Fin n → V) (i : Fin n) (v : DoubledSpace (RouterAmplitude n)) :
    routerModularHamiltonian n x i v = routerMeanEnergy n x i • v := by
  simp [routerModularHamiltonian]

end RouterHamiltonian

section KMSResidual

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Absolute algebraic KMS residual for a pair of observables. -/
noncomputable def kmsResidual
    (K : AlgebraEnd F) (ω : AlgebraEnd F →L[ℝ] ℝ) (β : ℝ)
    (A B : AlgebraEnd F) : ℝ :=
  |ω (A * modularShift (E := F) K β B) - ω (B * A)|

/-- `ε`-approximate KMS condition. -/
def SatisfiesApproxKMSLike
    (K : AlgebraEnd F) (ω : AlgebraEnd F →L[ℝ] ℝ) (β ε : ℝ) : Prop :=
  ∀ A B : AlgebraEnd F, kmsResidual K ω β A B ≤ ε

lemma satisfiesApproxKMSLike_of_satisfiesKMSLike
    (K : AlgebraEnd F) (ω : AlgebraEnd F →L[ℝ] ℝ) (β : ℝ)
    (hKMS : SatisfiesKMSLike (E := F) K ω β) :
    SatisfiesApproxKMSLike K ω β 0 := by
  intro A B
  unfold kmsResidual
  have hEq : ω (A * modularShift (E := F) K β B) - ω (B * A) = 0 := by
    exact sub_eq_zero.mpr (hKMS A B)
  simp [hEq]

lemma satisfiesKMSLike_of_approx_zero
    (K : AlgebraEnd F) (ω : AlgebraEnd F →L[ℝ] ℝ) (β : ℝ)
    (hApprox : SatisfiesApproxKMSLike K ω β 0) :
    SatisfiesKMSLike (E := F) K ω β := by
  intro A B
  have hle : kmsResidual K ω β A B ≤ 0 := hApprox A B
  have hEqAbs : kmsResidual K ω β A B = 0 :=
    le_antisymm hle (by
      unfold kmsResidual
      exact abs_nonneg _)
  have hEqSub :
      ω (A * modularShift (E := F) K β B) - ω (B * A) = 0 := by
    exact abs_eq_zero.mp (by simpa [kmsResidual] using hEqAbs)
  exact sub_eq_zero.mp hEqSub

end KMSResidual

section SinkhornBridge

variable (n : Nat)
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/--
Control hypothesis coupling Sinkhorn balancing to KMS residuals:
the residual at step `k+1` is bounded by the post-step RN barrier.
-/
def SinkhornKMSControl
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ) : Prop :=
  ∀ k : Nat, ∀ A B : AlgebraEnd F,
    kmsResidual K (ω (k + 1)) β A B ≤ trajectoryRNBarrierNext n T k

/--
Constructive thermodynamic state: exact KMS holds at every next Sinkhorn step.
-/
def SinkhornKMSClosure
    (_T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ) : Prop :=
  ∀ k : Nat, SatisfiesKMSLike (E := F) K (ω (k + 1)) β

/--
Canonical theorem name: Sinkhorn control closes to exact KMS at each next step.
-/
theorem sinkhorn_step_kmsClosure_of_control
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hControl : SinkhornKMSControl n T K ω β) :
    SinkhornKMSClosure n T K ω β := by
  intro k
  apply satisfiesKMSLike_of_approx_zero (K := K) (ω := ω (k + 1)) (β := β)
  intro A B
  have hAB : kmsResidual K (ω (k + 1)) β A B ≤ trajectoryRNBarrierNext n T k :=
    hControl k A B
  have hzero : trajectoryRNBarrierNext n T k = 0 :=
    trajectoryRNBarrierNext_eq_zero (n := n) T k
  simpa [hzero] using hAB

/-- Canonical theorem name: exact KMS closure implies Sinkhorn control. -/
theorem sinkhorn_control_of_step_kmsClosure
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hClosure : SinkhornKMSClosure n T K ω β) :
    SinkhornKMSControl n T K ω β := by
  intro k A B
  have hApprox :
      SatisfiesApproxKMSLike K (ω (k + 1)) β 0 :=
    satisfiesApproxKMSLike_of_satisfiesKMSLike (K := K) (ω := ω (k + 1)) (β := β) (hClosure k)
  have hAB : kmsResidual K (ω (k + 1)) β A B ≤ 0 := hApprox A B
  have hzero : trajectoryRNBarrierNext n T k = 0 :=
    trajectoryRNBarrierNext_eq_zero (n := n) T k
  simpa [hzero] using hAB

/--
Stepwise quantitative control: KMS residual is bounded by the pre-step RN barrier.
-/
theorem sinkhorn_stepwise_kms_bound
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hDrive : SinkhornKMSControl n T K ω β) :
    ∀ k : Nat, ∀ A B : AlgebraEnd F,
      kmsResidual K (ω (k + 1)) β A B ≤ trajectoryRNBarrier n T k := by
  intro k A B
  exact le_trans (hDrive k A B) (trajectoryRNBarrier_monotone (n := n) T k)

/- Constructive-iterate specialization in canonical naming. -/
theorem sinkhornIterate_kmsClosure_of_control
    (M0 : SinkhornMatrix n)
    (hrow : ∀ M : SinkhornMatrix n, HasPositiveRowSums n M)
    (hcol : ∀ M : SinkhornMatrix n, HasPositiveColSums n M)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hControl : SinkhornKMSControl n
      (sinkhornIterateTrajectory (n := n) M0 hrow hcol) K ω β) :
    SinkhornKMSClosure n (sinkhornIterateTrajectory (n := n) M0 hrow hcol) K ω β := by
  exact sinkhorn_step_kmsClosure_of_control
    (n := n) (T := sinkhornIterateTrajectory (n := n) M0 hrow hcol)
    (K := K) (ω := ω) (β := β) hControl

end SinkhornBridge

section RouterSinkhornBridge

variable (n : Nat)

/--
MoE-router specialization:
the modular Hamiltonian generated from router logits/energies satisfies the
same Sinkhorn-to-KMS step theorem.
-/
theorem router_sinkhornIterate_kmsClosure_of_control
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [Nonempty (Fin n)]
    (x : Fin n → V) (i : Fin n)
    (M0 : SinkhornMatrix n)
    (hrow : ∀ M : SinkhornMatrix n, HasPositiveRowSums n M)
    (hcol : ∀ M : SinkhornMatrix n, HasPositiveColSums n M)
    (ω : Nat → AlgebraEnd (RouterAmplitude n) →L[ℝ] ℝ)
    (β : ℝ)
    (hDrive : SinkhornKMSControl n
      (sinkhornIterateTrajectory (n := n) M0 hrow hcol)
      (routerModularHamiltonian n x i) ω β) :
    SinkhornKMSClosure n
      (sinkhornIterateTrajectory (n := n) M0 hrow hcol)
      (routerModularHamiltonian n x i) ω β := by
  exact sinkhornIterate_kmsClosure_of_control
    (n := n) (M0 := M0) (hrow := hrow) (hcol := hcol)
    (K := routerModularHamiltonian n x i) (ω := ω) (β := β) hDrive

end RouterSinkhornBridge

end InfoGeometry.Research.KMSSinkhornBridge
