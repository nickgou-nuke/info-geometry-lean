import InfoGeometry.Krein.Thermal
import InfoGeometry.Canonical.SinkhornFoundation
import Mathlib.Analysis.InnerProductSpace.LinearMap

set_option linter.unnecessarySeqFocus false

open scoped BigOperators

namespace InfoGeometry.Canonical.KMSSinkhornBridge

open InfoGeometry.Canonical.MoE
open InfoGeometry.Krein

/-- Doubled-space endomorphisms used for thermal/KMS operator statements. -/
abbrev AlgebraEnd
    (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] : Type _ :=
  DoubledSpace E →L[ℝ] DoubledSpace E

/-- CamelCase compatibility alias for `InfoGeometry.Krein.modular_shift`. -/
noncomputable abbrev modularShift
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : AlgebraEnd E) (β : ℝ) (B : AlgebraEnd E) : AlgebraEnd E :=
  InfoGeometry.Krein.modular_shift (E := E) K β B

/-- CamelCase compatibility alias for `InfoGeometry.Krein.satisfies_kms_like`. -/
abbrev SatisfiesKMSLike
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : AlgebraEnd E) (ω : AlgebraEnd E →L[ℝ] ℝ) (β : ℝ) : Prop :=
  InfoGeometry.Krein.satisfies_kms_like (E := E) K ω β

section RouterHamiltonian

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H]
variable (n : Nat) [Nonempty (Fin n)]

/-- Finite-coordinate specialization of the expert router carrier. -/
abbrev RouterAmplitude := EuclideanSpace ℝ (Fin n)

/-- Endomorphisms of a genuine Krein carrier. -/
abbrev KreinAlgebraEnd
    (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H] : Type _ :=
  H →L[ℝ] H

/-- Mean router energy over experts for a fixed token index. -/
noncomputable def routerMeanEnergy (x : Fin n → V) (i : Fin n) : ℝ :=
  (n : ℝ)⁻¹ * ∑ e : Fin n, routerEnergy n x i e

/--
Krein-rooted scalar modular generator driven by router energy on an actual
indefinite carrier `H`.
-/
noncomputable def kreinRouterModularHamiltonian (x : Fin n → V) (i : Fin n) :
    KreinAlgebraEnd H :=
  routerMeanEnergy n x i • ContinuousLinearMap.id ℝ H

omit [NormedSpace ℝ V] [Nonempty (Fin n)] in
@[simp] lemma kreinRouterModularHamiltonian_apply
    (x : Fin n → V) (i : Fin n) (v : H) :
    kreinRouterModularHamiltonian (H := H) n x i v = routerMeanEnergy n x i • v := by
  simp [kreinRouterModularHamiltonian]

omit [NormedSpace ℝ V] [Nonempty (Fin n)] in
/-- The Krein-rooted scalar router modular generator is Krein-self-adjoint. -/
lemma kreinRouterModularHamiltonian_isKreinSelfAdjoint
    (x : Fin n → V) (i : Fin n) :
    KreinSpace.IsKreinSelfAdjoint (H := H) (kreinRouterModularHamiltonian (H := H) n x i) := by
  simp [kreinRouterModularHamiltonian, KreinSpace.IsKreinSelfAdjoint]

/--
Compatibility specialization of the Krein-rooted generator to the doubled
finite-coordinate carrier used by the older count/router lane.
-/
noncomputable abbrev routerModularHamiltonian (x : Fin n → V) (i : Fin n) :
    AlgebraEnd (RouterAmplitude n) :=
  kreinRouterModularHamiltonian (H := DoubledSpace (RouterAmplitude n)) n x i

omit [NormedSpace ℝ V] [Nonempty (Fin n)] in
@[simp] lemma routerModularHamiltonian_apply
    (x : Fin n → V) (i : Fin n) (v : DoubledSpace (RouterAmplitude n)) :
    routerModularHamiltonian n x i v = routerMeanEnergy n x i • v := by
  exact kreinRouterModularHamiltonian_apply (H := DoubledSpace (RouterAmplitude n))
    (n := n) (x := x) (i := i) (v := v)

end RouterHamiltonian

section KMSResidual

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Absolute algebraic KMS residual for a pair of observables. -/
noncomputable def kmsResidual
    (K : AlgebraEnd F) (ω : AlgebraEnd F →L[ℝ] ℝ) (β : ℝ)
    (A B : AlgebraEnd F) : ℝ :=
  |ω (A * modularShift (E := F) K β B) - ω (B * A)|

/-- `ε`-approximate KMS condition. -/
def SatisfiesApproxKMSLike
    (K : AlgebraEnd F) (ω : AlgebraEnd F →L[ℝ] ℝ) (β ε : ℝ) : Prop :=
  ∀ A B : AlgebraEnd F, kmsResidual K ω β A B ≤ ε

end KMSResidual

section SinkhornBridge

variable (n : Nat)
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

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
Approximate stepwise KMS closure tracked by the RN barrier budget.
-/
def SinkhornApproxKMSClosure
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ) : Prop :=
  ∀ k : Nat,
    SatisfiesApproxKMSLike K (ω (k + 1)) β (trajectoryRNBarrierNext n T k)

/--
Control implies approximate stepwise KMS closure, with no zero-barrier collapse.
-/
private theorem sinkhorn_step_approxKMSClosure_of_control
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hControl : SinkhornKMSControl n T K ω β) :
    SinkhornApproxKMSClosure n T K ω β := by
  intro k A B
  exact hControl k A B

/--
Approximate stepwise closure upgrades to exact KMS closure when the RN barrier
vanishes identically.
-/
theorem sinkhorn_step_kmsClosure_of_approxClosure_of_barrierZero
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hApproxClosure : SinkhornApproxKMSClosure n T K ω β)
    (hBarrierZero : ∀ k : Nat, trajectoryRNBarrierNext n T k = 0) :
    SinkhornKMSClosure n T K ω β := by
  intro k A B
  have hle : kmsResidual K (ω (k + 1)) β A B ≤ 0 := by
    have hAB :
        kmsResidual K (ω (k + 1)) β A B
          ≤ trajectoryRNBarrierNext n T k :=
      hApproxClosure k A B
    simpa [hBarrierZero k] using hAB
  have hEqAbs : kmsResidual K (ω (k + 1)) β A B = 0 :=
    le_antisymm hle (by
      unfold kmsResidual
      exact abs_nonneg _)
  have hEqSub :
      ω (k + 1) (A * modularShift (E := F) K β B) - ω (k + 1) (B * A) = 0 := by
    exact abs_eq_zero.mp (by simpa [kmsResidual] using hEqAbs)
  exact sub_eq_zero.mp hEqSub

/--
Approximate stepwise closure directly yields Sinkhorn control.
-/
private theorem sinkhorn_control_of_step_approxKMSClosure
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hApproxClosure : SinkhornApproxKMSClosure n T K ω β) :
    SinkhornKMSControl n T K ω β := by
  intro k A B
  exact hApproxClosure k A B

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
  intro k A B
  have hApproxClosure : SinkhornApproxKMSClosure n T K ω β :=
    sinkhorn_step_approxKMSClosure_of_control
      (n := n) (T := T) (K := K) (ω := ω) (β := β) hControl
  exact sinkhorn_step_kmsClosure_of_approxClosure_of_barrierZero
    (n := n) (T := T) (K := K) (ω := ω) (β := β)
    (hApproxClosure := hApproxClosure)
    (hBarrierZero := fun j => trajectoryRNBarrierNext_eq_zero (n := n) T j)
    k A B

/-- Canonical theorem name: exact KMS closure implies Sinkhorn control. -/
private theorem sinkhorn_control_of_step_kmsClosure
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hClosure : SinkhornKMSClosure n T K ω β) :
    SinkhornKMSControl n T K ω β := by
  have hApproxClosure : SinkhornApproxKMSClosure n T K ω β := by
    intro k A B
    have hEq :
        ω (k + 1) (A * modularShift (E := F) K β B) - ω (k + 1) (B * A) = 0 := by
      rw [sub_eq_zero]
      exact hClosure k A B
    have hAB : kmsResidual K (ω (k + 1)) β A B ≤ 0 := by
      unfold kmsResidual
      simp [hEq]
    have hzero : trajectoryRNBarrierNext n T k = 0 :=
      trajectoryRNBarrierNext_eq_zero (n := n) T k
    simpa [hzero] using hAB
  exact sinkhorn_control_of_step_approxKMSClosure
    (n := n) (T := T) (K := K) (ω := ω) (β := β) hApproxClosure

/--
Closure equivalence: in this finite Sinkhorn scaffold, the control inequality and
exact stepwise KMS closure are equivalent.
-/
private theorem sinkhornKMSControl_iff_kmsClosure
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ) :
    SinkhornKMSControl n T K ω β ↔ SinkhornKMSClosure n T K ω β := by
  constructor
  · intro hControl
    exact sinkhorn_step_kmsClosure_of_control
      (n := n) (T := T) (K := K) (ω := ω) (β := β) hControl
  · intro hClosure
    exact sinkhorn_control_of_step_kmsClosure
      (n := n) (T := T) (K := K) (ω := ω) (β := β) hClosure

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

/--
Closure-first quantitative form: the pre-step RN-barrier bound follows directly
from exact KMS closure.
-/
private theorem sinkhorn_stepwise_kms_bound_of_kmsClosure
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hClosure : SinkhornKMSClosure n T K ω β) :
    ∀ k : Nat, ∀ A B : AlgebraEnd F,
      kmsResidual K (ω (k + 1)) β A B ≤ trajectoryRNBarrier n T k := by
  have hDrive : SinkhornKMSControl n T K ω β :=
    sinkhorn_control_of_step_kmsClosure (n := n) (T := T) (K := K) (ω := ω) (β := β) hClosure
  exact sinkhorn_stepwise_kms_bound
    (n := n) (T := T) (K := K) (ω := ω) (β := β) hDrive

end SinkhornBridge

end InfoGeometry.Canonical.KMSSinkhornBridge
