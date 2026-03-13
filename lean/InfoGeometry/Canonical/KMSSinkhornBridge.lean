import InfoGeometry.Krein.Thermal
import InfoGeometry.Canonical.ChiralAnomaly
import InfoGeometry.Canonical.IBCore
import Mathlib.Analysis.InnerProductSpace.LinearMap

open scoped BigOperators

namespace InfoGeometry.Canonical.KMSSinkhornBridge

open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.ChiralAnomaly
open InfoGeometry.Canonical.IB
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
variable (n : Nat) [Nonempty (Fin n)]

/-- Router-amplitude space over experts. -/
abbrev RouterAmplitude := EuclideanSpace ℝ (Fin n)

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

/-- Lemma `satisfiesApproxKMSLike_of_satisfiesKMSLike`. -/
lemma satisfiesApproxKMSLike_of_satisfiesKMSLike
    (K : AlgebraEnd F) (ω : AlgebraEnd F →L[ℝ] ℝ) (β : ℝ)
    (hKMS : SatisfiesKMSLike (E := F) K ω β) :
    SatisfiesApproxKMSLike K ω β 0 := by
  intro A B
  unfold kmsResidual
  have hEq : ω (A * modularShift (E := F) K β B) - ω (B * A) = 0 := by
    exact sub_eq_zero.mpr (hKMS A B)
  simp [hEq]

/-- Lemma `satisfiesKMSLike_of_approx_zero`. -/
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
Closure equivalence: in this finite Sinkhorn scaffold, the control inequality and
exact stepwise KMS closure are equivalent.
-/
theorem sinkhornKMSControl_iff_kmsClosure
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
theorem sinkhorn_stepwise_kms_bound_of_kmsClosure
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

/--
Expectation-based seed functional on doubled operators:
`ωSeed(A) = ⟪A Ω, Ω⟫`.
-/
noncomputable def expectationSeedFunctional
    (Ω : DoubledSpace F) :
    AlgebraEnd F →L[ℝ] ℝ :=
  (innerSL ℝ Ω).comp
    (ContinuousLinearMap.apply ℝ (DoubledSpace F) Ω)

@[simp] lemma expectationSeedFunctional_apply
    (Ω : DoubledSpace F) (A : AlgebraEnd F) :
    expectationSeedFunctional (F := F) Ω A = inner ℝ (A Ω) Ω := by
  simp [expectationSeedFunctional, real_inner_comm]

/-- Canonical notation for the expectation-based seed state `ωSeed`. -/
noncomputable abbrev omegaSeed (Ω : DoubledSpace F) :
    AlgebraEnd F →L[ℝ] ℝ :=
  expectationSeedFunctional (F := F) Ω

@[simp] lemma omegaSeed_apply
    (Ω : DoubledSpace F) (A : AlgebraEnd F) :
    omegaSeed (F := F) Ω A = inner ℝ (A Ω) Ω := by
  simp [omegaSeed]

@[simp] lemma expectationSeedFunctional_id
    (Ω : DoubledSpace F) :
    expectationSeedFunctional (F := F) Ω
      (ContinuousLinearMap.id ℝ (DoubledSpace F)) = ‖Ω‖ ^ (2 : Nat) := by
  rw [expectationSeedFunctional]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply]
  simp

/-- Nontriviality of the expectation seed from a nonzero doubled state. -/
lemma expectationSeedFunctional_nonzero
    (Ω : DoubledSpace F)
    (hΩ : Ω ≠ 0) :
    expectationSeedFunctional (F := F) Ω ≠ 0 := by
  intro hzero
  have hid :
      expectationSeedFunctional (F := F) Ω
        (ContinuousLinearMap.id ℝ (DoubledSpace F)) = 0 := by
    simp [hzero]
  have hnormsq : ‖Ω‖ ^ (2 : Nat) = 0 := by
    simpa [expectationSeedFunctional_id (F := F) Ω] using hid
  have hnorm : ‖Ω‖ = 0 := by
    exact sq_eq_zero_iff.mp (by simpa [pow_two] using hnormsq)
  exact hΩ (norm_eq_zero.mp hnorm)

/-- Nontriviality of `ωSeed` from a nonzero thermal vacuum vector. -/
lemma omegaSeed_nonzero_of_thermalVacuum
    (K : AlgebraEnd F)
    (vac : ThermalVacuum (E := F) K) :
    omegaSeed (F := F) vac.Omega ≠ 0 :=
  expectationSeedFunctional_nonzero (F := F) vac.Omega vac.vacuum_nonzero

/--
Structural hypotheses certifying KMS for the expectation seed.
These are the finite algebraic Tomita-style conditions used by this bridge.
-/
structure ExpectationSeedKMSHypotheses
    (K : AlgebraEnd F) (β : ℝ) (Ω : DoubledSpace F) : Prop where
  modularOnOmega :
    ∀ B : AlgebraEnd F,
      modularShift (E := F) K β B Ω = B Ω
  cyclicOnOmega :
    ∀ A B : AlgebraEnd F,
      inner ℝ ((A * B) Ω) Ω = inner ℝ ((B * A) Ω) Ω

/--
Joint-kernel hypothesis on `Ω`: the modular defect `(σ_β(B) - B)` annihilates
`Ω` for every observable `B`.
-/
def JointKernelOnOmega
    (K : AlgebraEnd F) (β : ℝ) (Ω : DoubledSpace F) : Prop :=
  ∀ B : AlgebraEnd F, (modularShift (E := F) K β B - B) Ω = 0

/--
Commutator orthogonality on `Ω`:
the expectation pairing of `[A,B]Ω` against `Ω` vanishes.
-/
def CommutatorOrthogonalOnOmega
    (Ω : DoubledSpace F) : Prop :=
  ∀ A B : AlgebraEnd F, inner ℝ (((A * B - B * A) Ω)) Ω = 0

/--
`JointKernelOnOmega` implies the structural modular-on-`Ω` identity.
-/
lemma modularOnOmega_of_jointKernel
    (K : AlgebraEnd F)
    (β : ℝ)
    (Ω : DoubledSpace F)
    (hJointKernel : JointKernelOnOmega (F := F) K β Ω) :
    ∀ B : AlgebraEnd F, modularShift (E := F) K β B Ω = B Ω := by
  intro B
  have hB : (modularShift (E := F) K β B - B) Ω = 0 := hJointKernel B
  have hSub : modularShift (E := F) K β B Ω - B Ω = 0 := by
    simpa using hB
  exact sub_eq_zero.mp hSub

/--
Commutator orthogonality implies cyclic expectation pairing on products.
-/
lemma cyclicOnOmega_of_commutator_orthogonal
    (Ω : DoubledSpace F)
    (hCommOrthogonal : CommutatorOrthogonalOnOmega (F := F) Ω) :
    ∀ A B : AlgebraEnd F,
      inner ℝ ((A * B) Ω) Ω = inner ℝ ((B * A) Ω) Ω := by
  intro A B
  have hAB : inner ℝ (((A * B - B * A) Ω)) Ω = 0 := hCommOrthogonal A B
  have hSub :
      inner ℝ ((A * B) Ω) Ω - inner ℝ ((B * A) Ω) Ω = 0 := by
    simpa [inner_sub_left] using hAB
  exact sub_eq_zero.mp hSub

/--
Constructive packing of `ExpectationSeedKMSHypotheses` from the explicit
joint-kernel and commutator-orthogonality inputs.
-/
theorem expectationSeedKMSHypotheses_of_jointKernel_commutator
    (K : AlgebraEnd F)
    (β : ℝ)
    (Ω : DoubledSpace F)
    (hJointKernel : JointKernelOnOmega (F := F) K β Ω)
    (hCommOrthogonal : CommutatorOrthogonalOnOmega (F := F) Ω) :
    ExpectationSeedKMSHypotheses (F := F) K β Ω := by
  refine ⟨?_, ?_⟩
  · exact modularOnOmega_of_jointKernel (F := F) (K := K) (β := β) (Ω := Ω) hJointKernel
  · exact cyclicOnOmega_of_commutator_orthogonal (F := F) (Ω := Ω) hCommOrthogonal

/--
Structural KMS theorem for the expectation seed:
if the modularly shifted observable acts identically on `Ω` and the induced
vector-state pairing is cyclic on products, then `ωSeed` satisfies KMS.
-/
theorem expectationSeedFunctional_kms_of_structural
    (K : AlgebraEnd F)
    (β : ℝ)
    (Ω : DoubledSpace F)
    (hModularOnOmega :
      ∀ B : AlgebraEnd F,
        modularShift (E := F) K β B Ω = B Ω)
    (hCyclicOnOmega :
      ∀ A B : AlgebraEnd F,
        inner ℝ ((A * B) Ω) Ω = inner ℝ ((B * A) Ω) Ω) :
    SatisfiesKMSLike (E := F) K (expectationSeedFunctional (F := F) Ω) β := by
  intro A B
  have hAB :
      inner ℝ ((A * modularShift (E := F) K β B) Ω) Ω
        = inner ℝ ((A * B) Ω) Ω := by
    have hmod : (A * modularShift (E := F) K β B) Ω = (A * B) Ω := by
      simpa using congrArg (fun v => A v) (hModularOnOmega B)
    simpa using congrArg (fun v => inner ℝ v Ω) hmod
  calc
    expectationSeedFunctional (F := F) Ω
      (A * modularShift (E := F) K β B)
        = inner ℝ ((A * modularShift (E := F) K β B) Ω) Ω := by
            simpa using
              (expectationSeedFunctional_apply
                (F := F) Ω (A * modularShift (E := F) K β B))
    _ = inner ℝ ((A * B) Ω) Ω := hAB
    _ = inner ℝ ((B * A) Ω) Ω := hCyclicOnOmega A B
    _ = expectationSeedFunctional (F := F) Ω (B * A) := by
            simpa using
              (expectationSeedFunctional_apply (F := F) Ω (B * A)).symm

/--
Packaged KMS law for `ωSeed` from explicit structural hypotheses.
-/
theorem omegaSeed_kms_of_hypotheses
    (K : AlgebraEnd F)
    (β : ℝ)
    (Ω : DoubledSpace F)
    (hStruct : ExpectationSeedKMSHypotheses (F := F) K β Ω) :
    SatisfiesKMSLike (E := F) K (omegaSeed (F := F) Ω) β := by
  exact expectationSeedFunctional_kms_of_structural
    (F := F) (K := K) (β := β) (Ω := Ω)
    hStruct.modularOnOmega hStruct.cyclicOnOmega

/--
KMS law for `ωSeed` from explicit joint-kernel and commutator-orthogonality
hypotheses.
-/
theorem omegaSeed_kms_of_jointKernel_commutator
    (K : AlgebraEnd F)
    (β : ℝ)
    (Ω : DoubledSpace F)
    (hJointKernel : JointKernelOnOmega (F := F) K β Ω)
    (hCommOrthogonal : CommutatorOrthogonalOnOmega (F := F) Ω) :
    SatisfiesKMSLike (E := F) K (omegaSeed (F := F) Ω) β := by
  exact omegaSeed_kms_of_hypotheses
    (F := F) (K := K) (β := β) (Ω := Ω)
    (expectationSeedKMSHypotheses_of_jointKernel_commutator
      (F := F) (K := K) (β := β) (Ω := Ω) hJointKernel hCommOrthogonal)

/--
IB-side Radon-Nikodym ratio at coordinate `(x0,t0)` and step `k`.
The additive `1` keeps the ratio strictly positive in the finite model.
-/
noncomputable def ibRNDerivative
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (pTrajectory : Nat → Xib → FinProb Tib)
    (x0 : Xib) (t0 : Tib) (k : Nat) : ℝ :=
  1 + (pTrajectory k x0 t0).toReal

lemma ibRNDerivative_pos
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (pTrajectory : Nat → Xib → FinProb Tib)
    (x0 : Xib) (t0 : Tib) (k : Nat) :
    0 < ibRNDerivative (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 k := by
  unfold ibRNDerivative
  have hnonneg : 0 ≤ (pTrajectory k x0 t0).toReal := by
    exact ENNReal.toReal_nonneg
  linarith

/--
Generating potential: negative logarithmic Radon-Nikodym derivative.
-/
noncomputable def ibRNPotential
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (pTrajectory : Nat → Xib → FinProb Tib)
    (x0 : Xib) (t0 : Tib) (k : Nat) : ℝ :=
  -Real.log (ibRNDerivative (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 k)

/--
IB-induced scalar observable weight generated by the RN potential:
`exp(-V_RN)`.
-/
noncomputable def ibObservableWeight
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (pTrajectory : Nat → Xib → FinProb Tib)
    (x0 : Xib) (t0 : Tib) (k : Nat) : ℝ :=
  Real.exp (-(ibRNPotential (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 k))

/-- Relative volume change induced by the RN generating potential. -/
noncomputable abbrev ibRelativeVolumeChange
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (pTrajectory : Nat → Xib → FinProb Tib)
    (x0 : Xib) (t0 : Tib) (k : Nat) : ℝ :=
  ibObservableWeight (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 k

/--
`exp(-V_RN)` reproduces the RN derivative: multiplicative relative-volume form.
-/
lemma ibRelativeVolumeChange_eq_ibRNDerivative
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (pTrajectory : Nat → Xib → FinProb Tib)
    (x0 : Xib) (t0 : Tib) (k : Nat) :
    ibRelativeVolumeChange (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 k
      = ibRNDerivative (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 k := by
  unfold ibRelativeVolumeChange ibObservableWeight ibRNPotential
  simp [Real.exp_log (ibRNDerivative_pos
    (Xib := Xib) (Yib := Yib) (Tib := Tib) (pTrajectory := pTrajectory) (x0 := x0) (t0 := t0) (k := k))]

/--
The RN potential is the negative log of relative-volume change.
-/
lemma ibRNPotential_eq_neg_log_relativeVolumeChange
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (pTrajectory : Nat → Xib → FinProb Tib)
    (x0 : Xib) (t0 : Tib) (k : Nat) :
    ibRNPotential (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 k
      = -Real.log (ibRelativeVolumeChange
          (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 k) := by
  rw [ibRelativeVolumeChange_eq_ibRNDerivative
    (Xib := Xib) (Yib := Yib) (Tib := Tib) (pTrajectory := pTrajectory) (x0 := x0) (t0 := t0) (k := k)]
  rfl

/--
Determinant-based relative volume of a Jacobian flow map.
-/
noncomputable def jacobianRelativeVolume
    [FiniteDimensional ℝ (DoubledSpace F)]
    (J : AlgebraEnd F) : ℝ :=
  |LinearMap.det J.toLinearMap|

/--
Negative log-determinant generating potential attached to a Jacobian flow map.
-/
noncomputable def jacobianLogPotential
    [FiniteDimensional ℝ (DoubledSpace F)]
    (J : AlgebraEnd F) : ℝ :=
  -Real.log (jacobianRelativeVolume (F := F) J)

lemma jacobianRelativeVolume_pos_of_det_ne_zero
    [FiniteDimensional ℝ (DoubledSpace F)]
    {J : AlgebraEnd F}
    (hJ : LinearMap.det J.toLinearMap ≠ 0) :
    0 < jacobianRelativeVolume (F := F) J := by
  unfold jacobianRelativeVolume
  exact abs_pos.mpr hJ

/--
`exp(-K_J)` reproduces determinant relative volume when the Jacobian determinant
is nonzero.
-/
lemma exp_neg_jacobianLogPotential_eq_jacobianRelativeVolume
    [FiniteDimensional ℝ (DoubledSpace F)]
    (J : AlgebraEnd F)
    (hJ : LinearMap.det J.toLinearMap ≠ 0) :
    Real.exp (-(jacobianLogPotential (F := F) J))
      = jacobianRelativeVolume (F := F) J := by
  unfold jacobianLogPotential
  simp [Real.exp_log, jacobianRelativeVolume_pos_of_det_ne_zero (F := F) hJ]

/--
Unification theorem:
if RN relative volume equals Jacobian determinant relative volume, then the
negative-log generating potentials coincide.
-/
theorem ibRNPotential_eq_jacobianLogPotential_of_relativeVolume_match
    [FiniteDimensional ℝ (DoubledSpace F)]
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (pTrajectory : Nat → Xib → FinProb Tib)
    (x0 : Xib) (t0 : Tib) (k : Nat)
    (J : AlgebraEnd F)
    (hMatch :
      ibRelativeVolumeChange (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 k
        = jacobianRelativeVolume (F := F) J) :
    ibRNPotential (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 k
      = jacobianLogPotential (F := F) J := by
  rw [ibRNPotential_eq_neg_log_relativeVolumeChange
    (Xib := Xib) (Yib := Yib) (Tib := Tib) (pTrajectory := pTrajectory) (x0 := x0) (t0 := t0) (k := k)]
  unfold jacobianLogPotential
  simp [hMatch]

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
IB-to-Sinkhorn control for the weighted family using a nonzero expectation seed
`ωSeed(A) = ⟪A Ω, Ω⟫` and explicit structural KMS hypotheses.
-/
theorem sinkhorn_kmsControl_of_ibDynamics_weighted_from_expectationSeed
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
    (hStruct : ExpectationSeedKMSHypotheses (F := F) K β Ω) :
    SinkhornKMSControl n T K
      (ibInducedObservableWeighted
        (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib)
        pTrajectory x0 t0 (omegaSeed (F := F) Ω)) β := by
  have hSeedNonzero : omegaSeed (F := F) Ω ≠ 0 :=
    expectationSeedFunctional_nonzero (F := F) Ω hΩ
  have hSeedKMS :
      SatisfiesKMSLike (E := F) K (omegaSeed (F := F) Ω) β :=
    omegaSeed_kms_of_hypotheses (F := F) (K := K) (β := β) (Ω := Ω) hStruct
  have _hWeightedNonzero :
      ∀ k : Nat,
        ibInducedObservableWeighted
          (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib)
          pTrajectory x0 t0 (omegaSeed (F := F) Ω) k ≠ 0 :=
    ibInducedObservableWeighted_nonzero
      (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib)
      (pTrajectory := pTrajectory) (x0 := x0) (t0 := t0)
      (ωSeed := omegaSeed (F := F) Ω)
      hSeedNonzero
  refine sinkhorn_kmsControl_of_ibDynamics_weighted
    (n := n) (T := T) (K := K) (β := β)
    (prob := prob) (pTrajectory := pTrajectory)
    hStep (x0 := x0) (t0 := t0)
    (ωSeed := omegaSeed (F := F) Ω)
    hSeedKMS

/--
Canonical specialization: seed `ωSeed` with a nonzero thermal vacuum vector.
-/
theorem sinkhorn_kmsControl_of_ibDynamics_weighted_from_thermalVacuum
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
    (vac : ThermalVacuum (E := F) K)
    (hStruct :
      ExpectationSeedKMSHypotheses (F := F) K β vac.Omega) :
    SinkhornKMSControl n T K
      (ibInducedObservableWeighted
        (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib)
        pTrajectory x0 t0 (omegaSeed (F := F) vac.Omega)) β := by
  exact sinkhorn_kmsControl_of_ibDynamics_weighted_from_expectationSeed
    (n := n) (T := T) (K := K) (β := β)
    (prob := prob) (pTrajectory := pTrajectory)
    hStep (x0 := x0) (t0 := t0)
    (Ω := vac.Omega) vac.vacuum_nonzero hStruct

/--
Backward-compatible unbundled form of the expectation-seed theorem.
-/
theorem sinkhorn_kmsControl_of_ibDynamics_weighted_from_ibData
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
    (hModularOnOmega :
      ∀ B : AlgebraEnd F,
        modularShift (E := F) K β B Ω = B Ω)
    (hCyclicOnOmega :
      ∀ A B : AlgebraEnd F,
        inner ℝ ((A * B) Ω) Ω = inner ℝ ((B * A) Ω) Ω) :
    SinkhornKMSControl n T K
      (ibInducedObservableWeighted
        (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib)
        pTrajectory x0 t0 (omegaSeed (F := F) Ω)) β := by
  exact sinkhorn_kmsControl_of_ibDynamics_weighted_from_expectationSeed
    (n := n) (T := T) (K := K) (β := β)
    (prob := prob) (pTrajectory := pTrajectory)
    hStep (x0 := x0) (t0 := t0)
    (Ω := Ω) hΩ
    ⟨hModularOnOmega, hCyclicOnOmega⟩

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
  refine sinkhorn_kmsControl_of_ibDynamics_weighted_from_expectationSeed
    (n := n) (T := T) (K := K) (β := β)
    (prob := prob) (pTrajectory := pTrajectory)
    hStep (x0 := x0) (t0 := t0)
    (Ω := Ω) hΩ ?_
  exact expectationSeedKMSHypotheses_of_jointKernel_commutator
    (F := F) (K := K) (β := β) (Ω := Ω) hJointKernel hCommOrthogonal

end SinkhornBridge

section RouterSinkhornBridge

variable (n : Nat)

end RouterSinkhornBridge

end InfoGeometry.Canonical.KMSSinkhornBridge
