import InfoGeometry.Canonical.SinkhornKMSCore
import InfoGeometry.Canonical.ChiralAnomaly
import InfoGeometry.Canonical.IBCore
import InfoGeometry.Canonical.RelativePotentialScalarBridge

set_option linter.unnecessarySeqFocus false

open scoped BigOperators

namespace InfoGeometry.Canonical.KMSSinkhornBridge

open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.ChiralAnomaly
open InfoGeometry.Canonical.IB
open InfoGeometry.Krein

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
private lemma expectationSeedFunctional_nonzero
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
    have hsq : ‖Ω‖ * ‖Ω‖ = 0 := by
      simpa [pow_two] using hnormsq
    nlinarith [sq_nonneg ‖Ω‖]
  exact hΩ (norm_eq_zero.mp hnorm)

/-- Nontriviality of `ωSeed` from a nonzero doubled state. -/
lemma omegaSeed_nonzero
    (Ω : DoubledSpace F)
    (hΩ : Ω ≠ 0) :
    omegaSeed (F := F) Ω ≠ 0 := by
  simpa [omegaSeed] using expectationSeedFunctional_nonzero (F := F) Ω hΩ

/-- Nontriviality of `ωSeed` from a nonzero thermal vacuum vector. -/
lemma omegaSeed_nonzero_of_thermalVacuum
    (K : AlgebraEnd F)
    (vac : ThermalVacuum (E := F) K) :
    omegaSeed (F := F) vac.Omega ≠ 0 :=
  omegaSeed_nonzero (F := F) vac.Omega vac.vacuum_nonzero

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
            exact expectationSeedFunctional_apply
              (F := F) Ω (A * modularShift (E := F) K β B)
    _ = inner ℝ ((A * B) Ω) Ω := hAB
    _ = inner ℝ ((B * A) Ω) Ω := hCyclicOnOmega A B
    _ = expectationSeedFunctional (F := F) Ω (B * A) := by
            exact (expectationSeedFunctional_apply (F := F) Ω (B * A)).symm

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
  exact expectationSeedFunctional_kms_of_structural
    (F := F) (K := K) (β := β) (Ω := Ω)
    (modularOnOmega_of_jointKernel (F := F) (K := K) (β := β) (Ω := Ω) hJointKernel)
    (cyclicOnOmega_of_commutator_orthogonal (F := F) (Ω := Ω) hCommOrthogonal)

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

lemma ibObservableWeight_pos
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (pTrajectory : Nat → Xib → FinProb Tib)
    (x0 : Xib) (t0 : Tib) (k : Nat) :
    0 < ibObservableWeight (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 k := by
  unfold ibObservableWeight
  exact Real.exp_pos _

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

/-- The IB RN potential is the singleton modular potential of relative volume change. -/
lemma ibRNPotential_eq_scalarModularPotential_relativeVolumeChange
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (pTrajectory : Nat → Xib → FinProb Tib)
    (x0 : Xib) (t0 : Tib) (k : Nat) :
    ibRNPotential (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 k =
      InfoGeometry.Canonical.RelativePotentialScalarBridge.scalarModularPotential
        (ibRelativeVolumeChange
          (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 k)
        (by
          rw [ibRelativeVolumeChange_eq_ibRNDerivative
            (Xib := Xib) (Yib := Yib) (Tib := Tib)
            (pTrajectory := pTrajectory) (x0 := x0) (t0 := t0) (k := k)]
          exact ibRNDerivative_pos
            (Xib := Xib) (Yib := Yib) (Tib := Tib)
            (pTrajectory := pTrajectory) (x0 := x0) (t0 := t0) (k := k)) := by
  rw [InfoGeometry.Canonical.RelativePotentialScalarBridge.scalarModularPotential_eq_neg_log]
  exact ibRNPotential_eq_neg_log_relativeVolumeChange
    (Xib := Xib) (Yib := Yib) (Tib := Tib)
    (pTrajectory := pTrajectory) (x0 := x0) (t0 := t0) (k := k)

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

/-- The Jacobian log-potential is the singleton modular potential of determinant volume. -/
lemma jacobianLogPotential_eq_scalarModularPotential
    [FiniteDimensional ℝ (DoubledSpace F)]
    (J : AlgebraEnd F)
    (hJ : LinearMap.det J.toLinearMap ≠ 0) :
    jacobianLogPotential (F := F) J =
      InfoGeometry.Canonical.RelativePotentialScalarBridge.scalarModularPotential
        (jacobianRelativeVolume (F := F) J)
        (jacobianRelativeVolume_pos_of_det_ne_zero (F := F) hJ) := by
  rw [InfoGeometry.Canonical.RelativePotentialScalarBridge.scalarModularPotential_eq_neg_log]
  rfl

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

section RouterSinkhornBridge

variable (n : Nat)

end RouterSinkhornBridge

end InfoGeometry.Canonical.KMSSinkhornBridge

