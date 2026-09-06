import InfoGeometry.Canonical.SinkhornKMSCore

set_option linter.unnecessarySeqFocus false

namespace InfoGeometry.Canonical.KMSSinkhornBridge

open InfoGeometry.Krein

/-!
# InfoGeometry.Canonical.KMSSinkhornSeedState

Seed-state KMS derivation layer for the Sinkhorn/KMS corridor.
-/

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

noncomputable local instance : NormedRing (AlgebraEnd F) := inferInstance
noncomputable local instance : NormedAlgebra ℝ (AlgebraEnd F) := inferInstance
local instance : IsTopologicalRing (AlgebraEnd F) := inferInstance
local instance : CompleteSpace (AlgebraEnd F) := inferInstance
local instance : SMulCommClass ℝ (AlgebraEnd F) (AlgebraEnd F) := inferInstance
local instance : IsScalarTower ℝ (AlgebraEnd F) (AlgebraEnd F) := inferInstance

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
Proof-carrying seed witness for the structural KMS lane: a concrete doubled seed
vector together with its nonzero, joint-kernel, and commutator-orthogonality
certificates.
-/
structure ExpectationSeedStructuralWitness
    (K : AlgebraEnd F) (β : ℝ) where
  Ω : DoubledSpace F
  hΩ : Ω ≠ 0
  jointKernel : JointKernelOnOmega (F := F) K β Ω
  commutatorOrthogonal : CommutatorOrthogonalOnOmega (F := F) Ω

namespace ExpectationSeedStructuralWitness

/-- Nontriviality of `ωSeed` extracted from a structural witness. -/
theorem omegaSeed_nonzero
    (W : ExpectationSeedStructuralWitness (F := F) K β) :
    omegaSeed (F := F) W.Ω ≠ 0 :=
  InfoGeometry.Canonical.KMSSinkhornBridge.omegaSeed_nonzero (F := F) W.Ω W.hΩ

end ExpectationSeedStructuralWitness

/--
At zero modular time (`β = 0`), the joint-kernel condition holds identically.
-/
@[simp] lemma jointKernelOnOmega_beta_zero
    (K : AlgebraEnd F)
    (Ω : DoubledSpace F) :
    JointKernelOnOmega (F := F) K 0 Ω := by
  intro B
  simp [modularShift]

/--
If the operator lane is pairwise commutative, the commutator-orthogonality
condition holds identically on every seed vector.
-/
lemma commutatorOrthogonalOnOmega_of_pairwise_commute
    (Ω : DoubledSpace F)
    (hComm : ∀ A B : AlgebraEnd F, A * B = B * A) :
    CommutatorOrthogonalOnOmega (F := F) Ω := by
  intro A B
  have hAB : A * B - B * A = 0 := sub_eq_zero.mpr (hComm A B)
  calc
    inner ℝ (((A * B - B * A) Ω)) Ω = inner ℝ ((0 : AlgebraEnd F) Ω) Ω := by
      simp [hAB]
    _ = 0 := by simp

/--
On a pairwise-commutative operator lane, modular conjugation is trivial for all
inverse temperatures `β`.
-/
lemma modularShift_eq_self_of_pairwise_commute
    (K : AlgebraEnd F)
    (β : ℝ)
    (hComm : ∀ A B : AlgebraEnd F, A * B = B * A)
    (B : AlgebraEnd F) :
    modularShift (E := F) K β B = B := by
  have hBK : Commute B K := by
    exact (hComm B K)
  have hBexp : Commute B (NormedSpace.exp (β • K)) := by
    simpa using (hBK.smul_right β).exp_right
  have hExpMul :
      NormedSpace.exp (β • K) * B = B * NormedSpace.exp (β • K) := by
    simpa using hBexp.eq.symm
  have hExpCancel :
      NormedSpace.exp (β • K) * NormedSpace.exp ((-β) • K) = 1 := by
    have hCommβ : Commute (β • K) ((-β) • K) :=
      ((Commute.refl K).smul_left β).smul_right (-β)
    calc
      NormedSpace.exp (β • K) * NormedSpace.exp ((-β) • K)
          = NormedSpace.exp ((β • K) + ((-β) • K)) := by
            rw [← NormedSpace.exp_add_of_commute hCommβ]
      _ = 1 := by simp
  unfold modularShift
  calc
    modularShift (E := F) K β B
        = NormedSpace.exp (β • K) * B * NormedSpace.exp ((-β) • K) := rfl
    _ = (B * NormedSpace.exp (β • K)) * NormedSpace.exp ((-β) • K) := by
          rw [hExpMul]
    _ = B * (NormedSpace.exp (β • K) * NormedSpace.exp ((-β) • K)) := by
          simp [mul_assoc]
    _ = B * 1 := by rw [hExpCancel]
    _ = B := by simp

/--
Nonzero/zero-temperature joint-kernel derivation from pairwise commutativity.
-/
lemma jointKernelOnOmega_of_pairwise_commute
    (K : AlgebraEnd F)
    (β : ℝ)
    (Ω : DoubledSpace F)
    (hComm : ∀ A B : AlgebraEnd F, A * B = B * A) :
    JointKernelOnOmega (F := F) K β Ω := by
  intro B
  have hShift :
      modularShift (E := F) K β B = B :=
    modularShift_eq_self_of_pairwise_commute (F := F) K β hComm B
  have hSub : modularShift (E := F) K β B - B = 0 := sub_eq_zero.mpr hShift
  simpa using congrArg (fun T => T Ω) hSub

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
Witness-routed KMS law for `ωSeed`, replacing the raw structural hypothesis pair
with a proof-carrying seed packet.
-/
theorem omegaSeed_kms_of_structuralWitness
    (K : AlgebraEnd F)
    (β : ℝ)
    (W : ExpectationSeedStructuralWitness (F := F) K β) :
    SatisfiesKMSLike (E := F) K (omegaSeed (F := F) W.Ω) β := by
  exact omegaSeed_kms_of_jointKernel_commutator
    (F := F) (K := K) (β := β) (Ω := W.Ω) W.jointKernel W.commutatorOrthogonal

/--
Constructive seed witness from a pairwise-commutative operator lane.
-/
def ExpectationSeedStructuralWitness.ofPairwiseCommute
    (K : AlgebraEnd F)
    (β : ℝ)
    (Ω : DoubledSpace F)
    (hΩ : Ω ≠ 0)
    (hComm : ∀ A B : AlgebraEnd F, A * B = B * A) :
    ExpectationSeedStructuralWitness (F := F) K β where
  Ω := Ω
  hΩ := hΩ
  jointKernel := jointKernelOnOmega_of_pairwise_commute (F := F) K β Ω hComm
  commutatorOrthogonal :=
    commutatorOrthogonalOnOmega_of_pairwise_commute (F := F) (Ω := Ω) hComm

/--
Constructive any-temperature surface:
if the operator lane is pairwise commutative, `ωSeed` satisfies KMS for any
inverse temperature `β`.
-/
theorem omegaSeed_kms_of_pairwise_commute
    (K : AlgebraEnd F)
    (β : ℝ)
    (Ω : DoubledSpace F)
    (hComm : ∀ A B : AlgebraEnd F, A * B = B * A) :
    SatisfiesKMSLike (E := F) K (omegaSeed (F := F) Ω) β := by
  by_cases hΩ : Ω = 0
  · subst hΩ
    have hJoint :
        JointKernelOnOmega (F := F) K β (0 : DoubledSpace F) :=
      jointKernelOnOmega_of_pairwise_commute (F := F) K β 0 hComm
    have hOrth :
        CommutatorOrthogonalOnOmega (F := F) (0 : DoubledSpace F) :=
      commutatorOrthogonalOnOmega_of_pairwise_commute (F := F) (Ω := 0) hComm
    exact omegaSeed_kms_of_jointKernel_commutator
      (F := F) (K := K) (β := β) (Ω := 0) hJoint hOrth
  · exact omegaSeed_kms_of_structuralWitness
      (F := F) (K := K) (β := β)
      (ExpectationSeedStructuralWitness.ofPairwiseCommute
        (F := F) K β Ω hΩ hComm)

/--
Constructive zero-temperature surface:
if the operator lane is pairwise commutative, `ωSeed` satisfies KMS at `β = 0`.
-/
theorem omegaSeed_kms_of_beta_zero_of_pairwise_commute
    (K : AlgebraEnd F)
    (Ω : DoubledSpace F)
    (hComm : ∀ A B : AlgebraEnd F, A * B = B * A) :
    SatisfiesKMSLike (E := F) K (omegaSeed (F := F) Ω) 0 := by
  simpa using
    (omegaSeed_kms_of_pairwise_commute (F := F) (K := K) (β := 0) (Ω := Ω) hComm)

end InfoGeometry.Canonical.KMSSinkhornBridge
