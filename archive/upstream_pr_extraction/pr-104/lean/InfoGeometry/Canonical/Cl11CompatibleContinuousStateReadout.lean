import InfoGeometry.Canonical.Cl11CompatibleRealAlgebraicStateNetTopological
import InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitBridge
import InfoGeometry.Canonical.Cl11MarkovJonesTopologicalColimit

/-!
# Real continuous state readouts for the `Cl(1,1)` tower

This is the real finite-stage counterpart of the repository's continuous
state-readout interfaces.  It packages normalization and positivity together
with the already proved compatible continuous family, without asserting a
completed C*-algebra or a KMS state space.
-/

namespace InfoGeometry.Canonical.Cl11CompatibleContinuousStateReadout

open InfoGeometry.Canonical.Cl11CompatibleRealAlgebraicStateNet
open InfoGeometry.Canonical.Cl11CompatibleRealAlgebraicStateNetTopological
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitBridge
open InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalTrace
open InfoGeometry.Canonical.CliffordCARAlgebraicTopologicalComparison
open InfoGeometry.Canonical.CliffordCARTopologicalColimit
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11MarkovJonesEngine
open InfoGeometry.Canonical.Cl11MarkovJonesTopologicalColimit

noncomputable section

structure CompatibleContinuousNormalizedPositiveReadout where
  readout : CompatibleContinuousReadoutFamily
  normalized : ∀ n : ℕ, readout.1 n (1 : MatStage n) = 1
  positive : ∀ n : ℕ, ∀ X : MatStage n,
    0 ≤ readout.1 n (star X * X)

noncomputable instance : TopologicalSpace
    CompatibleContinuousNormalizedPositiveReadout :=
  TopologicalSpace.induced
    (fun ρ : CompatibleContinuousNormalizedPositiveReadout => ρ.readout)
    (inferInstance : TopologicalSpace CompatibleContinuousReadoutFamily)

noncomputable def normalizedTraceStateReadout :
    CompatibleContinuousNormalizedPositiveReadout :=
  { readout := normalizedTraceReadoutFamily
    normalized := by
      intro n
      change normalizedTrace n (1 : MatStage n) = 1
      exact (Cl11FiniteNormalizedTraceState.normalizedTraceState n).normalized
    positive := by
      intro n X
      change 0 ≤ normalizedTrace n (star X * X)
      exact Cl11FiniteNormalizedTraceState.normalizedTraceState_positive n X }

@[simp] theorem normalizedTraceStateReadout_apply
    (n : ℕ) (X : MatStage n) :
    normalizedTraceStateReadout.readout.1 n X = normalizedTrace n X := rfl

theorem normalizedTraceStateReadout_normalized
    (n : ℕ) :
    normalizedTraceStateReadout.readout.1 n (1 : MatStage n) = 1 := by
  exact normalizedTraceStateReadout.normalized n

theorem normalizedTraceStateReadout_positive
    (n : ℕ) (X : MatStage n) :
    0 ≤ normalizedTraceStateReadout.readout.1 n (star X * X) := by
  exact normalizedTraceStateReadout.positive n X

theorem normalizedTraceStateReadout_agrees_with_algebraic_net
    (n : ℕ) (X : MatStage n) :
    normalizedTraceStateReadout.readout.1 n X =
      cl11CompatibleRealAlgebraicStateNet.state n X := by
  rw [normalizedTraceStateReadout_apply]
  exact (state_eq_normalizedTrace n X).symm

theorem normalizedTraceStateReadout_continuous
    (n : ℕ) :
    Continuous
      (fun X : MatStage n =>
        normalizedTraceStateReadout.readout.1 n X) := by
  exact (normalizedTraceStateReadout.readout.1 n).continuous

theorem normalizedTraceStateReadout_direct_compatibility
    {m n : ℕ} (h : m ≤ n) (X : MatStage m) :
    normalizedTraceStateReadout.readout.1 n (stageEmbedMap h X) =
      normalizedTraceStateReadout.readout.1 m X := by
  rw [normalizedTraceStateReadout_apply, normalizedTraceStateReadout_apply]
  exact normalizedTrace_stageEmbedMap h X

theorem normalizedTraceStateReadout_cyclic
    (n : ℕ) (X Y : MatStage n) :
    normalizedTraceStateReadout.readout.1 n (X * Y) =
      normalizedTraceStateReadout.readout.1 n (Y * X) := by
  rw [normalizedTraceStateReadout_apply, normalizedTraceStateReadout_apply]
  unfold normalizedTrace
  rw [Matrix.trace_mul_comm]

theorem normalizedTraceStateReadout_conjugation_invariant
    (n : ℕ) (u uInv X : MatStage n)
    (hunit : uInv * u = 1) :
    normalizedTraceStateReadout.readout.1 n (u * X * uInv) =
      normalizedTraceStateReadout.readout.1 n X := by
  rw [normalizedTraceStateReadout_apply, normalizedTraceStateReadout_apply]
  unfold normalizedTrace
  rw [Matrix.trace_mul_comm, ← mul_assoc, hunit]
  simp

theorem normalizedTraceColimitMap_matches_state_readout
    (n : ℕ) (X : MatStage n) :
    normalizedTraceTopologicalColimitMap
        (topologicalInjection n X) =
      normalizedTraceStateReadout.readout.1 n X := by
  rw [normalizedTraceColimitMap_matches_inverse_family,
    normalizedTraceReadoutFamily_apply,
    normalizedTraceStateReadout_apply]

theorem normalizedTraceColimitMap_unique_from_state_readout
    (f : InfoGeometry.Canonical.CliffordCARTopologicalColimit.topologicalColimit
      ⟶ TopCat.of ℝ)
    (hf : ∀ (n : ℕ) (X : MatStage n),
      f (topologicalInjection n X) =
        normalizedTraceStateReadout.readout.1 n X) :
    f = normalizedTraceTopologicalColimitMap := by
  apply normalizedTraceColimitMap_unique_from_inverse_family
  intro n X
  rw [hf n X, normalizedTraceStateReadout_apply,
    normalizedTraceReadoutFamily_apply]

end

end InfoGeometry.Canonical.Cl11CompatibleContinuousStateReadout
