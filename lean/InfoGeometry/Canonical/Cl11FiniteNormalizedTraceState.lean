import InfoGeometry.Canonical.Cl11CompatibleLocalStateNetTopological
import InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
import InfoGeometry.Prequantum.AlgebraicGNSState

/-!
# Finite real algebraic states for the `Cl(1,1)` matrix tower

The normalized matrix trace is packaged here using the repository's native
`RealAlgebraicState` interface.  Positivity is finite-stage positivity on
`star A * A`; no completed C*-state or global KMS state is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11FiniteNormalizedTraceState

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11MarkovJonesEngine
open InfoGeometry.Canonical.Cl11CompatibleLocalStateNet
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Prequantum.AlgebraicGNSState

def normalizedTraceState (n : ℕ) :
    RealAlgebraicState (MatStage n) where
  toLinearMap := normalizedTraceLinear n
  normalized := by
    change normalizedTrace n (1 : MatStage n) = 1
    unfold normalizedTrace
    rw [trace_one_matStage]
    field_simp [pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)]
  positive := by
    intro A
    change 0 ≤ normalizedTrace n (star A * A)
    unfold normalizedTrace
    apply div_nonneg
    · classical
      unfold Matrix.trace
      change 0 ≤ ∑ i : InfoGeometry.Clifford.TowerMatrix.Idx n,
        ∑ j : InfoGeometry.Clifford.TowerMatrix.Idx n, (A j i) * (A j i)
      exact Finset.sum_nonneg (fun i _ =>
        Finset.sum_nonneg (fun j _ => mul_self_nonneg (A j i)))
    · positivity
  symmetric := by
    intro A B
    change normalizedTrace n (star B * A) = normalizedTrace n (star A * B)
    unfold normalizedTrace
    have htrace : Matrix.trace (star B * A) =
        star (Matrix.trace (star A * B)) := by
      rw [← Matrix.trace_conjTranspose]
      congr 1
      simp [star]
    rw [htrace]
    simp [star]

@[simp] theorem normalizedTraceState_eval
    (n : ℕ) (A : MatStage n) :
    (normalizedTraceState n).eval A = normalizedTrace n A := rfl

theorem normalizedTraceState_positive
    (n : ℕ) (A : MatStage n) :
    0 ≤ (normalizedTraceState n).eval (star A * A) :=
  (normalizedTraceState n).positive A

theorem normalizedTraceState_restrict
    (n : ℕ) :
    (normalizedTraceState n).toLinearMap.comp
        (stageRestrict n) =
      (normalizedTraceState (n + 1)).toLinearMap := by
  ext A
  change normalizedTrace n (stageRestrict n A) = normalizedTrace (n + 1) A
  exact normalizedTrace_stageRestrict n A

theorem normalizedTraceState_continuous_readout
    (n : ℕ) :
    (normalizedTraceState n).toLinearMap.toContinuousLinearMap =
      LinearMap.toContinuousLinearMap (normalizedTraceLinear n) := rfl

theorem normalizedTraceReadoutFamily_eq_state_readout
    (n : ℕ) :
    normalizedTraceReadoutFamily.1 n =
      (normalizedTraceState n).toLinearMap.toContinuousLinearMap := by
  rfl

end Cl11FiniteNormalizedTraceState

end Canonical
