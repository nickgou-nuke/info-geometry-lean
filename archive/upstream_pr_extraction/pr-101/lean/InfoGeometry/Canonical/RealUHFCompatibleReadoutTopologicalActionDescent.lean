import InfoGeometry.Canonical.RealUHFCompatibleReadoutTopologicalDescent

/-!
# Continuous time slices of the normalized-trace descent

This owner records only consequences of the already constructed continuous
colimit action.  It does not assert a C*-completion, a KMS theorem, or a
state-space inverse-limit theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutTopologicalActionDescent

open CategoryTheory
open InfoGeometry.Canonical.CliffordCARTopologicalColimit
open InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalTrace
open InfoGeometry.Canonical.RealUHFCompatibleReadoutColimitDynamicsBridge
open InfoGeometry.Canonical.RealUHFCompatibleReadoutContinuousColimitAction
open InfoGeometry.Canonical.RealUHFCompatibleReadoutTopologicalDescent

theorem continuous_normalizedTraceReadoutAtTime (t : ℝ) :
    Continuous (normalizedTraceReadoutAtTime t) := by
  exact (normalizedTraceReadoutAtTime t).hom.continuous

theorem normalizedTraceReadoutAtTime_matches_action_slice
    (t : ℝ)
    (x : InfoGeometry.Canonical.CliffordCARTopologicalColimit.topologicalColimit) :
    normalizedTraceReadoutAtTime t x =
      normalizedTraceReadoutAction (t, x) := by
  rw [normalizedTraceReadoutAtTime_eq_postcomposition]
  rfl

theorem normalizedTraceReadoutAtTime_add
    (s t : ℝ)
    (x : InfoGeometry.Canonical.CliffordCARTopologicalColimit.topologicalColimit) :
    normalizedTraceReadoutAtTime (s + t) x =
      Real.exp s * normalizedTraceReadoutAtTime t x := by
  rw [normalizedTraceReadoutAtTime_eq_postcomposition,
    normalizedTraceReadoutAtTime_eq_postcomposition]
  simp [scalarValueMap, Real.exp_add, mul_assoc]

end InfoGeometry.Canonical.RealUHFCompatibleReadoutTopologicalActionDescent
