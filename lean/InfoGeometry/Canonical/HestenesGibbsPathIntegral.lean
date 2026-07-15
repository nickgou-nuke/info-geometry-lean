import InfoGeometry.Canonical.SpectroscopicGaugeKMSBridge
import InfoGeometry.Meta.Architecture
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.List.Basic

open scoped InnerProductSpace BigOperators

/-!
# InfoGeometry.Canonical.HestenesGibbsPathIntegral

Path-ensemble scaffold on the doubled real carrier:

- each step carries a source/target state compatible with the owned Unruh-KMS lane,
- action splits into a Lie-like channel and a Jordan/surprisal channel,
- path weight is a real Gibbs factor `exp(-surprisal)`.

This is a translator surface; it does not replace modular/KMS owners.
-/

namespace InfoGeometry.Canonical.PathIntegral

open InfoGeometry.Krein
open SpectroscopicGaugeKMSBridge

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- One directed transition in a path ensemble. -/
@[rep_depth transport]
structure TacticTransition where
  source_state : SpectroscopicKMSCompatible (E := E)
  target_state : SpectroscopicKMSCompatible (E := E)
  transition_rotor : EndH
  action_generator : EndH
  is_exp : transition_rotor = NormedSpace.exp action_generator

/-- A path is an ordered list of tactic transitions. -/
@[rep_depth transport]
abbrev TacticPath := List (TacticTransition (E := E))

/--
Action split at one transition:
- first component: Lie-like reactive channel,
- second component: Jordan-like dissipative channel (surprisal increment).
-/
@[rep_depth transport]
noncomputable def hestenesActionSplit
    (K : EndH) (step : TacticTransition (E := E)) : ℝ × ℝ :=
  let phase_action :=
    step.source_state.state
      (K * step.action_generator - step.action_generator * K)
  let entropy_action :=
    step.source_state.state
      (K * step.action_generator + step.action_generator * K)
  (phase_action, entropy_action)

/-- Total path surprisal from Jordan-like increments. -/
@[rep_depth transport]
noncomputable def pathSurprisal
    (K : EndH) (path : List (TacticTransition (E := E))) : ℝ :=
  (path.map (fun step => (hestenesActionSplit K step).2)).sum

/-- Real Gibbs weight for a path ensemble element. -/
@[rep_depth transport]
noncomputable def gibbsWeight
    (K : EndH) (path : List (TacticTransition (E := E))) : ℝ :=
  Real.exp (-pathSurprisal K path)

/-- Flat path predicate: all Jordan increments vanish. -/
@[rep_depth transport]
def IsFlatPath
    (K : EndH) (path : List (TacticTransition (E := E))) : Prop :=
  ∀ step ∈ path, (hestenesActionSplit K step).2 = 0

/-- Flat paths have zero total surprisal. -/
@[rep_depth transport]
theorem pathSurprisal_eq_zero_of_flat
    (K : EndH) (path : List (TacticTransition (E := E)))
    (hFlat : IsFlatPath K path) :
    pathSurprisal K path = 0 := by
  let _ : CompleteSpace E := inferInstance
  induction path with
  | nil =>
      simp [pathSurprisal]
  | cons step rest ih =>
      have hStep : (hestenesActionSplit K step).2 = 0 :=
        hFlat step (by simp)
      have hRestFlat : IsFlatPath K rest := by
        intro step' hmem
        exact hFlat step' (by simp [hmem])
      have hRest : pathSurprisal K rest = 0 := ih hRestFlat
      simpa [pathSurprisal, hStep] using hRest

/--
Eikonal collapse surface:
if every step is Jordan-flat, the Gibbs path weight is maximal (`1`).
-/
@[rep_depth transport]
theorem gibbs_weight_maximized_for_flat_paths
    (K : EndH) (path : List (TacticTransition (E := E)))
    (hFlat : IsFlatPath K path) :
    gibbsWeight K path = 1 := by
  have hSurprisal : pathSurprisal K path = 0 :=
    pathSurprisal_eq_zero_of_flat K path hFlat
  simp [gibbsWeight, hSurprisal]

/--
Pointwise Jordan-commuting condition for one transition.
-/
@[rep_depth transport]
def JordanCommutesAt
    (K : EndH) (step : TacticTransition (E := E)) : Prop :=
  K * step.action_generator + step.action_generator * K = 0

/--
Jordan-commuting transition has zero dissipative (entropy) increment.
-/
@[rep_depth transport]
theorem entropy_increment_eq_zero_of_jordan_commute
    (K : EndH) (step : TacticTransition (E := E))
    (hComm : JordanCommutesAt K step) :
    (hestenesActionSplit K step).2 = 0 := by
  let _ : CompleteSpace E := inferInstance
  have hEvalZero :
      step.source_state.state
        (K * step.action_generator + step.action_generator * K) = 0 := by
    simpa [JordanCommutesAt, hComm] using
      congrArg step.source_state.state hComm
  simpa [hestenesActionSplit] using hEvalZero

/--
If every step Jordan-commutes with `K`, the path is flat.
-/
@[rep_depth transport]
theorem isFlatPath_of_jordan_commuting
    (K : EndH) (path : List (TacticTransition (E := E)))
    (hComm : ∀ step ∈ path, JordanCommutesAt K step) :
    IsFlatPath K path := by
  let _ : CompleteSpace E := inferInstance
  intro step hmem
  exact entropy_increment_eq_zero_of_jordan_commute K step (hComm step hmem)

/--
Derived eikonal collapse from pointwise Jordan-commuting hypotheses.
-/
@[rep_depth transport]
theorem gibbs_weight_maximized_of_jordan_commuting
    (K : EndH) (path : List (TacticTransition (E := E)))
    (hComm : ∀ step ∈ path, JordanCommutesAt K step) :
    gibbsWeight K path = 1 := by
  let _ : CompleteSpace E := inferInstance
  exact gibbs_weight_maximized_for_flat_paths K path
    (isFlatPath_of_jordan_commuting K path hComm)

end Core

end InfoGeometry.Canonical.PathIntegral
