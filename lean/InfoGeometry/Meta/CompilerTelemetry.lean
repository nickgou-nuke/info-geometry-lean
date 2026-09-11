import Lean
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic

open Lean Elab Meta

namespace InfoGeometry.Meta

/--
Finite telemetry extracted from one tactic transition.

- `deltaGamma`: change in total local-context bindings across active goals.
- `deltaM`: change in total metavariable declarations.
- `phaseShadow`: lightweight antisymmetric proxy (goal-count delta).
- `dissipativeShadow`: additive friction/flux shadow (`deltaGamma + deltaM`).
-/
structure TacticTelemetry where
  gammaBefore : Nat
  gammaAfter : Nat
  mBefore : Nat
  mAfter : Nat
  goalBefore : Nat
  goalAfter : Nat
  deltaGamma : Int
  deltaM : Int
  phaseShadow : ℝ
  dissipativeShadow : ℝ

private def countMVarDecls (mctx : MetavarContext) : Nat :=
  mctx.decls.toList.length

private def localBindingCount (lctx : LocalContext) : Nat :=
  lctx.foldl (init := 0) fun acc _ => acc + 1

private def countGoalLocalBindings (mctx : MetavarContext) (goals : List MVarId) : Nat :=
  goals.foldl (init := 0) fun acc gid =>
    match mctx.findDecl? gid with
    | some decl => acc + localBindingCount decl.lctx
    | none => acc

private def natDeltaInt (before after : Nat) : Int :=
  Int.ofNat after - Int.ofNat before

/--
Extract compiler telemetry directly from `TacticInfo` (no DAG proxy counts).
-/
def telemetryOfTacticInfo (info : TacticInfo) : TacticTelemetry :=
  let gammaBefore := countGoalLocalBindings info.mctxBefore info.goalsBefore
  let gammaAfter := countGoalLocalBindings info.mctxAfter info.goalsAfter
  let mBefore := countMVarDecls info.mctxBefore
  let mAfter := countMVarDecls info.mctxAfter
  let goalBefore := info.goalsBefore.length
  let goalAfter := info.goalsAfter.length
  let deltaGamma := natDeltaInt gammaBefore gammaAfter
  let deltaM := natDeltaInt mBefore mAfter
  let phaseShadow : ℝ := (goalAfter : ℝ) - (goalBefore : ℝ)
  let dissipativeShadow : ℝ := (deltaGamma : ℝ) + (deltaM : ℝ)
  {
    gammaBefore := gammaBefore
    gammaAfter := gammaAfter
    mBefore := mBefore
    mAfter := mAfter
    goalBefore := goalBefore
    goalAfter := goalAfter
    deltaGamma := deltaGamma
    deltaM := deltaM
    phaseShadow := phaseShadow
    dissipativeShadow := dissipativeShadow
  }

/--
Extract compiler telemetry directly from `TacticInfo` (no DAG proxy counts).
-/
def measureTacticTelemetry (info : TacticInfo) : MetaM TacticTelemetry := do
  pure (telemetryOfTacticInfo info)

/--
Compact split used by downstream auditors `(phase, dissipative)`.
-/
def measureTacticAction (info : TacticInfo) : MetaM (ℝ × ℝ) := do
  let t ← measureTacticTelemetry info
  pure (t.phaseShadow, t.dissipativeShadow)

end InfoGeometry.Meta
