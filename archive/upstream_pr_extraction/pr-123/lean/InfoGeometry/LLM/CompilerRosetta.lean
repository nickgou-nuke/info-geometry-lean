import Lean
import InfoGeometry.LLM.ProofSamplingShadow

namespace InfoGeometry.LLM

open Lean Elab

/--
Finite compiler telemetry surrogate extracted from a tactic transition.
-/
structure CompilerTelemetryShadow where
  mvarCountBefore : Nat
  mvarCountAfter : Nat
  goalCountBefore : Nat
  goalCountAfter : Nat
  deriving Repr

private def natDistance (a b : Nat) : Nat :=
  if _ : a ≤ b then b - a else a - b

/--
Explicit extraction from Lean `TacticInfo` into a finite telemetry packet.
-/
def CompilerTelemetryShadow.ofTacticInfo (info : TacticInfo) : CompilerTelemetryShadow where
  mvarCountBefore := info.mctxBefore.decls.toList.length
  mvarCountAfter := info.mctxAfter.decls.toList.length
  goalCountBefore := info.goalsBefore.length
  goalCountAfter := info.goalsAfter.length

def CompilerTelemetryShadow.sourceState (t : CompilerTelemetryShadow) : ProofStateShadow where
  metavariableDebt := t.mvarCountBefore
  contextMass := t.goalCountBefore
  anomalyCost := t.mvarCountBefore
  regularityScore := t.goalCountBefore

def CompilerTelemetryShadow.targetState (t : CompilerTelemetryShadow) : ProofStateShadow where
  metavariableDebt := t.mvarCountAfter
  contextMass := t.goalCountAfter
  anomalyCost := t.mvarCountAfter
  regularityScore := t.goalCountAfter

/--
Deterministic Rosetta bridge:
compiler telemetry -> proof-sampling proposal.
-/
def CompilerTelemetryShadow.toProposal (t : CompilerTelemetryShadow) : TacticProposal where
  source := t.sourceState
  target := t.targetState
  proposalWeight := 1
  transportCost := natDistance t.goalCountBefore t.goalCountAfter
  repDepthPenalty := natDistance t.mvarCountBefore t.mvarCountAfter

def proposalOfTacticInfo (info : TacticInfo) : TacticProposal :=
  (CompilerTelemetryShadow.ofTacticInfo info).toProposal

def actionFromTacticInfo (w : ActionWeights) (info : TacticInfo) : ℝ :=
  pathAction w (proposalOfTacticInfo info)

noncomputable def acceptanceFromTacticInfo (w : ActionWeights) (β : ℝ) (info : TacticInfo) : ℝ :=
  gibbsAccept w β (proposalOfTacticInfo info)

@[simp] theorem sourceMetavariableDebt_ofTacticInfo (info : TacticInfo) :
    (proposalOfTacticInfo info).source.metavariableDebt =
      ((CompilerTelemetryShadow.ofTacticInfo info).mvarCountBefore : ℝ) := by
  simp [proposalOfTacticInfo, CompilerTelemetryShadow.toProposal, CompilerTelemetryShadow.sourceState]

@[simp] theorem targetMetavariableDebt_ofTacticInfo (info : TacticInfo) :
    (proposalOfTacticInfo info).target.metavariableDebt =
      ((CompilerTelemetryShadow.ofTacticInfo info).mvarCountAfter : ℝ) := by
  simp [proposalOfTacticInfo, CompilerTelemetryShadow.toProposal, CompilerTelemetryShadow.targetState]

@[simp] theorem transportCost_nonneg (t : CompilerTelemetryShadow) :
    0 ≤ t.toProposal.transportCost := by
  unfold CompilerTelemetryShadow.toProposal natDistance
  split_ifs <;> positivity

/--
Monotonic cooling theorem specialized to compiler-derived proposals:
smaller action implies larger Gibbs acceptance for `β > 0`.
-/
theorem acceptanceFromTacticInfo_uphill_lt_cooling
    (w : ActionWeights)
    {β : ℝ}
    (hβ : 0 < β)
    {coolInfo uphillInfo : TacticInfo}
    (h_action : actionFromTacticInfo w coolInfo < actionFromTacticInfo w uphillInfo) :
    acceptanceFromTacticInfo w β uphillInfo < acceptanceFromTacticInfo w β coolInfo := by
  simpa [acceptanceFromTacticInfo, actionFromTacticInfo] using
    (gibbsAccept_uphill_lt_cooling w hβ h_action)

end InfoGeometry.LLM
