import Mathlib.Analysis.SpecialFunctions.Exp

namespace InfoGeometry.LLM

/-!
# Proof-Sampling Shadow Geometry

This file provides a finite surrogate for Gibbs-style proof search:

- `ProofStateShadow`: coarse scalar shadow of a local proof state;
- `TacticProposal`: a directed transition between two shadow states;
- `pathAction`: decomposed action packet reduced to one scalar shadow;
- `gibbsAccept`: Gibbs-style acceptance shadow.

The model is intentionally modest: MH-like locally, without claiming full
detailed balance or reversible equilibrium dynamics.
-/

structure ProofStateShadow where
  metavariableDebt : ℝ
  contextMass : ℝ
  anomalyCost : ℝ
  regularityScore : ℝ

structure TacticProposal where
  source : ProofStateShadow
  target : ProofStateShadow
  proposalWeight : ℝ
  transportCost : ℝ
  repDepthPenalty : ℝ

structure ActionWeights where
  regularCore : ℝ
  defect : ℝ
  anomaly : ℝ
  transport : ℝ
  repDepth : ℝ

/--
Action decomposition before scalar collapse:
`(regular, defect, anomaly, transport, repDepth)`.
-/
def actionPacket (p : TacticProposal) : ℝ × ℝ × ℝ × ℝ × ℝ :=
  let regularCore :=
    (p.target.contextMass + p.target.metavariableDebt - p.target.regularityScore) -
      (p.source.contextMass + p.source.metavariableDebt - p.source.regularityScore)
  let defect := p.target.metavariableDebt - p.source.metavariableDebt
  let anomaly := p.target.anomalyCost - p.source.anomalyCost
  let transport := p.transportCost
  let repDepth := p.repDepthPenalty
  (regularCore, defect, anomaly, transport, repDepth)

/--
Scalar action shadow used by Gibbs-like acceptance rules.
-/
def pathAction (w : ActionWeights) (p : TacticProposal) : ℝ :=
  let pkt := actionPacket p
  w.regularCore * pkt.1 +
    w.defect * pkt.2.1 +
      w.anomaly * pkt.2.2.1 +
        w.transport * pkt.2.2.2.1 +
          w.repDepth * pkt.2.2.2.2

/--
Gibbs-style acceptance shadow.
-/
noncomputable def gibbsAccept (w : ActionWeights) (β : ℝ) (p : TacticProposal) : ℝ :=
  Real.exp (-(β * pathAction w p))

/--
If proposal `cool` has lower scalar action than `uphill`, then `cool` has
strictly larger Gibbs acceptance (for positive inverse-temperature `β`).
-/
theorem gibbsAccept_uphill_lt_cooling
    (w : ActionWeights)
    {β : ℝ}
    (hβ : 0 < β)
    {cool uphill : TacticProposal}
    (h_action : pathAction w cool < pathAction w uphill) :
    gibbsAccept w β uphill < gibbsAccept w β cool := by
  unfold gibbsAccept
  have hscaled : β * pathAction w cool < β * pathAction w uphill :=
    mul_lt_mul_of_pos_left h_action hβ
  have hneg : -(β * pathAction w uphill) < -(β * pathAction w cool) :=
    neg_lt_neg hscaled
  exact Real.exp_lt_exp.mpr hneg

end InfoGeometry.LLM
