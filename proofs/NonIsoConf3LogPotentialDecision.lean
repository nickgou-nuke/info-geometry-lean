import proofs.NonIsoConf3RankDecision
import proofs.NonIsoConf3LogWedgeObstruction
import proofs.NonIsoConf3LogCFTPotential

/-!
# Log-generating potential branch selector

This module gives an algebraic alternative to the invalid naive `dlog` Arnold
identity.  It treats each finite candidate presentation as a finite partition
function/rank sector and lets a log-potential or entropy selector choose a
branch.

No analytic CFT theorem is asserted here.  The proved content is the finite
rank/log-rank ordering:

* product/Leray branch: `2^3 * 2^2 = 32`;
* OS-alpha branch: `6 * 2^2 = 24`;
* a max-rank/max-entropy selector chooses `productLeray`.
-/

namespace NonIsoConf3LogPotentialDecision

open NonIsoConf3DeRhamCooperad
open NonIsoConf3RankDecision
open NonIsoConf3LogCFTPotential

/-- Two finite branches currently compared by the non-isotropic Conf3 model. -/
inductive Branch where
  | productLeray
  | osAlpha
  deriving DecidableEq, Fintype, Repr

/-- Finite rank/partition count of each branch. -/
def branchRank : Branch → ℕ
  | Branch.productLeray => 32
  | Branch.osAlpha => 24

/-- Formal log-generating potential.  The finite branch selector only needs the
positive rank and monotonicity data recorded here. -/
structure LogGeneratingPotential where
  branch : Branch
  rank : ℕ
  logZ : ℝ
  rankMatchesBranch : rank = branchRank branch

noncomputable def productPotential : LogGeneratingPotential where
  branch := Branch.productLeray
  rank := 32
  logZ := Real.log 32
  rankMatchesBranch := rfl

noncomputable def osAlphaPotential : LogGeneratingPotential where
  branch := Branch.osAlpha
  rank := 24
  logZ := Real.log 24
  rankMatchesBranch := rfl

theorem product_branch_rank :
    branchRank Branch.productLeray = 2 ^ 3 * 2 ^ 2 := by
  norm_num [branchRank]

theorem os_alpha_branch_rank :
    branchRank Branch.osAlpha = 6 * 2 ^ 2 := by
  norm_num [branchRank]

theorem product_rank_gt_os :
    branchRank Branch.osAlpha < branchRank Branch.productLeray := by
  norm_num [branchRank]

/-- A branch maximizes the finite log-potential when it maximizes finite rank.
This is the order-theoretic part of the log-rank selector. -/
def EntropyMaximizer (b : Branch) : Prop :=
  ∀ c : Branch, branchRank c ≤ branchRank b

theorem product_is_entropy_maximizer :
    EntropyMaximizer Branch.productLeray := by
  intro c
  cases c <;> norm_num [branchRank]

theorem os_alpha_not_entropy_maximizer :
    ¬ EntropyMaximizer Branch.osAlpha := by
  intro h
  have hle := h Branch.productLeray
  norm_num [branchRank] at hle

/-- The log-potential selector chooses the product/Leray branch. -/
theorem log_potential_selects_productLeray :
    ModelChoice.productLeray = ModelChoice.productLeray ∧
    EntropyMaximizer Branch.productLeray ∧
    Fintype.card ProductBasis = 32 ∧
    Fintype.card OSFluxBasis = 24 ∧
    Fintype.card ProductBasis - Fintype.card OSFluxBasis = 8 :=
  by
    constructor
    · rfl
    constructor
    · exact product_is_entropy_maximizer
    constructor
    · exact productBasis_card
    constructor
    · exact osFluxBasis_card
    · exact product_vs_os_rank_gap

/-- The log-potential branch agrees with the finite Dupont rank-decision branch. -/
theorem log_potential_agrees_with_rank32_decision :
    EntropyMaximizer Branch.productLeray ∧
    ¬ tripleDependent expectedCodimData ∧
    Fintype.card ProductBasis = 32 ∧
    Fintype.card OSFluxBasis = 24 := by
  constructor
  · exact product_is_entropy_maximizer
  constructor
  · exact expected_triple_not_dependent
  constructor
  · exact productBasis_card
  · exact osFluxBasis_card

/-- Compatibility with the finite Gibbs/log-CFT diagnostic layer: if the
product potential is strictly larger, the diagnostic chooses the same
product/Leray branch as the rank selector. -/
theorem logCFT_diagnostic_agrees_with_entropy_selector
    (d : LogPotentialBranchDiagnostic)
    (hGap : d.entropyPotentialProduct > d.entropyPotentialOS) :
    d.chosen = ModelChoice.productLeray ∧ EntropyMaximizer Branch.productLeray :=
  by
    constructor
    · exact liftDiagnosticToChoice d hGap
    · exact product_is_entropy_maximizer

end NonIsoConf3LogPotentialDecision
