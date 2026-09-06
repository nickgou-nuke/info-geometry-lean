import proofs.LogCFTGeneratingPotential
import proofs.NonIsoConf3LogPotentialDecision
import proofs.NonIsoConf3LiteratureLemmaChain

/-!
# Entropic branch choice for the Log-CFT potential channel

This module records the finite branch-choice rule used by the existing
log-rank selector and relation-choice chain.

The `LogCFTPotential` fields below are record data carried as propositions;
they are not asserted here as proved analytic semantics.  The kernel-proved
content in this file is the finite diagnostic rule:

* if the entropy/log-rank gap is positive, choose `ModelChoice.productLeray`;
* otherwise choose `ModelChoice.osAlpha`.

For the non-isotropic three-quadric spine the finite ranks give a positive gap,
so the diagnostic selects the rank-`32` product/Leray branch.
-/

noncomputable section

namespace LogCFTPotentialBranchChoice

open NonIsoConf3DeRhamCooperad
open NonIsoConf3RankDecision
open NonIsoConf3LiteratureLemmaChain
open NonIsoConf3LogPotentialDecision
open LogCFTGeneratingPotential

/-- Minimal algebraic LogCFT potential package.  The actual logarithm/trace/KMS
conditions are carried as `Prop` data fields; this file only uses the finite
partition and branch-selection data. -/
structure LogCFTPotential where
  spectrum : FiniteSpectrum
  referenceLambda : ℝ
  partitionFunctionWellDefined : Prop
  logPotentialWellDefined : Prop
  modularHamiltonianCompatible : Prop
  renyiEntropyDefined : Prop

/-- Entropic diagnostic for choosing a relation branch.  Positive gap selects the
rank-`32` product/Leray branch; non-positive gap falls back to the rank-`24`
OS-alpha diagnostic branch. -/
structure EntropicBranchChoice where
  entropyGap : ℤ
  chosen : ModelChoice
  chosen_rule : chosen = if 0 < entropyGap then ModelChoice.productLeray else ModelChoice.osAlpha

/-- The actual finite gap between the two current candidates. -/
def finiteRankEntropyGap : ℤ :=
  (Fintype.card ProductBasis : ℤ) - (Fintype.card OSFluxBasis : ℤ)

/-- The finite rank/entropy gap is positive: `32-24=8`. -/
theorem finiteRankEntropyGap_pos : 0 < finiteRankEntropyGap := by
  unfold finiteRankEntropyGap
  rw [productBasis_card, osFluxBasis_card]
  norm_num

/-- Positive entropy gap forces the product/Leray branch. -/
theorem EntropicBranchChoice.selects_productLeray_of_pos
    (E : EntropicBranchChoice) (hgap : 0 < E.entropyGap) :
    E.chosen = ModelChoice.productLeray := by
  rw [E.chosen_rule]
  simp [hgap]

/-- Non-positive entropy gap selects the OS-alpha diagnostic branch. -/
theorem EntropicBranchChoice.selects_osAlpha_of_not_pos
    (E : EntropicBranchChoice) (hgap : ¬ 0 < E.entropyGap) :
    E.chosen = ModelChoice.osAlpha := by
  rw [E.chosen_rule]
  simp [hgap]

/-- Canonical finite diagnostic branch choice from the compiled ranks. -/
def finiteRankEntropicBranchChoice : EntropicBranchChoice where
  entropyGap := finiteRankEntropyGap
  chosen := ModelChoice.productLeray
  chosen_rule := by
    simp [finiteRankEntropyGap_pos]

/-- The canonical finite diagnostic selects product/Leray. -/
theorem finiteRankEntropicBranchChoice_selects_productLeray :
    finiteRankEntropicBranchChoice.chosen = ModelChoice.productLeray := by
  exact EntropicBranchChoice.selects_productLeray_of_pos
    finiteRankEntropicBranchChoice finiteRankEntropyGap_pos

/-- Concrete relation-choice fed by a LogCFT potential and the finite
entropic diagnostic. Geometric/Dupont facts are implemented via actual data
rather than unused assumptions. -/
structure ConcreteRelationChoice (D : ℕ) where
  potential : LogCFTPotential
  entropicChoice : EntropicBranchChoice
  entropyGapPositive : 0 < entropicChoice.entropyGap
  threeQuadricCodimData : ThreeQuadricCodimData
  threeQuadricCodimData_eq_expected : threeQuadricCodimData = expectedCodimData

/-- Entropic branch choice feeds the existing finite LogCFT/Penrose bridge. -/
theorem entropicAlternative_penrose_rank32_bridge {D : ℕ}
    (C : ConcreteRelationChoice D) : 
    C.entropicChoice.chosen = ModelChoice.productLeray := by
  exact EntropicBranchChoice.selects_productLeray_of_pos
    C.entropicChoice C.entropyGapPositive

/-- Finite entropy-maximizer view agrees with the diagnostic branch. -/
theorem finite_entropy_maximizer_agrees_with_entropic_choice :
    EntropyMaximizer Branch.productLeray ∧
    finiteRankEntropicBranchChoice.chosen = ModelChoice.productLeray ∧
    Fintype.card ProductBasis = 32 ∧
    Fintype.card OSFluxBasis = 24 := by
  constructor
  · exact product_is_entropy_maximizer
  constructor
  · exact finiteRankEntropicBranchChoice_selects_productLeray
  constructor
  · exact productBasis_card
  · exact osFluxBasis_card

end LogCFTPotentialBranchChoice

end noncomputable section
