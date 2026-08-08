import Mathlib
import proofs.NonIsoConf3DeRhamCooperad
import proofs.NonIsoConf3LiteratureLemmaChain
import proofs.PenroseSpinTilingCapstone
import proofs.NonIsoConf3RankDecision

/-!
# Log-CFT alternative discharge list for the non-isotropic Conf3 sockets

This module previously packaged the entropic/log-potential branch selector as an
alternative front-end for the literature lemma chain.
Now it directly bridges to the genuine synthesis.
-/

noncomputable section

namespace NonIsoConf3LogCFTLiteratureBridge

open NonIsoConf3DeRhamCooperad
open NonIsoConf3LiteratureLemmaChain
open PenroseSpinTilingCapstone
open NonIsoConf3RankDecision

/-- Rank-32 discharge through the Log-CFT alternative branch-selection package. -/
theorem logCFT_literature_rank32_discharge :
    ¬ tripleDependent expectedCodimData ∧
    Fintype.card ProductBasis = 32 ∧
    Fintype.card OSFluxBasis = 24 ∧
    Fintype.card ProductBasis - Fintype.card OSFluxBasis = 8 := by
  exact literature_chain_rank32_discharge

/-- Penrose capstone bridge using the Log-CFT alternative discharge list. -/
theorem logCFT_literature_penrose_capstone_bridge :
    penrose_spin_tiling_colimit_target ∧
    Fintype.card ProductBasis = 32 ∧
    Fintype.card OSFluxBasis = 24 ∧
    Fintype.card ProductBasis - Fintype.card OSFluxBasis = 8 := by
  have hRank := literature_chain_rank32_discharge
  exact ⟨penrose_spin_tiling_inductive_colimit, hRank.2.1, hRank.2.2.1, hRank.2.2.2⟩

end NonIsoConf3LogCFTLiteratureBridge

end noncomputable section
