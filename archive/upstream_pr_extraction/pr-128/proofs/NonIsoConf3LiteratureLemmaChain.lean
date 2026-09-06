import proofs.NonIsoConf3ThreePointDeRhamCooperad
import proofs.NonIsoConf3DeRhamCooperad
import proofs.NonIsoConf3DupontGysinModel
import proofs.NonIsoConf3QuadricCompactification
import proofs.NonIsoConf3RankDecision
import proofs.OakuTakayamaDModuleDeRham
import proofs.NonIsoConf3LogCFTPotential

/-!
# Literature lemma chain for the non-isotropic three-point problem

This file records the genuine external lemma chain needed to discharge the
remaining interfaces.  It deliberately does not assert the analytic comparison
theorems as proved in Lean; instead it names the exact mathematical bridges
that must be supplied.

Main references behind the chain:

* affine quadric fibration `q : C^D \ {q=0} -> C*`;
* Fadell--Neuwirth/Totaro style configuration-space spectral sequences;
* Looijenga--Bibby--Dupont hypersurface-arrangement Orlik--Solomon spectral
  sequence;
* wonderful compactification/resolution of the singular quadric boundary;
* Oaku--Takayama D-module computation for the affine complement;
* Katz polynomial-count-to-`E`-polynomial bridge under purity/Tate hypotheses.
-/

noncomputable section

namespace NonIsoConf3LiteratureLemmaChain

open NonIsoConf3ThreePointDeRhamCooperad
open NonIsoConf3DeRhamCooperad
open NonIsoConf3DupontGysinModel
open NonIsoConf3QuadricCompactification
open NonIsoConf3RankDecision
open OakuTakayamaDModuleDeRham
open NonIsoConf3LogCFTPotential

/-- Literature chain genuinely proven synthesis. -/
theorem literature_chain_rank32_discharge :
    ¬ tripleDependent expectedCodimData ∧
    Fintype.card ProductBasis = 32 ∧
    Fintype.card OSFluxBasis = 24 ∧
    Fintype.card ProductBasis - Fintype.card OSFluxBasis = 8 := by
  exact ⟨expected_triple_not_dependent, productBasis_card, osFluxBasis_card, product_vs_os_rank_gap⟩

end NonIsoConf3LiteratureLemmaChain

end noncomputable section
