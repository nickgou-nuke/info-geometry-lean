import InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
import InfoGeometry.Algebra.Zorn.G2FlagWordEvaluator

/-! The CAS word table evaluated in the exact Lean carrier.  No theorem about
    injectivity or coverage is bundled with this definition. -/

namespace InfoGeometry.Algebra.Zorn.G2FlagWordCertificate

open InfoGeometry.Algebra.Zorn.G2FlagWordEvaluator
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable def flagRepresentative : Fin 189 → SplitOctF2Aut :=
  fun i => evaluateWord (flagRepWords i)

theorem flagRepresentative_mem (i : Fin 189) :
    flagRepresentative i ∈ flagGeneratedSubgroup := by
  exact evaluateWord_mem_flagGeneratedSubgroup (flagRepWords i)

set_option maxRecDepth 100000 in
theorem flagCells_partition :
    Finset.univ.biUnion flagCells = Finset.univ := by
  decide

def flagCellCard : Fin 12 → Nat
  | 0 => 1
  | 1 => 4
  | 2 => 16
  | 3 => 64
  | 4 => 16
  | 5 => 4
  | 6 => 2
  | 7 => 2
  | 8 => 8
  | 9 => 32
  | 10 => 32
  | 11 => 8

set_option maxRecDepth 100000 in
theorem flagCells_card (k : Fin 12) :
    (flagCells k).card = flagCellCard k := by
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
theorem flagCells_total_card :
    (∑ k : Fin 12, (flagCells k).card) = 189 := by
  native_decide

end InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
