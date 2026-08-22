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

end InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
