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

end InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
