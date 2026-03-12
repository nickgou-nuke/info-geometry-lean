import InfoGeometry.Krein.HilbertBridge
import InfoGeometry.Krein.DoubledAdjoint

namespace InfoGeometry.tmp

open InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma noetherInferenceSandboxNew_sanity
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) : True := by
  trivial

end InfoGeometry.tmp
