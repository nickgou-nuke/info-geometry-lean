import InfoGeometry.Clifford.Cl55WittPinSignatureBoundary
import InfoGeometry.Clifford.Cl55WittNegativeVectorPin

namespace InfoGeometry.Clifford.Clifford55

/-!
# Exact vector-generator locus for the native `pinGroup Q55`

The signature-boundary owner proves the necessary norm condition, while the
negative-vector owner proves sufficiency.  This file is only the downstream
coherence theorem combining those two existing results.
-/

theorem vector_mem_pinGroup_iff_Q_eq_neg_one (v : V55) :
    ι55 v ∈ Pin55 ↔ Q55 v = -1 := by
  constructor
  · exact vector_mem_pinGroup_forces_Q_eq_neg_one v
  · exact negativeVector_mem_pinGroup v

end InfoGeometry.Clifford.Clifford55
