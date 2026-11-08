import InfoGeometry.Algebra.Zorn.G2TwoSplitZorn
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismOrderLedger

/-!
# Real split-octonion `G₂` classification boundary

The finite `G₂(2)` order ledger and the real split-octonion classification are
different statements.  The finite owner is imported above; no real Lie-group
classification is manufactured from finite numerical data here.  A genuine
real classification can use `G2TwoCandidate` together with an explicitly
proved multiplicative equivalence in its own owner.
-/

namespace InfoGeometry.Algebra.Zorn.RealSplitOctonionG2Classification

theorem pgl3F3Order_ne_finiteG2TwoOrder :
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismOrderLedger.pgl3F3Order ≠
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.g2twoOrder := by
  exact InfoGeometry.OperatorAlgebra.G2TwoAutomorphismOrderLedger.pgl3F3Order_ne_g2TwoOrder

end InfoGeometry.Algebra.Zorn.RealSplitOctonionG2Classification
