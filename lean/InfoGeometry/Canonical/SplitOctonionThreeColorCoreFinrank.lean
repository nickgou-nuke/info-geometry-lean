import InfoGeometry.Canonical.SplitOctonionThreeColorSplitQuaternionCores
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace InfoGeometry.Canonical

noncomputable section

theorem finrank_threeColorCore (c : SplitOctonionColour) :
    Module.finrank ℚ (threeColorCore c) = 4 := by
  exact finrank_colorCore c

end
end InfoGeometry.Canonical
