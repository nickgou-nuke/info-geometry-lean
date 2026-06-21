import InfoGeometry.Canonical.SplitCliffordTensorBridge
import InfoGeometry.Canonical.SplitCliffordDirectLimit
import Mathlib.LinearAlgebra.Basis.Basic
import InfoGeometry.Clifford.ClNN

namespace InfoGeometry.Canonical

open SplitCliffordTensorBridge
open InfoGeometry.Clifford.ClNN

/-- The inclusion map $i_n : V_n \to V_{n+1}$ for the split Clifford tower. -/
noncomputable def splitCliffordInclusion (n : ℕ) (x : SplitClNNCarrier n) : SplitClNNAlg (n + 1) :=
  CliffordAlgebra.ι (SplitClNNQuad (n + 1)) (tailLift n x)

/-- The inclusion $i_n$ is an isometry with respect to the split quadratic forms $Q_n$ and $Q_{n+1}$. -/
theorem splitCliffordInclusion_is_isometry (n : ℕ) (x : SplitClNNCarrier n) :
    SplitClNNQuad (n + 1) (splitCliffordInclusion n x) = SplitClNNQuad n x := by
  simp [splitCliffordInclusion, splitCliffordTensorStep_tailFactor]

end InfoGeometry.Canonical
