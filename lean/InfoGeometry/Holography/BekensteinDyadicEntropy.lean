import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

open Real

namespace InfoGeometry.Holography.BekensteinDyadicEntropy

/-- The structural components of the Abelian KAN factor scaling the horizon. -/
def AbelianHorizonFactor : Type :=
  {area_scale : ℝ // 0 < area_scale}

/-- The thermodynamic parameters of the Bekenstein-Hawking horizon. -/
noncomputable def bekenstein_hawking_entropy (A : AbelianHorizonFactor) (G : ℝ) : ℝ :=
  A.1 / (4 * G)

/-- 
The Kubo-Martin-Schwinger (KMS) state at critical inverse temperature β = ln 2.
Models the Shannon-von Neumann entropy of the dyadic rationals.
-/
structure KmsDyadicState where
  branch_depth : ℕ

namespace KmsDyadicState

/-- The dyadic KMS inverse temperature is canonically `log 2`. -/
noncomputable def beta (_state : KmsDyadicState) : ℝ :=
  log 2

/-- The canonical dyadic inverse temperature is `log 2`. -/
@[simp]
theorem h_beta (state : KmsDyadicState) : state.beta = log 2 :=
  rfl

end KmsDyadicState

/-- The von Neumann statistical entropy of the dyadic path tree. -/
noncomputable def von_neumann_entropy (state : KmsDyadicState) : ℝ :=
  (state.branch_depth : ℝ) * log 2

end InfoGeometry.Holography.BekensteinDyadicEntropy
