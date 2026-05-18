import Mathlib
import InfoGeometry.Arithmetic.HestenesKreinChiralProjectors

/-!
# InfoGeometry.Arithmetic.HestenesKreinSplitHolomorphic

Closed split-holomorphic decomposition theory for the Hestenes--Krein lane.

This file keeps the statement level narrow and algebraic:

* a split-holomorphic map is a pair of left/right scalar channels;
* the map reconstructs from its two channels through the idempotent basis;
* the two chiral projections recover the channels exactly.

No PDE theorem is claimed here.  The split Cauchy--Riemann discussion from the
review note is reflected only as a decomposition theorem at the level that is
native to the repo's split-complex carrier.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.HestenesKreinSplitHolomorphic

open InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics
open InfoGeometry.Arithmetic.HestenesKreinChiralProjectors

/-- A split-holomorphic channel pair on the split-temperature plane. -/
def splitHolomorphic (φL φR : ℝ → ℝ) (s : SplitSouriauTemperature) :
    SplitComplex :=
  chiralReconstruct (φL (leftCone s)) (φR (rightCone s))

/-- Left chiral readout of a split-holomorphic channel pair. -/
theorem leftPart_splitHolomorphic
    (φL φR : ℝ → ℝ) (s : SplitSouriauTemperature) :
    SplitComplex.leftPart (splitHolomorphic φL φR s) =
      φL (leftCone s) := by
  unfold splitHolomorphic
  simp [chiralReconstruct, leftCone]

/-- Right chiral readout of a split-holomorphic channel pair. -/
theorem rightPart_splitHolomorphic
    (φL φR : ℝ → ℝ) (s : SplitSouriauTemperature) :
    SplitComplex.rightPart (splitHolomorphic φL φR s) =
      φR (rightCone s) := by
  unfold splitHolomorphic
  simp [chiralReconstruct, rightCone]

/-- A split-holomorphic map reconstructs from its two chiral channels. -/
theorem splitHolomorphic_reconstruct
    (φL φR : ℝ → ℝ) (s : SplitSouriauTemperature) :
    chiralReconstruct
      (SplitComplex.leftPart (splitHolomorphic φL φR s))
      (SplitComplex.rightPart (splitHolomorphic φL φR s))
      =
    splitHolomorphic φL φR s := by
  simp [splitHolomorphic, chiralReconstruct]

/-- The `e₊` projection of a split-holomorphic map recovers the left channel. -/
theorem projectPlus_splitHolomorphic
    (φL φR : ℝ → ℝ) (s : SplitSouriauTemperature) :
    projectPlus (splitHolomorphic φL φR s) =
      SplitComplex.smul (φL (leftCone s)) ePlus := by
  rw [projectPlus_eq_smul_plusCoeff]
  simp [splitHolomorphic, plusCoeff, leftPart_splitHolomorphic]

/-- The `e₋` projection of a split-holomorphic map recovers the right channel. -/
theorem projectMinus_splitHolomorphic
    (φL φR : ℝ → ℝ) (s : SplitSouriauTemperature) :
    projectMinus (splitHolomorphic φL φR s) =
      SplitComplex.smul (φR (rightCone s)) eMinus := by
  rw [projectMinus_eq_smul_minusCoeff]
  simp [splitHolomorphic, minusCoeff, rightPart_splitHolomorphic]

/-- The split-holomorphic map decomposes into its chiral projector pieces. -/
theorem splitHolomorphic_chiral_decomposition
    (φL φR : ℝ → ℝ) (s : SplitSouriauTemperature) :
    SplitComplex.add (projectPlus (splitHolomorphic φL φR s))
      (projectMinus (splitHolomorphic φL φR s)) =
    splitHolomorphic φL φR s := by
  exact projectPlus_add_projectMinus (splitHolomorphic φL φR s)

end InfoGeometry.Arithmetic.HestenesKreinSplitHolomorphic
