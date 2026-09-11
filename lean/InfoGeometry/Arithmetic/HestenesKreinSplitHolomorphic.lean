import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

/-- A t-free split-holomorphic channel pair on the split-complex carrier. -/
def splitHolomorphicComplex (φL φR : ℝ → ℝ) (z : SplitComplex) : SplitComplex :=
  chiralReconstruct (φL (SplitComplex.leftPart z)) (φR (SplitComplex.rightPart z))

/-- Left chiral readout of a split-holomorphic channel pair. -/
theorem leftPart_splitHolomorphic
    (φL φR : ℝ → ℝ) (s : SplitSouriauTemperature) :
    SplitComplex.leftPart (splitHolomorphic φL φR s) =
      φL (leftCone s) := by
  cases s
  simp [splitHolomorphic, chiralReconstruct, leftCone,
    SplitComplex.leftPart, SplitComplex.add, SplitComplex.smul,
    ePlus, eMinus]
  ring

/-- Left chiral readout of the t-free split-holomorphic channel pair. -/
theorem leftPart_splitHolomorphicComplex
    (φL φR : ℝ → ℝ) (z : SplitComplex) :
    SplitComplex.leftPart (splitHolomorphicComplex φL φR z) =
      φL (SplitComplex.leftPart z) := by
  cases z
  simp [splitHolomorphicComplex, chiralReconstruct,
    SplitComplex.leftPart, SplitComplex.add, SplitComplex.smul,
    ePlus, eMinus]
  ring

/-- Right chiral readout of a split-holomorphic channel pair. -/
theorem rightPart_splitHolomorphic
    (φL φR : ℝ → ℝ) (s : SplitSouriauTemperature) :
    SplitComplex.rightPart (splitHolomorphic φL φR s) =
      φR (rightCone s) := by
  cases s
  simp [splitHolomorphic, chiralReconstruct, rightCone,
    SplitComplex.rightPart, SplitComplex.add, SplitComplex.smul,
    ePlus, eMinus]
  ring

/-- Right chiral readout of the t-free split-holomorphic channel pair. -/
theorem rightPart_splitHolomorphicComplex
    (φL φR : ℝ → ℝ) (z : SplitComplex) :
    SplitComplex.rightPart (splitHolomorphicComplex φL φR z) =
      φR (SplitComplex.rightPart z) := by
  cases z
  simp [splitHolomorphicComplex, chiralReconstruct,
    SplitComplex.rightPart, SplitComplex.add, SplitComplex.smul,
    ePlus, eMinus]
  ring

/-- A split-holomorphic map reconstructs from its two chiral channels. -/
theorem splitHolomorphic_reconstruct
    (φL φR : ℝ → ℝ) (s : SplitSouriauTemperature) :
    chiralReconstruct
      (SplitComplex.leftPart (splitHolomorphic φL φR s))
      (SplitComplex.rightPart (splitHolomorphic φL φR s))
      =
    splitHolomorphic φL φR s := by
  rw [leftPart_splitHolomorphic, rightPart_splitHolomorphic]
  simp [splitHolomorphic, chiralReconstruct]

/-- The t-free split-holomorphic map reconstructs from its two chiral channels. -/
theorem splitHolomorphicComplex_reconstruct
    (φL φR : ℝ → ℝ) (z : SplitComplex) :
    chiralReconstruct
      (SplitComplex.leftPart (splitHolomorphicComplex φL φR z))
      (SplitComplex.rightPart (splitHolomorphicComplex φL φR z))
      =
    splitHolomorphicComplex φL φR z := by
  rw [leftPart_splitHolomorphicComplex, rightPart_splitHolomorphicComplex]
  simp [splitHolomorphicComplex, chiralReconstruct]

/-- The `e₊` projection of a split-holomorphic map recovers the left channel. -/
theorem projectPlus_splitHolomorphic
    (φL φR : ℝ → ℝ) (s : SplitSouriauTemperature) :
    projectPlus (splitHolomorphic φL φR s) =
      SplitComplex.smul (φL (leftCone s)) ePlus := by
  rw [projectPlus_eq_smul_plusCoeff]
  simpa [plusCoeff, SplitComplex.leftPart] using
    congrArg (fun t : ℝ => SplitComplex.smul t ePlus)
      (leftPart_splitHolomorphic φL φR s)

/-- The `e₊` projection of the t-free split-holomorphic map recovers the left channel. -/
theorem projectPlus_splitHolomorphicComplex
    (φL φR : ℝ → ℝ) (z : SplitComplex) :
    projectPlus (splitHolomorphicComplex φL φR z) =
      SplitComplex.smul (φL (SplitComplex.leftPart z)) ePlus := by
  rw [projectPlus_eq_smul_plusCoeff]
  simpa [plusCoeff, SplitComplex.leftPart] using
    congrArg (fun t : ℝ => SplitComplex.smul t ePlus)
      (leftPart_splitHolomorphicComplex φL φR z)

/-- The `e₋` projection of a split-holomorphic map recovers the right channel. -/
theorem projectMinus_splitHolomorphic
    (φL φR : ℝ → ℝ) (s : SplitSouriauTemperature) :
    projectMinus (splitHolomorphic φL φR s) =
      SplitComplex.smul (φR (rightCone s)) eMinus := by
  rw [projectMinus_eq_smul_minusCoeff]
  simpa [minusCoeff, SplitComplex.rightPart] using
    congrArg (fun t : ℝ => SplitComplex.smul t eMinus)
      (rightPart_splitHolomorphic φL φR s)

/-- The `e₋` projection of the t-free split-holomorphic map recovers the right channel. -/
theorem projectMinus_splitHolomorphicComplex
    (φL φR : ℝ → ℝ) (z : SplitComplex) :
    projectMinus (splitHolomorphicComplex φL φR z) =
      SplitComplex.smul (φR (SplitComplex.rightPart z)) eMinus := by
  rw [projectMinus_eq_smul_minusCoeff]
  simpa [minusCoeff, SplitComplex.rightPart] using
    congrArg (fun t : ℝ => SplitComplex.smul t eMinus)
      (rightPart_splitHolomorphicComplex φL φR z)

/-- The split-holomorphic map decomposes into its chiral projector pieces. -/
theorem splitHolomorphic_chiral_decomposition
    (φL φR : ℝ → ℝ) (s : SplitSouriauTemperature) :
    SplitComplex.add (projectPlus (splitHolomorphic φL φR s))
      (projectMinus (splitHolomorphic φL φR s)) =
    splitHolomorphic φL φR s := by
  exact projectPlus_add_projectMinus (splitHolomorphic φL φR s)

/-- The t-free split-holomorphic map decomposes into its chiral projector pieces. -/
theorem splitHolomorphicComplex_chiral_decomposition
    (φL φR : ℝ → ℝ) (z : SplitComplex) :
    SplitComplex.add (projectPlus (splitHolomorphicComplex φL φR z))
      (projectMinus (splitHolomorphicComplex φL φR z)) =
    splitHolomorphicComplex φL φR z := by
  exact projectPlus_add_projectMinus (splitHolomorphicComplex φL φR z)

end InfoGeometry.Arithmetic.HestenesKreinSplitHolomorphic
