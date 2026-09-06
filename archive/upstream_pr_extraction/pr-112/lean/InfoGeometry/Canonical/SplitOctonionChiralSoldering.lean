import InfoGeometry.Canonical.SplitOctonionThreeColorChiralRelations
import InfoGeometry.Canonical.SplitOctonionPolarizedZornMultiplication
import InfoGeometry.Canonical.ChiralBasisChangeMatrix
import InfoGeometry.Canonical.SplitQuaternionAssociativeCoassociativeCalibrationBridge

namespace InfoGeometry.Canonical

open SplitOctonionColour
open SplitQuaternionAssociativeCoassociativeCalibrationBridge

noncomputable section

/-- Left multiplication on the native split-octonion carrier, viewed as an endomorphism. -/
def chiralLeftSoldering (x : StandardRationalSplitOctonion) :
    StandardRationalSplitOctonion →ₗ[ℚ] StandardRationalSplitOctonion where
  toFun y := splitOctonionMulQ x y
  map_add' y z := by
    simpa using splitOctonionMulQ_add_right x y z
  map_smul' c y := by
    simpa using splitOctonionMulQ_smul_right c x y

/-- Operator soldering: a split-octonion element acts by left multiplication. -/
def chiralSoldering (x : StandardRationalSplitOctonion) :
    Module.End ℚ StandardRationalSplitOctonion :=
  chiralLeftSoldering x

@[simp] theorem chiralSoldering_apply
    (x y : StandardRationalSplitOctonion) :
    chiralSoldering x y = splitOctonionMulQ x y := by
  rfl

/-- The polarized chiral basis acts through the native basis dictionary. -/
def polarizedChiralSoldering (X : PolarizedZorn) :
    Module.End ℚ StandardRationalSplitOctonion :=
  chiralSoldering (toNative X)

@[simp] theorem polarizedChiralSoldering_nPlus :
    polarizedChiralSoldering polarizedNPlus =
      chiralSoldering ((1 / 2 : ℚ) • (rationalBasis .one + rationalBasis .l)) := by
  simp [polarizedChiralSoldering, chiralSoldering, modularNPlus, fundamentalSymmetry]

@[simp] theorem polarizedChiralSoldering_nMinus :
    polarizedChiralSoldering polarizedNMinus =
      chiralSoldering ((1 / 2 : ℚ) • (rationalBasis .one - rationalBasis .l)) := by
  simp [polarizedChiralSoldering, chiralSoldering, modularNMinus, fundamentalSymmetry]

@[simp] theorem polarizedChiralSoldering_sigmaRedPlus :
    polarizedChiralSoldering polarizedSigmaRedPlus =
      chiralSoldering ((1 / 2 : ℚ) • (rationalBasis .il - rationalBasis .i)) := by
  simp [polarizedChiralSoldering, chiralSoldering, modularSigmaPlus,
    modularJ_eq_colourLUnit, phaseAxis, colourUnit, colourLUnit]

@[simp] theorem polarizedChiralSoldering_sigmaGreenPlus :
    polarizedChiralSoldering polarizedSigmaGreenPlus =
      chiralSoldering ((1 / 2 : ℚ) • (rationalBasis .jl - rationalBasis .j)) := by
  simp [polarizedChiralSoldering, chiralSoldering, modularSigmaPlus,
    modularJ_eq_colourLUnit, phaseAxis, colourUnit, colourLUnit]

@[simp] theorem polarizedChiralSoldering_sigmaBluePlus :
    polarizedChiralSoldering polarizedSigmaBluePlus =
      chiralSoldering ((1 / 2 : ℚ) • (rationalBasis .kl - rationalBasis .k)) := by
  simp [polarizedChiralSoldering, chiralSoldering, modularSigmaPlus,
    modularJ_eq_colourLUnit, phaseAxis, colourUnit, colourLUnit]

@[simp] theorem polarizedChiralSoldering_sigmaRedMinus :
    polarizedChiralSoldering polarizedSigmaRedMinus =
      chiralSoldering ((1 / 2 : ℚ) • (rationalBasis .il + rationalBasis .i)) := by
  simp [polarizedChiralSoldering, chiralSoldering, modularSigmaMinus,
    modularJ_eq_colourLUnit, phaseAxis, colourUnit, colourLUnit]

@[simp] theorem polarizedChiralSoldering_sigmaGreenMinus :
    polarizedChiralSoldering polarizedSigmaGreenMinus =
      chiralSoldering ((1 / 2 : ℚ) • (rationalBasis .jl + rationalBasis .j)) := by
  simp [polarizedChiralSoldering, chiralSoldering, modularSigmaMinus,
    modularJ_eq_colourLUnit, phaseAxis, colourUnit, colourLUnit]

@[simp] theorem polarizedChiralSoldering_sigmaBlueMinus :
    polarizedChiralSoldering polarizedSigmaBlueMinus =
      chiralSoldering ((1 / 2 : ℚ) • (rationalBasis .kl + rationalBasis .k)) := by
  simp [polarizedChiralSoldering, chiralSoldering, modularSigmaMinus,
    modularJ_eq_colourLUnit, phaseAxis, colourUnit, colourLUnit]

theorem polarizedChiralSolderingTable :
    polarizedChiralSoldering polarizedNPlus =
      chiralSoldering ((1 / 2 : ℚ) • (rationalBasis .one + rationalBasis .l)) ∧
    polarizedChiralSoldering polarizedNMinus =
      chiralSoldering ((1 / 2 : ℚ) • (rationalBasis .one - rationalBasis .l)) ∧
    polarizedChiralSoldering polarizedSigmaRedPlus =
      chiralSoldering ((1 / 2 : ℚ) • (rationalBasis .il - rationalBasis .i)) ∧
    polarizedChiralSoldering polarizedSigmaGreenPlus =
      chiralSoldering ((1 / 2 : ℚ) • (rationalBasis .jl - rationalBasis .j)) ∧
    polarizedChiralSoldering polarizedSigmaBluePlus =
      chiralSoldering ((1 / 2 : ℚ) • (rationalBasis .kl - rationalBasis .k)) ∧
    polarizedChiralSoldering polarizedSigmaRedMinus =
      chiralSoldering ((1 / 2 : ℚ) • (rationalBasis .il + rationalBasis .i)) ∧
    polarizedChiralSoldering polarizedSigmaGreenMinus =
      chiralSoldering ((1 / 2 : ℚ) • (rationalBasis .jl + rationalBasis .j)) ∧
    polarizedChiralSoldering polarizedSigmaBlueMinus =
      chiralSoldering ((1 / 2 : ℚ) • (rationalBasis .kl + rationalBasis .k)) := by
  constructor
  · exact polarizedChiralSoldering_nPlus
  constructor
  · exact polarizedChiralSoldering_nMinus
  constructor
  · exact polarizedChiralSoldering_sigmaRedPlus
  constructor
  · exact polarizedChiralSoldering_sigmaGreenPlus
  constructor
  · exact polarizedChiralSoldering_sigmaBluePlus
  constructor
  · exact polarizedChiralSoldering_sigmaRedMinus
  constructor
  · exact polarizedChiralSoldering_sigmaGreenMinus
  · exact polarizedChiralSoldering_sigmaBlueMinus

end

end InfoGeometry.Canonical
