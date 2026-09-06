import InfoGeometry.Canonical.SplitQuaternionAssociativeCoassociativeCalibrationBridge
import InfoGeometry.Canonical.SplitOctonionThreeColorSplitQuaternionCores

namespace InfoGeometry.Canonical

open SplitOctonionColour
open SplitQuaternionAssociativeCoassociativeCalibrationBridge

noncomputable section

/-! Native Dirac elements in one associative coloured split-quaternion core.

The ambient carrier remains the nonassociative split-octonion carrier.  All
identities below use its native multiplication; associativity is only used
through membership in a previously verified colour core.
-/

def colorDirac (c : SplitOctonionColour) (a b : ℚ) :
    StandardRationalSplitOctonion :=
  a • modularSigmaPlus c + b • modularSigmaMinus c

@[simp] theorem colorDirac_mem_colorCore
    (c : SplitOctonionColour) (a b : ℚ) :
    colorDirac c a b ∈ colorCore c := by
  apply (colorCore c).add_mem
  · exact (colorCore c).smul_mem a (modularSigmaPlus_mem_threeColorCore c)
  · exact (colorCore c).smul_mem b (modularSigmaMinus_mem_threeColorCore c)

theorem colorDirac_sq (c : SplitOctonionColour) (a b : ℚ) :
    splitOctonionMulQ (colorDirac c a b) (colorDirac c a b) =
      (a * b) • rationalBasis .one := by
  simp only [colorDirac, splitOctonionMulQ_add_left,
    splitOctonionMulQ_add_right, splitOctonionMulQ_smul_left,
    splitOctonionMulQ_smul_right, modularSigmaPlus_sq_zero,
    modularSigmaMinus_sq_zero, modularSigmaPlus_mul_modularSigmaMinus,
    modularSigmaMinus_mul_modularSigmaPlus, smul_zero, smul_smul,
    zero_add, add_zero]
  rw [show b * a = a * b by ring]
  have hunit : modularNMinus + modularNPlus = rationalBasis .one := by
    simpa [add_comm] using modularPolarized_one
  have hsmul : (a * b) • (modularNMinus + modularNPlus) =
      (a * b) • rationalBasis .one := by
    exact congrArg (fun x : StandardRationalSplitOctonion => (a * b) • x) hunit
  simpa [smul_add] using hsmul

def balancedColorDirac (c : SplitOctonionColour) (m : ℚ) :
    StandardRationalSplitOctonion := colorDirac c m m

theorem balancedColorDirac_sq (c : SplitOctonionColour) (m : ℚ) :
    splitOctonionMulQ (balancedColorDirac c m) (balancedColorDirac c m) =
      (m ^ 2) • rationalBasis .one := by
  simpa [balancedColorDirac, pow_two] using colorDirac_sq c m m

def colorChiralGrading : StandardRationalSplitOctonion := fundamentalSymmetry

theorem colorDirac_anticommutes_grading
    (c : SplitOctonionColour) (a b : ℚ) :
    splitOctonionMulQ colorChiralGrading (colorDirac c a b) +
        splitOctonionMulQ (colorDirac c a b) colorChiralGrading = 0 := by
  simp [colorChiralGrading, colorDirac,
    splitOctonionMulQ_add_left, splitOctonionMulQ_add_right,
    splitOctonionMulQ_smul_left, splitOctonionMulQ_smul_right,
    fundamentalSymmetry_mul_modularSigmaPlus,
    fundamentalSymmetry_mul_modularSigmaMinus,
    modularSigmaPlus_mul_fundamentalSymmetry,
    modularSigmaMinus_mul_fundamentalSymmetry,
    add_comm, add_left_comm, add_assoc, sub_eq_add_neg, neg_add_cancel]

end
end InfoGeometry.Canonical
