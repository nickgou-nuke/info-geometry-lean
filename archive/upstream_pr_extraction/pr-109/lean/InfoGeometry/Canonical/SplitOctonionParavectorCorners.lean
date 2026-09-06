import InfoGeometry.Canonical.SplitOctonionChiralZornMultiplication
import InfoGeometry.Canonical.ZornVectorMatrixIsomorphism
import InfoGeometry.Canonical.SplitQuaternionAssociativeCoassociativeCalibrationBridge

namespace InfoGeometry.Canonical

open SplitOctonionColour
open SplitQuaternionAssociativeCoassociativeCalibrationBridge

noncomputable section

def chiralParavectorPlus (c : SplitOctonionColour) : ChiralZornCarrier :=
  modularNPlus + modularSigmaMinus c

def chiralParavectorMinus (c : SplitOctonionColour) : ChiralZornCarrier :=
  modularNMinus + modularSigmaPlus c

theorem chiralParavectorPlus_sq (c : SplitOctonionColour) :
    chiralZornMul (chiralParavectorPlus c) (chiralParavectorPlus c) =
      chiralParavectorPlus c := by
  simp only [chiralParavectorPlus, chiralZornMul,
    splitOctonionMulQ_add_left, splitOctonionMulQ_add_right,
    modularNPlus_sq, modularNPlus_mul_modularSigmaMinus,
    modularSigmaMinus_mul_modularNPlus, modularSigmaMinus_sq_zero,
    add_zero, zero_add]

theorem chiralParavectorMinus_sq (c : SplitOctonionColour) :
    chiralZornMul (chiralParavectorMinus c) (chiralParavectorMinus c) =
      chiralParavectorMinus c := by
  simp only [chiralParavectorMinus, chiralZornMul,
    splitOctonionMulQ_add_left, splitOctonionMulQ_add_right,
    modularNMinus_sq, modularNMinus_mul_modularSigmaPlus,
    modularSigmaPlus_mul_modularNMinus, modularSigmaPlus_sq_zero,
    add_zero, zero_add]

theorem chiralParavectorPlus_mul_minus (c : SplitOctonionColour) :
    chiralZornMul (chiralParavectorPlus c) (chiralParavectorMinus c) =
      chiralParavectorMinus c := by
  simp only [chiralParavectorPlus, chiralParavectorMinus, chiralZornMul,
    splitOctonionMulQ_add_left, splitOctonionMulQ_add_right,
    modularNPlus_mul_modularNMinus, modularNPlus_mul_modularSigmaPlus,
    modularSigmaMinus_mul_modularNMinus,
    modularSigmaMinus_mul_modularSigmaPlus, zero_add, add_zero,
    add_comm]

theorem chiralParavectorMinus_mul_plus (c : SplitOctonionColour) :
    chiralZornMul (chiralParavectorMinus c) (chiralParavectorPlus c) =
      chiralParavectorPlus c := by
  simp only [chiralParavectorPlus, chiralParavectorMinus, chiralZornMul,
    splitOctonionMulQ_add_left, splitOctonionMulQ_add_right,
    modularNMinus_mul_modularNPlus, modularNMinus_mul_modularSigmaMinus,
    modularSigmaPlus_mul_modularNPlus,
    modularSigmaPlus_mul_modularSigmaMinus, zero_add, add_zero,
    add_comm]

end
end InfoGeometry.Canonical
