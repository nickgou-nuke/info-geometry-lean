import InfoGeometry.Canonical.SplitOctonionThreeColorModularCl11
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ZornVectorMatrixIsomorphism

namespace InfoGeometry.Canonical

open SplitOctonionColour

noncomputable section

def modularNPlus : StandardRationalSplitOctonion :=
  (1 / 2 : ℚ) • (rationalBasis .one + fundamentalSymmetry)

def modularNMinus : StandardRationalSplitOctonion :=
  (1 / 2 : ℚ) • (rationalBasis .one - fundamentalSymmetry)

def modularSigmaPlus (c : SplitOctonionColour) : StandardRationalSplitOctonion :=
  (1 / 2 : ℚ) • (modularJ c - phaseAxis c)

def modularSigmaMinus (c : SplitOctonionColour) : StandardRationalSplitOctonion :=
  (1 / 2 : ℚ) • (modularJ c + phaseAxis c)

/-- The mixed color-plane products needed to expand the chiral generators. -/
theorem phaseAxis_mul_fundamentalSymmetry (c : SplitOctonionColour) :
    splitOctonionMulQ (phaseAxis c) fundamentalSymmetry = modularJ c := by
  cases c <;> funext b <;> fin_cases b <;>
    simp [phaseAxis, colourUnit, fundamentalSymmetry,
      modularJ_eq_colourLUnit, colourLUnit, rationalBasis,
      splitOctonionMulQ, splitQuaternionOfQ, splitQuaternionLPartQ,
      splitQuaternionAddQ, splitQuaternionMulQ, splitQuaternionConjQ,
      splitOctonionOfQuaternionPairQ, Pi.single] <;>
      norm_num

theorem fundamentalSymmetry_mul_phaseAxis (c : SplitOctonionColour) :
    splitOctonionMulQ fundamentalSymmetry (phaseAxis c) = -modularJ c := by
  simp [modularJ, phaseAxis]

theorem modularJ_mul_phaseAxis (c : SplitOctonionColour) :
    splitOctonionMulQ (modularJ c) (phaseAxis c) = fundamentalSymmetry := by
  cases c <;> funext b <;> fin_cases b <;>
    simp [modularJ_eq_colourLUnit, phaseAxis, colourUnit,
      colourLUnit, fundamentalSymmetry, rationalBasis,
      splitOctonionMulQ, splitQuaternionOfQ, splitQuaternionLPartQ,
      splitQuaternionAddQ, splitQuaternionMulQ, splitQuaternionConjQ,
      splitOctonionOfQuaternionPairQ, Pi.single] <;>
    norm_num

theorem phaseAxis_mul_modularJ (c : SplitOctonionColour) :
    splitOctonionMulQ (phaseAxis c) (modularJ c) = -fundamentalSymmetry := by
  cases c <;> funext b <;> fin_cases b <;>
    simp [modularJ_eq_colourLUnit, phaseAxis, colourUnit,
      colourLUnit, fundamentalSymmetry, rationalBasis,
      splitOctonionMulQ, splitQuaternionOfQ, splitQuaternionLPartQ,
      splitQuaternionAddQ, splitQuaternionMulQ, splitQuaternionConjQ,
      splitOctonionOfQuaternionPairQ, Pi.single] <;>
    norm_num

@[simp] theorem modularNPlus_sq :
    splitOctonionMulQ modularNPlus modularNPlus = modularNPlus := by
  change splitOctonionMulQ
      ((1 / 2 : ℚ) • (rationalBasis .one + fundamentalSymmetry))
      ((1 / 2 : ℚ) • (rationalBasis .one + fundamentalSymmetry)) =
    (1 / 2 : ℚ) • (rationalBasis .one + fundamentalSymmetry)
  simp only [splitOctonionMulQ_smul_left, splitOctonionMulQ_smul_right,
    splitOctonionMulQ_add_left, splitOctonionMulQ_add_right,
    splitOctonionMulQ_one_left, splitOctonionMulQ_one_right,
    fundamentalSymmetry_sq]
  module

@[simp] theorem modularNMinus_sq :
    splitOctonionMulQ modularNMinus modularNMinus = modularNMinus := by
  change splitOctonionMulQ
      ((1 / 2 : ℚ) • (rationalBasis .one - fundamentalSymmetry))
      ((1 / 2 : ℚ) • (rationalBasis .one - fundamentalSymmetry)) =
    (1 / 2 : ℚ) • (rationalBasis .one - fundamentalSymmetry)
  simp only [splitOctonionMulQ_smul_left, splitOctonionMulQ_smul_right,
    splitOctonionMulQ_sub_left, splitOctonionMulQ_sub_right,
    splitOctonionMulQ_one_left, splitOctonionMulQ_one_right,
    fundamentalSymmetry_sq]
  module

@[simp] theorem modularNPlus_mul_modularNMinus :
    splitOctonionMulQ modularNPlus modularNMinus = 0 := by
  change splitOctonionMulQ
      ((1 / 2 : ℚ) • (rationalBasis .one + fundamentalSymmetry))
      ((1 / 2 : ℚ) • (rationalBasis .one - fundamentalSymmetry)) = 0
  simp only [splitOctonionMulQ_smul_left, splitOctonionMulQ_smul_right,
    splitOctonionMulQ_add_left, splitOctonionMulQ_sub_right,
    splitOctonionMulQ_one_left, splitOctonionMulQ_one_right,
    fundamentalSymmetry_sq]
  module

@[simp] theorem modularNMinus_mul_modularNPlus :
    splitOctonionMulQ modularNMinus modularNPlus = 0 := by
  change splitOctonionMulQ
      ((1 / 2 : ℚ) • (rationalBasis .one - fundamentalSymmetry))
      ((1 / 2 : ℚ) • (rationalBasis .one + fundamentalSymmetry)) = 0
  simp only [splitOctonionMulQ_smul_left, splitOctonionMulQ_smul_right,
    splitOctonionMulQ_sub_left, splitOctonionMulQ_add_right,
    splitOctonionMulQ_one_left, splitOctonionMulQ_one_right,
    fundamentalSymmetry_sq]
  module

@[simp] theorem modularSigmaPlus_sq_zero (c : SplitOctonionColour) :
    splitOctonionMulQ (modularSigmaPlus c) (modularSigmaPlus c) = 0 := by
  change splitOctonionMulQ
      ((1 / 2 : ℚ) • (modularJ c - phaseAxis c))
      ((1 / 2 : ℚ) • (modularJ c - phaseAxis c)) = 0
  simp only [splitOctonionMulQ_smul_left, splitOctonionMulQ_smul_right,
    splitOctonionMulQ_sub_left, splitOctonionMulQ_sub_right,
    modularJ_sq, modularJ_mul_phaseAxis, phaseAxis_mul_modularJ,
    phaseAxis_sq]
  module

@[simp] theorem modularSigmaMinus_sq_zero (c : SplitOctonionColour) :
    splitOctonionMulQ (modularSigmaMinus c) (modularSigmaMinus c) = 0 := by
  change splitOctonionMulQ
      ((1 / 2 : ℚ) • (modularJ c + phaseAxis c))
      ((1 / 2 : ℚ) • (modularJ c + phaseAxis c)) = 0
  simp only [splitOctonionMulQ_smul_left, splitOctonionMulQ_smul_right,
    splitOctonionMulQ_add_left, splitOctonionMulQ_add_right,
    modularJ_sq, modularJ_mul_phaseAxis, phaseAxis_mul_modularJ,
    phaseAxis_sq]
  module

@[simp] theorem modularSigmaPlus_mul_modularSigmaMinus (c : SplitOctonionColour) :
    splitOctonionMulQ (modularSigmaPlus c) (modularSigmaMinus c) = modularNPlus := by
  change splitOctonionMulQ
      ((1 / 2 : ℚ) • (modularJ c - phaseAxis c))
      ((1 / 2 : ℚ) • (modularJ c + phaseAxis c)) = modularNPlus
  simp only [splitOctonionMulQ_smul_left, splitOctonionMulQ_smul_right,
    splitOctonionMulQ_sub_left, splitOctonionMulQ_sub_right,
    splitOctonionMulQ_add_left, splitOctonionMulQ_add_right,
    modularJ_sq, modularJ_mul_phaseAxis, phaseAxis_mul_modularJ,
    phaseAxis_sq, modularNPlus]
  module

@[simp] theorem modularSigmaMinus_mul_modularSigmaPlus (c : SplitOctonionColour) :
    splitOctonionMulQ (modularSigmaMinus c) (modularSigmaPlus c) = modularNMinus := by
  change splitOctonionMulQ
      ((1 / 2 : ℚ) • (modularJ c + phaseAxis c))
      ((1 / 2 : ℚ) • (modularJ c - phaseAxis c)) = modularNMinus
  simp only [splitOctonionMulQ_smul_left, splitOctonionMulQ_smul_right,
    splitOctonionMulQ_add_left, splitOctonionMulQ_add_right,
    splitOctonionMulQ_sub_left, splitOctonionMulQ_sub_right,
    modularJ_sq, modularJ_mul_phaseAxis, phaseAxis_mul_modularJ,
    phaseAxis_sq, modularNMinus]
  module

@[simp] theorem fundamentalSymmetry_mul_modularSigmaPlus
    (c : SplitOctonionColour) :
    splitOctonionMulQ fundamentalSymmetry (modularSigmaPlus c) = modularSigmaPlus c := by
  change splitOctonionMulQ fundamentalSymmetry
      ((1 / 2 : ℚ) • (modularJ c - phaseAxis c)) =
    (1 / 2 : ℚ) • (modularJ c - phaseAxis c)
  rw [splitOctonionMulQ_smul_right, splitOctonionMulQ_sub_right,
    fundamentalSymmetry_mul_modularJ, fundamentalSymmetry_mul_phaseAxis]
  module

@[simp] theorem fundamentalSymmetry_mul_modularSigmaMinus
    (c : SplitOctonionColour) :
    splitOctonionMulQ fundamentalSymmetry (modularSigmaMinus c) =
      -modularSigmaMinus c := by
  change splitOctonionMulQ fundamentalSymmetry
      ((1 / 2 : ℚ) • (modularJ c + phaseAxis c)) =
    -((1 / 2 : ℚ) • (modularJ c + phaseAxis c))
  rw [splitOctonionMulQ_smul_right, splitOctonionMulQ_add_right,
    fundamentalSymmetry_mul_modularJ, fundamentalSymmetry_mul_phaseAxis]
  module

@[simp] theorem modularSigmaPlus_mul_fundamentalSymmetry
    (c : SplitOctonionColour) :
    splitOctonionMulQ (modularSigmaPlus c) fundamentalSymmetry =
      -modularSigmaPlus c := by
  change splitOctonionMulQ
      ((1 / 2 : ℚ) • (modularJ c - phaseAxis c)) fundamentalSymmetry =
    -((1 / 2 : ℚ) • (modularJ c - phaseAxis c))
  rw [splitOctonionMulQ_smul_left, splitOctonionMulQ_sub_left,
    modularJ_mul_fundamentalSymmetry, phaseAxis_mul_fundamentalSymmetry]
  module

@[simp] theorem modularSigmaMinus_mul_fundamentalSymmetry
    (c : SplitOctonionColour) :
    splitOctonionMulQ (modularSigmaMinus c) fundamentalSymmetry =
      modularSigmaMinus c := by
  change splitOctonionMulQ
      ((1 / 2 : ℚ) • (modularJ c + phaseAxis c)) fundamentalSymmetry =
    (1 / 2 : ℚ) • (modularJ c + phaseAxis c)
  rw [splitOctonionMulQ_smul_left, splitOctonionMulQ_add_left,
    modularJ_mul_fundamentalSymmetry, phaseAxis_mul_fundamentalSymmetry]
  module

@[simp] theorem modularNPlus_mul_modularSigmaPlus
    (c : SplitOctonionColour) :
    splitOctonionMulQ modularNPlus (modularSigmaPlus c) = modularSigmaPlus c := by
  change splitOctonionMulQ
    ((1 / 2 : ℚ) • (rationalBasis .one + fundamentalSymmetry))
    (modularSigmaPlus c) = modularSigmaPlus c
  rw [splitOctonionMulQ_smul_left, splitOctonionMulQ_add_left,
    splitOctonionMulQ_one_left, fundamentalSymmetry_mul_modularSigmaPlus]
  module

@[simp] theorem modularSigmaPlus_mul_modularNMinus
    (c : SplitOctonionColour) :
    splitOctonionMulQ (modularSigmaPlus c) modularNMinus = modularSigmaPlus c := by
  change splitOctonionMulQ (modularSigmaPlus c)
    ((1 / 2 : ℚ) • (rationalBasis .one - fundamentalSymmetry)) =
      modularSigmaPlus c
  rw [splitOctonionMulQ_smul_right, splitOctonionMulQ_sub_right,
    splitOctonionMulQ_one_right, modularSigmaPlus_mul_fundamentalSymmetry]
  module

@[simp] theorem modularNMinus_mul_modularSigmaMinus
    (c : SplitOctonionColour) :
    splitOctonionMulQ modularNMinus (modularSigmaMinus c) = modularSigmaMinus c := by
  change splitOctonionMulQ
    ((1 / 2 : ℚ) • (rationalBasis .one - fundamentalSymmetry))
    (modularSigmaMinus c) = modularSigmaMinus c
  rw [splitOctonionMulQ_smul_left, splitOctonionMulQ_sub_left,
    splitOctonionMulQ_one_left, fundamentalSymmetry_mul_modularSigmaMinus]
  module

@[simp] theorem modularSigmaMinus_mul_modularNPlus
    (c : SplitOctonionColour) :
    splitOctonionMulQ (modularSigmaMinus c) modularNPlus = modularSigmaMinus c := by
  change splitOctonionMulQ (modularSigmaMinus c)
    ((1 / 2 : ℚ) • (rationalBasis .one + fundamentalSymmetry)) =
      modularSigmaMinus c
  rw [splitOctonionMulQ_smul_right, splitOctonionMulQ_add_right,
    splitOctonionMulQ_one_right, modularSigmaMinus_mul_fundamentalSymmetry]
  module

@[simp] theorem modularNMinus_mul_modularSigmaPlus
    (c : SplitOctonionColour) :
    splitOctonionMulQ modularNMinus (modularSigmaPlus c) = 0 := by
  change splitOctonionMulQ
    ((1 / 2 : ℚ) • (rationalBasis .one - fundamentalSymmetry))
    (modularSigmaPlus c) = 0
  rw [splitOctonionMulQ_smul_left, splitOctonionMulQ_sub_left,
    splitOctonionMulQ_one_left, fundamentalSymmetry_mul_modularSigmaPlus]
  simp

@[simp] theorem modularSigmaPlus_mul_modularNPlus
    (c : SplitOctonionColour) :
    splitOctonionMulQ (modularSigmaPlus c) modularNPlus = 0 := by
  change splitOctonionMulQ (modularSigmaPlus c)
    ((1 / 2 : ℚ) • (rationalBasis .one + fundamentalSymmetry)) = 0
  rw [splitOctonionMulQ_smul_right, splitOctonionMulQ_add_right,
    splitOctonionMulQ_one_right, modularSigmaPlus_mul_fundamentalSymmetry]
  simp

@[simp] theorem modularNPlus_mul_modularSigmaMinus
    (c : SplitOctonionColour) :
    splitOctonionMulQ modularNPlus (modularSigmaMinus c) = 0 := by
  change splitOctonionMulQ
    ((1 / 2 : ℚ) • (rationalBasis .one + fundamentalSymmetry))
    (modularSigmaMinus c) = 0
  rw [splitOctonionMulQ_smul_left, splitOctonionMulQ_add_left,
    splitOctonionMulQ_one_left, fundamentalSymmetry_mul_modularSigmaMinus]
  simp

@[simp] theorem modularSigmaMinus_mul_modularNMinus
    (c : SplitOctonionColour) :
    splitOctonionMulQ (modularSigmaMinus c) modularNMinus = 0 := by
  change splitOctonionMulQ (modularSigmaMinus c)
    ((1 / 2 : ℚ) • (rationalBasis .one - fundamentalSymmetry)) = 0
  rw [splitOctonionMulQ_smul_right, splitOctonionMulQ_sub_right,
    splitOctonionMulQ_one_right, modularSigmaMinus_mul_fundamentalSymmetry]
  simp

theorem modularPolarized_one :
    modularNPlus + modularNMinus = rationalBasis .one := by
  simp [modularNPlus, modularNMinus]
  module

theorem modularPolarized_epsilon :
    modularNPlus - modularNMinus = fundamentalSymmetry := by
  simp [modularNPlus, modularNMinus]
  module

theorem modularPolarized_phaseAxis (c : SplitOctonionColour) :
    modularSigmaMinus c - modularSigmaPlus c = phaseAxis c := by
  simp [modularSigmaPlus, modularSigmaMinus]
  module

theorem modularPolarized_modularJ (c : SplitOctonionColour) :
    modularSigmaPlus c + modularSigmaMinus c = modularJ c := by
  simp [modularSigmaPlus, modularSigmaMinus]
  module

end
end InfoGeometry.Canonical
