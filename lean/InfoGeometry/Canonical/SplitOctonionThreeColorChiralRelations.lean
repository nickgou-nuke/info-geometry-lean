import InfoGeometry.Canonical.SplitOctonionThreeColorModularCl11
import InfoGeometry.Algebra.FiniteSpinAlgebra

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

@[simp] theorem modularNPlus_sq :
    splitOctonionMulQ modularNPlus modularNPlus = modularNPlus := by
  native_decide

@[simp] theorem modularNMinus_sq :
    splitOctonionMulQ modularNMinus modularNMinus = modularNMinus := by
  native_decide

@[simp] theorem modularNPlus_mul_modularNMinus :
    splitOctonionMulQ modularNPlus modularNMinus = 0 := by
  native_decide

@[simp] theorem modularNMinus_mul_modularNPlus :
    splitOctonionMulQ modularNMinus modularNPlus = 0 := by
  native_decide

@[simp] theorem modularSigmaPlus_sq_zero (c : SplitOctonionColour) :
    splitOctonionMulQ (modularSigmaPlus c) (modularSigmaPlus c) = 0 := by
  cases c <;> native_decide

@[simp] theorem modularSigmaMinus_sq_zero (c : SplitOctonionColour) :
    splitOctonionMulQ (modularSigmaMinus c) (modularSigmaMinus c) = 0 := by
  cases c <;> native_decide

@[simp] theorem modularSigmaPlus_mul_modularSigmaMinus (c : SplitOctonionColour) :
    splitOctonionMulQ (modularSigmaPlus c) (modularSigmaMinus c) = modularNPlus := by
  cases c <;> native_decide

@[simp] theorem modularSigmaMinus_mul_modularSigmaPlus (c : SplitOctonionColour) :
    splitOctonionMulQ (modularSigmaMinus c) (modularSigmaPlus c) = modularNMinus := by
  cases c <;> native_decide

@[simp] theorem fundamentalSymmetry_mul_modularSigmaPlus
    (c : SplitOctonionColour) :
    splitOctonionMulQ fundamentalSymmetry (modularSigmaPlus c) = modularSigmaPlus c := by
  cases c <;> native_decide

@[simp] theorem fundamentalSymmetry_mul_modularSigmaMinus
    (c : SplitOctonionColour) :
    splitOctonionMulQ fundamentalSymmetry (modularSigmaMinus c) =
      -modularSigmaMinus c := by
  cases c <;> native_decide

@[simp] theorem modularSigmaPlus_mul_fundamentalSymmetry
    (c : SplitOctonionColour) :
    splitOctonionMulQ (modularSigmaPlus c) fundamentalSymmetry =
      -modularSigmaPlus c := by
  cases c <;> native_decide

@[simp] theorem modularSigmaMinus_mul_fundamentalSymmetry
    (c : SplitOctonionColour) :
    splitOctonionMulQ (modularSigmaMinus c) fundamentalSymmetry =
      modularSigmaMinus c := by
  cases c <;> native_decide

@[simp] theorem modularNPlus_mul_modularSigmaPlus
    (c : SplitOctonionColour) :
    splitOctonionMulQ modularNPlus (modularSigmaPlus c) = modularSigmaPlus c := by
  cases c <;> native_decide

@[simp] theorem modularSigmaPlus_mul_modularNMinus
    (c : SplitOctonionColour) :
    splitOctonionMulQ (modularSigmaPlus c) modularNMinus = modularSigmaPlus c := by
  cases c <;> native_decide

@[simp] theorem modularNMinus_mul_modularSigmaMinus
    (c : SplitOctonionColour) :
    splitOctonionMulQ modularNMinus (modularSigmaMinus c) = modularSigmaMinus c := by
  cases c <;> native_decide

@[simp] theorem modularSigmaMinus_mul_modularNPlus
    (c : SplitOctonionColour) :
    splitOctonionMulQ (modularSigmaMinus c) modularNPlus = modularSigmaMinus c := by
  cases c <;> native_decide

@[simp] theorem modularNMinus_mul_modularSigmaPlus
    (c : SplitOctonionColour) :
    splitOctonionMulQ modularNMinus (modularSigmaPlus c) = 0 := by
  cases c <;> native_decide

@[simp] theorem modularSigmaPlus_mul_modularNPlus
    (c : SplitOctonionColour) :
    splitOctonionMulQ (modularSigmaPlus c) modularNPlus = 0 := by
  cases c <;> native_decide

@[simp] theorem modularNPlus_mul_modularSigmaMinus
    (c : SplitOctonionColour) :
    splitOctonionMulQ modularNPlus (modularSigmaMinus c) = 0 := by
  cases c <;> native_decide

@[simp] theorem modularSigmaMinus_mul_modularNMinus
    (c : SplitOctonionColour) :
    splitOctonionMulQ (modularSigmaMinus c) modularNMinus = 0 := by
  cases c <;> native_decide

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
