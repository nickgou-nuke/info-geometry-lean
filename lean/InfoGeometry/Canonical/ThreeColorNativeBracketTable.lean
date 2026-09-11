import InfoGeometry.Canonical.SplitOctonionThreeColorChiralRelations
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

open SplitOctonionColour

/-!
# Native three-colour commutator and anticommutator table

This is the bracket readout of the native split-octonion multiplication.  It
does not install a Lie or Lie-superalgebra instance: the full carrier is
nonassociative, and the ordinary commutator has an associator-controlled
Jacobi defect.  The table is nevertheless a genuine calculation in the
native rational Zorn product.
-/

noncomputable section

def nativeCommutator
    (x y : StandardRationalSplitOctonion) : StandardRationalSplitOctonion :=
  splitOctonionMulQ x y - splitOctonionMulQ y x

def nativeAnticommutator
    (x y : StandardRationalSplitOctonion) : StandardRationalSplitOctonion :=
  splitOctonionMulQ x y + splitOctonionMulQ y x

@[simp] theorem nativeCommutator_self (x : StandardRationalSplitOctonion) :
    nativeCommutator x x = 0 := by
  simp [nativeCommutator]

@[simp] theorem nativeAnticommutator_sigmaPlus_sigmaPlus
    (c d : SplitOctonionColour) :
    nativeAnticommutator (modularSigmaPlus c) (modularSigmaPlus d) = 0 := by
  cases c <;> cases d <;> native_decide

@[simp] theorem nativeAnticommutator_sigmaMinus_sigmaMinus
    (c d : SplitOctonionColour) :
    nativeAnticommutator (modularSigmaMinus c) (modularSigmaMinus d) = 0 := by
  cases c <;> cases d <;> native_decide

theorem nativeSigmaPlus_red_green_commutator :
    nativeCommutator (modularSigmaPlus .red) (modularSigmaPlus .green) =
      (2 : ℚ) • modularSigmaMinus .blue := by
  native_decide

theorem nativeSigmaPlus_red_blue_commutator :
    nativeCommutator (modularSigmaPlus .red) (modularSigmaPlus .blue) =
      (-2 : ℚ) • modularSigmaMinus .green := by
  native_decide

theorem nativeSigmaPlus_green_blue_commutator :
    nativeCommutator (modularSigmaPlus .green) (modularSigmaPlus .blue) =
      (2 : ℚ) • modularSigmaMinus .red := by
  native_decide

theorem nativeSigmaMinus_red_green_commutator :
    nativeCommutator (modularSigmaMinus .red) (modularSigmaMinus .green) =
      (-2 : ℚ) • modularSigmaPlus .blue := by
  native_decide

theorem nativeSigmaMinus_red_blue_commutator :
    nativeCommutator (modularSigmaMinus .red) (modularSigmaMinus .blue) =
      (2 : ℚ) • modularSigmaPlus .green := by
  native_decide

theorem nativeSigmaMinus_green_blue_commutator :
    nativeCommutator (modularSigmaMinus .green) (modularSigmaMinus .blue) =
      (-2 : ℚ) • modularSigmaPlus .red := by
  native_decide

@[simp] theorem nativeSigmaPlusSigmaMinus_commutator
    (c d : SplitOctonionColour) :
    nativeCommutator (modularSigmaPlus c) (modularSigmaMinus d) =
      if c = d then fundamentalSymmetry else 0 := by
  cases c <;> cases d <;> native_decide

@[simp] theorem nativeSigmaPlusSigmaMinus_anticommutator
    (c d : SplitOctonionColour) :
    nativeAnticommutator (modularSigmaPlus c) (modularSigmaMinus d) =
      if c = d then rationalBasis .one else 0 := by
  cases c <;> cases d <;> native_decide

@[simp] theorem nativeNPlus_sigmaPlus_commutator
    (c : SplitOctonionColour) :
    nativeCommutator modularNPlus (modularSigmaPlus c) =
      modularSigmaPlus c := by
  cases c <;> native_decide

@[simp] theorem nativeNPlus_sigmaPlus_anticommutator
    (c : SplitOctonionColour) :
    nativeAnticommutator modularNPlus (modularSigmaPlus c) =
      modularSigmaPlus c := by
  cases c <;> native_decide

@[simp] theorem nativeNMinus_sigmaPlus_commutator
    (c : SplitOctonionColour) :
    nativeCommutator modularNMinus (modularSigmaPlus c) =
      -modularSigmaPlus c := by
  cases c <;> native_decide

@[simp] theorem nativeNMinus_sigmaPlus_anticommutator
    (c : SplitOctonionColour) :
    nativeAnticommutator modularNMinus (modularSigmaPlus c) =
      modularSigmaPlus c := by
  cases c <;> native_decide

@[simp] theorem nativeNPlus_sigmaMinus_commutator
    (c : SplitOctonionColour) :
    nativeCommutator modularNPlus (modularSigmaMinus c) =
      -modularSigmaMinus c := by
  cases c <;> native_decide

@[simp] theorem nativeNPlus_sigmaMinus_anticommutator
    (c : SplitOctonionColour) :
    nativeAnticommutator modularNPlus (modularSigmaMinus c) =
      modularSigmaMinus c := by
  cases c <;> native_decide

@[simp] theorem nativeNMinus_sigmaMinus_commutator
    (c : SplitOctonionColour) :
    nativeCommutator modularNMinus (modularSigmaMinus c) =
      modularSigmaMinus c := by
  cases c <;> native_decide

@[simp] theorem nativeNMinus_sigmaMinus_anticommutator
    (c : SplitOctonionColour) :
    nativeAnticommutator modularNMinus (modularSigmaMinus c) =
      modularSigmaMinus c := by
  cases c <;> native_decide

@[simp] theorem nativeNPlus_NMinus_commutator :
    nativeCommutator modularNPlus modularNMinus = 0 := by
  native_decide

@[simp] theorem nativeNPlus_NMinus_anticommutator :
    nativeAnticommutator modularNPlus modularNMinus = 0 := by
  native_decide

@[simp] theorem nativeNPlus_self_commutator :
    nativeCommutator modularNPlus modularNPlus = 0 := by
  native_decide

@[simp] theorem nativeNPlus_self_anticommutator :
    nativeAnticommutator modularNPlus modularNPlus =
      (2 : ℚ) • modularNPlus := by
  native_decide

@[simp] theorem nativeNMinus_self_commutator :
    nativeCommutator modularNMinus modularNMinus = 0 := by
  native_decide

@[simp] theorem nativeNMinus_self_anticommutator :
    nativeAnticommutator modularNMinus modularNMinus =
      (2 : ℚ) • modularNMinus := by
  native_decide

end
end InfoGeometry.Canonical
