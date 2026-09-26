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

set_option maxHeartbeats 800000

def nativeCommutator
    (x y : StandardRationalSplitOctonion) : StandardRationalSplitOctonion :=
  splitOctonionMulQ x y - splitOctonionMulQ y x

def nativeAnticommutator
    (x y : StandardRationalSplitOctonion) : StandardRationalSplitOctonion :=
  splitOctonionMulQ x y + splitOctonionMulQ y x

@[simp] theorem nativeCommutator_self (x : StandardRationalSplitOctonion) :
    nativeCommutator x x = 0 := by
  simp [nativeCommutator]

theorem nativeAnticommutator_comm (x y : StandardRationalSplitOctonion) :
    nativeAnticommutator x y = nativeAnticommutator y x := by
  simp [nativeAnticommutator, add_comm]

local macro "solve_bracket" : tactic =>
  `(tactic| (
    funext b
    fin_cases b <;>
      simp [nativeCommutator, nativeAnticommutator, modularSigmaPlus, modularSigmaMinus,
        modularNPlus, modularNMinus, modularJ, phaseAxis, colourUnit, fundamentalSymmetry,
        rationalBasis, splitOctonionMulQ, splitQuaternionOfQ,
        splitQuaternionLPartQ, splitQuaternionAddQ, splitQuaternionMulQ,
        splitQuaternionConjQ, splitOctonionOfQuaternionPairQ, Pi.single] <;>
      ring
  ))

theorem nativeAnticommutator_sigmaPlus_diag (c : SplitOctonionColour) :
    nativeAnticommutator (modularSigmaPlus c) (modularSigmaPlus c) = 0 := by
  cases c
  · solve_bracket
  · solve_bracket
  · solve_bracket

theorem nativeAnticommutator_sigmaPlus_red_green :
    nativeAnticommutator (modularSigmaPlus .red) (modularSigmaPlus .green) = 0 := by
  solve_bracket

theorem nativeAnticommutator_sigmaPlus_red_blue :
    nativeAnticommutator (modularSigmaPlus .red) (modularSigmaPlus .blue) = 0 := by
  solve_bracket

theorem nativeAnticommutator_sigmaPlus_green_blue :
    nativeAnticommutator (modularSigmaPlus .green) (modularSigmaPlus .blue) = 0 := by
  solve_bracket

@[simp] theorem nativeAnticommutator_sigmaPlus_sigmaPlus
    (c d : SplitOctonionColour) :
    nativeAnticommutator (modularSigmaPlus c) (modularSigmaPlus d) = 0 := by
  cases c <;> cases d
  · exact nativeAnticommutator_sigmaPlus_diag .red
  · exact nativeAnticommutator_sigmaPlus_red_green
  · exact nativeAnticommutator_sigmaPlus_red_blue
  · rw [nativeAnticommutator_comm]; exact nativeAnticommutator_sigmaPlus_red_green
  · exact nativeAnticommutator_sigmaPlus_diag .green
  · exact nativeAnticommutator_sigmaPlus_green_blue
  · rw [nativeAnticommutator_comm]; exact nativeAnticommutator_sigmaPlus_red_blue
  · rw [nativeAnticommutator_comm]; exact nativeAnticommutator_sigmaPlus_green_blue
  · exact nativeAnticommutator_sigmaPlus_diag .blue

theorem nativeAnticommutator_sigmaMinus_diag (c : SplitOctonionColour) :
    nativeAnticommutator (modularSigmaMinus c) (modularSigmaMinus c) = 0 := by
  cases c
  · solve_bracket
  · solve_bracket
  · solve_bracket

theorem nativeAnticommutator_sigmaMinus_red_green :
    nativeAnticommutator (modularSigmaMinus .red) (modularSigmaMinus .green) = 0 := by
  solve_bracket

theorem nativeAnticommutator_sigmaMinus_red_blue :
    nativeAnticommutator (modularSigmaMinus .red) (modularSigmaMinus .blue) = 0 := by
  solve_bracket

theorem nativeAnticommutator_sigmaMinus_green_blue :
    nativeAnticommutator (modularSigmaMinus .green) (modularSigmaMinus .blue) = 0 := by
  solve_bracket

@[simp] theorem nativeAnticommutator_sigmaMinus_sigmaMinus
    (c d : SplitOctonionColour) :
    nativeAnticommutator (modularSigmaMinus c) (modularSigmaMinus d) = 0 := by
  cases c <;> cases d
  · exact nativeAnticommutator_sigmaMinus_diag .red
  · exact nativeAnticommutator_sigmaMinus_red_green
  · exact nativeAnticommutator_sigmaMinus_red_blue
  · rw [nativeAnticommutator_comm]; exact nativeAnticommutator_sigmaMinus_red_green
  · exact nativeAnticommutator_sigmaMinus_diag .green
  · exact nativeAnticommutator_sigmaMinus_green_blue
  · rw [nativeAnticommutator_comm]; exact nativeAnticommutator_sigmaMinus_red_blue
  · rw [nativeAnticommutator_comm]; exact nativeAnticommutator_sigmaMinus_green_blue
  · exact nativeAnticommutator_sigmaMinus_diag .blue

theorem nativeSigmaPlus_red_green_commutator :
    nativeCommutator (modularSigmaPlus .red) (modularSigmaPlus .green) =
      (2 : ℚ) • modularSigmaMinus .blue := by
  solve_bracket

theorem nativeSigmaPlus_red_blue_commutator :
    nativeCommutator (modularSigmaPlus .red) (modularSigmaPlus .blue) =
      (-2 : ℚ) • modularSigmaMinus .green := by
  solve_bracket

theorem nativeSigmaPlus_green_blue_commutator :
    nativeCommutator (modularSigmaPlus .green) (modularSigmaPlus .blue) =
      (2 : ℚ) • modularSigmaMinus .red := by
  solve_bracket

theorem nativeSigmaMinus_red_green_commutator :
    nativeCommutator (modularSigmaMinus .red) (modularSigmaMinus .green) =
      (-2 : ℚ) • modularSigmaPlus .blue := by
  solve_bracket

theorem nativeSigmaMinus_red_blue_commutator :
    nativeCommutator (modularSigmaMinus .red) (modularSigmaMinus .blue) =
      (2 : ℚ) • modularSigmaPlus .green := by
  solve_bracket

theorem nativeSigmaMinus_green_blue_commutator :
    nativeCommutator (modularSigmaMinus .green) (modularSigmaMinus .blue) =
      (-2 : ℚ) • modularSigmaPlus .red := by
  solve_bracket

theorem nativeSigmaPlusSigmaMinus_commutator_diag (c : SplitOctonionColour) :
    nativeCommutator (modularSigmaPlus c) (modularSigmaMinus c) = fundamentalSymmetry := by
  cases c
  · solve_bracket
  · solve_bracket
  · solve_bracket

theorem nativeSigmaPlusSigmaMinus_commutator_red_green :
    nativeCommutator (modularSigmaPlus .red) (modularSigmaMinus .green) = 0 := by
  solve_bracket

theorem nativeSigmaPlusSigmaMinus_commutator_red_blue :
    nativeCommutator (modularSigmaPlus .red) (modularSigmaMinus .blue) = 0 := by
  solve_bracket

theorem nativeSigmaPlusSigmaMinus_commutator_green_red :
    nativeCommutator (modularSigmaPlus .green) (modularSigmaMinus .red) = 0 := by
  solve_bracket

theorem nativeSigmaPlusSigmaMinus_commutator_green_blue :
    nativeCommutator (modularSigmaPlus .green) (modularSigmaMinus .blue) = 0 := by
  solve_bracket

theorem nativeSigmaPlusSigmaMinus_commutator_blue_red :
    nativeCommutator (modularSigmaPlus .blue) (modularSigmaMinus .red) = 0 := by
  solve_bracket

theorem nativeSigmaPlusSigmaMinus_commutator_blue_green :
    nativeCommutator (modularSigmaPlus .blue) (modularSigmaMinus .green) = 0 := by
  solve_bracket

@[simp] theorem nativeSigmaPlusSigmaMinus_commutator
    (c d : SplitOctonionColour) :
    nativeCommutator (modularSigmaPlus c) (modularSigmaMinus d) =
      if c = d then fundamentalSymmetry else 0 := by
  cases c <;> cases d
  · simpa using nativeSigmaPlusSigmaMinus_commutator_diag .red
  · simpa using nativeSigmaPlusSigmaMinus_commutator_red_green
  · simpa using nativeSigmaPlusSigmaMinus_commutator_red_blue
  · simpa using nativeSigmaPlusSigmaMinus_commutator_green_red
  · simpa using nativeSigmaPlusSigmaMinus_commutator_diag .green
  · simpa using nativeSigmaPlusSigmaMinus_commutator_green_blue
  · simpa using nativeSigmaPlusSigmaMinus_commutator_blue_red
  · simpa using nativeSigmaPlusSigmaMinus_commutator_blue_green
  · simpa using nativeSigmaPlusSigmaMinus_commutator_diag .blue

theorem nativeSigmaPlusSigmaMinus_anticommutator_diag (c : SplitOctonionColour) :
    nativeAnticommutator (modularSigmaPlus c) (modularSigmaMinus c) = rationalBasis .one := by
  cases c
  · solve_bracket
  · solve_bracket
  · solve_bracket

theorem nativeSigmaPlusSigmaMinus_anticommutator_red_green :
    nativeAnticommutator (modularSigmaPlus .red) (modularSigmaMinus .green) = 0 := by
  solve_bracket

theorem nativeSigmaPlusSigmaMinus_anticommutator_red_blue :
    nativeAnticommutator (modularSigmaPlus .red) (modularSigmaMinus .blue) = 0 := by
  solve_bracket

theorem nativeSigmaPlusSigmaMinus_anticommutator_green_red :
    nativeAnticommutator (modularSigmaPlus .green) (modularSigmaMinus .red) = 0 := by
  solve_bracket

theorem nativeSigmaPlusSigmaMinus_anticommutator_green_blue :
    nativeAnticommutator (modularSigmaPlus .green) (modularSigmaMinus .blue) = 0 := by
  solve_bracket

theorem nativeSigmaPlusSigmaMinus_anticommutator_blue_red :
    nativeAnticommutator (modularSigmaPlus .blue) (modularSigmaMinus .red) = 0 := by
  solve_bracket

theorem nativeSigmaPlusSigmaMinus_anticommutator_blue_green :
    nativeAnticommutator (modularSigmaPlus .blue) (modularSigmaMinus .green) = 0 := by
  solve_bracket

@[simp] theorem nativeSigmaPlusSigmaMinus_anticommutator
    (c d : SplitOctonionColour) :
    nativeAnticommutator (modularSigmaPlus c) (modularSigmaMinus d) =
      if c = d then rationalBasis .one else 0 := by
  cases c <;> cases d
  · simpa using nativeSigmaPlusSigmaMinus_anticommutator_diag .red
  · simpa using nativeSigmaPlusSigmaMinus_anticommutator_red_green
  · simpa using nativeSigmaPlusSigmaMinus_anticommutator_red_blue
  · simpa using nativeSigmaPlusSigmaMinus_anticommutator_green_red
  · simpa using nativeSigmaPlusSigmaMinus_anticommutator_diag .green
  · simpa using nativeSigmaPlusSigmaMinus_anticommutator_green_blue
  · simpa using nativeSigmaPlusSigmaMinus_anticommutator_blue_red
  · simpa using nativeSigmaPlusSigmaMinus_anticommutator_blue_green
  · simpa using nativeSigmaPlusSigmaMinus_anticommutator_diag .blue

@[simp] theorem nativeNPlus_sigmaPlus_commutator
    (c : SplitOctonionColour) :
    nativeCommutator modularNPlus (modularSigmaPlus c) =
      modularSigmaPlus c := by
  cases c
  · solve_bracket
  · solve_bracket
  · solve_bracket

@[simp] theorem nativeNPlus_sigmaPlus_anticommutator
    (c : SplitOctonionColour) :
    nativeAnticommutator modularNPlus (modularSigmaPlus c) =
      modularSigmaPlus c := by
  cases c
  · solve_bracket
  · solve_bracket
  · solve_bracket

@[simp] theorem nativeNMinus_sigmaPlus_commutator
    (c : SplitOctonionColour) :
    nativeCommutator modularNMinus (modularSigmaPlus c) =
      -modularSigmaPlus c := by
  cases c
  · solve_bracket
  · solve_bracket
  · solve_bracket

@[simp] theorem nativeNMinus_sigmaPlus_anticommutator
    (c : SplitOctonionColour) :
    nativeAnticommutator modularNMinus (modularSigmaPlus c) =
      modularSigmaPlus c := by
  cases c
  · solve_bracket
  · solve_bracket
  · solve_bracket

@[simp] theorem nativeNPlus_sigmaMinus_commutator
    (c : SplitOctonionColour) :
    nativeCommutator modularNPlus (modularSigmaMinus c) =
      -modularSigmaMinus c := by
  cases c
  · solve_bracket
  · solve_bracket
  · solve_bracket

@[simp] theorem nativeNPlus_sigmaMinus_anticommutator
    (c : SplitOctonionColour) :
    nativeAnticommutator modularNPlus (modularSigmaMinus c) =
      modularSigmaMinus c := by
  cases c
  · solve_bracket
  · solve_bracket
  · solve_bracket

@[simp] theorem nativeNMinus_sigmaMinus_commutator
    (c : SplitOctonionColour) :
    nativeCommutator modularNMinus (modularSigmaMinus c) =
      modularSigmaMinus c := by
  cases c
  · solve_bracket
  · solve_bracket
  · solve_bracket

@[simp] theorem nativeNMinus_sigmaMinus_anticommutator
    (c : SplitOctonionColour) :
    nativeAnticommutator modularNMinus (modularSigmaMinus c) =
      modularSigmaMinus c := by
  cases c
  · solve_bracket
  · solve_bracket
  · solve_bracket

@[simp] theorem nativeNPlus_NMinus_commutator :
    nativeCommutator modularNPlus modularNMinus = 0 := by
  solve_bracket

@[simp] theorem nativeNPlus_NMinus_anticommutator :
    nativeAnticommutator modularNPlus modularNMinus = 0 := by
  solve_bracket

@[simp] theorem nativeNPlus_self_commutator :
    nativeCommutator modularNPlus modularNPlus = 0 := by
  exact nativeCommutator_self modularNPlus

@[simp] theorem nativeNPlus_self_anticommutator :
    nativeAnticommutator modularNPlus modularNPlus =
      (2 : ℚ) • modularNPlus := by
  solve_bracket

@[simp] theorem nativeNMinus_self_commutator :
    nativeCommutator modularNMinus modularNMinus = 0 := by
  exact nativeCommutator_self modularNMinus

@[simp] theorem nativeNMinus_self_anticommutator :
    nativeAnticommutator modularNMinus modularNMinus =
      (2 : ℚ) • modularNMinus := by
  solve_bracket

end
end InfoGeometry.Canonical


#print axioms InfoGeometry.Canonical.nativeCommutator
#print axioms InfoGeometry.Canonical.nativeAnticommutator
#print axioms InfoGeometry.Canonical.nativeCommutator_self
#print axioms InfoGeometry.Canonical.nativeAnticommutator_comm
#print axioms InfoGeometry.Canonical.nativeAnticommutator_sigmaPlus_diag
#print axioms InfoGeometry.Canonical.nativeAnticommutator_sigmaPlus_red_green
#print axioms InfoGeometry.Canonical.nativeAnticommutator_sigmaPlus_red_blue
#print axioms InfoGeometry.Canonical.nativeAnticommutator_sigmaPlus_green_blue
#print axioms InfoGeometry.Canonical.nativeAnticommutator_sigmaPlus_sigmaPlus
#print axioms InfoGeometry.Canonical.nativeAnticommutator_sigmaMinus_diag
#print axioms InfoGeometry.Canonical.nativeAnticommutator_sigmaMinus_red_green
#print axioms InfoGeometry.Canonical.nativeAnticommutator_sigmaMinus_red_blue
#print axioms InfoGeometry.Canonical.nativeAnticommutator_sigmaMinus_green_blue
#print axioms InfoGeometry.Canonical.nativeAnticommutator_sigmaMinus_sigmaMinus
#print axioms InfoGeometry.Canonical.nativeSigmaPlus_red_green_commutator
#print axioms InfoGeometry.Canonical.nativeSigmaPlus_red_blue_commutator
#print axioms InfoGeometry.Canonical.nativeSigmaPlus_green_blue_commutator
#print axioms InfoGeometry.Canonical.nativeSigmaMinus_red_green_commutator
#print axioms InfoGeometry.Canonical.nativeSigmaMinus_red_blue_commutator
#print axioms InfoGeometry.Canonical.nativeSigmaMinus_green_blue_commutator
#print axioms InfoGeometry.Canonical.nativeSigmaPlusSigmaMinus_commutator_diag
#print axioms InfoGeometry.Canonical.nativeSigmaPlusSigmaMinus_commutator_red_green
#print axioms InfoGeometry.Canonical.nativeSigmaPlusSigmaMinus_commutator_red_blue
#print axioms InfoGeometry.Canonical.nativeSigmaPlusSigmaMinus_commutator_green_red
#print axioms InfoGeometry.Canonical.nativeSigmaPlusSigmaMinus_commutator_green_blue
#print axioms InfoGeometry.Canonical.nativeSigmaPlusSigmaMinus_commutator_blue_red
#print axioms InfoGeometry.Canonical.nativeSigmaPlusSigmaMinus_commutator_blue_green
#print axioms InfoGeometry.Canonical.nativeSigmaPlusSigmaMinus_commutator
#print axioms InfoGeometry.Canonical.nativeSigmaPlusSigmaMinus_anticommutator_diag
#print axioms InfoGeometry.Canonical.nativeSigmaPlusSigmaMinus_anticommutator_red_green
#print axioms InfoGeometry.Canonical.nativeSigmaPlusSigmaMinus_anticommutator_red_blue
#print axioms InfoGeometry.Canonical.nativeSigmaPlusSigmaMinus_anticommutator_green_red
#print axioms InfoGeometry.Canonical.nativeSigmaPlusSigmaMinus_anticommutator_green_blue
#print axioms InfoGeometry.Canonical.nativeSigmaPlusSigmaMinus_anticommutator_blue_red
#print axioms InfoGeometry.Canonical.nativeSigmaPlusSigmaMinus_anticommutator_blue_green
#print axioms InfoGeometry.Canonical.nativeSigmaPlusSigmaMinus_anticommutator
#print axioms InfoGeometry.Canonical.nativeNPlus_sigmaPlus_commutator
#print axioms InfoGeometry.Canonical.nativeNPlus_sigmaPlus_anticommutator
#print axioms InfoGeometry.Canonical.nativeNMinus_sigmaPlus_commutator
#print axioms InfoGeometry.Canonical.nativeNMinus_sigmaPlus_anticommutator
#print axioms InfoGeometry.Canonical.nativeNPlus_sigmaMinus_commutator
#print axioms InfoGeometry.Canonical.nativeNPlus_sigmaMinus_anticommutator
#print axioms InfoGeometry.Canonical.nativeNMinus_sigmaMinus_commutator
#print axioms InfoGeometry.Canonical.nativeNMinus_sigmaMinus_anticommutator
#print axioms InfoGeometry.Canonical.nativeNPlus_NMinus_commutator
#print axioms InfoGeometry.Canonical.nativeNPlus_NMinus_anticommutator
#print axioms InfoGeometry.Canonical.nativeNPlus_self_commutator
#print axioms InfoGeometry.Canonical.nativeNPlus_self_anticommutator
#print axioms InfoGeometry.Canonical.nativeNMinus_self_commutator
#print axioms InfoGeometry.Canonical.nativeNMinus_self_anticommutator
