/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SignedNetwork.BranchingInitialization
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.SignedNetwork.QubitWignerBridge
import InfoGeometry.SignedNetwork.BranchingEnsembleGenerator

set_option maxHeartbeats 800000

/-! The finite ensemble bridge to the existing qubit frame.

This owner proves reconstruction of the Pauli carrier from the installed
phase-point coordinates.  It deliberately stops before claiming a
continuous-time branching process or identifying signed counts with density
matrices.
-/
namespace InfoGeometry.SignedNetwork.BranchingQubitGenerator

noncomputable section

open InfoGeometry.SignedNetwork.ExactCancellation
open InfoGeometry.SignedNetwork.QubitWignerBridge
open InfoGeometry.SignedNetwork.BranchingEnsembleGenerator
open InfoGeometry.SignedNetwork.PauliContextBridge
open InfoGeometry.Canonical.PauliHestenesSpinMomentum

theorem synthesis_analysis_pauli (P : PauliParavector) :
    synthesis (analysis P.pauliMatrix) = P.pauliMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [synthesis, analysis, phasePoint, phaseDirection,
      contextProjector, PauliParavector.pauliMatrix, Matrix.trace,
      Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply,
      Fin.sum_univ_four, Fin.sum_univ_two, Complex.mul_re,
      Complex.mul_im] <;> ring


def empiricalDensity (weight : ℝ) (p : Counts (Fin 4)) : Mat2 :=
  (weight : ℂ) • synthesis (signedReal p)

@[simp] theorem empiricalDensity_cancel (weight : ℝ) (p : Counts (Fin 4)) :
    empiricalDensity weight (cancel p) = empiricalDensity weight p := by
  simp only [empiricalDensity, synthesis, signedReal_cancel]

@[simp] theorem empiricalDensity_addNullPairs
    (weight : ℝ) (p : Counts (Fin 4)) (k : Fin 4 → ℕ) :
    empiricalDensity weight (addNullPairs p k) = empiricalDensity weight p := by
  simp only [empiricalDensity, synthesis, signedReal_addNullPairs]


end

end InfoGeometry.SignedNetwork.BranchingQubitGenerator
