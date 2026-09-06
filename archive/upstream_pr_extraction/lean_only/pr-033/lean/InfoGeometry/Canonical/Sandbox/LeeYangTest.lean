import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import InfoGeometry.Canonical.LeeYangQuadraticCircleTheoremNative

open Complex
open Polynomial
open Set
open Filter
open InfoGeometry.Canonical.LeeYangQuadraticCircleTheoremNative

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-!
# Sandbox: Single Lemma Test

Testing one lemma at a time to verify the sandbox works.
-/

namespace InfoGeometry.Canonical.LeeYangSandbox

open Complex
open Polynomial
open Set
open Filter
open InfoGeometry.Canonical.LeeYangQuadraticCircleTheoremNative

/-- Test 1: Basic complex abs and normSq -/
theorem test_complex_abs_normSq (a : ℝ) (ha : a ^ 2 ≤ 1) :
    ‖(⟨-a, Real.sqrt (1 - a ^ 2)⟩ : ℂ)‖ = 1 := by
  let z : ℂ := ⟨-a, Real.sqrt (1 - a ^ 2)⟩
  have hz_sq : Complex.normSq z = 1 :=
    quadratic_leeyang_root_normSq_eq_one a ha
  rw [Complex.normSq_eq_norm_sq] at hz_sq
  nlinarith [norm_nonneg z]

end InfoGeometry.Canonical.LeeYangSandbox
