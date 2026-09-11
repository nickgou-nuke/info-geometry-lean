import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import InfoGeometry.Canonical.LeeYangQuadraticCircleTheoremNative

open Complex
open Polynomial
open Set
open Filter
open InfoGeometry.Canonical.LeeYangQuadraticCircleTheoremNative

/-!
# Small test: verify the quadratic Lee-Yang circle theorem connects to existing native theorems
-/

namespace InfoGeometry.Canonical.LeeYangCapstoneTest

open Complex
open Polynomial
open Set
open Filter
open InfoGeometry.Canonical.LeeYangQuadraticCircleTheoremNative

/-- Test: quadratic Lee-Yang root norm -/
theorem test_quadratic_root_norm (a : ℝ) (ha : a ^ 2 ≤ 1) :
    ‖(⟨-a, Real.sqrt (1 - a ^ 2)⟩ : ℂ)‖ = 1 := by
  let z : ℂ := ⟨-a, Real.sqrt (1 - a ^ 2)⟩
  have hz_sq : Complex.normSq z = 1 :=
    quadratic_leeyang_root_normSq_eq_one a ha
  rw [Complex.normSq_eq_norm_sq] at hz_sq
  nlinarith [norm_nonneg z]

/-- Test: verify the existing native theorem connects correctly -/
theorem test_existing_native_connection (a : ℝ) (ha : a ^ 2 ≤ 1) (z : ℂ)
    (h_root : z ^ 2 + 2 * (a : ℂ) * z + 1 = 0)
    (h_re : z.re = -a) :
    ‖z‖ = 1 := by
  have hz_circle :=
    quadratic_partition_polynomial_root_on_circle a ha z h_root h_re
  change Complex.normSq z = 1 at hz_circle
  rw [Complex.normSq_eq_norm_sq] at hz_circle
  nlinarith [norm_nonneg z]

end InfoGeometry.Canonical.LeeYangCapstoneTest
