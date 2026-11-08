/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

open Complex

set_option maxHeartbeats 400000

/-! A finite owner for the exponential remainder and its scalar divergence
    interpretation.  Operator-level modular claims are intentionally kept out
    of this scalar carrier. -/

noncomputable def masterOp (K : ℂ) : ℂ := exp K - 1 - K

noncomputable def masterOpReal (K : ℝ) : ℝ := Real.exp K - 1 - K

theorem masterOp_shift (K c : ℂ) :
    masterOp (K + c) = exp c * exp K - 1 - K - c := by
  dsimp [masterOp]
  rw [Complex.exp_add]
  ring

noncomputable def itakuraSaito (x y : ℝ) : ℝ :=
  x / y - Real.log (x / y) - 1

theorem masterOp_is_IS (K : ℝ) :
    masterOpReal K = itakuraSaito (Real.exp K) 1 := by
  dsimp [masterOpReal, itakuraSaito]
  simp
  ring

noncomputable def arakiUmegamiGen
    (traceOmega traceEta arakiEntropy : ℝ) : ℝ :=
  traceEta - traceOmega + arakiEntropy

theorem arakiUmegamiGen_unnormalized_correction
    (traceOmega traceEta arakiEntropy : ℝ) :
    arakiUmegamiGen traceOmega traceEta arakiEntropy =
      traceEta - traceOmega + arakiEntropy := by
  rfl

abbrev ConnesFlow := ℂ

namespace ConnesFlow

abbrev K (F : ConnesFlow) : ℂ := F

noncomputable def cocycle (F : ConnesFlow) (t : ℝ) : ℂ :=
  exp (Complex.I * t • F.K)

noncomputable def cost (F : ConnesFlow) : ℂ := masterOp F.K

theorem cocycle_zero (F : ConnesFlow) : F.cocycle 0 = 1 := by
  simp [cocycle]

end ConnesFlow

theorem masterOp_derivative (K : ℂ) :
    masterOp (K + 1) - masterOp K = exp K * (exp 1 - 1) - 1 := by
  dsimp [masterOp]
  rw [Complex.exp_add]
  ring

theorem masterOp_nonneg (K : ℝ) : 0 ≤ masterOpReal K := by
  unfold masterOpReal
  linarith [Real.add_one_le_exp K]
