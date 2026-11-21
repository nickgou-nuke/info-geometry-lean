/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

noncomputable section

open Matrix Complex

/-!
This file contains finite complex-algebra identities used as interfaces. The
carriers do not encode a local QFT net, positivity of physical constants, or an
analytic KMS condition; the theorem names therefore describe only the proved
algebraic content.
-/

namespace BisognanoWichmannUnruh

/-- Physical Constants Structure for Unruh Thermalization. -/
structure PhysicalConstants where
  hbar : ℂ
  c : ℂ
  kB : ℂ

/-- Rindler Observer Acceleration Parameter. -/
structure RindlerObserver where
  acc : ℂ

namespace BisognanoWichmannUnruh

/-- Finite linear modular-parameter rescaling `s = -two_pi * t`. -/
def boostFromModular (two_pi t : ℂ) : ℂ :=
  - two_pi * t

/-- The finite modular-parameter rescaling is additive. -/
theorem modular_parameter_linear (two_pi t1 t2 : ℂ) :
    boostFromModular two_pi (t1 + t2) = boostFromModular two_pi t1 + boostFromModular two_pi t2 := by
  dsimp [boostFromModular]
  ring

/-- Reassociation of the finite proper-time scale expression. -/
theorem proper_time_scale_reassociation (two_pi c a : ℂ) :
    (two_pi * c) / a = two_pi * c / a := rfl

/-- Conditional finite thermal-scale cancellation. This is not an Unruh or
analytic KMS derivation: it is field cancellation under nonzero denominator
factors. -/
theorem thermal_scale_cancellation (consts : PhysicalConstants) (obs : RindlerObserver) (two_pi : ℂ)
    (h_two_pi : two_pi ≠ 0) (h_c : consts.c ≠ 0) (h_kB : consts.kB ≠ 0) :
    let T_unruh := (consts.hbar * obs.acc) / (two_pi * consts.c * consts.kB)
    T_unruh * (two_pi * consts.c * consts.kB) = consts.hbar * obs.acc := by
  intro T_unruh
  dsimp [T_unruh]
  field_simp

/-- Conjugation by an involutive finite complex matrix preserves trace. -/
theorem involutive_conjugation_trace_conservation {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]
    (J A : Matrix (Fin n) (Fin n) ℂ) (h_J_involutive : J * J = 1) :
    trace (J * A * J) = trace A := by
  rw [trace_mul_comm (J * A) J, ← mul_assoc, h_J_involutive, one_mul]

end BisognanoWichmannUnruh

end BisognanoWichmannUnruh
