/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import InfoGeometry.Quantum.ModularSurprisalDeficit

namespace InfoGeometry.Canonical.ModularMasterOperator

noncomputable def masterOperator (K : ℂ) : ℂ := Complex.exp K - 1 - K

noncomputable def masterOperatorReal (K : ℝ) : ℝ := Real.exp K - 1 - K

theorem masterOperator_shift (K c : ℂ) :
    masterOperator (K + c) = Complex.exp c * Complex.exp K - 1 - K - c := by
  simp only [masterOperator, Complex.exp_add]
  ring

theorem masterOperator_is_modular_deficit (K : ℝ) :
    masterOperatorReal K =
      InfoGeometry.Quantum.ModularSurprisalDeficit.modularDeficit (-K) := by
  simp [masterOperatorReal,
    InfoGeometry.Quantum.ModularSurprisalDeficit.modularDeficit]
  ring

theorem masterOperator_nonneg (K : ℝ) : 0 ≤ masterOperatorReal K := by
  rw [masterOperator_is_modular_deficit]
  exact InfoGeometry.Quantum.ModularSurprisalDeficit.modular_deficit_nonneg (-K)

theorem masterOperator_zero : masterOperatorReal 0 = 0 := by
  simp [masterOperatorReal]

end InfoGeometry.Canonical.ModularMasterOperator
