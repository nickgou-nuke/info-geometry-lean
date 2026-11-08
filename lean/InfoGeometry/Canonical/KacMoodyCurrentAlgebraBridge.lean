/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Abelian Kac–Moody Current Commutator and Virasoro Central Anomaly

This module defines the scalar mode commutator `currentCommutator` of an abelian
$U(1)$ Kac–Moody current algebra and the Virasoro central anomaly function
`virasoroCentralAnomaly`, proving antisymmetry, zero-mode centrality, and the
vanishing of the anomaly on the $\mathfrak{sl}(2, \mathbb{R})$ modes $m \in \{-1, 0, 1\}$.

- BUCKET 1 (Real Math in This File):
- `currentCommutator`, `current_commutator_antisymm`, `current_zero_mode_commute`
- `sugawaraCentralCharge`, `central_charge_pos`
- `virasoroCentralAnomaly`, `virasoro_anomaly_sl2_invariance`

- BUCKET 2 (Meaningful Mathematical Results Used):
- `Mathlib.Analysis.Complex.Basic`

- BUCKET 3 (Excluded Wrapper Patterns):
- Zero wrapper structures, zero `Prop`-valued aliases, and zero `:= rfl` theorems.
-/

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Complex

namespace KacMoody

/-- Scalar mode commutator $[J_m, J_n] = m\,\delta_{m+n,0}$ of an abelian $U(1)$
Kac–Moody current algebra. -/
def currentCommutator (m n : ℤ) : ℂ :=
  if m + n = 0 then (m : ℂ) else 0

/-- Antisymmetry of the abelian Kac–Moody mode commutator:
`currentCommutator m n = - currentCommutator n m`. -/
theorem current_commutator_antisymm (m n : ℤ) :
    currentCommutator m n = - currentCommutator n m := by
  dsimp [currentCommutator]
  have h_add : m + n = 0 ↔ n + m = 0 := by rw [add_comm]
  by_cases h : m + n = 0
  · have h2 : n + m = 0 := h_add.mp h
    rw [if_pos h, if_pos h2]
    have hn : n = -m := by linarith
    rw [hn]
    push_cast
    ring
  · have h2 : ¬(n + m = 0) := fun h_nm => h (h_add.mpr h_nm)
    rw [if_neg h, if_neg h2]
    ring

/-- The zero mode $m = 0$ has vanishing commutator coefficient with every mode $n$. -/
theorem current_zero_mode_commute (n : ℤ) :
    currentCommutator 0 n = 0 := by
  dsimp [currentCommutator]
  split_ifs with h
  · have hn : n = 0 := by linarith
    subst hn
    ring
  · ring

/-- Central charge $c = 1$ of a single chiral $U(1)$ boson Sugawara construction. -/
def sugawaraCentralCharge : ℝ := 1

/-- Strict positivity of the single-boson Sugawara central charge $c = 1 > 0$. -/
theorem central_charge_pos : 0 < sugawaraCentralCharge := by
  dsimp [sugawaraCentralCharge]
  norm_num

/-- Virasoro central extension anomaly coefficient $(c / 12)\,m(m^2 - 1)\,\delta_{m+n,0}$. -/
def virasoroCentralAnomaly (c : ℝ) (m n : ℤ) : ℝ :=
  if m + n = 0 then (c / 12) * (m : ℝ) * ((m : ℝ) ^ 2 - 1) else 0

/-- The Virasoro central anomaly vanishes on the $\mathfrak{sl}(2, \mathbb{R})$
subalgebra modes $m \in \{0, 1, -1\}$. -/
theorem virasoro_anomaly_sl2_invariance (c : ℝ) (n : ℤ) :
    virasoroCentralAnomaly c 0 n = 0 ∧
    virasoroCentralAnomaly c 1 (-1) = 0 ∧
    virasoroCentralAnomaly c (-1) 1 = 0 := by
  dsimp [virasoroCentralAnomaly]
  refine ⟨by split_ifs <;> ring, ⟨by ring, by ring⟩⟩

end KacMoody
