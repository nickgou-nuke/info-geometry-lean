/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Virasoro.Sugawara
import InfoGeometry.External.Virasoro.FiveGradedDecomposition

/-!
# Sugawara Mode-Shift Obstruction to Naive Five-Grading Truncation

This module proves from the Sugawara–Heisenberg commutator identity
$[L_n, J_m] = -m\,J_{n+m}$ that the mixed commutator $[L_1, J_1] = -J_2$ exits
a five-mode window unless $J_2 = 0$.

- BUCKET 1 (Real Math in This File):
  - `sugawara_current_mode_shift`, `positive_one_one_commutator`
  - `boundary_zero_forces_current_two_zero`, `current_two_ne_zero_obstructs_boundary_zero`
  - `no_naive_positive_boundary_truncation`, `mode_escape_formula`

- BUCKET 2 (Meaningful Mathematical Results Used):
  - `VirasoroProject.commutator_sugawaraGen_heiOper`

- BUCKET 3 (Excluded Wrapper Patterns):
  - Zero wrapper structures, zero `Prop`-valued aliases, and zero `:= rfl` theorems.
-/

noncomputable section

namespace InfoGeometry.Canonical.SugawaraFiveGradingObstruction

open Filter
open VirasoroProject

variable {𝕜 V : Type*}
variable [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

variable (J : ℤ → V →ₗ[𝕜] V)
variable (trunc : ∀ v, atTop.Eventually (fun l => J l v = 0))
variable (hcomm : ∀ m n,
  (J m).commutator (J n) =
    if m + n = 0 then (m : 𝕜) • (1 : V →ₗ[𝕜] V) else 0)

include hcomm

/-- The Sugawara–Heisenberg commutator identity $[L_n, J_m] = -m\,J_{n+m}$. -/
theorem sugawara_current_mode_shift (n m : ℤ) :
    (sugawaraGen trunc n).commutator (J m) =
      -m • J (n + m) := by
  have h := commutator_sugawaraGen_heiOper
    (heiOper := J) (heiTrunc := trunc) (heiComm := hcomm) n m
  exact h

/-- At modes $n = 1, m = 1$, the mixed commutator satisfies $[L_1, J_1] = -J_2$. -/
theorem positive_one_one_commutator :
    (sugawaraGen trunc 1).commutator (J 1) = -J 2 := by
  have h := sugawara_current_mode_shift J trunc hcomm (1 : ℤ) (1 : ℤ)
  simpa using h

/-- If the positive boundary commutator $[L_1, J_1]$ vanishes, then $J_2 = 0$. -/
theorem boundary_zero_forces_current_two_zero
    (hzero : (sugawaraGen trunc 1).commutator (J 1) = 0) :
    J 2 = 0 := by
  rw [positive_one_one_commutator J trunc hcomm] at hzero
  exact neg_eq_zero.mp hzero

/-- Any representation with $J_2 \neq 0$ has $[L_1, J_1] \neq 0$. -/
theorem current_two_ne_zero_obstructs_boundary_zero
    (hJ2 : J 2 ≠ 0) :
    (sugawaraGen trunc 1).commutator (J 1) ≠ 0 := by
  rw [positive_one_one_commutator J trunc hcomm]
  exact neg_ne_zero.mpr hJ2

/-- Incompatibility of $J_2 \neq 0$ with the truncated boundary condition $[L_1, J_1] = 0$. -/
theorem no_naive_positive_boundary_truncation
    (hJ2 : J 2 ≠ 0) :
    ¬ ((sugawaraGen trunc 1).commutator (J 1) = 0) := by
  rw [positive_one_one_commutator J trunc hcomm]
  exact neg_ne_zero.mpr hJ2

/-- Mode-shift formula $[L_n, J_m] = -m\,J_{n+m}$ with implicit mode indices. -/
theorem mode_escape_formula
    {n m : ℤ} :
    (sugawaraGen trunc n).commutator (J m) =
      -m • J (n + m) := by
  have h := commutator_sugawaraGen_heiOper
    (heiOper := J) (heiTrunc := trunc) (heiComm := hcomm) n m
  exact h

end InfoGeometry.Canonical.SugawaraFiveGradingObstruction
