/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Algebra.DihedralArtinI2SixSpinLift

namespace InfoGeometry.Algebra.DihedralArtin

/-- A spin lift element $c$ satisfying $c^6 = \epsilon$ with $\epsilon^2 = 1$ and $\epsilon \ne 1$
    has exact period 12 ($c^{12} = 1$) and $c^6 \ne 1$. -/
theorem spin_coxeter_twelfth_and_nontrivial_sixth
    {G : Type*} [Group G] (c eps : G) (hc6 : c ^ 6 = eps) (heps2 : eps ^ 2 = 1) (heps_ne : eps ≠ 1) :
    c ^ 12 = 1 ∧ c ^ 6 ≠ 1 := by
  have h12 : c ^ 12 = (c ^ 6) ^ 2 := by
    have h_mul : (6 : ℕ) * 2 = 12 := rfl
    rw [← pow_mul, h_mul]
  refine ⟨?_, ?_⟩
  · rw [h12, hc6, heps2]
  · rw [hc6]
    exact heps_ne

/-- Lower-order divisor test for 12th-periodic element:
    excluding order 4 and having $c^6 = \epsilon \ne 1$. -/
theorem spin_coxeter_twelfth_lower_order_obstructions
    {G : Type*} [Group G] (c eps : G) (hc6 : c ^ 6 = eps) (heps2 : eps ^ 2 = 1) (heps_ne : eps ≠ 1)
    (h4 : c ^ 4 ≠ 1) :
    c ^ 12 = 1 ∧ c ^ 4 ≠ 1 ∧ c ^ 6 ≠ 1 := by
  rcases spin_coxeter_twelfth_and_nontrivial_sixth c eps hc6 heps2 heps_ne with ⟨h12, h6⟩
  exact ⟨h12, h4, h6⟩

/-- Exact order 12 in a finite group or representation where all strictly smaller positive powers are nontrivial. -/
theorem spin_coxeter_orderOf_eq_twelve
    {G : Type*} [Group G] (c : G) (h12 : c ^ 12 = 1)
    (hsmall : ∀ m : ℕ, m < 12 → 0 < m → c ^ m ≠ 1) :
    orderOf c = 12 := by
  apply (orderOf_eq_iff (x := c) (by norm_num)).2
  exact ⟨h12, hsmall⟩

end InfoGeometry.Algebra.DihedralArtin
