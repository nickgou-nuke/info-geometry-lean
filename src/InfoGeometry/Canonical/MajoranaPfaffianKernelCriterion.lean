/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MajoranaCoefficientAction
import InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Pfaffian kernel criterion for the finite Majorana span

The supplied Pfaffian square law concerns the same skew coefficient matrix
that acts by commutator on the Majorana span. A conserved nonzero operator
in this span is not a state-space kernel vector of the quadratic operator.
-/
namespace InfoGeometry.Canonical.MajoranaPfaffianKernelCriterion

open ProjectivePfaffianDeterminantCounts MajoranaCoefficientAction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The square-law witness vanishes exactly when its coefficient matrix has
a nonzero kernel vector. No Pfaffian sign or phase claim is used. -/
theorem pfaffian_zero_iff_nonzero_kernel (P : PfaffianKernel ι) :
    P.pfaffian = 0 ↔ ∃ v : ι → ℝ, v ≠ 0 ∧ P.omega.mulVec v = 0 := by
  rw [Matrix.exists_mulVec_eq_zero_iff, ← P.pf_sq_eq_det]
  simp

/-- A zero Pfaffian is equivalent to a nonzero conserved Majorana linear
combination for the quadratic element built from that same skew matrix. -/
theorem pfaffian_zero_iff_conserved_majorana
    {A : Type*} [Ring A] [Algebra ℝ A] [Nontrivial A]
    {gamma : ι → A}
    (h : ∀ i j, gamma i * gamma j + gamma j * gamma i = if i = j then 2 else 0)
    (P : PfaffianKernel ι) :
    P.pfaffian = 0 ↔ ∃ v : ι → ℝ,
      Fintype.linearCombination ℝ gamma v ≠ 0 ∧
      quadraticElement gamma P.omega * Fintype.linearCombination ℝ gamma v -
        Fintype.linearCombination ℝ gamma v * quadraticElement gamma P.omega = 0 := by
  have hz (v : ι → ℝ) : Fintype.linearCombination ℝ gamma v = 0 ↔ v = 0 :=
    (linearCombination_injective h).eq_iff' (map_zero _)
  rw [pfaffian_zero_iff_nonzero_kernel]
  apply exists_congr
  intro v
  exact and_congr (not_congr (hz v)).symm
    (quadraticElement_commutator_eq_zero_iff h P.omega P.skew v).symm

end InfoGeometry.Canonical.MajoranaPfaffianKernelCriterion
