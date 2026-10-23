/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ObliqueShellCounterexample
import InfoGeometry.Singular.MoorePenroseSectorExamples

/-!
# Consequences of the native oblique shell and skew-chain witnesses

All matrices and shell definitions
are imported from native owners. The actual zeroth Drazin shell is not
selfadjoint and annihilates its operator only on the right. Separately, the two
Moore–Penrose support projections of the native skew chain do not commute;
this is a statement about products of supports, not just unequal supports.
No general shell selfadjointness or two-sided extinction claim is made.
-/

namespace InfoGeometry.Canonical.DrazinShellConsequenceExamples

open Matrix
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Canonical.DrazinNilpotentShell
open InfoGeometry.Canonical.ObliqueShellCounterexample
open InfoGeometry.Singular.MoorePenroseSectorExamples

/-- The native zeroth shell is oblique for the standard matrix star. -/
theorem oblique_shell_zero_not_selfadjoint :
    ¬ IsSelfAdjoint (drazinShellProj obliqueA obliqueD obliquePowers 0) := by
  intro h
  change (drazinShellProj obliqueA obliqueD obliquePowers 0).conjTranspose =
    drazinShellProj obliqueA obliqueD obliquePowers 0 at h
  rw [oblique_shell_zero] at h
  have he := congrArg (fun C : Matrix (Fin 3) (Fin 3) ℝ => C 0 2) h
  norm_num [Matrix.conjTranspose_apply] at he

/-- Multiplication by the operator on the right kills the zeroth shell. -/
theorem oblique_shell_zero_mul_operator :
    drazinShellProj obliqueA obliqueD obliquePowers 0 * obliqueA = 0 := by
  exact drazinShellProj_zero_mul_eq_zero oblique_drazin oblique_mp_family

/-- The reverse product has a nonzero entry in the native coordinate basis. -/
theorem operator_mul_oblique_shell_zero_entry :
    (obliqueA * drazinShellProj obliqueA obliqueD obliquePowers 0) 0 2 = -1 := by
  rw [oblique_shell_zero]
  norm_num [obliqueA, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The same shell does not satisfy extinction with the operator on the left. -/
theorem operator_mul_oblique_shell_zero_ne_zero :
    obliqueA * drazinShellProj obliqueA obliqueD obliquePowers 0 ≠ 0 := by
  intro h
  have he := congrArg (fun C : Matrix (Fin 3) (Fin 3) ℝ => C 0 2) h
  rw [operator_mul_oblique_shell_zero_entry] at he
  norm_num at he

/-- The ordered product of the range and source supports has entry zero. -/
theorem skewChain_support_product_entry :
    ((skewChain * skewChainMP) * (skewChainMP * skewChain)) 1 3 = 0 := by
  norm_num [skewChain, skewChainMP, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Reversing the supports changes the same entry to one half. -/
theorem skewChain_reverse_support_product_entry :
    ((skewChainMP * skewChain) * (skewChain * skewChainMP)) 1 3 = 1 / 2 := by
  norm_num [skewChain, skewChainMP, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Support commutation fails, beyond the owner's operator/inverse inequality. -/
theorem skewChain_supports_not_commute :
    ¬ Commute (skewChain * skewChainMP) (skewChainMP * skewChain) := by
  intro h
  have he := congrArg (fun C : Matrix (Fin 4) (Fin 4) ℝ => C 1 3) h.eq
  rw [skewChain_support_product_entry, skewChain_reverse_support_product_entry] at he
  norm_num at he

end InfoGeometry.Canonical.DrazinShellConsequenceExamples
