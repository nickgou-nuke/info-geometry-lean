/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MajoranaPfaffianKernelCriterion
import InfoGeometry.Canonical.KreinMajoranaKernelCriterion

/-! Axiom audit and compatibility with the native finite-chain CAR predicate. -/
open InfoGeometry.Canonical

#print axioms MajoranaCoefficientAction.linearCombination_injective
#print axioms MajoranaCoefficientAction.quadraticElement_commutator_linearCombination
#print axioms MajoranaPfaffianKernelCriterion.pfaffian_zero_iff_nonzero_kernel
#print axioms MajoranaPfaffianKernelCriterion.pfaffian_zero_iff_conserved_majorana
#print axioms KreinMajoranaKernelCriterion.polarized_nonzero_kernel_iff_pfaffian_zero

example {A : Type*} [Ring A] [Algebra ℝ A] [Nontrivial A]
    {N : ℕ} {gamma : Fin (2 * N) → A}
    (h : KitaevChainMajoranaZeroModes.IsMajoranaBasis N gamma) :
    Function.Injective (Fintype.linearCombination ℝ gamma) :=
  MajoranaCoefficientAction.linearCombination_injective h
