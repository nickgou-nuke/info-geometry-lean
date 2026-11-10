/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.ChiralRetainedWordFiveGradeClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.OperatorExteriorAlgebra
import InfoGeometry.Algebra.NonAssocDerivation

/-!
# Derivations preserving noncommutative adjoint weights

This is the operator-algebra seam used by the braid, current and Virasoro
lanes.  It is deliberately stated for an associative operator algebra `A`
over a (possibly noncommutative) ring `R`; the carrier may have originated
from a nonassociative algebra, but no commutative or diagonal model is
introduced here.
-/

namespace InfoGeometry.OperatorAlgebra

open InfoGeometry.OperatorAlgebra.ExteriorAlgebra

variable {R A : Type*}

theorem derivation_preserves_inner_weight
    [Ring R] [Ring A] [Module R A]
    (D : Module.End R A)
    (hD : InfoGeometry.Algebra.NonAssocDerivation.IsLeibniz R A D)
    (N X : A) (k : R)
    (hN : D N = 0)
    (hX : N * X - X * N = k • X) :
    N * D X - D X * N = k • D X := by
  have h := congrArg D hX
  rw [map_sub, hD, hD] at h
  rw [hN, zero_mul, mul_zero] at h
  simp only [zero_add, add_zero] at h
  rw [map_smul] at h
  exact h

variable [Ring A] [Algebra ℝ A]

theorem derivation_preserves_gradeSubmodule
    (D : Module.End ℝ A)
    (hD : InfoGeometry.Algebra.NonAssocDerivation.IsLeibniz ℝ A D)
    (N : A) (k : ℤ)
    (hN : D N = 0) :
    Set.MapsTo (D : A → A)
      (gradeSubmodule N k : Set A) (gradeSubmodule N k : Set A) := by
  intro X hX
  change HasOperatorGrade N X k at hX
  change HasOperatorGrade N (D X) k
  unfold HasOperatorGrade at hX ⊢
  exact derivation_preserves_inner_weight D hD N X (k : ℝ) hN hX

end InfoGeometry.OperatorAlgebra
