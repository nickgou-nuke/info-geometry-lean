import InfoGeometry.OperatorAlgebra.ChiralRetainedWordFiveGradeClosure
import InfoGeometry.OperatorAlgebra.OperatorExteriorAlgebra
import InfoGeometry.Algebra.NonAssocDerivation

/-!
# Derivations preserving noncommutative adjoint weights

This is the operator-algebra seam used by the braid, current and Virasoro
lanes.  It is deliberately stated for an associative operator algebra `A`;
the carrier may have originated from a nonassociative algebra, but no
commutative or diagonal model is introduced here.
-/

namespace InfoGeometry.OperatorAlgebra

open InfoGeometry.OperatorAlgebra.ExteriorAlgebra

variable {A : Type*}
variable [Ring A] [Algebra ℝ A]

theorem derivation_preserves_inner_weight
    (D : Module.End ℝ A)
    (hD : InfoGeometry.Algebra.NonAssocDerivation.IsLeibniz ℝ A D)
    (N X : A) (k : ℝ)
    (hN : D N = 0)
    (hX : N * X - X * N = k • X) :
    N * D X - D X * N = k • D X := by
  have h := congrArg D hX
  rw [map_sub, hD, hD] at h
  rw [hN, zero_mul, mul_zero] at h
  simp only [zero_add, add_zero] at h
  rw [map_smul] at h
  exact h

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
