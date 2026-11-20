/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

/-!
# What the adjoint curvature action detects

For the existing derivation-based connection, vanishing of the commutator
defect on every coefficient is equivalent to centrality of the curvature
value. Nonzero curvature alone does not supply a coefficient detecting it.
No idempotent projector is identified with a square-zero differential.
-/

namespace InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

open InfoGeometry.Algebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable (K : DerivationLieLane R A)

/-- Exact pointwise vanishing criterion for the covariant commutator defect. -/
theorem covariant_commutator_zero_iff_commute
    (Γ : OneForm K) (x y : K.L) (a : A) :
    covariantDerivative K Γ x (covariantDerivative K Γ y a) -
        covariantDerivative K Γ y (covariantDerivative K Γ x a) -
          covariantDerivative K Γ ⁅x, y⁆ a = 0 ↔
      Commute (connectionCurvature K Γ x y) a := by
  rw [covariantDerivative_commutator]
  exact sub_eq_zero

/-- Vanishing on all coefficients detects the center, without asserting
that the curvature itself vanishes. -/
theorem covariant_commutator_zero_iff_central
    (Γ : OneForm K) (x y : K.L) :
    (∀ a : A,
      covariantDerivative K Γ x (covariantDerivative K Γ y a) -
        covariantDerivative K Γ y (covariantDerivative K Γ x a) -
          covariantDerivative K Γ ⁅x, y⁆ a = 0) ↔
      ∀ a : A, Commute (connectionCurvature K Γ x y) a := by
  exact forall_congr' (covariant_commutator_zero_iff_commute K Γ x y)

/-- A noncommuting coefficient is exactly the witness needed for nonzero
curvature action. -/
theorem covariant_commutator_ne_zero_iff_not_commute
    (Γ : OneForm K) (x y : K.L) (a : A) :
    covariantDerivative K Γ x (covariantDerivative K Γ y a) -
        covariantDerivative K Γ y (covariantDerivative K Γ x a) -
          covariantDerivative K Γ ⁅x, y⁆ a ≠ 0 ↔
      ¬ Commute (connectionCurvature K Γ x y) a :=
  not_congr (covariant_commutator_zero_iff_commute K Γ x y a)

end InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
