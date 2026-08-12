import InfoGeometry.Algebra.FiniteSingleModeCAR
import InfoGeometry.Canonical.CantorCuntzCliffordBridge
import InfoGeometry.Algebra.CuntzFockRepresentation
import InfoGeometry.Canonical.Cuntz2Isometries
import InfoGeometry.Algebra.CuntzTensorQuotient
import InfoGeometry.OperatorAlgebra.QCCRResidual
import InfoGeometry.Canonical.FiniteSingleModeCARMatrixBridge

/-!
# CAR / q‑CCR / Cuntz / Fock bridge

This owner bridges the one-mode CAR relations to the non-commutative `q`‑CCR
polynomial identity

`qCcrRelation c c⋆ q := c * c⋆ - q * c⋆ * c - 1`.

No diagonal surrogates are used: only genuine algebraic relations are
transported.
-/

noncomputable section

namespace InfoGeometry.Algebra.CARFockBridge

open InfoGeometry.OperatorAlgebra.QCCRResidual
open InfoGeometry.Canonical
open InfoGeometry.Canonical.FiniteSingleModeCARMatrixBridge
open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzFockRepresentation

/-! ### One-mode CAR as the q=-1 specialization -/

/-- Finite one-mode CAR matrix pair satisfies the q-CCR residual at q = -1. -/
theorem one_mode_car_qccr_minus_one :
    qCcrRelation annMatrix2 creMatrix2 (-1) = 0 := by
  exact (qccr_fermionic_limit annMatrix2 creMatrix2).2 annMatrix2_CAR

/-- Equivalent finite CAR anticommutator statement in matrix form. -/
theorem one_mode_car_anticommutator :
    annMatrix2 * creMatrix2 + creMatrix2 * annMatrix2 = 1 :=
  annMatrix2_CAR

/-! ### Cuntz -> CAR, via `a = S_left * S_right⋆` -/

/-- A Cuntz-derived CAR generator satisfies `{a, a⋆} = 1`, hence q = -1 q-CCR. -/
theorem cuntz_derived_car_qccr_minus_one
    {Op : Type*} [Ring Op] [StarRing Op] (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    qCcrRelation (carFromCuntz C) (star (carFromCuntz C)) (-1) = 0 := by
  exact (qccr_fermionic_limit (carFromCuntz C) (star (carFromCuntz C))).2
    (by simpa [cantorAnticommutator] using
      carFromCuntz_anticommutator_star_eq_one C)

/-! ### q = 0 Cuntz boundary in generators -/

/-- Cuntz isometries realize the q = 0 boundary `a⋆ a = 1`. -/
theorem cuntz_generator_qccr_zero {R : Type*} [Ring R] [StarRing R]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) R) :
    qCcrRelation (star (_root_.CuntzAlgebra.S1 C))
      (_root_.CuntzAlgebra.S1 C) 0 = 0 := by
  rw [qccr_to_cuntz_limit]
  exact _root_.CuntzAlgebra.h_isometry1 C

/-- The same zero‑q relation on left multiplication in the (finite) Cuntz algebra. -/
theorem fock_left_regular_cuntz_qccr_zero
    (n : ℕ) (i : Fin n) (x : CuntzAlg n) :
    qCcrRelation
        (leftMultiplication n (cuntzSdag n i))
        (leftMultiplication n (cuntzS n i)) 0 x = 0 := by
  simpa [qCcrRelation] using
    leftMultiplication_cuntz_qccr_zero n i x

/-! ### Operator-level q = 0 left-regular residue vanishes (pointwise-extensionality). -/

theorem fock_left_regular_cuntz_qccr_zero_operator
    (n : ℕ) (i : Fin n) :
    qCcrRelation
        (leftMultiplication n (cuntzSdag n i))
        (leftMultiplication n (cuntzS n i)) 0 = 0 := by
  ext x
  simpa using fock_left_regular_cuntz_qccr_zero n i x

end InfoGeometry.Algebra.CARFockBridge
