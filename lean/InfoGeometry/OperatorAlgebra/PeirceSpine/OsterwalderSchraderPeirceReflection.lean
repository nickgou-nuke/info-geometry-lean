/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic.Abel
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Star.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.StarGrading

open scoped ComplexOrder

/-!
# Algebraic Peirce reflection identities

For a self-adjoint idempotent, the grading-twisted star operation is an
involution and sends the forward Peirce corner to the negative adjoint corner.
The resulting Jordan pairing is the algebraic Gram expression. This file
does not assert positivity, reflection positivity, or a transfer-matrix gap.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B] [StarRing B]

/-- Grading-twisted star reflection `Θ_P(X) = S_P * X* * S_P`. -/
def osPeirceReflection (P X : B) : B := invS P * star X * invS P

/-- Jordan pairing between the two reflected Peirce corners. -/
def osPeirceMassPairing (P A : B) : B := genV P A (star A)

/-- Spin commutator associated with the forward corner and its adjoint. -/
def osPeirceSpinPairing (P A : B) : B := genSig P A (star A)

theorem osPeirceReflection_involutive {P : B} (hP : P * P = P)
    (hPs : star P = P) (X : B) :
    osPeirceReflection P (osPeirceReflection P X) = X := by
  exact grading_star_involutive hPs hP X

/-- Reflection of the upper Peirce corner is the negative adjoint lower
corner. The sign comes from the opposite grading weights of the two corners. -/
theorem osPeirceReflection_conePlus {P : B} (hP : P * P = P)
    (hPs : star P = P) (A : B) :
    osPeirceReflection P (conePlus P A) = -coneMinus P (star A) := by
  rw [osPeirceReflection, star_conePlus hPs]
  peirce_nf hP

/-- The negative anticommutator with the reflected upper corner is exactly
the algebraic Jordan mass pairing. This identity alone is not an order or
positivity statement. -/
theorem neg_osPeirce_anticomm_eq_mass {P : B} (hP : P * P = P)
    (hPs : star P = P) (A : B) :
    -(anticomm (osPeirceReflection P (conePlus P A)) (conePlus P A)) =
      osPeirceMassPairing P A := by
  rw [osPeirceReflection_conePlus hP hPs A]
  simp only [osPeirceMassPairing, genV, anticomm, neg_mul, mul_neg]
  abel

/-- In an ordered star-ring, the Peirce mass pairing is positive: it is the
sum of `C * star C` and `star C * C` for `C = conePlus P A`. -/
theorem osPeirceMassPairing_nonneg [PartialOrder B] [StarOrderedRing B]
    {P : B} (hPs : star P = P) (A : B) :
    0 ≤ osPeirceMassPairing P A := by
  change 0 ≤ genV P A (star A)
  rw [genV, anticomm, ← star_conePlus hPs A]
  exact add_nonneg (mul_star_self_nonneg (conePlus P A))
    (star_mul_self_nonneg (conePlus P A))

/-- The reflected Jordan pairing is nonnegative in an ordered star-ring.
This is the order-valued conclusion; the unqualified ring identities above
remain purely algebraic. -/
theorem osPeirce_reflection_form_nonneg [PartialOrder B] [StarOrderedRing B]
    {P : B} (hP : P * P = P) (hPs : star P = P) (A : B) :
    0 ≤ -(anticomm (osPeirceReflection P (conePlus P A)) (conePlus P A)) := by
  rw [neg_osPeirce_anticomm_eq_mass hP hPs A]
  exact osPeirceMassPairing_nonneg hPs A

/-- The commutator pairing of the reflected upper corner is the intrinsic
spin commutator of the two Peirce corners. -/
theorem osPeirce_comm_eq_spin {P : B} (hP : P * P = P)
    (hPs : star P = P) (A : B) :
    comm (osPeirceReflection P (conePlus P A)) (conePlus P A) =
      osPeirceSpinPairing P A := by
  rw [osPeirceReflection_conePlus hP hPs A]
  simp only [osPeirceSpinPairing, genSig, comm, neg_mul, mul_neg]
  abel

end InfoGeometry.OperatorAlgebra.PeirceSpine

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

open scoped ComplexOrder

/-- Every positive complex-linear functional has nonnegative real part on
the reflected Peirce pairing. This is a scalar positivity consequence, not a
claim of the full Osterwalder--Schrader axiom system. -/
theorem osPeirce_reflection_state_nonneg (φ : B →ₚ[ℂ] ℂ) {P : B}
    (hP : P * P = P) (hPs : star P = P) (A : B) :
    0 ≤ (φ (-(anticomm (osPeirceReflection P (conePlus P A))
      (conePlus P A)))).re := by
  rw [neg_osPeirce_anticomm_eq_mass hP hPs A]
  exact (Complex.nonneg_iff.mp
    (PositiveLinearMap.map_nonneg φ (osPeirceMassPairing_nonneg hPs A))).1

end InfoGeometry.OperatorAlgebra.PeirceSpine
