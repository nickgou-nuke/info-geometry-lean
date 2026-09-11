import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Singular.Drazin
import InfoGeometry.Canonical.TrifactorDecomposition

/-!
# Drazin Tripotent / Trifactor Bridge

This module closes the finite algebraic part of the Drazin/trifactor
dictionary:

* a tripotent `T`, with `T ^ 3 = T`, is its own Drazin inverse at index `1`;
* the Drazin regular/support projector is `T ^ 2`;
* this support is exactly `P_plus T + P_minus T`;
* the complementary Drazin null projector is `P_zero T`.

#### BUCKET 1: CLOSED FINITE THEOREMS
All theorem statements below are polynomial identities in a commutative ring
with `2` invertible.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The Drazin inverse and projector claims depend only on the explicit tripotent
hypothesis `hT : T ^ 3 = T`.

#### BUCKET 3: OPEN CLOSURE DEBT
No theorem here asserts a KMS state, a critical-line theorem, Riemann-zero
localization, Cuntz/UHF completion, infinite Fock-space Witten index, or
Spector-style physical supersymmetry theorem.
-/

namespace InfoGeometry.Canonical.DrazinTripotentTrifactorBridge

open InfoGeometry.Singular.Drazin
open TrifactorDecomposition
open TriFacetGeometry

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Candidate Drazin inverse for a tripotent: the element itself. -/
def tripotentDrazinInverse (T : R) : R := T

/-- Drazin support/regular projector for a tripotent. -/
def tripotentDrazinProjector (T : R) : R := T * tripotentDrazinInverse T

/-- Complementary Drazin null projector for a tripotent. -/
def tripotentDrazinNullProjector (T : R) : R :=
  1 - tripotentDrazinProjector T

omit [Invertible (2 : R)] in
/-- A tripotent element is its own Drazin inverse at index `1`. -/
theorem tripotent_is_own_drazin_inverse
    (T : R) (hT : T ^ 3 = T) :
    IsDrazinInverse T (tripotentDrazinInverse T) 1 := by
  refine IsDrazinInverse.mk ?_ ?_ ?_
  · unfold tripotentDrazinInverse
    simpa [pow_succ] using hT
  · rfl
  · unfold tripotentDrazinInverse
    simpa [pow_succ, pow_two] using hT.symm

omit [Invertible (2 : R)] in
/-- The Drazin support projector of a tripotent is `T ^ 2`. -/
theorem tripotent_drazin_projector_eq_square (T : R) :
    tripotentDrazinProjector T = T ^ 2 := by
  unfold tripotentDrazinProjector tripotentDrazinInverse
  ring

omit [Invertible (2 : R)] in
/-- The tripotent Drazin support is idempotent. -/
theorem tripotent_drazin_projector_idempotent
    (T : R) (hT : T ^ 3 = T) :
    tripotentDrazinProjector T * tripotentDrazinProjector T =
      tripotentDrazinProjector T := by
  rw [tripotent_drazin_projector_eq_square]
  calc
    T ^ 2 * T ^ 2 = T ^ 4 := by ring
    _ = T ^ 2 := TriFacetGeometry.T_pow4 T hT

/-- The Drazin support projector is exactly the active `P_plus + P_minus` sector. -/
theorem tripotent_drazin_projector_eq_active_trifactor
    (T : R) :
    tripotentDrazinProjector T = P_plus T + P_minus T := by
  rw [tripotent_drazin_projector_eq_square]
  unfold P_plus P_minus P_hyp P_ell
  calc
    T ^ 2 =
        (⅟(2 : R) * (2 : R)) * T ^ 2 := by
          rw [invOf_mul_self (2 : R)]
          ring
    _ = ⅟(2 : R) * (T ^ 2 + T) + ⅟(2 : R) * (T ^ 2 - T) := by
          ring

omit [Invertible (2 : R)] in
/-- The complementary Drazin null projector is exactly the `P_zero` sector. -/
theorem tripotent_drazin_null_projector_eq_P_zero
    (T : R) :
    tripotentDrazinNullProjector T = P_zero T := by
  unfold tripotentDrazinNullProjector P_zero
  rw [tripotent_drazin_projector_eq_square]
  rfl

omit [Invertible (2 : R)] in
/-- The tripotent annihilates its Drazin null projector. -/
theorem tripotent_annihilates_drazin_null_projector
    (T : R) (hT : T ^ 3 = T) :
    T * tripotentDrazinNullProjector T = 0 := by
  unfold tripotentDrazinNullProjector tripotentDrazinProjector tripotentDrazinInverse
  calc
    T * (1 - T * T) = T - T ^ 3 := by ring
    _ = T - T := by rw [hT]
    _ = 0 := by ring

/--
Bundled finite Drazin/trifactor dictionary.

This is the closed algebraic theorem: `T^D = T`, `P_D = T^2 = P_plus + P_minus`,
and `1 - P_D = P_zero`.
-/
theorem drazin_tripotent_trifactor_capstone
    (T : R) (hT : T ^ 3 = T) :
    IsDrazinInverse T (tripotentDrazinInverse T) 1 ∧
      tripotentDrazinProjector T = T ^ 2 ∧
      tripotentDrazinProjector T = P_plus T + P_minus T ∧
      tripotentDrazinNullProjector T = P_zero T ∧
      T * tripotentDrazinNullProjector T = 0 := by
  exact ⟨
    tripotent_is_own_drazin_inverse T hT,
    tripotent_drazin_projector_eq_square T,
    tripotent_drazin_projector_eq_active_trifactor T,
    tripotent_drazin_null_projector_eq_P_zero T,
    tripotent_annihilates_drazin_null_projector T hT⟩

end InfoGeometry.Canonical.DrazinTripotentTrifactorBridge
