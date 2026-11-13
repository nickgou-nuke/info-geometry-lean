/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Modular.GKSLDissipatorAlgebraic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarRingHom

/-!
# Algebraic star-product defects of the existing GKSL operators

The existing single-channel and finite-family dissipators have a polarized
star-product defect equal to a sum of ordered commutator products. A
skew-adjoint inner derivation contributes zero to this defect. The proof is
valid in any associative star ring with a central self-adjoint half; native
invertibility of two supplies that half without a norm or a topology.

Nonnegativity is a separate consequence under `StarOrderedRing`. These
identities and their naturality under star-preserving maps do not construct a
completely positive semigroup, eliminate recurrence, or identify a modular
Hamiltonian.
-/

set_option autoImplicit false

namespace InfoGeometry.Modular.GKSL

open scoped BigOperators

attribute [local instance 100] LieRing.ofAssociativeRing

section Ring

variable {A : Type*} [Ring A] [StarRing A]

/-- The polarized star-product defect of one jump channel is its ordered
commutator Gram product. The dissipator is the existing owner definition. -/
theorem dissipatorTerm_star_mul_defect
    (half : A) (h_half : (2 : A) * half = 1)
    (h_half_comm : ∀ z : A, half * z = z * half)
    (h_half_star : star half = half) (L X Y : A) :
    dissipatorTerm half L (star X * Y) -
        star (dissipatorTerm half L X) * Y -
        star X * dissipatorTerm half L Y = star ⁅L, X⁆ * ⁅L, Y⁆ := by
  rw [dissipatorTerm_star half h_half_comm h_half_star]
  dsimp only [dissipatorTerm]
  rw [mul_sub (star X)]
  have htransport (Z : A) : star X * (half * Z) = half * (star X * Z) := by
    rw [← mul_assoc, ← h_half_comm (star X), mul_assoc]
  rw [htransport]
  have htwo : half + half = 1 := by
    simpa only [two_mul] using h_half
  calc
    _ = star L * star X * Y * L - star L * star X * L * Y -
        star X * star L * Y * L +
        (half + half) * (star X * star L * L * Y) := by noncomm_ring
    _ = star ⁅L, X⁆ * ⁅L, Y⁆ := by
      rw [htwo]
      simp only [Ring.lie_def, star_sub, star_mul]
      noncomm_ring

/-- The diagonal star-product defect of one jump channel is a star square. -/
theorem dissipatorTerm_star_self_defect
    (half : A) (h_half : (2 : A) * half = 1)
    (h_half_comm : ∀ z : A, half * z = z * half)
    (h_half_star : star half = half) (L X : A) :
    dissipatorTerm half L (star X * X) -
        star (dissipatorTerm half L X) * X -
        star X * dissipatorTerm half L X = star ⁅L, X⁆ * ⁅L, X⁆ :=
  dissipatorTerm_star_mul_defect half h_half h_half_comm h_half_star L X X

/-- A skew-adjoint inner derivation has zero polarized star-product defect. -/
theorem inner_star_mul_defect {H : A} (hH : star H = -H) (X Y : A) :
    ⁅H, star X * Y⁆ - star ⁅H, X⁆ * Y - star X * ⁅H, Y⁆ = 0 := by
  simp only [Ring.lie_def, star_sub, star_mul, hH]
  noncomm_ring

/-- A jump channel commuting together with its adjoint with an observable
annihilates that observable. Both commutation hypotheses are explicit. -/
theorem dissipatorTerm_eq_zero_of_commute
    (half : A) (h_half : (2 : A) * half = 1)
    (h_half_comm : ∀ z : A, half * z = z * half) (L X : A)
    (hLX : Commute L X) (hsLX : Commute (star L) X) :
    dissipatorTerm half L X = 0 := by
  have hleft : star L * X * L = star L * L * X := by
    rw [mul_assoc, ← hLX.eq, ← mul_assoc]
  have hright : X * star L * L = star L * L * X := by
    rw [← hsLX.eq, hleft]
  have hhalf_two : half * (2 : A) = 1 := by
    rw [h_half_comm, h_half]
  unfold dissipatorTerm
  rw [hleft, hright, ← two_mul, ← mul_assoc, hhalf_two, one_mul, sub_self]

section FiniteFamily

variable {ι : Type*} [Fintype ι]

/-- The finite-family dissipator preserves star on every input. -/
theorem gkslDissipator_star
    (half : A) (h_half_comm : ∀ z : A, half * z = z * half)
    (h_half_star : star half = half) (L : ι → A) (X : A) :
    star (gkslDissipator half L X) = gkslDissipator half L (star X) := by
  simp only [gkslDissipator, star_sum,
    dissipatorTerm_star half h_half_comm h_half_star]

/-- The polarized defect of the finite-family operator is the finite sum
of its channel commutator Gram products. -/
theorem gkslDissipator_star_mul_defect
    (half : A) (h_half : (2 : A) * half = 1)
    (h_half_comm : ∀ z : A, half * z = z * half)
    (h_half_star : star half = half) (L : ι → A) (X Y : A) :
    gkslDissipator half L (star X * Y) -
        star (gkslDissipator half L X) * Y -
        star X * gkslDissipator half L Y =
      ∑ a, star ⁅L a, X⁆ * ⁅L a, Y⁆ := by
  simp only [gkslDissipator, star_sum, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ =>
    dissipatorTerm_star_mul_defect half h_half h_half_comm h_half_star (L a) X Y

/-- Adding a skew-adjoint inner derivation leaves the defect unchanged. -/
theorem totalLindbladian_star_mul_defect
    (half : A) (h_half : (2 : A) * half = 1)
    (h_half_comm : ∀ z : A, half * z = z * half)
    (h_half_star : star half = half) {H : A} (hH : star H = -H)
    (L : ι → A) (X Y : A) :
    totalLindbladian half H L (star X * Y) -
        star (totalLindbladian half H L X) * Y -
        star X * totalLindbladian half H L Y =
      ∑ a, star ⁅L a, X⁆ * ⁅L a, Y⁆ := by
  simp only [totalLindbladian, star_add, add_mul, mul_add]
  calc
    _ = (⁅H, star X * Y⁆ - star ⁅H, X⁆ * Y - star X * ⁅H, Y⁆) +
        (gkslDissipator half L (star X * Y) -
          star (gkslDissipator half L X) * Y -
          star X * gkslDissipator half L Y) := by
      simp only [Ring.lie_def]
      abel
    _ = ∑ a, star ⁅L a, X⁆ * ⁅L a, Y⁆ := by
      rw [inner_star_mul_defect hH,
        gkslDissipator_star_mul_defect half h_half h_half_comm h_half_star, zero_add]

end FiniteFamily

section InvertibleTwo

variable [Invertible (2 : A)]

/-- Native invertibility of two supplies the normalized single-channel
identity, including centrality and self-adjointness of its inverse. -/
theorem dissipatorTerm_invOf_two_star_mul_defect (L X Y : A) :
    dissipatorTerm (⅟(2 : A)) L (star X * Y) -
        star (dissipatorTerm (⅟(2 : A)) L X) * Y -
        star X * dissipatorTerm (⅟(2 : A)) L Y =
      star ⁅L, X⁆ * ⁅L, Y⁆ :=
  dissipatorTerm_star_mul_defect (⅟(2 : A)) (mul_invOf_self (2 : A))
    (fun z => (Commute.ofNat_left 2 z).invOf_left.eq)
    ((IsSelfAdjoint.invOf_iff (2 : A)).mpr (IsSelfAdjoint.ofNat 2)).star_eq L X Y

/-- The finite-family identity with the native inverse of two. -/
theorem totalLindbladian_invOf_two_star_mul_defect
    {ι : Type*} [Fintype ι] {H : A} (hH : star H = -H)
    (L : ι → A) (X Y : A) :
    totalLindbladian (⅟(2 : A)) H L (star X * Y) -
        star (totalLindbladian (⅟(2 : A)) H L X) * Y -
        star X * totalLindbladian (⅟(2 : A)) H L Y =
      ∑ a, star ⁅L a, X⁆ * ⁅L a, Y⁆ :=
  totalLindbladian_star_mul_defect (⅟(2 : A)) (mul_invOf_self (2 : A))
    (fun z => (Commute.ofNat_left 2 z).invOf_left.eq)
    ((IsSelfAdjoint.invOf_iff (2 : A)).mpr (IsSelfAdjoint.ofNat 2)).star_eq hH L X Y

end InvertibleTwo

section Naturality

variable {B : Type*} [Ring B] [StarRing B]

/-- Every native star-ring map transports a channel and its half parameter.
No unitality assumption is needed for this polynomial identity. -/
theorem map_dissipatorTerm (f : A →⋆ₙ+* B) (half L X : A) :
    f (dissipatorTerm half L X) = dissipatorTerm (f half) (f L) (f X) := by
  simp only [dissipatorTerm, map_sub, map_mul, map_add, map_star]

/-- A finite family is natural under star-ring maps. -/
theorem map_gkslDissipator {ι : Type*} [Fintype ι]
    (f : A →⋆ₙ+* B) (half : A) (L : ι → A) (X : A) :
    f (gkslDissipator half L X) = gkslDissipator (f half) (fun a => f (L a)) (f X) := by
  simp only [gkslDissipator, map_sum, map_dissipatorTerm]

/-- The total operator is natural when all its coefficients are transported. -/
theorem map_totalLindbladian {ι : Type*} [Fintype ι]
    (f : A →⋆ₙ+* B) (half H : A) (L : ι → A) (X : A) :
    f (totalLindbladian half H L X) =
      totalLindbladian (f half) (f H) (fun a => f (L a)) (f X) := by
  simp only [totalLindbladian, map_add, map_sub, map_mul, map_gkslDissipator]

end Naturality

end Ring

section Ordered

variable {A : Type*} [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]

/-- A star order makes the diagonal defect nonnegative. This is separate
from the algebraic polarized identity and does not assert a spectral gap. -/
theorem totalLindbladian_star_self_defect_nonneg
    (half : A) (h_half : (2 : A) * half = 1)
    (h_half_comm : ∀ z : A, half * z = z * half)
    (h_half_star : star half = half) {H : A} (hH : star H = -H)
    {ι : Type*} [Fintype ι] (L : ι → A) (X : A) :
    0 ≤ totalLindbladian half H L (star X * X) -
        star (totalLindbladian half H L X) * X -
        star X * totalLindbladian half H L X := by
  rw [totalLindbladian_star_mul_defect half h_half h_half_comm h_half_star hH]
  exact Finset.sum_nonneg fun a _ => star_mul_self_nonneg ⁅L a, X⁆

end Ordered

end InfoGeometry.Modular.GKSL
