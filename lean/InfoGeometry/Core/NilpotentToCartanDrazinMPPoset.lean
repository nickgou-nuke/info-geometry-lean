/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceGrading
import InfoGeometry.Singular.SquareZeroMoorePenrose

/-!
# Conditional nilpotent, Peirce, Drazin and Moore–Penrose constructions

The historical filename is retained, but these constructions are not a poset
or an unconditional cycle. An inner inverse is an input, not a consequence of
square-zero. Returning to a square-zero corner does not produce an inverse.

The carrier is an arbitrary associative ring, with a star only for Penrose
results. `IsIdempotentElem`, `IsStarProjection`, `unitary`, `LinearMap.range`,
and the Lie bracket are native Mathlib objects. Drazin and Penrose predicates
are imported from their existing owners, not redefined here. No finite-dimensional,
diagonalizability, or characteristic-zero assumption is used.

`PeirceGrading` supplies the internal direct sum and all three Lie routing
laws in every characteristic. Only its identification with full reflection
eigenspaces requires injective doubling. This algebraic symmetric splitting
does not assert positivity of a Cartan involution. The difference of arbitrary
Penrose supports is not asserted to be tripotent.
-/

namespace NoncommutativeNilpotentCartanPoset

open InfoGeometry.Core.PeirceGrading
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Singular.ProjectionSectors

variable {A : Type*} [Ring A]

/-- An inner inverse already suffices for both support idempotents.
Square-zero supplies one orientation of orthogonality, not both. -/
theorem nilpotent_to_idempotent {d b : A} (h : d * b * d = d) (hd : d * d = 0) :
    IsIdempotentElem (d * b) ∧ IsIdempotentElem (b * d) ∧ (b * d) * (d * b) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · change (d * b) * (d * b) = d * b
    calc
      _ = (d * b * d) * b := by simp only [mul_assoc]
      _ = d * b := by rw [h]
  · change (b * d) * (b * d) = b * d
    calc
      _ = b * (d * b * d) := by simp only [mul_assoc]
      _ = b * d := by rw [h]
  · exact IsMoorePenroseInverse.domain_mul_range_eq_zero hd

/-- Given an inner inverse, its normalization is a reflexive inverse.
This is a construction from a witness, not an existence theorem for all rings. -/
theorem reflexive_partner_of_inner {d b : A} (h : d * b * d = d) :
    d * (b * d * b) * d = d ∧ (b * d * b) * d * (b * d * b) = b * d * b := by
  constructor
  · calc
      _ = (d * b * d) * b * d := by simp only [mul_assoc]
      _ = d := by rw [h, h]
  · calc
      _ = b * (d * b * d) * b * d * b := by simp only [mul_assoc]
      _ = b * d * b * d * b := by rw [h]
      _ = b * (d * b * d) * b := by simp only [mul_assoc]
      _ = b * d * b := by rw [h]

/-- Two-sided orthogonality is sufficient for the difference identities. -/
theorem orthogonal_difference {p q : A} (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) (hpq : p * q = 0) (hqp : q * p = 0) :
    (p - q)^2 = p + q ∧ (p - q)^3 = p - q := by
  have hs : (p - q)^2 = p + q := by
    rw [sq, sub_mul, mul_sub, mul_sub, hp.eq, hq.eq, hpq, hqp]
    abel
  refine ⟨hs, ?_⟩
  rw [pow_succ, hs, add_mul, mul_sub, mul_sub, hp.eq, hq.eq, hpq, hqp]
  abel

/-- Spectral, inverse, and nilpotent components lie in the actual even submodule. -/
theorem drazin_even {x d : A} {k : ℕ} (h : IsDrazinInverse x d k) :
    x ∈ LinearMap.range (even (projection x d)) ∧
    d ∈ LinearMap.range (even (projection x d)) ∧
    fittingNilpotentPart x d ∈ LinearMap.range (even (projection x d)) := by
  have hp : IsIdempotentElem (projection x d) := h.projection_is_idempotent
  refine ⟨(mem_even_iff hp).mpr h.projection_comm_self,
    (mem_even_iff hp).mpr h.projection_comm, ?_⟩
  apply (mem_even_iff hp).mpr
  exact (show Commute (projection x d) x from h.projection_comm_self).mul_right
    ((Commute.one_right (projection x d)).sub_right (Commute.refl _))

/-- The anomaly identities are algebraic: `l` and `r` need not be projections. -/
theorem support_anomalies {p : A} (hp : IsIdempotentElem p) (l r : A) :
    odd p l = reflection p * ⁅p, l⁆ ∧
    odd p r = reflection p * ⁅p, r⁆ ∧
    odd p (r - l) = reflection p * (⁅p, r⁆ - ⁅p, l⁆) ∧
    ⁅p, l⁆ ∈ LinearMap.range (odd p) ∧
    ⁅p, r⁆ ∈ LinearMap.range (odd p) ∧
    ⁅reflection p, r - l⁆ = 2 • (⁅p, r⁆ - ⁅p, l⁆) := by
  refine ⟨(odd_reconstruction hp l).1, (odd_reconstruction hp r).1, ?_,
    commutator_odd hp l, commutator_odd hp r, ?_⟩
  · rw [map_sub, (odd_reconstruction hp r).1, (odd_reconstruction hp l).1]
    exact (mul_sub _ _ _).symm
  · change reflection p * (r - l) - (r - l) * reflection p = _
    rw [reflection_commutator]
    congr 1
    change p * (r - l) - (r - l) * p = (p * r - r * p) - (p * l - l * p)
    noncomm_ring

end NoncommutativeNilpotentCartanPoset
