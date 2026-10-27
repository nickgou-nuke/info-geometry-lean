/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Projective subspaces inside the full operator algebra

Subspaces and orthogonal projections are equivalent carriers. Incidence is
operator absorption. Multiplication gives the intersection projection exactly
when the two projections commute; commutativity is not assumed globally.
-/

noncomputable section

namespace InfoGeometry.Projective.ProjectionIncidence

open Module

section StarAlgebra

variable {A : Type*} [NonUnitalSemiring A] [StarRing A] {P Q : A}

/-- For self-adjoint idempotents, the product is an orthogonal projection
exactly when the factors commute. -/
theorem isStarProjection_mul_iff (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    IsStarProjection (P * Q) ↔ Commute P Q :=
  ⟨fun h => (IsSelfAdjoint.commute_iff hP.isSelfAdjoint hQ.isSelfAdjoint).mpr
    h.isSelfAdjoint, hP.mul hQ⟩

/-- Adjoint reverses the order in an incidence equation. -/
theorem absorption_reverse_iff (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    Q * P = P ↔ P * Q = P := by
  constructor <;> intro h <;>
    simpa only [star_mul, hP.isSelfAdjoint.star_eq, hQ.isSelfAdjoint.star_eq]
      using congrArg star h

end StarAlgebra

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Range inclusion is an operator absorption equation. Only the receiving
operator needs to be idempotent. -/
theorem range_le_iff_mul_eq {P Q : E →L[𝕜] E} (hQ : IsIdempotentElem Q) :
    P.range ≤ Q.range ↔ Q * P = P := by
  constructor
  · intro h
    ext x
    obtain ⟨y, hy⟩ := h (show P x ∈ P.range from ⟨x, rfl⟩)
    change Q (P x) = P x
    rw [← hy]
    exact DFunLike.congr_fun hQ.eq y
  · intro h x hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨P y, DFunLike.congr_fun h y⟩

section FiniteDimensional

variable [FiniteDimensional 𝕜 E]

/-- Every subspace is represented by exactly one self-adjoint idempotent. -/
def projectionEquiv :
    Submodule 𝕜 E ≃ {P : E →L[𝕜] E // IsStarProjection P} where
  toFun U := ⟨U.starProjection, isStarProjection_starProjection⟩
  invFun P := P.1.range
  left_inv U := Submodule.range_starProjection U
  right_inv P := Subtype.ext <|
    ContinuousLinearMap.IsStarProjection.ext isStarProjection_starProjection P.2
      (Submodule.range_starProjection P.1.range)

/-- Native projective points act as rank-one orthogonal projections. -/
def pointProjection (p : Projectivization 𝕜 E) : E →L[𝕜] E :=
  p.submodule.starProjection

@[simp] theorem pointProjection_range (p : Projectivization 𝕜 E) :
    (pointProjection p).range = p.submodule :=
  Submodule.range_starProjection _

theorem pointProjection_isStarProjection (p : Projectivization 𝕜 E) :
    IsStarProjection (pointProjection p) :=
  isStarProjection_starProjection

@[simp] theorem pointProjection_rank (p : Projectivization 𝕜 E) :
    finrank 𝕜 (pointProjection p).range = 1 := by
  rw [pointProjection_range, p.finrank_submodule]

theorem pointProjection_injective :
    Function.Injective (pointProjection : Projectivization 𝕜 E → E →L[𝕜] E) := by
  intro p q h
  apply Projectivization.submodule_injective
  simpa only [pointProjection_range] using congrArg ContinuousLinearMap.range h

/-- This is a two-sided equivalence with the actual projective quotient,
not just a representation of selected vectors. -/
def pointProjectionEquiv : Projectivization 𝕜 E ≃
    {P : E →L[𝕜] E // IsStarProjection P ∧ finrank 𝕜 P.range = 1} where
  toFun p := ⟨pointProjection p, pointProjection_isStarProjection p, pointProjection_rank p⟩
  invFun P := Projectivization.mk'' P.1.range P.2.2
  left_inv p := by
    simp only [pointProjection_range, Projectivization.mk''_submodule]
  right_inv P := by
    apply Subtype.ext
    apply ContinuousLinearMap.IsStarProjection.ext (pointProjection_isStarProjection _) P.2.1
    simp only [pointProjection_range, Projectivization.submodule_mk'']

/-- Incidence is absorption in the full noncommutative operator algebra. -/
theorem le_iff_projection_mul (U W : Submodule 𝕜 E) :
    U ≤ W ↔ W.starProjection * U.starProjection = U.starProjection := by
  simpa only [Submodule.range_starProjection] using
    (range_le_iff_mul_eq (P := U.starProjection) W.isIdempotentElem_starProjection)

/-- The reversed product expresses the same incidence because the operators
are self-adjoint. -/
theorem le_iff_projection_mul_reverse (U W : Submodule 𝕜 E) :
    U ≤ W ↔ U.starProjection * W.starProjection = U.starProjection :=
  (le_iff_projection_mul U W).trans
    (absorption_reverse_iff isStarProjection_starProjection isStarProjection_starProjection)

theorem point_incident_iff (p : Projectivization 𝕜 E) (W : Submodule 𝕜 E) :
    p.submodule ≤ W ↔ W.starProjection * pointProjection p = pointProjection p :=
  le_iff_projection_mul p.submodule W

/-- The range of a product of commuting orthogonal projections is their
intersection. -/
theorem range_mul_of_commute (U W : Submodule 𝕜 E)
    (h : Commute U.starProjection W.starProjection) :
    (U.starProjection * W.starProjection).range = U ⊓ W := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    constructor
    · exact U.starProjection_apply_mem _
    · have heq := DFunLike.congr_fun h.eq y
      change U.starProjection (W.starProjection y) = W.starProjection (U.starProjection y) at heq
      change U.starProjection (W.starProjection y) ∈ W
      rw [heq]
      exact W.starProjection_apply_mem _
  · intro x hx
    refine ⟨x, ?_⟩
    change U.starProjection (W.starProjection x) = x
    rw [W.starProjection_eq_self_iff.mpr hx.2, U.starProjection_eq_self_iff.mpr hx.1]

/-- Multiplication computes the geometric meet in precisely the commuting case. -/
theorem mul_eq_inf_projection (U W : Submodule 𝕜 E)
    (h : Commute U.starProjection W.starProjection) :
    U.starProjection * W.starProjection = (U ⊓ W).starProjection := by
  apply ContinuousLinearMap.IsStarProjection.ext
    (IsStarProjection.mul isStarProjection_starProjection isStarProjection_starProjection h)
    isStarProjection_starProjection
  rw [range_mul_of_commute U W h, Submodule.range_starProjection]

theorem mul_eq_inf_projection_iff (U W : Submodule 𝕜 E) :
    U.starProjection * W.starProjection = (U ⊓ W).starProjection ↔
      Commute U.starProjection W.starProjection := by
  constructor
  · intro h
    apply (isStarProjection_mul_iff isStarProjection_starProjection
      isStarProjection_starProjection).mp
    rw [h]
    exact isStarProjection_starProjection
  · exact mul_eq_inf_projection U W

/-- Without commutativity the geometric meet still exists, but cannot be
replaced by the product of the two projections. -/
theorem mul_ne_inf_projection_of_not_commute (U W : Submodule 𝕜 E)
    (h : ¬ Commute U.starProjection W.starProjection) :
    U.starProjection * W.starProjection ≠ (U ⊓ W).starProjection :=
  fun hEq => h ((mul_eq_inf_projection_iff U W).mp hEq)

end FiniteDimensional

end InfoGeometry.Projective.ProjectionIncidence
