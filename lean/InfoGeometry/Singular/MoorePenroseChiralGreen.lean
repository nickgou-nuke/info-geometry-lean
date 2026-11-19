/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Singular.SquareZeroChiralHodge

/-!
# Canonical closed-range chiral Green operators

For a bounded self-adjoint operator `Q` with closed range, the existing
`moorePenroseInverse` construction gives a self-adjoint inverse on the
orthogonal kernel complement. Its square is the canonical Moore--Penrose
inverse of `Q * Q`, whose range is proved to equal the range of `Q`.

Every bounded operator anticommuting with `Q` also anticommutes with this
inverse and commutes with its regular and kernel projections. In particular
this applies to a chiral grading, without assuming that the grading is
self-adjoint or involutive. The proof uses the group-inverse identities
derived from self-adjointness of `Q`, not arbitrary similarity covariance.

The ambient real or complex Hilbert space need not be finite-dimensional.
These are bounded closed-range results; no unbounded domain, heat trace,
Fredholm index, or boundary eta invariant is constructed here.
-/

namespace InfoGeometry.Singular.MoorePenrose

section Algebra

variable {R : Type*} [Ring R] [StarRing R]

namespace IsMoorePenroseInverse

variable {a b g : R}

/-- The Moore--Penrose inverse of a self-adjoint element is self-adjoint. -/
theorem isSelfAdjoint_of_selfAdjoint (h : IsMoorePenroseInverse a b)
    (ha : IsSelfAdjoint a) : IsSelfAdjoint b := by
  change star b = b
  exact MoorePenrose_unique (by simpa only [ha.star_eq] using h.star_same_order) h

/-- Self-adjointness of the original element forces it to commute with its
Moore--Penrose inverse; no ambient commutativity is assumed. -/
theorem commute_of_selfAdjoint (h : IsMoorePenroseInverse a b)
    (ha : IsSelfAdjoint a) : Commute a b := by
  change a * b = b * a
  calc
    a * b = star (a * b) := h.ab_adj_eq.symm
    _ = b * a := by
      rw [star_mul, (h.isSelfAdjoint_of_selfAdjoint ha).star_eq, ha.star_eq]

/-- A commuting Moore--Penrose pair satisfies the group-inverse equation. -/
theorem mul_mul_inverse (h : IsMoorePenroseInverse a b) (hab : Commute a b) :
    a * a * b = a := by
  calc
    a * a * b = a * (a * b) := mul_assoc _ _ _
    _ = a * (b * a) := by rw [hab.eq]
    _ = a * b * a := (mul_assoc _ _ _).symm
    _ = a := h.aba_eq_a

/-- The reverse group-inverse equation for a commuting Moore--Penrose pair. -/
theorem inverse_mul_inverse (h : IsMoorePenroseInverse a b) (hab : Commute a b) :
    b * b * a = b := by
  calc
    b * b * a = b * (b * a) := mul_assoc _ _ _
    _ = b * (a * b) := by rw [hab.eq]
    _ = b * a * b := (mul_assoc _ _ _).symm
    _ = b := h.bab_eq_b

/-- Squaring a commuting Moore--Penrose pair preserves all four Penrose laws. -/
theorem square_of_commute (h : IsMoorePenroseInverse a b) (hab : Commute a b) :
    IsMoorePenroseInverse (a * a) (b * b) := by
  have hp : (a * a) * (b * b) = a * b := by
    rw [← mul_assoc, h.mul_mul_inverse hab]
  have hq : (b * b) * (a * a) = b * a := by
    rw [← mul_assoc, h.inverse_mul_inverse hab]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hp, ← mul_assoc, h.aba_eq_a]
  · rw [hq, ← mul_assoc, h.bab_eq_b]
  · simpa only [hp] using h.ab_adj_eq
  · simpa only [hq] using h.ba_adj_eq

/-- Any anticommuting element preserves the support of a commuting
Moore--Penrose pair. This needs no invertibility or star condition on `g`. -/
theorem commute_support_of_anticommute (h : IsMoorePenroseInverse a b)
    (hab : Commute a b) (hga : g * a = -(a * g)) : Commute g (a * b) := by
  have hag : a * g = -(g * a) := by rw [hga, neg_neg]
  have hleft : (a * b) * g * (a * b) = g * (a * b) := by
    calc
      (a * b) * g * (a * b) = (a * b) * (g * a) * b := by noncomm_ring
      _ = -((a * b * a) * g * b) := by rw [hga]; noncomm_ring
      _ = -(a * g * b) := by rw [h.aba_eq_a]
      _ = g * (a * b) := by rw [← mul_assoc, hga, neg_mul]
  have hright : (a * b) * g * (a * b) = (a * b) * g := by
    calc
      (a * b) * g * (a * b) = (b * a) * g * (a * b) :=
        congrArg (fun z => z * g * (a * b)) hab.eq
      _ = b * (a * g) * (a * b) := by noncomm_ring
      _ = -(b * g * (a * a * b)) := by rw [hag]; noncomm_ring
      _ = -(b * g * a) := by rw [h.mul_mul_inverse hab]
      _ = (b * a) * g := by rw [mul_assoc b a g, hag]; noncomm_ring
      _ = (a * b) * g := congrArg (fun z => z * g) hab.eq.symm
  exact hleft.symm.trans hright

/-- The group-inverse identities transport anticommutation to the inverse.
The anticommuting element need not be an involution or a unit. -/
theorem anticommute_of_commute (h : IsMoorePenroseInverse a b)
    (hab : Commute a b) (hga : g * a = -(a * g)) : g * b = -(b * g) := by
  have hag : a * g = -(g * a) := by rw [hga, neg_neg]
  have hgp := (h.commute_support_of_anticommute hab hga).eq
  have habb : a * b * b = b := by rw [hab.eq, h.bab_eq_b]
  calc
    g * b = g * ((a * b) * b) := by rw [habb]
    _ = (g * (a * b)) * b := (mul_assoc _ _ _).symm
    _ = ((a * b) * g) * b := by rw [hgp]
    _ = b * (a * g) * b := by rw [hab.eq]; noncomm_ring
    _ = -(b * (g * (a * b))) := by rw [hag]; noncomm_ring
    _ = -(b * ((a * b) * g)) := by rw [hgp]
    _ = -((b * a * b) * g) := by noncomm_ring
    _ = -(b * g) := by rw [h.bab_eq_b]

end IsMoorePenroseInverse

end Algebra

noncomputable section Hilbert

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

variable (Q : E →L[𝕜] E) (hQ : IsSelfAdjoint Q)
  (hClosed : IsClosed (Q.range : Set E))

include hQ hClosed

/-- The actual canonical inverse is self-adjoint. -/
theorem moorePenroseInverse_isSelfAdjoint :
    IsSelfAdjoint (moorePenroseInverse Q hClosed) :=
  (show IsMoorePenroseInverse Q (moorePenroseInverse Q hClosed) from
    isMoorePenroseInverse_moorePenroseInverse Q hClosed).isSelfAdjoint_of_selfAdjoint hQ

/-- The original self-adjoint operator commutes with its constructed inverse. -/
theorem moorePenroseInverse_commute : Commute Q (moorePenroseInverse Q hClosed) :=
  (show IsMoorePenroseInverse Q (moorePenroseInverse Q hClosed) from
    isMoorePenroseInverse_moorePenroseInverse Q hClosed).commute_of_selfAdjoint hQ

/-- Closed range removes the closure in the self-adjoint kernel/range duality. -/
theorem range_eq_orthogonal_ker_of_selfAdjoint : Q.range = Q.kerᗮ := by
  have hstar : Q.adjoint = Q := hQ.star_eq
  rw [Q.orthogonal_ker, hstar, hClosed.submodule_topologicalClosure_eq]

/-- The canonical regular support is the orthogonal kernel-complement projection. -/
theorem moorePenroseInverse_regular_projection :
    Q * moorePenroseInverse Q hClosed = Q.kerᗮ.starProjection := by
  calc
    Q * moorePenroseInverse Q hClosed = Q.range.starProjection :=
      moorePenroseInverse_range_projector_eq_starProjection Q hClosed
    _ = Q.kerᗮ.starProjection := by
      simp only [range_eq_orthogonal_ker_of_selfAdjoint Q hQ hClosed]

/-- Domain and range supports agree for the canonical self-adjoint inverse. -/
theorem moorePenroseInverse_domain_projection :
    moorePenroseInverse Q hClosed * Q = Q.kerᗮ.starProjection := by
  rw [← (moorePenroseInverse_commute Q hQ hClosed).eq,
    moorePenroseInverse_regular_projection Q hQ hClosed]

/-- The kernel projection is the complement of the regular support. -/
theorem moorePenroseInverse_kernel_projection :
    Q.ker.starProjection = 1 - Q * moorePenroseInverse Q hClosed := by
  rw [moorePenroseInverse_regular_projection Q hQ hClosed,
    Submodule.starProjection_orthogonal']
  abel

/-- The constructed inverse annihilates the kernel projection on its right. -/
theorem moorePenroseInverse_mul_kernel_projection :
    moorePenroseInverse Q hClosed * Q.ker.starProjection = 0 := by
  have h : IsMoorePenroseInverse Q (moorePenroseInverse Q hClosed) :=
    isMoorePenroseInverse_moorePenroseInverse Q hClosed
  rw [moorePenroseInverse_kernel_projection Q hQ hClosed, mul_sub, mul_one,
    ← mul_assoc, h.bab_eq_b, sub_self]

/-- The constructed inverse annihilates the kernel projection on its left. -/
theorem kernel_projection_mul_moorePenroseInverse :
    Q.ker.starProjection * moorePenroseInverse Q hClosed = 0 := by
  have h := congrArg star (moorePenroseInverse_mul_kernel_projection Q hQ hClosed)
  simpa only [star_mul, (moorePenroseInverse_isSelfAdjoint Q hQ hClosed).star_eq,
    (isSelfAdjoint_starProjection Q.ker).star_eq, star_zero] using h

/-- Pointwise kernel annihilation by the actual inverse. -/
theorem moorePenroseInverse_apply_of_mem_ker {x : E} (hx : x ∈ Q.ker) :
    moorePenroseInverse Q hClosed x = 0 := by
  have h := congrArg (fun T : E →L[𝕜] E => T x)
    (moorePenroseInverse_mul_kernel_projection Q hQ hClosed)
  simpa only [mul_apply_eq_comp,
    Submodule.starProjection_mem_subspace_eq_self ⟨x, hx⟩,
    zero_apply] using h

/-- Squaring a bounded self-adjoint closed-range operator preserves its range. -/
theorem range_square_eq_of_selfAdjoint : (Q * Q).range = Q.range := by
  have h : IsMoorePenroseInverse Q (moorePenroseInverse Q hClosed) :=
    isMoorePenroseInverse_moorePenroseInverse Q hClosed
  have hQQB := h.mul_mul_inverse (h.commute_of_selfAdjoint hQ)
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    exact ⟨Q x, rfl⟩
  · rintro y ⟨x, rfl⟩
    refine ⟨moorePenroseInverse Q hClosed x, ?_⟩
    exact congrArg (fun T : E →L[𝕜] E => T x) hQQB

/-- Closed range of the square is derived from closed range of `Q`. -/
theorem isClosed_range_square_of_selfAdjoint : IsClosed ((Q * Q).range : Set E) := by
  rw [range_square_eq_of_selfAdjoint Q hQ hClosed]
  exact hClosed

/-- The square of the constructed inverse is the canonical inverse of the square. -/
theorem moorePenroseInverse_square :
    moorePenroseInverse (Q * Q) (isClosed_range_square_of_selfAdjoint Q hQ hClosed) =
      moorePenroseInverse Q hClosed * moorePenroseInverse Q hClosed := by
  have h : IsMoorePenroseInverse Q (moorePenroseInverse Q hClosed) :=
    isMoorePenroseInverse_moorePenroseInverse Q hClosed
  exact MoorePenrose_unique
    (show IsMoorePenroseInverse (Q * Q)
      (moorePenroseInverse (Q * Q) (isClosed_range_square_of_selfAdjoint Q hQ hClosed)) from
      isMoorePenroseInverse_moorePenroseInverse (Q * Q)
        (isClosed_range_square_of_selfAdjoint Q hQ hClosed))
    (h.square_of_commute (h.commute_of_selfAdjoint hQ))

/-- The bounded Green identity `(Q²)⁺ Q = Q⁺` uses the canonical inverse. -/
theorem moorePenroseInverse_square_mul :
    moorePenroseInverse (Q * Q) (isClosed_range_square_of_selfAdjoint Q hQ hClosed) * Q =
      moorePenroseInverse Q hClosed := by
  rw [moorePenroseInverse_square Q hQ hClosed]
  exact (show IsMoorePenroseInverse Q (moorePenroseInverse Q hClosed) from
    isMoorePenroseInverse_moorePenroseInverse Q hClosed).inverse_mul_inverse
      (moorePenroseInverse_commute Q hQ hClosed)

/-- The reverse Green identity `Q (Q²)⁺ = Q⁺`. -/
theorem mul_moorePenroseInverse_square :
    Q * moorePenroseInverse (Q * Q) (isClosed_range_square_of_selfAdjoint Q hQ hClosed) =
      moorePenroseInverse Q hClosed := by
  have h : IsMoorePenroseInverse Q (moorePenroseInverse Q hClosed) :=
    isMoorePenroseInverse_moorePenroseInverse Q hClosed
  rw [moorePenroseInverse_square Q hQ hClosed, ← mul_assoc,
    (moorePenroseInverse_commute Q hQ hClosed).eq, h.bab_eq_b]

variable (Γ : E →L[𝕜] E) (hOdd : Γ * Q = -(Q * Γ))

include hOdd

/-- Chirality passes to the actual canonical Green inverse. No additional
metric or involution condition on the anticommuting operator is required. -/
theorem moorePenroseInverse_anticommute :
    Γ * moorePenroseInverse Q hClosed = -(moorePenroseInverse Q hClosed * Γ) :=
  (show IsMoorePenroseInverse Q (moorePenroseInverse Q hClosed) from
    isMoorePenroseInverse_moorePenroseInverse Q hClosed).anticommute_of_commute
      (moorePenroseInverse_commute Q hQ hClosed) hOdd

/-- The regular support is even under every operator anticommuting with `Q`. -/
theorem commute_regular_projection_of_anticommute : Commute Γ Q.kerᗮ.starProjection := by
  rw [← moorePenroseInverse_regular_projection Q hQ hClosed]
  exact (show IsMoorePenroseInverse Q (moorePenroseInverse Q hClosed) from
    isMoorePenroseInverse_moorePenroseInverse Q hClosed).commute_support_of_anticommute
      (moorePenroseInverse_commute Q hQ hClosed) hOdd

/-- The kernel projection is even under the same anticommuting operator. -/
theorem commute_kernel_projection_of_anticommute : Commute Γ Q.ker.starProjection := by
  have h := commute_regular_projection_of_anticommute Q hQ hClosed Γ hOdd
  rw [moorePenroseInverse_kernel_projection Q hQ hClosed,
    moorePenroseInverse_regular_projection Q hQ hClosed]
  exact (Commute.one_right Γ).sub_right h

end Hilbert

end InfoGeometry.Singular.MoorePenrose
