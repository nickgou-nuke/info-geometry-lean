import Mathlib

open scoped BigOperators

/-!
# Generic Dirac Self-Adjointness — No Cuntz Relations Required

Corrected formal package per Cuntz theory:
1. `selfAdjoint_add_star`: x + x* is self-adjoint ∀ x.
2. `finiteDirac_selfAdjoint`: D = Σ_i (S_i + S*_i) is self-adjoint.
3. Cuntz relations needed only for idempotent projections.
-/

namespace InfoGeometry.Algebra.Cuntz

/-- x + x* is always self-adjoint. -/
lemma selfAdjoint_add_star {A : Type*} [AddCommMonoid A] [StarAddMonoid A]
    [InvolutiveStar A] (x : A) : IsSelfAdjoint (x + star x) := by
  unfold IsSelfAdjoint; rw [star_add, star_star, add_comm]

/-- Finite Dirac D = Σ_i (S_i + S*_i) is self-adjoint. No Cuntz hypotheses. -/
lemma finiteDirac_selfAdjoint {A ι : Type*} [AddCommMonoid A] [StarAddMonoid A]
    [InvolutiveStar A] [Fintype ι] (S : ι → A) :
    IsSelfAdjoint (∑ i, (S i + star (S i))) := by
  unfold IsSelfAdjoint
  -- Star of sum = sum of stars, then each term simplifies
  have h : star (∑ i, (S i + star (S i))) = ∑ i, (S i + star (S i)) := by
    simp [star_add, add_comm, star_star, Finset.sum_add_distrib]
  exact h

/-- Range projection idempotence (uses isometry S*_i·S_i = 1). -/
lemma range_projection_idempotent {A : Type*} [Ring A] [StarRing A]
    {ι : Type*} [DecidableEq ι] (S : ι → A)
    (h_isometry : ∀ i j, star (S i) * S j = if i = j then 1 else 0)
    (i : ι) : (S i * star (S i)) * (S i * star (S i)) = S i * star (S i) := by
  have h_isom : star (S i) * S i = 1 := by simpa using h_isometry i i
  calc
    (S i * star (S i)) * (S i * star (S i))
        = S i * (star (S i) * S i) * star (S i) := by noncomm_ring
    _ = S i * 1 * star (S i) := by rw [h_isom]
    _ = S i * star (S i) := by simp

/-- Range projection orthogonality (uses isometry S*_i·S_j = 0 for i≠j). -/
lemma range_projection_orthogonal {A : Type*} [Ring A] [StarRing A]
    {ι : Type*} [DecidableEq ι] (S : ι → A)
    (h_isometry : ∀ i j, star (S i) * S j = if i = j then 1 else 0)
    {i j : ι} (hij : i ≠ j) :
    (S i * star (S i)) * (S j * star (S j)) = 0 := by
  have h_orth : star (S i) * S j = 0 := by
    have := h_isometry i j
    simpa [hij] using this
  calc
    (S i * star (S i)) * (S j * star (S j))
        = S i * (star (S i) * S j) * star (S j) := by noncomm_ring
    _ = S i * 0 * star (S j) := by rw [h_orth]
    _ = 0 := by simp

end InfoGeometry.Algebra.Cuntz
