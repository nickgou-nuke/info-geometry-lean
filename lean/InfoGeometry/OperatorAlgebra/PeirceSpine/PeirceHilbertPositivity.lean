/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.BoundedHomotopyCoercivity
import InfoGeometry.OperatorAlgebra.PeirceSpine.StarGrading
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Hilbert positivity of an adjoint-paired Peirce corner

The carrier is the full algebra of bounded operators on an arbitrary complete
real inner product space. The adjoint pairing supplies positivity and identifies
the whole kernel. A rank-one off-diagonal realization shows that a nonzero
coupling can still annihilate a nonzero orthogonal vector. Thus nonvanishing does
not imply a coercive lower bound on the whole Hilbert space. This statement does
not deny a gap after removing the kernel, nor does it identify a field-theoretic
Hamiltonian with this bounded operator.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.BoundedHomotopyCoercivity

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The sum of the two Gram operators has native operator positivity. -/
theorem hodge_isPositive (d : E →L[ℝ] E) : (hodge d).IsPositive := by
  exact (isPositive_self_comp_adjoint d).add (isPositive_adjoint_comp_self d)

/-- Positivity detects vanishing of the whole coupling, not its injectivity. -/
theorem hodge_eq_zero_iff (d : E →L[ℝ] E) : hodge d = 0 ↔ d = 0 := by
  constructor
  · intro h
    ext x
    exact ((hodge_apply_eq_zero_iff d x).mp (by rw [h]; rfl)).1
  · rintro rfl
    simp [hodge]

/-- The actual rank-one Gram sum, with both multiplication orders retained. -/
theorem hodge_rankOne (u v : E) :
    hodge (InnerProductSpace.rankOne ℝ u v) =
      ‖v‖ ^ 2 • InnerProductSpace.rankOne ℝ u u +
      ‖u‖ ^ 2 • InnerProductSpace.rankOne ℝ v v := by
  rw [hodge, InnerProductSpace.adjoint_rankOne]
  change InnerProductSpace.rankOne ℝ u v ∘L InnerProductSpace.rankOne ℝ v u +
      InnerProductSpace.rankOne ℝ v u ∘L InnerProductSpace.rankOne ℝ u v = _
  rw [InnerProductSpace.rankOne_comp_rankOne, InnerProductSpace.rankOne_comp_rankOne,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- The zero modes of the rank-one coupling are precisely the vectors
orthogonal to both its source and target lines. -/
theorem hodge_rankOne_apply_eq_zero_iff (u v x : E) (hu : u ≠ 0) (hv : v ≠ 0) :
    hodge (InnerProductSpace.rankOne ℝ u v) x = 0 ↔
      inner ℝ v x = 0 ∧ inner ℝ u x = 0 := by
  rw [hodge_apply_eq_zero_iff, InnerProductSpace.adjoint_rankOne]
  simp only [InnerProductSpace.rankOne_apply, smul_eq_zero, hu, hv, or_false]

/-- Any actual nonzero common zero mode forbids a positive lower bound on
the whole space. No claim about the kernel complement is made. -/
theorem no_coercive_bound_of_common_zero_mode (d : E →L[ℝ] E) (x : E)
    (hx : x ≠ 0) (hd : d x = 0) (ha : adjoint d x = 0) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ y : E,
      c * ‖y‖ ^ 2 ≤ inner ℝ y (hodge d y) := by
  rintro ⟨c, hc, hbound⟩
  have hzero := (hodge_apply_eq_zero_iff d x).mpr ⟨hd, ha⟩
  have h := hbound x
  rw [hzero, inner_zero_right] at h
  exact (not_le_of_gt (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hx)))) h

end InfoGeometry.OperatorAlgebra.BoundedHomotopyCoercivity

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open ContinuousLinearMap InnerProductSpace BoundedHomotopyCoercivity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Orthogonality makes the actual transfer square-zero. -/
theorem rankOne_transfer_square_zero (u v : E) (huv : inner ℝ u v = 0) :
    rankOne ℝ u v * rankOne ℝ u v = 0 := by
  have hvu : inner ℝ v u = 0 := by rw [real_inner_comm, huv]
  change rankOne ℝ u v ∘L rankOne ℝ u v = 0
  rw [rankOne_comp_rankOne, hvu, zero_smul]

/-- Native Hilbert positivity of the existing Peirce coupling under its
actual adjoint pairing. Idempotency of the cut is unnecessary for this fact. -/
theorem genV_hilbert_isPositive {P : E →L[ℝ] E} (hPs : star P = P)
    (A : E →L[ℝ] E) : (genV P A (star A)).IsPositive := by
  rw [genV, anticomm, ← star_conePlus hPs A]
  exact hodge_isPositive (conePlus P A)

/-- The native kernel retains both opposite corners. -/
theorem genV_hilbert_ker {P : E →L[ℝ] E} (hPs : star P = P)
    (A : E →L[ℝ] E) :
    (genV P A (star A)).ker = (conePlus P A).ker ⊓ (coneMinus P (star A)).ker := by
  rw [genV, anticomm, ← star_conePlus hPs A]
  exact hodge_ker (conePlus P A)

/-- Nonzero upper corner is equivalent to nonzero coupling; no invertibility
or positive lower bound is asserted. -/
theorem genV_hilbert_eq_zero_iff {P : E →L[ℝ] E} (hPs : star P = P)
    (A : E →L[ℝ] E) : genV P A (star A) = 0 ↔ conePlus P A = 0 := by
  rw [genV, anticomm, ← star_conePlus hPs A]
  exact hodge_eq_zero_iff (conePlus P A)

/-- An orthogonal rank-one transfer is exactly its own upper Peirce corner. -/
theorem conePlus_rankOne (u v : E) (hu : ‖u‖ = 1) (huv : inner ℝ u v = 0) :
    conePlus (rankOne ℝ u u) (rankOne ℝ u v) = rankOne ℝ u v := by
  have hvu : inner ℝ v u = 0 := by rw [real_inner_comm, huv]
  unfold conePlus
  rw [mul_sub, mul_one]
  change rankOne ℝ u u ∘L rankOne ℝ u v -
    (rankOne ℝ u u ∘L rankOne ℝ u v) ∘L rankOne ℝ u u = _
  rw [rankOne_comp_rankOne, real_inner_self_eq_norm_sq, hu]
  simp only [one_pow, one_smul]
  rw [rankOne_comp_rankOne, hvu, zero_smul, sub_zero]

/-- Adjoint pairing of the rank-one transfer gives the two orthogonal line
projections as the existing Peirce coupling. -/
theorem genV_rankOne (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = 0) :
    genV (rankOne ℝ u u) (rankOne ℝ u v) (star (rankOne ℝ u v)) =
      rankOne ℝ u u + rankOne ℝ v v := by
  have hPs : star (rankOne ℝ u u) = rankOne ℝ u u := adjoint_rankOne u u
  rw [genV, anticomm, ← star_conePlus hPs, conePlus_rankOne u v hu huv]
  change hodge (rankOne ℝ u v) = _
  rw [hodge_rankOne, hu, hv]
  simp

/-- The orthogonal transfer and its adjoint do not commute. Their commutator
acts by the identity on the target unit vector. -/
theorem rankOne_adjoint_commutator_apply (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0) :
    comm (rankOne ℝ u v) (star (rankOne ℝ u v)) u = u := by
  have hvu : inner ℝ v u = 0 := by rw [real_inner_comm, huv]
  rw [show star (rankOne ℝ u v) = rankOne ℝ v u from adjoint_rankOne u v]
  change rankOne ℝ u v (rankOne ℝ v u u) - rankOne ℝ v u (rankOne ℝ u v u) = u
  simp [rankOne_apply, real_inner_self_eq_norm_sq, hu, hv, hvu]

/-- The rank-one realization remains noncommutative inside the full bounded
operator algebra, including on an infinite-dimensional ambient space. -/
theorem rankOne_adjoint_not_commute (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0) :
    ¬ Commute (rankOne ℝ u v) (star (rankOne ℝ u v)) := by
  intro h
  have hzero : comm (rankOne ℝ u v) (star (rankOne ℝ u v)) = 0 := sub_eq_zero.mpr h.eq
  have he := rankOne_adjoint_commutator_apply u v hu hv huv
  rw [hzero, zero_apply] at he
  have hnorm := congrArg norm he
  simp [hu] at hnorm

/-- Nonzero adjoint-paired off-diagonal coupling can fail every positive
whole-space coercive estimate. The surviving orthogonal vector is explicit. -/
theorem genV_rankOne_no_coercive_bound (u v w : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (hw : w ≠ 0) (huw : inner ℝ u w = 0) (hvw : inner ℝ v w = 0) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ x : E,
      c * ‖x‖ ^ 2 ≤ inner ℝ x
        (genV (rankOne ℝ u u) (rankOne ℝ u v) (star (rankOne ℝ u v)) x) := by
  rintro ⟨c, hc, hbound⟩
  have h := hbound w
  rw [genV_rankOne u v hu hv huv] at h
  simp only [add_apply, rankOne_apply, huw, hvw, zero_smul, add_zero,
    inner_zero_right] at h
  exact (not_le_of_gt (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hw)))) h

/-- The same coupling is nonzero, so the previous obstruction is not the
zero-operator example. -/
theorem genV_rankOne_ne_zero (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0) :
    genV (rankOne ℝ u u) (rankOne ℝ u v) (star (rankOne ℝ u v)) ≠ 0 := by
  have hPs : star (rankOne ℝ u u) = rankOne ℝ u u := adjoint_rankOne u u
  rw [ne_eq, genV_hilbert_eq_zero_iff hPs, conePlus_rankOne u v hu huv]
  apply rankOne_ne_zero
  · intro h
    simp [h] at hu
  · intro h
    simp [h] at hv

/-- A nonzero lower-corner seed can have zero upper corner. -/
theorem conePlus_rankOne_reverse (u v : E) (huv : inner ℝ u v = 0) :
    conePlus (rankOne ℝ u u) (rankOne ℝ v u) = 0 := by
  unfold conePlus
  have hleft : rankOne ℝ u u * rankOne ℝ v u = 0 := by
    change rankOne ℝ u u ∘L rankOne ℝ v u = 0
    rw [rankOne_comp_rankOne, huv, zero_smul]
  rw [hleft, zero_mul]

/-- Adjoint pairing does not make the upper seed nonzero merely because the
uncompressed input fails to commute with the cut. -/
theorem genV_rankOne_reverse_eq_zero (u v : E) (huv : inner ℝ u v = 0) :
    genV (rankOne ℝ u u) (rankOne ℝ v u) (star (rankOne ℝ v u)) = 0 := by
  have hPs : star (rankOne ℝ u u) = rankOne ℝ u u := adjoint_rankOne u u
  exact (genV_hilbert_eq_zero_iff hPs _).mpr (conePlus_rankOne_reverse u v huv)

/-- The zero-coupling reverse seed does fail to commute with its cut. -/
theorem rankOne_cut_reverse_not_commute (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0) :
    ¬ Commute (rankOne ℝ u u) (rankOne ℝ v u) := by
  intro h
  have hleft : rankOne ℝ u u * rankOne ℝ v u = 0 := by
    change rankOne ℝ u u ∘L rankOne ℝ v u = 0
    rw [rankOne_comp_rankOne, huv, zero_smul]
  have hright : rankOne ℝ v u * rankOne ℝ u u = rankOne ℝ v u := by
    change rankOne ℝ v u ∘L rankOne ℝ u u = rankOne ℝ v u
    rw [rankOne_comp_rankOne, real_inner_self_eq_norm_sq, hu]
    simp
  have hn : rankOne ℝ v u ≠ 0 := by
    apply rankOne_ne_zero
    · intro hv0
      simp [hv0] at hv
    · intro hu0
      simp [hu0] at hu
  exact hn (hright.symm.trans (h.eq.symm.trans hleft))

end InfoGeometry.OperatorAlgebra.PeirceSpine
