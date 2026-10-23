/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.LinearAlgebra.RegularDyadCompression

/-!
# Dyadic compression for the existing regular two-boundary functional

This owner connects the existing boundary-pair functional to the native
rank-one dyad, without identifying it with a density matrix.
-/

noncomputable section

namespace InfoGeometry.Streaming.TwoBoundaryDyadCompression

open InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional
open InfoGeometry.LinearAlgebra.RegularDyadCompression

variable {ι : Type*} [Fintype ι]

def postCovector (p : RegularBoundaryPair ι) : Module.Dual ℂ (State ι) where
  toFun x := pairing p.post x
  map_add' x y := pairing_add_right p.post x y
  map_smul' c x := by
    change pairing p.post (c • x) = c * pairing p.post x
    exact pairing_smul_right c p.post x

@[simp] theorem postCovector_apply (p : RegularBoundaryPair ι) (x : State ι) :
    postCovector p x = pairing p.post x := rfl

def boundaryDyad (p : RegularBoundaryPair ι) : Operator ι :=
  normalizedDyad p.pre (postCovector p)

@[simp] theorem boundaryDyad_apply (p : RegularBoundaryPair ι) (x : State ι) :
    boundaryDyad p x = (pairing p.post x / overlap p) • p.pre := by
  rw [boundaryDyad, normalizedDyad_apply]
  rfl

@[simp] theorem boundaryDyad_pre (p : RegularBoundaryPair ι) :
    boundaryDyad p p.pre = p.pre :=
  normalizedDyad_self p.pre (postCovector p) p.overlap_ne

theorem boundaryDyad_compression (p : RegularBoundaryPair ι) (A : Operator ι) :
    boundaryDyad p * A * boundaryDyad p = weakValue p A • boundaryDyad p := by
  exact normalizedDyad_compression p.pre (postCovector p) A

theorem boundaryDyad_idempotent (p : RegularBoundaryPair ι) :
    boundaryDyad p * boundaryDyad p = boundaryDyad p :=
  normalizedDyad_idempotent p.pre (postCovector p) p.overlap_ne

theorem boundaryDyad_ker (p : RegularBoundaryPair ι) :
    (boundaryDyad p).ker = (postCovector p).ker :=
  normalizedDyad_ker p.pre (postCovector p) p.overlap_ne

@[simp] theorem weakValue_boundaryDyad (p : RegularBoundaryPair ι) :
    weakValue p (boundaryDyad p) = 1 := by
  unfold weakValue numerator
  rw [boundaryDyad_pre]
  exact div_self p.overlap_ne

theorem weakValue_finset_sum (p : RegularBoundaryPair ι)
    {κ : Type*} (s : Finset κ) (A : κ → Operator ι) :
    weakValue p (∑ k ∈ s, A k) = ∑ k ∈ s, weakValue p (A k) := by
  exact map_sum (weakValueLinear p) A s

def obliquePair : RegularBoundaryPair (Fin 2) where
  pre := ![1, 0]
  post := ![1, 1]
  overlap_ne := by norm_num [pairing, Fin.sum_univ_two]

def coordinateMatrix [DecidableEq ι] (A : Operator ι) : Matrix ι ι ℂ :=
  fun i j => A (Pi.single j 1) i

/-- The matrix of the normalized dyad, with the post-selection conjugated. -/
theorem boundaryDyad_matrix_apply [DecidableEq ι]
    (p : RegularBoundaryPair ι) (i j : ι) :
    coordinateMatrix (boundaryDyad p) i j =
      p.pre i * star (p.post j) / overlap p := by
  simp [coordinateMatrix, boundaryDyad_apply, pairing, Pi.single_apply,
    mul_div_assoc, mul_comm]

/-- On a common ray the normalization removes the post-selection scale.
This is the normalized self-outer-product matrix, not an arbitrary oblique
dyad. Regularity already excludes a zero scale. -/
theorem boundaryDyad_matrix_of_same_ray [DecidableEq ι]
    (p : RegularBoundaryPair ι) (c : ℂ) (hc : p.post = c • p.pre) (i j : ι) :
    coordinateMatrix (boundaryDyad p) i j =
      p.pre i * star (p.pre j) / pairing p.pre p.pre := by
  have hnonzero : star c * pairing p.pre p.pre ≠ 0 := by
    simpa [hc, pairing_smul_left] using p.overlap_ne
  have hstar : star c ≠ 0 := (mul_ne_zero_iff.mp hnonzero).1
  have hnorm : pairing p.pre p.pre ≠ 0 := (mul_ne_zero_iff.mp hnonzero).2
  rw [boundaryDyad_matrix_apply, overlap, hc, pairing_smul_left]
  simp only [Pi.smul_apply, smul_eq_mul, star_mul]
  field_simp

/-- A regular same-ray boundary dyad is Hermitian. Together with
`boundaryDyad_idempotent`, this is the orthogonal-projection case. -/
theorem boundaryDyad_self_adjoint_of_same_ray [DecidableEq ι]
    (p : RegularBoundaryPair ι) (c : ℂ) (hc : p.post = c • p.pre) :
    Matrix.conjTranspose (coordinateMatrix (boundaryDyad p)) =
      coordinateMatrix (boundaryDyad p) := by
  have hnorm : star (pairing p.pre p.pre) = pairing p.pre p.pre := by
    simp [pairing, star_sum, star_mul, mul_comm]
  ext i j
  simp only [Matrix.conjTranspose_apply,
    boundaryDyad_matrix_of_same_ray p c hc, star_div₀, star_mul, star_star, hnorm]

/-- A regular dyad is Hermitian exactly when both boundary directions lie
on the same complex ray. -/
theorem boundaryDyad_self_adjoint_iff_same_ray [DecidableEq ι]
    (p : RegularBoundaryPair ι) :
    Matrix.conjTranspose (coordinateMatrix (boundaryDyad p)) =
      coordinateMatrix (boundaryDyad p) ↔ ∃ c : ℂ, p.post = c • p.pre := by
  constructor
  · intro hs
    classical
    have hv : p.pre ≠ 0 := by
      intro hz
      exact p.overlap_ne (by simp [hz])
    obtain ⟨i, hi⟩ : ∃ i, p.pre i ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hv (funext hn)
    have hsi : star (p.pre i) ≠ 0 := by simpa using hi
    have ho := p.overlap_ne
    have hso : star (overlap p) ≠ 0 := by simp
    refine ⟨star (p.post i) * star (overlap p) /
      (overlap p * star (p.pre i)), ?_⟩
    funext j
    have he := congrArg star (congrArg (fun M : Matrix ι ι ℂ => M i j) hs)
    simp only [Matrix.conjTranspose_apply, boundaryDyad_matrix_apply,
      star_star, star_div₀, star_mul] at he
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [ho, hso, hsi] at he ⊢
    linear_combination -he
  · rintro ⟨c, hc⟩
    exact boundaryDyad_self_adjoint_of_same_ray p c hc

theorem obliquePair_matrix : coordinateMatrix (boundaryDyad obliquePair) =
    !![1, 1; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coordinateMatrix, boundaryDyad_apply, obliquePair, overlap, pairing,
      Fin.sum_univ_two, Pi.single_apply]

theorem obliquePair_not_self_adjoint :
    Matrix.conjTranspose (coordinateMatrix (boundaryDyad obliquePair)) ≠
      coordinateMatrix (boundaryDyad obliquePair) := by
  rw [obliquePair_matrix]
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  norm_num [Matrix.conjTranspose_apply] at h01

end InfoGeometry.Streaming.TwoBoundaryDyadCompression
