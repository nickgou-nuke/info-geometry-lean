/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Singular.MoorePenrose
import Mathlib

/-!
# Gramian inverse contracts and the true obliqueness defect

Existing Drazin and Moore--Penrose predicates are reused. The Gramian formula
is proved from a symmetric group-inverse witness (Drazin exponent one).
No existence theorem or general reverse-order law is assumed.
The projector defect detects obliqueness exactly; core/nilpotent operator
cross-Gramians need not detect it because multiplication by A loses directions.
-/
namespace InfoGeometry.Canonical.GramianInverseContracts
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Singular.MoorePenrose
open scoped BigOperators

section StarRing
variable {R : Type*} [Ring R] [StarRing R]

/-- Exact projector-level criterion, not an A-sandwiched surrogate. -/
theorem projector_cross_zero_iff (e : R) :
    e * e = e → (e * (1 - star e) = 0 ↔ star e = e) := by
  intro he
  constructor
  · intro h
    have h1 : e = e * star e := by
      have hh : e - e * star e = 0 := by simpa [mul_sub] using h
      exact sub_eq_zero.mp hh
    have h2 : star e = e * star e := by
      simpa only [star_mul, star_star] using congrArg star h1
    exact h2.trans h1.symm
  · intro hs
    rw [hs, mul_sub, mul_one, he, sub_self]

/-- The second ordered projector cross product has the same zero criterion. -/
theorem adjoint_projector_cross_zero_iff (e : R) (he : e * e = e) :
    star e * (1 - e) = 0 ↔ star e = e := by
  have hs : star e * star e = star e := by simpa using congrArg star he
  simpa only [star_star, eq_comm] using projector_cross_zero_iff (star e) hs

/-- Gram expansion: valid without Drazin or orthogonality hypotheses. -/
theorem gram_sum (c n : R) :
    (c + n) * star (c + n) =
      c * star c + n * star n + (c * star n + n * star c) ∧
    star (c + n) * (c + n) =
      star c * c + star n * n + (star c * n + star n * c) := by
  simp only [star_add]
  constructor <;> noncomm_ring

/-- Orthogonal spectral splitting suffices to kill both operator cross products. -/
theorem orthogonal_split_cross_zero (a e : R)
    (he : e * e = e) (hs : star e = e) (hc : e * a = a * e) :
    (a * e) * star (a * (1 - e)) = 0 ∧
    star (a * e) * (a * (1 - e)) = 0 := by
  have hEF : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have hF : (1 - e) * a = a * (1 - e) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hc]
  constructor
  · rw [star_mul, star_sub, star_one, hs]
    calc
      (a * e) * ((1 - e) * star a) = a * (e * (1 - e)) * star a := by
        simp only [mul_assoc]
      _ = 0 := by rw [hEF, mul_zero, zero_mul]
  · rw [← hc, ← hF, star_mul, hs]
    calc
      (star a * e) * ((1 - e) * a) = star a * (e * (1 - e)) * a := by
        simp only [mul_assoc]
      _ = 0 := by rw [hEF, mul_zero, zero_mul]

/-- The CMP sandwich uses the existing inverse witnesses. -/
def cmp (a d m : R) : R := (m * a) * d * (a * m)

theorem cmp_outer {a d m : R} {k : ℕ}
    (hd : IsDrazinInverse a d k) (hm : IsMoorePenroseInverse a m) :
    cmp a d m * a * cmp a d m = cmp a d m := by
  unfold cmp
  calc
    (m * a) * d * (a * m) * a * ((m * a) * d * (a * m)) =
        (m * a) * d * ((a * m * a) * m * a) * d * (a * m) := by
          simp only [mul_assoc]
    _ = (m * a) * d * a * d * (a * m) := by
      rw [hm.aba_eq_a, hm.aba_eq_a]
    _ = (m * a) * (d * a * d) * (a * m) := by simp only [mul_assoc]
    _ = (m * a) * d * (a * m) := by rw [hd.idempotent]

/-- Stronger and simpler inner formula: the result is exactly the Drazin core. -/
theorem cmp_recovers_core {a d m : R} {k : ℕ}
    (hd : IsDrazinInverse a d k) (hm : IsMoorePenroseInverse a m) :
    a * cmp a d m * a = fittingRegularPart a d := by
  unfold cmp fittingRegularPart projection
  calc
    a * ((m * a) * d * (a * m)) * a = (a * m * a) * d * (a * m * a) := by
      simp only [mul_assoc]
    _ = a * d * a := by rw [hm.aba_eq_a]
    _ = a * (a * d) := by rw [mul_assoc, ← hd.comm]

theorem cmp_support_idempotents {a d m : R} {k : ℕ}
    (hd : IsDrazinInverse a d k) (hm : IsMoorePenroseInverse a m) :
    IsIdempotentElem (a * cmp a d m) ∧ IsIdempotentElem (cmp a d m * a) := by
  have h := cmp_outer hd hm
  constructor
  · change (a * cmp a d m) * (a * cmp a d m) = _
    calc
      _ = a * (cmp a d m * a * cmp a d m) := by simp only [mul_assoc]
      _ = _ := by rw [h]
  · change (cmp a d m * a) * (cmp a d m * a) = _
    calc
      _ = (cmp a d m * a * cmp a d m) * a := by simp only [mul_assoc]
      _ = _ := by rw [h]
end StarRing

section RealMatrices
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma star_real_matrix (X : Matrix ι ι ℝ) : star X = X.transpose := by
  ext i j
  simp

lemma matrix_zero_of_gram_zero (X : Matrix ι ι ℝ)
    (h : X * X.transpose = 0) : X = 0 := by
  ext i j
  have hh := congrArg (fun M : Matrix ι ι ℝ => M i i) h
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply] at hh
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun r (_ : r ∈ Finset.univ) => mul_self_nonneg (X i r))).mp hh j (Finset.mem_univ j)
  exact mul_self_eq_zero.mp hz

/-- Gramian group-inverse formula, with each Penrose equation discharged. -/
theorem mp_from_left_gramian {A H : Matrix ι ι ℝ}
    (hcomm : (A * A.transpose) * H = H * (A * A.transpose))
    (houter : H * (A * A.transpose) * H = H)
    (hinner : (A * A.transpose) * H * (A * A.transpose) = A * A.transpose)
    (hs : H.transpose = H) :
    IsMoorePenroseInverse A (A.transpose * H) := by
  let G := A * A.transpose
  have hGs : G.transpose = G := by simp [G, Matrix.transpose_mul]
  have hEs : (G * H).transpose = G * H := by
    rw [Matrix.transpose_mul, hs, hGs]
    exact hcomm.symm
  have hz : (1 - G * H) * G = 0 := by
    rw [sub_mul, one_mul, hinner, sub_self]
  have hXA : (1 - G * H) * A = 0 := by
    apply matrix_zero_of_gram_zero
    rw [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one, hEs]
    calc
      ((1 - G * H) * A) * (A.transpose * (1 - G * H)) =
          ((1 - G * H) * G) * (1 - G * H) := by dsimp [G]; simp only [mul_assoc]
      _ = 0 := by rw [hz, zero_mul]
  have hAMA : A * (A.transpose * H) * A = A := by
    have h : A - (G * H) * A = 0 := by simpa only [sub_mul, one_mul] using hXA
    have he := (sub_eq_zero.mp h).symm
    simpa only [G, mul_assoc] using he
  refine ⟨hAMA, ?_, ?_, ?_⟩
  · calc
      (A.transpose * H) * A * (A.transpose * H) =
          A.transpose * (H * (A * A.transpose) * H) := by simp only [mul_assoc]
      _ = A.transpose * H := by rw [houter]
  · rw [star_real_matrix]
    simpa only [G, mul_assoc] using hEs
  · rw [star_real_matrix]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hs, mul_assoc]

/-- An explicitly symmetric index-one Drazin witness supplies the Gramian contract. -/
theorem mp_from_left_gramian_drazin_one {A H : Matrix ι ι ℝ}
    (h : IsDrazinInverse (A * A.transpose) H 1) (hs : H.transpose = H) :
    IsMoorePenroseInverse A (A.transpose * H) := by
  apply mp_from_left_gramian h.comm h.idempotent ?_ hs
  calc
    (A * A.transpose) * H * (A * A.transpose) =
        ((A * A.transpose) * (A * A.transpose)) * H := by
      rw [mul_assoc, ← h.comm, ← mul_assoc]
    _ = A * A.transpose := by simpa [pow_succ] using h.power

/-- Vanishing operator cross-Gramians do not characterize projector orthogonality. -/
theorem oblique_idempotent_counterexample :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 0]
    IsDrazinInverse A A 1 ∧
    (A * A).transpose ≠ A * A ∧
    A * (1 - A * A) = 0 ∧
    (A * (A * A)) * (A * (1 - A * A)).transpose = 0 ∧
    (A * (A * A)).transpose * (A * (1 - A * A)) = 0 := by
  dsimp only
  have hAA : (!![1, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 1; 0, 0] =
      !![1, 1; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨IsDrazinInverse.of_idempotent hAA, ?_, ?_, ?_, ?_⟩
  · rw [hAA]
    intro he
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) he
    norm_num [Matrix.transpose_apply] at hh
  · rw [hAA, mul_sub, mul_one, hAA, sub_self]
  · rw [hAA, mul_sub, mul_one, hAA, sub_self, Matrix.transpose_zero, mul_zero]
  · rw [hAA, mul_sub, mul_one, hAA, sub_self, mul_zero]
/-- Commutation of the two Gramians is weaker than normality of A. -/
theorem commuting_gramians_not_normal :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
    let G := A * A.transpose
    let H := A.transpose * A
    G * H = H * G ∧ G ≠ H := by
  dsimp only
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.transpose_apply, Fin.sum_univ_two]
  · intro h
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    norm_num [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.transpose_apply, Fin.sum_univ_two] at he

end RealMatrices
end InfoGeometry.Canonical.GramianInverseContracts
