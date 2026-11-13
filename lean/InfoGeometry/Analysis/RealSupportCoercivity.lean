/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.RealPositiveOperatorGap
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Support-projected coercivity of real positive operators

The carrier throughout is the full real endomorphism ring. The support is
constructed as the native orthogonal projection onto the complement of the
entire kernel, not an arbitrary idempotent satisfying `P*T=T`.

The spectral equivalence is finite-dimensional; it assumes no diagonal form
of its input. The orthonormal spectral theorem appears only in the proof.
The kernel obstruction and the declining sequence theorem need no finite
dimension. The latter is a sequence theorem, not an inductive-limit theorem.
-/

noncomputable section

namespace InfoGeometry.Analysis.RealSupportCoercivity

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A nonzero zero mode prevents every strictly positive ambient lower bound. -/
theorem not_positive_sub_identity_of_kernel (T : Module.End ℝ E)
    {x : E} (hx : x ≠ 0) (hTx : T x = 0) {c : ℝ} (hc : 0 < c) :
    ¬ (T - c • (1 : Module.End ℝ E)).IsPositive := by
  intro h
  have he := h.inner_nonneg_right x
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    hTx, zero_sub, inner_neg_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq] at he
  have hn : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have : 0 < c * ‖x‖ ^ 2 := mul_pos hc hn
  exact (not_le_of_gt this) (neg_nonneg.mp he)

/-- Positivity can be checked on a supplied orthonormal eigenbasis. The
operator is still the full native endomorphism; the basis is proof data. -/
theorem isPositive_iff_of_orthonormal_eigenbasis {ι : Type*} [Fintype ι]
    (T : Module.End ℝ E) (hT : T.IsSymmetric)
    (b : OrthonormalBasis ι ℝ E) (μ : ι → ℝ)
    (hb : ∀ i, T (b i) = μ i • b i) :
    T.IsPositive ↔ ∀ i, 0 ≤ μ i := by
  constructor
  · intro h i
    have he := h.inner_nonneg_left (b i)
    simpa only [hb i, real_inner_smul_left, real_inner_self_eq_norm_sq,
      b.norm_eq_one i, one_pow, mul_one] using he
  · intro hμ
    apply (LinearMap.isPositive_iff T).mpr
    refine ⟨hT, fun x => ?_⟩
    rw [← b.sum_inner_mul_inner (T x) x]
    apply Finset.sum_nonneg
    intro i _
    calc
      0 ≤ μ i * (inner ℝ (b i) x) ^ 2 := mul_nonneg (hμ i) (sq_nonneg _)
      _ = inner ℝ (T x) (b i) * inner ℝ (b i) x := by
        rw [hT x (b i), hb i, real_inner_smul_right, real_inner_comm x (b i)]
        rw [pow_two, mul_assoc]

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- The actual orthogonal support projection of the full real operator. -/
def supportProjection (T : Module.End ℝ E) : Module.End ℝ E :=
  (T.kerᗮ).starProjection.toLinearMap

/-- The range is exactly the orthogonal complement of the whole kernel. -/
theorem supportProjection_range (T : Module.End ℝ E) :
    (supportProjection T).range = T.kerᗮ :=
  Submodule.range_starProjection _

/-- The support projection has exactly the same kernel as the operator. -/
theorem supportProjection_ker (T : Module.End ℝ E) :
    (supportProjection T).ker = T.ker := by
  change ((T.kerᗮ).starProjection).ker = T.ker
  rw [Submodule.ker_starProjection, Submodule.orthogonal_orthogonal]

/-- The constructed support is idempotent. -/
theorem supportProjection_idempotent (T : Module.End ℝ E) :
    IsIdempotentElem (supportProjection T) := by
  exact congrArg ContinuousLinearMap.toLinearMap
    (T.kerᗮ).isIdempotentElem_starProjection

/-- The constructed support is symmetric with respect to the real inner product. -/
theorem supportProjection_isSymmetric (T : Module.End ℝ E) :
    (supportProjection T).IsSymmetric :=
  (T.kerᗮ).starProjection_isSymmetric

/-- Symmetry places the image of `T` in its actual support. -/
theorem supportProjection_mul (T : Module.End ℝ E) (hT : T.IsSymmetric) :
    supportProjection T * T = T := by
  ext x
  apply Submodule.starProjection_eq_self_iff.mpr
  apply (T.ker.mem_orthogonal (T x)).mpr
  intro y hy
  rw [← hT y x, show T y = 0 from hy, inner_zero_left]

/-- The support acts as zero on zero-eigenvalue vectors and as identity on
every vector with a nonzero eigenvalue. -/
theorem supportProjection_apply_eigenvector (T : Module.End ℝ E)
    (hT : T.IsSymmetric) {μ : ℝ} {x : E} (hx : T x = μ • x) :
    supportProjection T x = if μ = 0 then 0 else x := by
  classical
  by_cases hμ : μ = 0
  · simp only [hμ, ↓reduceIte]
    apply ((T.kerᗮ).starProjection_apply_eq_zero_iff).mpr
    apply T.ker.le_orthogonal_orthogonal
    change T x = 0
    simpa only [hμ, zero_smul] using hx
  · simp only [hμ, ↓reduceIte]
    apply Submodule.starProjection_eq_self_iff.mpr
    exact RealPositiveOperatorGap.eigenvector_mem_ker_orthogonal T hT hμ hx

/-- For every finite-dimensional positive real operator, positivity of the
quadratic gap defect is equivalent to the lower bound on its actual support.
This permits a nontrivial zero-mode kernel. -/
theorem gap_defect_positive_iff_support_bound (T : Module.End ℝ E)
    (hT : T.IsPositive) (c : ℝ) :
    (T * T - c • T).IsPositive ↔
      (T - c • supportProjection T).IsPositive := by
  classical
  let n := Module.finrank ℝ E
  let b := hT.isSymmetric.eigenvectorBasis (n := n) rfl
  let μ := hT.isSymmetric.eigenvalues (n := n) rfl
  have hb : ∀ i, T (b i) = μ i • b i :=
    hT.isSymmetric.apply_eigenvectorBasis rfl
  have hμ : ∀ i, 0 ≤ μ i := hT.nonneg_eigenvalues rfl
  have hd : (T * T - c • T).IsSymmetric :=
    (hT.isSymmetric.mul_of_commute hT.isSymmetric (Commute.refl T)).sub
      (hT.isSymmetric.smul (by simp))
  have hs : (T - c • supportProjection T).IsSymmetric :=
    hT.isSymmetric.sub ((supportProjection_isSymmetric T).smul (by simp))
  have hdb : ∀ i, (T * T - c • T) (b i) =
      (μ i ^ 2 - c * μ i) • b i := by
    intro i
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      hb i, map_smul, smul_smul, sub_smul, pow_two]
  have hsb : ∀ i, (T - c • supportProjection T) (b i) =
      (μ i - if μ i = 0 then 0 else c) • b i := by
    intro i
    rw [LinearMap.sub_apply, hb i, LinearMap.smul_apply,
      supportProjection_apply_eigenvector T hT.isSymmetric (hb i)]
    split_ifs with hi <;> simp [hi, sub_smul]
  rw [isPositive_iff_of_orthonormal_eigenbasis _ hd b _ hdb,
    isPositive_iff_of_orthonormal_eigenbasis _ hs b _ hsb]
  constructor
  · intro hg i
    by_cases hi : μ i = 0
    · simp [hi]
    · have hip : 0 < μ i := lt_of_le_of_ne (hμ i) (Ne.symm hi)
      have he : 0 ≤ μ i * (μ i - c) := by
        simpa only [mul_sub, mul_comm (μ i) c, ← pow_two] using hg i
      have hc := (mul_nonneg_iff_of_pos_left hip).mp he
      simpa [hi] using hc
  · intro hg i
    by_cases hi : μ i = 0
    · simp [hi]
    · have hc : 0 ≤ μ i - c := by simpa [hi] using hg i
      simpa only [mul_sub, mul_comm (μ i) c, ← pow_two] using mul_nonneg (hμ i) hc

/-- Equivalent statement in the native Loewner order on endomorphisms. -/
theorem gap_defect_nonneg_iff_support_le (T : Module.End ℝ E)
    (hT : T.IsPositive) (c : ℝ) :
    0 ≤ T * T - c • T ↔ c • supportProjection T ≤ T := by
  rw [LinearMap.nonneg_iff_isPositive, LinearMap.le_def]
  exact gap_defect_positive_iff_support_bound T hT c

end FiniteDimensional

/-! ## A positive sequence with no common support gap -/

/-- The positive scalar coefficient is a concrete sequence, not a tower map. -/
def decliningScale (k : ℕ) : ℝ := ((k : ℝ) + 1)⁻¹

/-- Scale an arbitrary full projection by the declining positive coefficient. -/
def decliningProjection (P : Module.End ℝ E) (k : ℕ) : Module.End ℝ E :=
  decliningScale k • P

theorem decliningScale_pos (k : ℕ) : 0 < decliningScale k := by
  unfold decliningScale
  positivity

/-- The exact polynomial defect of the scaled projection. -/
theorem decliningProjection_defect (P : Module.End ℝ E)
    (hP : P * P = P) (k : ℕ) (c : ℝ) :
    decliningProjection P k * decliningProjection P k - c • decliningProjection P k =
      (decliningScale k * (decliningScale k - c)) • P := by
  unfold decliningProjection
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, hP]
  rw [← sub_smul]
  congr 1
  rw [mul_sub, mul_comm (decliningScale k) c]

/-- Each stage is a positive operator. -/
theorem decliningProjection_positive (P : Module.End ℝ E)
    (hP : P.IsPositive) (k : ℕ) : (decliningProjection P k).IsPositive :=
  hP.smul_of_nonneg (decliningScale_pos k).le

/-- At its own positive scale, each stage has zero gap defect. -/
theorem decliningProjection_own_gap (P : Module.End ℝ E)
    (hP : P * P = P) (k : ℕ) :
    decliningProjection P k * decliningProjection P k -
      decliningScale k • decliningProjection P k = 0 := by
  rw [decliningProjection_defect P hP]
  simp

/-- No positive candidate is a common lower bound for the scalar coefficients. -/
theorem exists_decliningScale_lt {c : ℝ} (hc : 0 < c) :
    ∃ k : ℕ, decliningScale k < c := by
  obtain ⟨k, hk⟩ := exists_nat_gt c⁻¹
  refine ⟨k, ?_⟩
  have hk' : c⁻¹ < (k : ℝ) + 1 := lt_trans hk (by linarith)
  have hkpos : 0 < (k : ℝ) + 1 := by positivity
  unfold decliningScale
  simpa only [inv_inv] using
    (inv_lt_inv₀ hkpos (inv_pos.mpr hc)).mpr hk'

/-- Stagewise positive gaps do not imply a uniform gap for this sequence
of full, arbitrary nonzero positive idempotent operators. -/
theorem decliningProjection_no_uniform_gap (P : Module.End ℝ E)
    (hP : P * P = P) (hPpos : P.IsPositive) (hPne : P ≠ 0)
    {c : ℝ} (hc : 0 < c) :
    ∃ k : ℕ, ¬ (decliningProjection P k * decliningProjection P k -
      c • decliningProjection P k).IsPositive := by
  obtain ⟨k, hk⟩ := exists_decliningScale_lt hc
  refine ⟨k, ?_⟩
  rw [decliningProjection_defect P hP,
    hPpos.isPositive_smul_iff hPne]
  have hprod : decliningScale k * (decliningScale k - c) < 0 :=
    mul_neg_of_pos_of_neg (decliningScale_pos k) (sub_neg.mpr hk)
  exact not_le_of_gt hprod

end InfoGeometry.Analysis.RealSupportCoercivity
