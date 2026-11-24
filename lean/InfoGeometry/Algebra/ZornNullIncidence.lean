/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornLeftInverse
import InfoGeometry.Algebra.ZornLeftDeterminant

/-!
# Null planes of the real Zorn left action

The carrier is the genuine eight-dimensional real split-octonion algebra.
A nonzero null element has a four-dimensional left-multiplication kernel,
and that kernel is maximal among subspaces on which the norm vanishes.
The zero element is deliberately excluded from the dimension-four theorem.

The dimension bound is constructive: projection onto `(a+b,v-w)` is injective
on every norm-null subspace.  Norm composition makes the range of a null left
action null; right Kirmse contraction makes its kernel null when the acting
element is nonzero. Rank-nullity then gives dimension four for each.

Kernel isotropy is a statement about two vectors in the kernel.  It must not
be confused with norm-polar orthogonality of the acting element and a kernel
vector. The final two counterexamples separate these incidence predicates.
-/

noncomputable section

namespace InfoGeometry.Algebra.ZornNullIncidence

open ZornLeftCAR

abbrev Z := ZornVectorMatrix ℝ

/-- The positive four-coordinate projection for the split norm. -/
def positiveProjection : Z →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun z := ![z.a + z.b, z.v 0 - z.w 0, z.v 1 - z.w 1, z.v 2 - z.w 2]
  map_add' x y := by
    funext i
    fin_cases i <;> simp [ZornVectorMatrix.add] <;> ring
  map_smul' r x := by
    funext i
    fin_cases i <;> simp [ZornVectorMatrix.smul] <;> ring

/-- A null element with zero positive projection is zero. This is the
definiteness calculation behind the dimension bound. -/
theorem eq_zero_of_norm_eq_zero_of_positiveProjection_eq_zero (z : Z)
    (hn : ZornVectorMatrix.norm z = 0) (hp : positiveProjection z = 0) : z = 0 := by
  have hab := congrFun hp 0
  have hvw0 := congrFun hp 1
  have hvw1 := congrFun hp 2
  have hvw2 := congrFun hp 3
  change z.a + z.b = 0 at hab
  change z.v 0 - z.w 0 = 0 at hvw0
  change z.v 1 - z.w 1 = 0 at hvw1
  change z.v 2 - z.w 2 = 0 at hvw2
  have hb : z.b = -z.a := by linarith
  have hw0 : z.w 0 = z.v 0 := by linarith
  have hw1 : z.w 1 = z.v 1 := by linarith
  have hw2 : z.w 2 = z.v 2 := by linarith
  simp only [ZornVectorMatrix.norm, ZornVec3.dot, Fin.sum_univ_three,
    hb, hw0, hw1, hw2] at hn
  have ha0 : z.a = 0 := by
    nlinarith [sq_nonneg (z.v 0), sq_nonneg (z.v 1), sq_nonneg (z.v 2)]
  have hv0 : z.v 0 = 0 := by
    nlinarith [sq_nonneg z.a, sq_nonneg (z.v 1), sq_nonneg (z.v 2)]
  have hv1 : z.v 1 = 0 := by
    nlinarith [sq_nonneg z.a, sq_nonneg (z.v 0), sq_nonneg (z.v 2)]
  have hv2 : z.v 2 = 0 := by
    nlinarith [sq_nonneg z.a, sq_nonneg (z.v 0), sq_nonneg (z.v 1)]
  ext i <;> (try fin_cases i) <;>
    simp [ZornVectorMatrix.zero, ha0, hb, hw0, hw1, hw2, hv0, hv1, hv2]

/-- Every norm-null real subspace has dimension at most four. -/
theorem nullSubmodule_finrank_le_four (W : Submodule ℝ Z)
    (hW : ∀ z ∈ W, ZornVectorMatrix.norm z = 0) :
    Module.finrank ℝ W ≤ 4 := by
  let f : W →ₗ[ℝ] (Fin 4 → ℝ) := positiveProjection.domRestrict W
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply eq_zero_of_norm_eq_zero_of_positiveProjection_eq_zero
    · exact hW _ (W.sub_mem x.property y.property)
    · change positiveProjection (x : Z) = positiveProjection (y : Z) at hxy
      rw [map_sub, hxy, sub_self]
  simpa using LinearMap.finrank_le_finrank_of_injective hf

/-- Every vector in the kernel of a nonzero left action is norm-null. -/
theorem norm_eq_zero_of_mem_leftKernel {x y : Z} (hx : x ≠ 0)
    (hy : y ∈ LinearMap.ker (leftMultiplication x)) :
    ZornVectorMatrix.norm y = 0 := by
  change ZornVectorMatrix.mul x y = ZornVectorMatrix.zero at hy
  have hk := ZornVectorMatrix.kirmse_right y x
  rw [hy, ZornVectorMatrix.zero_mul] at hk
  have hsmul : ZornVectorMatrix.norm y • x = 0 := hk.symm
  exact (smul_eq_zero.mp hsmul).resolve_right hx

/-- The range of multiplication by a null element is norm-null. -/
theorem norm_eq_zero_of_mem_leftRange {x y : Z}
    (hx : ZornVectorMatrix.norm x = 0)
    (hy : y ∈ LinearMap.range (leftMultiplication x)) :
    ZornVectorMatrix.norm y = 0 := by
  rcases hy with ⟨z, rfl⟩
  change ZornVectorMatrix.norm (ZornVectorMatrix.mul x z) = 0
  rw [ZornVectorMatrix.norm_mul, hx, zero_mul]

/-- Internal total isotropy of the kernel, expressed by norm polarization. -/
theorem leftKernel_polar_eq_zero {x y z : Z} (hx : x ≠ 0)
    (hy : y ∈ LinearMap.ker (leftMultiplication x))
    (hz : z ∈ LinearMap.ker (leftMultiplication x)) :
    ZornVectorMatrix.norm (y + z) - ZornVectorMatrix.norm y -
      ZornVectorMatrix.norm z = 0 := by
  rw [norm_eq_zero_of_mem_leftKernel hx
      ((LinearMap.ker (leftMultiplication x)).add_mem hy hz),
    norm_eq_zero_of_mem_leftKernel hx hy,
    norm_eq_zero_of_mem_leftKernel hx hz]
  simp only [sub_zero]

/-- The coordinate equivalence gives the actual carrier dimension. -/
theorem zorn_finrank : Module.finrank ℝ Z = 8 := by
  rw [ZornLeftDeterminant.coordinates.finrank_eq]
  simp [ZornLeftDeterminant.CoordinateIndex]

/-- The kernel of left multiplication by every nonzero null real split octonion has
dimension four; no trace-zero or nonzero-coordinate hypothesis is needed. -/
theorem leftKernel_finrank {x : Z} (hx : x ≠ 0)
    (hn : ZornVectorMatrix.norm x = 0) :
    Module.finrank ℝ (LinearMap.ker (leftMultiplication x)) = 4 := by
  let : FiniteDimensional ℝ Z :=
    FiniteDimensional.of_finrank_eq_succ zorn_finrank
  let kernelDim : ℕ := Module.finrank ℝ (LinearMap.ker (leftMultiplication x))
  let rangeDim : ℕ := Module.finrank ℝ (LinearMap.range (leftMultiplication x))
  change kernelDim = 4
  have hk : kernelDim ≤ 4 :=
    nullSubmodule_finrank_le_four (LinearMap.ker (leftMultiplication x))
      (fun y hy => norm_eq_zero_of_mem_leftKernel hx hy)
  have hr : rangeDim ≤ 4 :=
    nullSubmodule_finrank_le_four (LinearMap.range (leftMultiplication x))
      (fun y hy => norm_eq_zero_of_mem_leftRange hn hy)
  have hdim : rangeDim + kernelDim = 8 :=
    (LinearMap.finrank_range_add_finrank_ker (leftMultiplication x)).trans zorn_finrank
  omega

/-- The full range of a nonzero null left action also has dimension four. -/
theorem leftRange_finrank {x : Z} (hx : x ≠ 0)
    (hn : ZornVectorMatrix.norm x = 0) :
    Module.finrank ℝ (LinearMap.range (leftMultiplication x)) = 4 := by
  let : FiniteDimensional ℝ Z :=
    FiniteDimensional.of_finrank_eq_succ zorn_finrank
  have hdim := LinearMap.finrank_range_add_finrank_ker (leftMultiplication x)
  rw [leftKernel_finrank hx hn, zorn_finrank] at hdim
  omega

/-- Conjugate contraction places the conjugate left range in the left kernel
for every null element, including zero. -/
theorem conjugate_leftRange_le_leftKernel {x : Z}
    (hn : ZornVectorMatrix.norm x = 0) :
    LinearMap.range (leftMultiplication (ZornVectorMatrix.conj x)) ≤
      LinearMap.ker (leftMultiplication x) := by
  apply LinearMap.range_le_ker_iff.mpr
  change leftMultiplication x * leftMultiplication (ZornVectorMatrix.conj x) = 0
  rw [leftMultiplication_mul_conjugate, hn, zero_smul]

/-- For a nonzero null element, conjugate multiplication fills the entire
four-dimensional left kernel. The nonzero hypothesis is essential: at zero,
the range is zero and the kernel is the whole eight-dimensional carrier. -/
theorem conjugate_leftRange_eq_leftKernel {x : Z} (hx : x ≠ 0)
    (hn : ZornVectorMatrix.norm x = 0) :
    LinearMap.range (leftMultiplication (ZornVectorMatrix.conj x)) =
      LinearMap.ker (leftMultiplication x) := by
  let : FiniteDimensional ℝ Z :=
    FiniteDimensional.of_finrank_eq_succ zorn_finrank
  have hc : ZornVectorMatrix.conj x ≠ 0 := by
    intro h
    change ZornVectorMatrix.conj x = ZornVectorMatrix.zero at h
    apply hx
    change x = ZornVectorMatrix.zero
    simpa only [ZornVectorMatrix.conj_conj, ZornVectorMatrix.conj_zero] using
      congrArg ZornVectorMatrix.conj h
  have hnconj : ZornVectorMatrix.norm (ZornVectorMatrix.conj x) = 0 := by
    simpa only [ZornVectorMatrix.norm_conj] using hn
  apply Submodule.eq_of_le_of_finrank_eq (conjugate_leftRange_le_leftKernel hn)
  rw [leftRange_finrank hc hnconj, leftKernel_finrank hx hn]

/-- The null kernel is maximal among norm-null subspaces. -/
theorem leftKernel_maximal_null {x : Z} (hx : x ≠ 0)
    (hn : ZornVectorMatrix.norm x = 0) (W : Submodule ℝ Z)
    (hW : ∀ z ∈ W, ZornVectorMatrix.norm z = 0)
    (hle : LinearMap.ker (leftMultiplication x) ≤ W) :
    W = LinearMap.ker (leftMultiplication x) := by
  let : FiniteDimensional ℝ Z :=
    FiniteDimensional.of_finrank_eq_succ zorn_finrank
  apply (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  rw [leftKernel_finrank hx hn]
  exact nullSubmodule_finrank_le_four W hW

/-- The excluded zero element has an eight-dimensional left kernel. -/
theorem leftKernel_zero_finrank :
    Module.finrank ℝ (LinearMap.ker (leftMultiplication (0 : Z))) = 8 := by
  have hzero : leftMultiplication (0 : Z) = 0 := leftMultiplication.map_zero
  rw [hzero, LinearMap.ker_zero, finrank_top, zorn_finrank]

/-- Nullness and polar orthogonality do not imply zero-product incidence:
the null pole is a nonzero idempotent. -/
theorem null_polar_zero_nonzero_product :
    ∃ x y : Z, x ≠ 0 ∧ y ≠ 0 ∧
      ZornVectorMatrix.norm x = 0 ∧ ZornVectorMatrix.norm y = 0 ∧
      ZornVectorMatrix.norm (x + y) - ZornVectorMatrix.norm x -
        ZornVectorMatrix.norm y = 0 ∧ ZornVectorMatrix.mul x y ≠ 0 := by
  refine ⟨ZornVectorMatrix.E11, ZornVectorMatrix.E11, ?_⟩
  have he : (ZornVectorMatrix.E11 : Z) ≠ 0 := by
    intro h
    have ha := congrArg ZornVectorMatrix.a h
    norm_num [ZornVectorMatrix.E11, ZornVectorMatrix.zero] at ha
  refine ⟨he, he, ?_, ?_, ?_, ?_⟩
  · simp [ZornVectorMatrix.norm, ZornVectorMatrix.E11, ZornVec3.dot]
  · simp [ZornVectorMatrix.norm, ZornVectorMatrix.E11, ZornVec3.dot]
  · simp [ZornVectorMatrix.norm, ZornVectorMatrix.E11, ZornVectorMatrix.add,
      ZornVec3.dot]
  · simpa only [ZornVectorMatrix.E11_mul_E11] using he

/-- Zero-product incidence does not imply norm-polar orthogonality of the
two factors: the opposite null poles multiply to zero and polarize to one. -/
theorem null_product_zero_nonzero_polar :
    ∃ x y : Z, x ≠ 0 ∧ y ≠ 0 ∧
      ZornVectorMatrix.norm x = 0 ∧ ZornVectorMatrix.norm y = 0 ∧
      ZornVectorMatrix.mul x y = 0 ∧
      ZornVectorMatrix.norm (x + y) - ZornVectorMatrix.norm x -
        ZornVectorMatrix.norm y ≠ 0 := by
  refine ⟨ZornVectorMatrix.E11, ZornVectorMatrix.E22, ?_⟩
  have h11 : (ZornVectorMatrix.E11 : Z) ≠ 0 := by
    intro h
    have ha := congrArg ZornVectorMatrix.a h
    norm_num [ZornVectorMatrix.E11, ZornVectorMatrix.zero] at ha
  have h22 : (ZornVectorMatrix.E22 : Z) ≠ 0 := by
    intro h
    have hb := congrArg ZornVectorMatrix.b h
    norm_num [ZornVectorMatrix.E22, ZornVectorMatrix.zero] at hb
  refine ⟨h11, h22, ?_, ?_, ?_, ?_⟩
  · simp [ZornVectorMatrix.norm, ZornVectorMatrix.E11, ZornVec3.dot]
  · simp [ZornVectorMatrix.norm, ZornVectorMatrix.E22, ZornVec3.dot]
  · exact ZornVectorMatrix.E11_mul_E22
  · norm_num [ZornVectorMatrix.norm, ZornVectorMatrix.E11, ZornVectorMatrix.E22,
      ZornVectorMatrix.add, ZornVec3.dot]

end InfoGeometry.Algebra.ZornNullIncidence
