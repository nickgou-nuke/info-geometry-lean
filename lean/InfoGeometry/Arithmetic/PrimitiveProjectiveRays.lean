import InfoGeometry.Arithmetic.PrimitiveSetsAbove
import Mathlib.Data.List.Basic

/-!
# InfoGeometry.Arithmetic.PrimitiveProjectiveRays

Projective-ray and count-profile sidecar for the arithmetic Mellin kernel.

This module deliberately stays separate from `PrimitiveSetsAbove` so the
primitive-set theorem spine can remain focused on the Erdos bound while this
file carries the count/ray vocabulary suggested by the modular and
projective-scale discussion.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimitiveProjectiveRays

/-- Arithmetic count profiles indexed by `ℕ`. -/
abbrev CountProfile := ℕ → ℝ

/-- Count profile induced by a finite sample of draws. -/
def sampleCountProfile (draws : List ℕ) : CountProfile :=
  fun n => (draws.count n : ℝ)

/-- Finite support of a sample profile. -/
def sampleSupport (draws : List ℕ) : Finset ℕ :=
  draws.toFinset

/-- Inverse arithmetic sampling channel `a ↦ a⁻¹`. -/
def arithmeticInverseSample (a : ℕ) : ℝ :=
  ((a : ℝ) : ℝ)⁻¹

/-- Logarithmic inverse channel. -/
def arithmeticInverseLogSample (a : ℕ) : ℝ :=
  Real.log (arithmeticInverseSample a)

theorem arithmeticInverseLogSample_eq_neg_log
    {a : ℕ} (_ha : 0 < a) :
    arithmeticInverseLogSample a = -Real.log (a : ℝ) := by
  unfold arithmeticInverseLogSample arithmeticInverseSample
  rw [Real.log_inv]

/--
Inverse-channel Mellin kernel, expressed through the logarithm of the inverse
sample.
-/
def inverseMellinKernel (a : ℕ) (s : ℝ) : ℝ :=
  if 1 < a then Real.exp (s * arithmeticInverseLogSample a) else 0

theorem inverseMellinKernel_eq_primitiveMellinKernel
    {a : ℕ} (ha : 1 < a) (s : ℝ) :
    inverseMellinKernel a s = primitiveMellinKernel a s := by
  rw [inverseMellinKernel, primitiveMellinKernel, if_pos ha, if_pos ha]
  rw [arithmeticInverseLogSample_eq_neg_log (Nat.lt_trans Nat.zero_lt_one ha)]
  congr 1
  ring

/-- Unnormalized arithmetic count weight against the primitive Mellin kernel. -/
def arithmeticWeight (counts : CountProfile) (s : ℝ) (n : ℕ) : ℝ :=
  counts n * primitiveMellinKernel n s

/-- Infinite arithmetic partition readout. -/
def arithmeticPartition (counts : CountProfile) (s : ℝ) : ℝ :=
  ∑' n : ℕ, arithmeticWeight counts s n

/-- Log-partition / arithmetic Massieu potential. -/
def arithmeticCountMassieuPotential (counts : CountProfile) (s : ℝ) : ℝ :=
  Real.log (arithmeticPartition counts s)

/-- Projectively normalized arithmetic ray, when the partition is nonzero. -/
def arithmeticNormalizedRay (counts : CountProfile) (s : ℝ) : CountProfile :=
  fun n => arithmeticWeight counts s n / arithmeticPartition counts s

/-- Positive projective-ray equivalence of count profiles. -/
def SamePositiveRay (counts₁ counts₂ : CountProfile) : Prop :=
  ∃ c : ℝ, 0 < c ∧ counts₂ = fun n => c * counts₁ n

theorem SamePositiveRay.refl (counts : CountProfile) :
    SamePositiveRay counts counts := by
  refine ⟨1, zero_lt_one, ?_⟩
  funext n
  simp

theorem SamePositiveRay.symm {counts₁ counts₂ : CountProfile}
    (h : SamePositiveRay counts₁ counts₂) :
    SamePositiveRay counts₂ counts₁ := by
  rcases h with ⟨c, hc, rfl⟩
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  funext n
  simp [hc.ne']

theorem SamePositiveRay.trans {counts₁ counts₂ counts₃ : CountProfile}
    (h₁₂ : SamePositiveRay counts₁ counts₂)
    (h₂₃ : SamePositiveRay counts₂ counts₃) :
    SamePositiveRay counts₁ counts₃ := by
  rcases h₁₂ with ⟨c₁₂, hc₁₂, rfl⟩
  rcases h₂₃ with ⟨c₂₃, hc₂₃, rfl⟩
  refine ⟨c₂₃ * c₁₂, mul_pos hc₂₃ hc₁₂, ?_⟩
  funext n
  ring

/-- Finite-support arithmetic weight. -/
def finiteArithmeticWeight (counts : CountProfile) (s : ℝ) (n : ℕ) : ℝ :=
  counts n * primitiveMellinKernel n s

lemma finiteArithmeticWeight_nonneg
    {counts : CountProfile} (hcounts : ∀ n, 0 ≤ counts n) (s : ℝ) (n : ℕ) :
    0 ≤ finiteArithmeticWeight counts s n := by
  unfold finiteArithmeticWeight
  exact mul_nonneg (hcounts n) (InfoGeometry.Arithmetic.primitiveMellinKernel_nonneg n s)

/-- Finite-support arithmetic partition. -/
def finiteArithmeticPartition (counts : CountProfile) (support : Finset ℕ) (s : ℝ) : ℝ :=
  Finset.sum support (fun n => finiteArithmeticWeight counts s n)

lemma finiteArithmeticPartition_nonneg
    {counts : CountProfile} (hcounts : ∀ n, 0 ≤ counts n) (support : Finset ℕ) (s : ℝ) :
    0 ≤ finiteArithmeticPartition counts support s := by
  unfold finiteArithmeticPartition
  exact Finset.sum_nonneg (fun n _hn => finiteArithmeticWeight_nonneg hcounts s n)

lemma finiteArithmeticPartition_pos_of_positive_count
    {counts : CountProfile} {support : Finset ℕ} {s : ℝ} {n : ℕ}
    (hcounts : ∀ n, 0 ≤ counts n) (hnS : n ∈ support) (hcount : 0 < counts n) (hn : 1 < n) :
    0 < finiteArithmeticPartition counts support s := by
  unfold finiteArithmeticPartition
  exact Finset.sum_pos'
    (fun m _hm => finiteArithmeticWeight_nonneg hcounts s m)
    ⟨n, hnS, by
      unfold finiteArithmeticWeight
      rw [InfoGeometry.Arithmetic.primitiveMellinKernel_eq_exp_neg_mul_log hn]
      exact mul_pos hcount (Real.exp_pos _)⟩

/-- Finite-support normalized projective ray. -/
def finiteArithmeticNormalizedRay (counts : CountProfile) (support : Finset ℕ) (s : ℝ) : CountProfile :=
  fun n => finiteArithmeticWeight counts s n / finiteArithmeticPartition counts support s

lemma finiteArithmeticNormalizedRay_nonneg
    {counts : CountProfile} {support : Finset ℕ} {s : ℝ}
    (hcounts : ∀ n, 0 ≤ counts n) (hZ : 0 < finiteArithmeticPartition counts support s) (n : ℕ) :
    0 ≤ finiteArithmeticNormalizedRay counts support s n := by
  unfold finiteArithmeticNormalizedRay
  exact div_nonneg (finiteArithmeticWeight_nonneg hcounts s n) (le_of_lt hZ)

theorem finiteArithmeticWeight_scale_counts
    (counts : CountProfile) (_support : Finset ℕ) (s c : ℝ) (n : ℕ) :
    finiteArithmeticWeight (fun k => c * counts k) s n
      = c * finiteArithmeticWeight counts s n := by
  unfold finiteArithmeticWeight
  ring

theorem finiteArithmeticPartition_scale_counts
    (counts : CountProfile) (support : Finset ℕ) (s c : ℝ) :
    finiteArithmeticPartition (fun k => c * counts k) support s
      = c * finiteArithmeticPartition counts support s := by
  unfold finiteArithmeticPartition finiteArithmeticWeight
  calc
    ∑ n ∈ support, (fun k => c * counts k) n * primitiveMellinKernel n s
      = ∑ n ∈ support, c * (counts n * primitiveMellinKernel n s) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          ring
    _ = c * ∑ n ∈ support, counts n * primitiveMellinKernel n s := by
          symm
          exact Finset.mul_sum support (fun n => counts n * primitiveMellinKernel n s) c

theorem finiteArithmeticNormalizedRay_scale_counts
    (counts : CountProfile) (support : Finset ℕ) (s c : ℝ)
    (hc : c ≠ 0) :
    finiteArithmeticNormalizedRay (fun k => c * counts k) support s
      = finiteArithmeticNormalizedRay counts support s := by
  ext n
  unfold finiteArithmeticNormalizedRay
  rw [finiteArithmeticWeight_scale_counts counts support s c n,
    finiteArithmeticPartition_scale_counts counts support s c]
  field_simp [hc]

theorem finiteArithmeticNormalizedRay_eq_of_samePositiveRay
    {counts₁ counts₂ : CountProfile} {support : Finset ℕ} {s : ℝ}
    (hray : SamePositiveRay counts₁ counts₂)
    (_hZ : finiteArithmeticPartition counts₁ support s ≠ 0) (n : ℕ) :
    finiteArithmeticNormalizedRay counts₂ support s n =
      finiteArithmeticNormalizedRay counts₁ support s n := by
  rcases hray with ⟨c, hc, rfl⟩
  simpa using congrFun
    (finiteArithmeticNormalizedRay_scale_counts counts₁ support s c hc.ne') n

theorem finiteArithmeticNormalizedRay_sum_eq_one
    (counts : CountProfile) (support : Finset ℕ) (s : ℝ)
    (hZ : finiteArithmeticPartition counts support s ≠ 0) :
    Finset.sum support (fun n => finiteArithmeticNormalizedRay counts support s n) = 1 := by
  unfold finiteArithmeticNormalizedRay
  rw [← Finset.sum_div]
  change finiteArithmeticPartition counts support s / finiteArithmeticPartition counts support s = 1
  rw [div_self hZ]

theorem finiteArithmeticWeight_eq_partition_mul_normalizedRay
    (counts : CountProfile) (support : Finset ℕ) (s : ℝ)
    (hZ : finiteArithmeticPartition counts support s ≠ 0) (n : ℕ) :
    finiteArithmeticWeight counts s n
      = finiteArithmeticPartition counts support s
          * finiteArithmeticNormalizedRay counts support s n := by
  unfold finiteArithmeticNormalizedRay
  field_simp [hZ]

/-- Sample-side finite partition readout. -/
def sampleArithmeticPartition (draws : List ℕ) (s : ℝ) : ℝ :=
  finiteArithmeticPartition (sampleCountProfile draws) (sampleSupport draws) s

lemma sampleCountProfile_nonneg (draws : List ℕ) (n : ℕ) :
    0 ≤ sampleCountProfile draws n := by
  unfold sampleCountProfile
  exact_mod_cast Nat.zero_le (draws.count n)

lemma sampleArithmeticPartition_nonneg (draws : List ℕ) (s : ℝ) :
    0 ≤ sampleArithmeticPartition draws s := by
  unfold sampleArithmeticPartition
  exact finiteArithmeticPartition_nonneg (sampleCountProfile_nonneg draws) (sampleSupport draws) s

/-- Sample-side normalized arithmetic shape. -/
def sampleArithmeticShape (draws : List ℕ) (s : ℝ) : CountProfile :=
  finiteArithmeticNormalizedRay (sampleCountProfile draws) (sampleSupport draws) s

/-- Finite unnormalized KL-type readout over a chosen support. -/
def finiteUnnormalizedKLDivergence
    (counts₁ counts₂ : CountProfile) (support : Finset ℕ) (s : ℝ) : ℝ :=
  Finset.sum support (fun n =>
    finiteArithmeticWeight counts₁ s n *
      Real.log
        (finiteArithmeticWeight counts₁ s n / finiteArithmeticWeight counts₂ s n))

/-- Finite shape KL readout over a chosen support. -/
def finiteShapeKLDivergence
    (counts₁ counts₂ : CountProfile) (support : Finset ℕ) (s : ℝ) : ℝ :=
  Finset.sum support (fun n =>
    finiteArithmeticNormalizedRay counts₁ support s n *
      Real.log
        (finiteArithmeticNormalizedRay counts₁ support s n
          / finiteArithmeticNormalizedRay counts₂ support s n))

/-- Scalar Weyl-scale KL contribution. -/
def scalarWeylKLDivergence (z₁ z₂ : ℝ) : ℝ :=
  z₁ * Real.log (z₁ / z₂)

/-- Scalar Itakura-Saito contribution on positive scales. -/
def scalarItakuraSaitoDivergence (z₁ z₂ : ℝ) : ℝ :=
  z₁ / z₂ - Real.log (z₁ / z₂) - 1

/--
Proof-carrying finite shape/scale KL packaging.

This avoids asserting a global closed-form identity without the positivity and
nonvanishing hypotheses needed to split logarithms safely at every active atom.
-/
structure FiniteShapeScaleKLDecomposition
    (counts₁ counts₂ : CountProfile) (support : Finset ℕ) (s : ℝ) where
  shapeKL : ℝ
  scalarKL : ℝ
  unnormalizedKL_eq_shape_plus_scalar :
    finiteUnnormalizedKLDivergence counts₁ counts₂ support s = shapeKL + scalarKL

theorem FiniteShapeScaleKLDecomposition.finiteUnnormalizedKL_eq_shape_plus_scalar
    {counts₁ counts₂ : CountProfile} {support : Finset ℕ} {s : ℝ}
    (D : FiniteShapeScaleKLDecomposition counts₁ counts₂ support s) :
    finiteUnnormalizedKLDivergence counts₁ counts₂ support s = D.shapeKL + D.scalarKL :=
  D.unnormalizedKL_eq_shape_plus_scalar

end InfoGeometry.Arithmetic.PrimitiveProjectiveRays
