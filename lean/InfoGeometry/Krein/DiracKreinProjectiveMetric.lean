/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.DiracKreinFisherBridge
import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Krein.PontryaginSpace
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Tactic

/-!
# Real projective metric on the positive Dirac--Krein sheet

The Dirac conjugation `spectral_epsilon` defines the indefinite pairing on the
doubled real carrier.  Its positive fundamental sheet inherits a positive
metric.  This file constructs the real radial projection and its horizontal
metric on that sheet, and proves invariance under rescaling the ray
representative.  It does not identify the result with a complex or elliptic
Fubini--Study metric: the Hestenes phase axis exchanges the two Krein sheets.
-/

noncomputable section

namespace InfoGeometry.Krein.DiracKreinProjectiveMetric

open InfoGeometry.Krein
open InfoGeometry.Krein.DiracKreinFisherBridge

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "B" => KreinSpace.kreinInner (H := H₂)

/-- The original Hilbert pairing, packaged in the bilinear-form interface used
by `diracKreinBilin`. -/
def hilbertBilin : LinearMap.BilinForm ℝ E :=
  LinearMap.mk₂ ℝ
    (fun x y => inner ℝ x y)
    (by intro x y z; simp [inner_add_left])
    (by intro c x y; simp [real_inner_smul_left, smul_eq_mul])
    (by intro x y z; simp [inner_add_right])
    (by intro c x y; simp [real_inner_smul_right, smul_eq_mul])

/-- The Krein pairing used below is exactly the existing Dirac-conjugated
pairing, with the original Hilbert inner product as its positive form. -/
theorem diracKreinBilin_eq_kreinInner (u v : H₂) :
    diracKreinBilin hilbertBilin u v = B u v := by
  simp only [diracKreinBilin_apply, hilbertBilin, LinearMap.mk₂_apply]
  rw [InfoGeometry.Krein.krein_inner_prod_l2]
  rfl

/-- Krein-orthogonal projection onto the real ray spanned by `ψ`.
The denominator is the Dirac-conjugated Krein norm of the representative. -/
def radialProjection (ψ x : H₂) : H₂ :=
  (B ψ x / B ψ ψ) • ψ

/-- The real horizontal component relative to the radial line of `ψ`. -/
def horizontal (ψ x : H₂) : H₂ := x - radialProjection ψ x

/-- The unnormalized bilinear readout on horizontal representatives. -/
def horizontalMetric (ψ x y : H₂) : ℝ :=
  B (horizontal ψ x) (horizontal ψ y)

/-- The scale-free metric coefficient on the tangent class represented by `x`
and `y`.  The denominator is the Dirac-conjugated norm of the ray base. -/
def normalizedHorizontalMetric (ψ x y : H₂) : ℝ :=
  horizontalMetric ψ x y / B ψ ψ

theorem radialProjection_scale_invariant (ψ x : H₂) (a : ℝ) (ha : a ≠ 0)
    (hψ : B ψ ψ ≠ 0) :
    radialProjection (a • ψ) x = radialProjection ψ x := by
  unfold radialProjection
  rw [KreinSpace.kreinInner_smul_left, KreinSpace.kreinInner_smul_right]
  rw [KreinSpace.kreinInner_smul_left]
  rw [smul_smul]
  have hcoef : (a * B ψ x / (a * (a * B ψ ψ))) * a = B ψ x / B ψ ψ := by
    field_simp [ha, hψ]
  rw [hcoef]

theorem horizontal_scale_invariant (ψ x : H₂) (a : ℝ) (ha : a ≠ 0)
    (hψ : B ψ ψ ≠ 0) :
    horizontal (a • ψ) x = horizontal ψ x := by
  simp [horizontal, radialProjection_scale_invariant ψ x a ha hψ]

/-- The horizontal component is Krein-orthogonal to its base ray. -/
theorem horizontal_orthogonal (ψ x : H₂) (hψ : B ψ ψ ≠ 0) :
    B ψ (horizontal ψ x) = 0 := by
  change B ψ (x - (B ψ x / B ψ ψ) • ψ) = 0
  have hexpand : x - (B ψ x / B ψ ψ) • ψ =
      x + (-(B ψ x / B ψ ψ)) • ψ := by module
  rw [hexpand, KreinSpace.kreinInner_add_right,
    KreinSpace.kreinInner_smul_right]
  have hmul : (B ψ x / B ψ ψ) * B ψ ψ = B ψ x :=
    div_mul_cancel₀ (B ψ x) hψ
  simp only [neg_mul]
  linarith

/-- Horizontal projection kills the vertical (radial) direction. -/
theorem horizontal_radial (ψ : H₂) (a : ℝ) (hψ : B ψ ψ ≠ 0) :
    horizontal ψ (a • ψ) = 0 := by
  unfold horizontal radialProjection
  rw [KreinSpace.kreinInner_smul_right]
  have hmul : (a * B ψ ψ) / B ψ ψ = a := by
    field_simp [hψ]
  rw [hmul, sub_self]

/-- The projective horizontal metric is unchanged when its base vector is
rescaled by any nonzero real scalar. -/
theorem horizontalMetric_scale_invariant (ψ x y : H₂) (a : ℝ) (ha : a ≠ 0)
    (hψ : B ψ ψ ≠ 0) :
    horizontalMetric (a • ψ) x y = horizontalMetric ψ x y := by
  simp [horizontalMetric, horizontal_scale_invariant ψ x a ha hψ,
    horizontal_scale_invariant ψ y a ha hψ]

/-- Horizontal projection is real-linear in the tangent representative. -/
theorem horizontal_smul_right (ψ x : H₂) (a : ℝ) :
    horizontal ψ (a • x) = a • horizontal ψ x := by
  unfold horizontal radialProjection
  rw [KreinSpace.kreinInner_smul_right]
  simp only [smul_sub, smul_smul]
  congr 1
  ring_nf

/-- Horizontal projection is additive in the tangent representative. -/
theorem horizontal_add_right (ψ x y : H₂) (hψ : B ψ ψ ≠ 0) :
    horizontal ψ (x + y) = horizontal ψ x + horizontal ψ y := by
  unfold horizontal radialProjection
  rw [KreinSpace.kreinInner_add_right]
  have hcoeff : (B ψ x + B ψ y) / B ψ ψ =
      B ψ x / B ψ ψ + B ψ y / B ψ ψ := by
    field_simp [hψ]
  rw [hcoeff, add_smul]
  module

/-- Adding a vertical/radial tangent representative does not change its
horizontal class. -/
theorem horizontal_add_radial (ψ x : H₂) (a : ℝ)
    (hψ : B ψ ψ ≠ 0) :
    horizontal ψ (x + a • ψ) = horizontal ψ x := by
  rw [horizontal_add_right ψ x (a • ψ) hψ, horizontal_radial ψ a hψ,
    add_zero]

/-- Rescaling the ray base and its tangent representatives together leaves the
normalized metric coefficient unchanged.  This is the representative law
needed for a metric on real projective tangent classes. -/
theorem normalizedHorizontalMetric_scale_invariant (ψ x y : H₂)
    (a : ℝ) (ha : a ≠ 0) (hψ : B ψ ψ ≠ 0) :
    normalizedHorizontalMetric (a • ψ) (a • x) (a • y) =
      normalizedHorizontalMetric ψ x y := by
  unfold normalizedHorizontalMetric
  simp only [horizontalMetric]
  rw [horizontal_smul_right (a • ψ) x a,
    horizontal_smul_right (a • ψ) y a,
    horizontal_scale_invariant ψ x a ha hψ,
    horizontal_scale_invariant ψ y a ha hψ]
  simp only [KreinSpace.kreinInner_smul_left,
    KreinSpace.kreinInner_smul_right]
  field_simp [ha, hψ]

/-- The normalized readout depends only on horizontal tangent classes: adding
any radial component to either tangent representative leaves it unchanged. -/
theorem normalizedHorizontalMetric_radial_invariant (ψ x y : H₂)
    (a b : ℝ) (hψ : B ψ ψ ≠ 0) :
    normalizedHorizontalMetric ψ (x + a • ψ) (y + b • ψ) =
      normalizedHorizontalMetric ψ x y := by
  simp [normalizedHorizontalMetric, horizontalMetric,
    horizontal_add_radial ψ x a hψ,
    horizontal_add_radial ψ y b hψ]

/-- Additivity of the normalized horizontal form in its first tangent
representative. -/
theorem normalizedHorizontalMetric_add_left (ψ x y z : H₂)
    (hψ : B ψ ψ ≠ 0) :
    normalizedHorizontalMetric ψ (x + y) z =
      normalizedHorizontalMetric ψ x z + normalizedHorizontalMetric ψ y z := by
  unfold normalizedHorizontalMetric horizontalMetric
  rw [horizontal_add_right ψ x y hψ, KreinSpace.kreinInner_add_left]
  simp [add_div]

/-- Real homogeneity of the normalized horizontal form in its first tangent
representative. -/
theorem normalizedHorizontalMetric_smul_left (ψ x y : H₂) (a : ℝ) :
    normalizedHorizontalMetric ψ (a • x) y =
      a * normalizedHorizontalMetric ψ x y := by
  unfold normalizedHorizontalMetric horizontalMetric
  rw [horizontal_smul_right ψ x a, KreinSpace.kreinInner_smul_left]
  simp [div_eq_mul_inv, mul_assoc]

/-- Additivity of the normalized horizontal form in its second tangent
representative. -/
theorem normalizedHorizontalMetric_add_right (ψ x y z : H₂)
    (hψ : B ψ ψ ≠ 0) :
    normalizedHorizontalMetric ψ x (y + z) =
      normalizedHorizontalMetric ψ x y + normalizedHorizontalMetric ψ x z := by
  unfold normalizedHorizontalMetric horizontalMetric
  rw [horizontal_add_right ψ y z hψ, KreinSpace.kreinInner_add_right]
  simp [add_div]

/-- Real homogeneity of the normalized horizontal form in its second tangent
representative. -/
theorem normalizedHorizontalMetric_smul_right (ψ x y : H₂) (a : ℝ) :
    normalizedHorizontalMetric ψ x (a • y) =
      a * normalizedHorizontalMetric ψ x y := by
  unfold normalizedHorizontalMetric horizontalMetric
  rw [horizontal_smul_right ψ y a, KreinSpace.kreinInner_smul_right]
  simp [div_eq_mul_inv, mul_assoc]

/-- Symmetry of the real projective metric readout. -/
theorem horizontalMetric_symm (ψ x y : H₂) :
    horizontalMetric ψ x y = horizontalMetric ψ y x := by
  exact KreinSpace.kreinInner_symm _ _

/-- On the positive fundamental sheet, the Dirac--Krein norm is strictly
positive away from zero. -/
theorem positiveSheet_krein_norm_pos {ψ : H₂}
    (hψ : ψ ∈ KreinSpace.posSubspace H₂) (hψ0 : ψ ≠ 0) :
    0 < B ψ ψ :=
  KreinSpace.kreinInner_pos_on_posSubspace hψ hψ0

/-- Horizontal projection preserves the positive fundamental sheet. -/
theorem horizontal_mem_positiveSheet {ψ x : H₂}
    (hψ : ψ ∈ KreinSpace.posSubspace H₂)
    (hx : x ∈ KreinSpace.posSubspace H₂) :
    horizontal ψ x ∈ KreinSpace.posSubspace H₂ := by
  exact Submodule.sub_mem _ hx
    (Submodule.smul_mem _ (B ψ x / B ψ ψ) hψ)

/-- The horizontal metric is positive on every nonzero horizontal vector in
the positive fundamental sheet. -/
theorem horizontalMetric_pos {ψ x : H₂}
    (hψ : ψ ∈ KreinSpace.posSubspace H₂)
    (hx : x ∈ KreinSpace.posSubspace H₂)
    (hxhor : horizontal ψ x ≠ 0) :
    0 < horizontalMetric ψ x x := by
  unfold horizontalMetric
  exact KreinSpace.kreinInner_pos_on_posSubspace
    (horizontal_mem_positiveSheet hψ hx) hxhor

/-- The projective metric readout is nonnegative on the positive sheet. -/
theorem horizontalMetric_nonneg {ψ x : H₂}
    (hψ : ψ ∈ KreinSpace.posSubspace H₂)
    (hx : x ∈ KreinSpace.posSubspace H₂) :
    0 ≤ horizontalMetric ψ x x := by
  by_cases hzero : horizontal ψ x = 0
  · simp [horizontalMetric, hzero]
  · exact le_of_lt (horizontalMetric_pos hψ hx hzero)

/-- On a positive fundamental-sheet ray, the normalized horizontal metric is
nonnegative on tangent representatives in that sheet. -/
theorem normalizedHorizontalMetric_nonneg {ψ x : H₂}
    (hψ : ψ ∈ KreinSpace.posSubspace H₂) (hψ0 : ψ ≠ 0)
    (hx : x ∈ KreinSpace.posSubspace H₂) :
    0 ≤ normalizedHorizontalMetric ψ x x := by
  unfold normalizedHorizontalMetric
  have hden : 0 < B ψ ψ := positiveSheet_krein_norm_pos hψ hψ0
  exact div_nonneg (horizontalMetric_nonneg hψ hx) (le_of_lt hden)

/-- The normalized metric is strictly positive on a nonzero horizontal
positive-sheet tangent class. -/
theorem normalizedHorizontalMetric_pos {ψ x : H₂}
    (hψ : ψ ∈ KreinSpace.posSubspace H₂) (hψ0 : ψ ≠ 0)
    (hx : x ∈ KreinSpace.posSubspace H₂)
    (hxhor : horizontal ψ x ≠ 0) :
    0 < normalizedHorizontalMetric ψ x x := by
  unfold normalizedHorizontalMetric
  exact div_pos (horizontalMetric_pos hψ hx hxhor)
    (positiveSheet_krein_norm_pos hψ hψ0)

/-- Tangent representatives to the positive-sheet ray, modulo the radial
direction inside that same positive polarization. -/
abbrev positiveProjectiveTangent (ψ : H₂)
    (hψ : ψ ∈ KreinSpace.posSubspace H₂) (_hψ0 : ψ ≠ 0) :=
  KreinSpace.posSubspace H₂ ⧸
    Submodule.span ℝ { (⟨ψ, hψ⟩ : KreinSpace.posSubspace H₂) }

/-- The normalized horizontal form restricted to the positive fundamental
sheet. -/
def positiveSheetHorizontalForm (ψ : H₂)
    (hψ : ψ ∈ KreinSpace.posSubspace H₂) (hψ0 : ψ ≠ 0) :
    KreinSpace.posSubspace H₂ →ₗ[ℝ]
      KreinSpace.posSubspace H₂ →ₗ[ℝ] ℝ := by
  let hB : B ψ ψ ≠ 0 := ne_of_gt (positiveSheet_krein_norm_pos hψ hψ0)
  exact LinearMap.mk₂ ℝ
    (fun x y => normalizedHorizontalMetric ψ x y)
    (by
      intro x y z
      change normalizedHorizontalMetric ψ ((x : H₂) + y) z = _
      exact normalizedHorizontalMetric_add_left ψ x y z hB)
    (by
      intro a x y
      change normalizedHorizontalMetric ψ (a • (x : H₂)) y = _
      exact normalizedHorizontalMetric_smul_left ψ x y a)
    (by
      intro x y z
      change normalizedHorizontalMetric ψ x ((y : H₂) + z) = _
      exact normalizedHorizontalMetric_add_right ψ x y z hB)
    (by
      intro a x y
      change normalizedHorizontalMetric ψ x (a • (y : H₂)) = _
      exact normalizedHorizontalMetric_smul_right ψ x y a)

/-- The normalized positive-sheet horizontal form descends through the
radial subspace, yielding a bilinear form on the actual quotient tangent. -/
noncomputable def descendedPositiveSheetProjectiveMetric (ψ : H₂)
    (hψ : ψ ∈ KreinSpace.posSubspace H₂) (hψ0 : ψ ≠ 0) :
    positiveProjectiveTangent ψ hψ hψ0 →ₗ[ℝ]
      positiveProjectiveTangent ψ hψ hψ0 →ₗ[ℝ] ℝ := by
  let S : Submodule ℝ (KreinSpace.posSubspace H₂) :=
    Submodule.span ℝ { (⟨ψ, hψ⟩ : KreinSpace.posSubspace H₂) }
  let f := positiveSheetHorizontalForm ψ hψ hψ0
  have hB : B ψ ψ ≠ 0 := ne_of_gt (positiveSheet_krein_norm_pos hψ hψ0)
  have hleft : S ≤ f.ker := by
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    apply LinearMap.ext
    intro y
    change normalizedHorizontalMetric ψ (a • ψ) y = 0
    simp [normalizedHorizontalMetric, horizontalMetric,
      horizontal_radial ψ a hB]
  have hright : S ≤ f.flip.ker := by
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    apply LinearMap.ext
    intro y
    change normalizedHorizontalMetric ψ y (a • ψ) = 0
    simp [normalizedHorizontalMetric, horizontalMetric,
      horizontal_radial ψ a hB]
  exact f.liftQ₂ S S hleft hright

@[simp] theorem descendedPositiveSheetProjectiveMetric_mk
    (ψ : H₂) (hψ : ψ ∈ KreinSpace.posSubspace H₂) (hψ0 : ψ ≠ 0)
    (x y : KreinSpace.posSubspace H₂) :
    descendedPositiveSheetProjectiveMetric ψ hψ hψ0
      (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
        normalizedHorizontalMetric ψ x y := by
  rfl

/-- The descended projective tangent form is nonnegative on the positive
fundamental sheet. -/
theorem descendedPositiveSheetProjectiveMetric_nonneg
    (ψ : H₂) (hψ : ψ ∈ KreinSpace.posSubspace H₂) (hψ0 : ψ ≠ 0)
    (x : positiveProjectiveTangent ψ hψ hψ0) :
    0 ≤ descendedPositiveSheetProjectiveMetric ψ hψ hψ0 x x := by
  refine Submodule.Quotient.induction_on (p :=
    Submodule.span ℝ { (⟨ψ, hψ⟩ : KreinSpace.posSubspace H₂) }) x ?_
  intro x
  rw [descendedPositiveSheetProjectiveMetric_mk]
  exact normalizedHorizontalMetric_nonneg hψ hψ0 x.2

/-- The descended form is strictly positive on every nonzero real
projective tangent class.  Thus it is positive definite on the quotient
tangent space, rather than only nonnegative on representatives. -/
theorem descendedPositiveSheetProjectiveMetric_pos
    (ψ : H₂) (hψ : ψ ∈ KreinSpace.posSubspace H₂) (hψ0 : ψ ≠ 0)
    (x : positiveProjectiveTangent ψ hψ hψ0) (hx : x ≠ 0) :
    0 < descendedPositiveSheetProjectiveMetric ψ hψ hψ0 x x := by
  revert hx
  refine Submodule.Quotient.induction_on (p :=
    Submodule.span ℝ { (⟨ψ, hψ⟩ : KreinSpace.posSubspace H₂) }) x ?_
  intro x hx
  rw [descendedPositiveSheetProjectiveMetric_mk]
  apply normalizedHorizontalMetric_pos hψ hψ0 x.2
  intro hhor
  apply hx
  let S : Submodule ℝ (KreinSpace.posSubspace H₂) :=
    Submodule.span ℝ { (⟨ψ, hψ⟩ : KreinSpace.posSubspace H₂) }
  have hmem : x ∈ S := by
    apply Submodule.mem_span_singleton.mpr
    refine ⟨B ψ (x : H₂) / B ψ ψ, ?_⟩
    apply Subtype.ext
    have hzero : (x : H₂) - (B ψ (x : H₂) / B ψ ψ) • ψ = 0 := by
      simpa [horizontal, radialProjection] using hhor
    exact (sub_eq_zero.mp hzero).symm
  exact (Submodule.Quotient.mk_eq_zero S).2 hmem

end InfoGeometry.Krein.DiracKreinProjectiveMetric
