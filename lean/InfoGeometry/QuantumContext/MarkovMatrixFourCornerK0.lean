/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Matrix.Bilinear
import InfoGeometry.Algebra.FiniteProjectiveModuleGrothendieck
import InfoGeometry.QuantumContext.MarkovGroupInversePetzCorner

/-!
# Four-corner projective-module split for a Markov group inverse

The full matrix module decomposes under the four maps `X ↦ E * X * E`,
`X ↦ E * X * F`, `X ↦ F * X * E`, and `X ↦ F * X * F`, where `E` is the
Markov group-inverse range idempotent and `F = 1 - E`. Their ranges are finite
projective real modules and their classes sum in the repository's `K₀(ℝ)`.
This is a module decomposition, not a claim about `K₀(Matrix ι ι ℝ)`; the
idempotents need not be orthogonal for an inner product and no corner is
asserted nonzero.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovMatrixFourCornerK0

open InfoGeometry.Algebra.FiniteProjectiveModuleGrothendieck
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.QuantumContext.MarkovDrazin

local instance : AddCommGroup (K0 ℝ) := by
  change AddCommGroup (Grothendieck (ProjectiveModuleClass ℝ))
  infer_instance

variable {ι : Type} [Fintype ι] [DecidableEq ι]

abbrev MatrixCarrier := Matrix ι ι ℝ
abbrev MatrixEnd := Module.End ℝ (MatrixCarrier (ι := ι))

/-- The linear map `X ↦ A * X * B` on the full matrix module. -/
def cornerMap (A B : MatrixCarrier (ι := ι)) : MatrixEnd (ι := ι) :=
  (mulLeftLinearMap ι ℝ A).comp (mulRightLinearMap ι ℝ B)

omit [DecidableEq ι] in
@[simp]
theorem cornerMap_apply (A B X : MatrixCarrier (ι := ι)) :
    cornerMap A B X = A * (X * B) := by
  simp [cornerMap, mulLeftLinearMap, mulRightLinearMap]

omit [DecidableEq ι] in
theorem cornerMap_mul (A B C D : MatrixCarrier (ι := ι)) :
    cornerMap A B * cornerMap C D = cornerMap (A * C) (D * B) := by
  apply LinearMap.ext
  intro X
  simp [cornerMap, Module.End.mul_eq_comp, mulLeftLinearMap_apply,
    mulRightLinearMap_apply]
  noncomm_ring

/-- Labels for the four corners of a complementary pair of idempotents. -/
inductive Corner where
  | rangeRange
  | rangeKernel
  | kernelRange
  | kernelKernel
  deriving DecidableEq

private def cornerLeft (E F : MatrixCarrier (ι := ι)) : Corner → MatrixCarrier (ι := ι)
  | .rangeRange => E
  | .rangeKernel => E
  | .kernelRange => F
  | .kernelKernel => F

private def cornerRight (E F : MatrixCarrier (ι := ι)) : Corner → MatrixCarrier (ι := ι)
  | .rangeRange => E
  | .rangeKernel => F
  | .kernelRange => E
  | .kernelKernel => F

/-- The four Peirce endomorphisms of the full matrix module. -/
def cornerEnd (E F : MatrixCarrier (ι := ι)) (c : Corner) : MatrixEnd (ι := ι) :=
  cornerMap (cornerLeft E F c) (cornerRight E F c)

omit [DecidableEq ι] in
private theorem cornerMap_zero_left (B : MatrixCarrier (ι := ι)) :
    cornerMap (0 : MatrixCarrier (ι := ι)) B = 0 := by
  apply LinearMap.ext
  intro X
  simp [cornerMap]

omit [DecidableEq ι] in
private theorem cornerMap_zero_right (A : MatrixCarrier (ι := ι)) :
    cornerMap A (0 : MatrixCarrier (ι := ι)) = 0 := by
  apply LinearMap.ext
  intro X
  simp [cornerMap]

omit [DecidableEq ι] in
private theorem cornerEnd_mul
    (E F : MatrixCarrier (ι := ι)) (c d : Corner) :
    cornerEnd E F c * cornerEnd E F d =
      cornerMap (cornerLeft E F c * cornerLeft E F d)
        (cornerRight E F d * cornerRight E F c) := by
  rw [cornerEnd, cornerEnd, cornerMap_mul]

omit [DecidableEq ι] in
private theorem cornerEnd_idempotent
    (E F : MatrixCarrier (ι := ι)) (c : Corner)
    (hE : E * E = E) (hF : F * F = F) :
    cornerEnd E F c * cornerEnd E F c = cornerEnd E F c := by
  rw [cornerEnd_mul]
  cases c <;> simp [cornerEnd, cornerLeft, cornerRight, hE, hF]

omit [DecidableEq ι] in
private theorem cornerEnd_mul_eq_zero_of_ne
    (E F : MatrixCarrier (ι := ι)) (c d : Corner)
    (hEF : E * F = 0) (hFE : F * E = 0) (hcd : c ≠ d) :
    cornerEnd E F c * cornerEnd E F d = 0 := by
  rw [cornerEnd_mul]
  cases c <;> cases d
  all_goals simp only [cornerLeft, cornerRight]
  all_goals
    first
    | exact False.elim (hcd rfl)
    | rw [hEF]; exact cornerMap_zero_left _
    | rw [hEF]; exact cornerMap_zero_right _
    | rw [hFE]; exact cornerMap_zero_left _
    | rw [hFE]; exact cornerMap_zero_right _

/-- The four corner endomorphisms sum to the identity endomorphism. -/
private theorem cornerEnd_sum
    (E F : MatrixCarrier (ι := ι)) (hEF : E + F = 1) :
    cornerEnd E F .rangeRange + cornerEnd E F .rangeKernel +
      cornerEnd E F .kernelRange + cornerEnd E F .kernelKernel = 1 := by
  apply LinearMap.ext
  intro X
  simp only [cornerEnd, cornerMap, cornerLeft, cornerRight,
    Module.End.one_apply]
  change E * (X * E) + E * (X * F) + F * (X * E) + F * (X * F) = X
  calc
    _ = (E + F) * (X * (E + F)) := by noncomm_ring
    _ = 1 * (X * 1) := by rw [hEF]
    _ = X := by simp

omit [DecidableEq ι] in
private theorem cornerEnd_range_fixes
    (E F : MatrixCarrier (ι := ι)) (c : Corner)
    (hE : E * E = E) (hF : F * F = F)
    (x : LinearMap.range (cornerEnd E F c)) :
    cornerEnd E F c x.1 = x.1 := by
  obtain ⟨y, hy⟩ := x.2
  calc
    cornerEnd E F c x.1 = cornerEnd E F c (cornerEnd E F c y) := by rw [hy]
    _ = x.1 := by
      have h := congrArg (fun f : MatrixEnd (ι := ι) => f y)
        (cornerEnd_idempotent E F c hE hF)
      have h' : cornerEnd E F c (cornerEnd E F c y) = cornerEnd E F c y := by
        simpa [Module.End.mul_eq_comp] using h
      rw [h']
      exact hy

omit [DecidableEq ι] in
private theorem cornerEnd_annihilates_range
    (E F : MatrixCarrier (ι := ι)) (c d : Corner)
    (hEF : E * F = 0) (hFE : F * E = 0) (hcd : c ≠ d)
    (x : LinearMap.range (cornerEnd E F d)) :
    cornerEnd E F c x.1 = 0 := by
  obtain ⟨y, hy⟩ := x.2
  calc
    cornerEnd E F c x.1 = cornerEnd E F c (cornerEnd E F d y) := by rw [hy]
    _ = 0 := by
      have h := congrArg (fun f : MatrixEnd (ι := ι) => f y)
        (cornerEnd_mul_eq_zero_of_ne E F c d hEF hFE hcd)
      simpa [Module.End.mul_eq_comp] using h

omit [DecidableEq ι] in
private theorem cornerEnd_apply_range
    (E F : MatrixCarrier (ι := ι)) (c d : Corner)
    (hE : E * E = E) (hF : F * F = F)
    (hEF : E * F = 0) (hFE : F * E = 0)
    (x : LinearMap.range (cornerEnd E F d)) :
    cornerEnd E F c x.1 = if c = d then x.1 else 0 := by
  by_cases h : c = d
  · subst d
    simp [cornerEnd_range_fixes, hE, hF]
  · simp [h, cornerEnd_annihilates_range E F c d hEF hFE h x]

private def rangeInjection (e : MatrixEnd (ι := ι)) :
    LinearMap.range e →ₗ[ℝ] MatrixCarrier (ι := ι) :=
  (LinearMap.range e).subtype

private def rangeProjection (e : MatrixEnd (ι := ι)) (_he : e * e = e) :
    MatrixCarrier (ι := ι) →ₗ[ℝ] LinearMap.range e where
  toFun X := ⟨e X, ⟨X, rfl⟩⟩
  map_add' X Y := by apply Subtype.ext; simp
  map_smul' c X := by apply Subtype.ext; simp

omit [Fintype ι] [DecidableEq ι] in
private theorem rangeProjection_subtype (e : MatrixEnd (ι := ι))
    (he : e * e = e) :
    (rangeProjection e he).comp (rangeInjection e) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have hx : e x.1 = x.1 := by
    obtain ⟨y, hy⟩ := x.2
    calc
      e x.1 = e (e y) := by rw [hy]
      _ = x.1 := by
        have h := congrArg (fun f : MatrixEnd (ι := ι) => f y) he
        have h' : e (e y) = e y := by simpa [Module.End.mul_eq_comp] using h
        rw [h']
        exact hy
  exact hx

omit [DecidableEq ι] in
private theorem range_is_projective (e : MatrixEnd (ι := ι)) (he : e * e = e) :
    Module.Projective ℝ (LinearMap.range e) := by
  let i := rangeInjection e
  let r := rangeProjection e he
  have hri : r.comp i = LinearMap.id := rangeProjection_subtype e he
  exact @Module.Projective.of_split ℝ _ (LinearMap.range e) _ _
    (MatrixCarrier (ι := ι)) _ _ Module.Projective.of_free i r hri

omit [DecidableEq ι] in
private theorem range_is_finite (e : MatrixEnd (ι := ι)) :
    Module.Finite ℝ (LinearMap.range e) := inferInstance

def cornerRangeModule (E F : MatrixCarrier (ι := ι)) (c : Corner)
    (hE : E * E = E) (hF : F * F = F) : FiniteProjectiveModule ℝ :=
  ⟨ModuleCat.of ℝ (LinearMap.range (cornerEnd E F c)),
    range_is_finite (cornerEnd E F c),
    range_is_projective (cornerEnd E F c) (cornerEnd_idempotent E F c hE hF)⟩

def matrixModule (ι : Type) [Fintype ι] [DecidableEq ι] :
    FiniteProjectiveModule ℝ :=
  ⟨ModuleCat.of ℝ (Matrix ι ι ℝ), inferInstance, Module.Projective.of_free⟩

/-- The full matrix module is linearly equivalent to the product of its four
corner ranges. The inverse adds the four corner components. -/
private def fourCornerEquiv
    (E F : MatrixCarrier (ι := ι))
    (hE : E * E = E) (hF : F * F = F)
    (hEF : E * F = 0) (hFE : F * E = 0) (hEFsum : E + F = 1) :
    MatrixCarrier (ι := ι) ≃ₗ[ℝ]
      ((LinearMap.range (cornerEnd E F .rangeRange) ×
        LinearMap.range (cornerEnd E F .rangeKernel)) ×
       (LinearMap.range (cornerEnd E F .kernelRange) ×
        LinearMap.range (cornerEnd E F .kernelKernel))) where
  toFun X :=
    ((⟨cornerEnd E F .rangeRange X, ⟨X, rfl⟩⟩,
      ⟨cornerEnd E F .rangeKernel X, ⟨X, rfl⟩⟩),
     (⟨cornerEnd E F .kernelRange X, ⟨X, rfl⟩⟩,
      ⟨cornerEnd E F .kernelKernel X, ⟨X, rfl⟩⟩))
  invFun z := z.1.1.1 + z.1.2.1 + z.2.1.1 + z.2.2.1
  left_inv X := by
    change cornerEnd E F .rangeRange X + cornerEnd E F .rangeKernel X +
      cornerEnd E F .kernelRange X + cornerEnd E F .kernelKernel X = X
    have h := congrArg (fun f : MatrixEnd (ι := ι) => f X)
      (cornerEnd_sum E F hEFsum)
    exact h
  right_inv z := by
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        change cornerEnd E F .rangeRange
          (z.1.1.1 + z.1.2.1 + z.2.1.1 + z.2.2.1) = z.1.1.1
        simp only [map_add]
        rw [cornerEnd_apply_range E F .rangeRange .rangeRange hE hF hEF hFE z.1.1,
          cornerEnd_apply_range E F .rangeRange .rangeKernel hE hF hEF hFE z.1.2,
          cornerEnd_apply_range E F .rangeRange .kernelRange hE hF hEF hFE z.2.1,
          cornerEnd_apply_range E F .rangeRange .kernelKernel hE hF hEF hFE z.2.2]
        simp
      · apply Subtype.ext
        change cornerEnd E F .rangeKernel
          (z.1.1.1 + z.1.2.1 + z.2.1.1 + z.2.2.1) = z.1.2.1
        simp only [map_add]
        rw [cornerEnd_apply_range E F .rangeKernel .rangeRange hE hF hEF hFE z.1.1,
          cornerEnd_apply_range E F .rangeKernel .rangeKernel hE hF hEF hFE z.1.2,
          cornerEnd_apply_range E F .rangeKernel .kernelRange hE hF hEF hFE z.2.1,
          cornerEnd_apply_range E F .rangeKernel .kernelKernel hE hF hEF hFE z.2.2]
        simp
    · apply Prod.ext
      · apply Subtype.ext
        change cornerEnd E F .kernelRange
          (z.1.1.1 + z.1.2.1 + z.2.1.1 + z.2.2.1) = z.2.1.1
        simp only [map_add]
        rw [cornerEnd_apply_range E F .kernelRange .rangeRange hE hF hEF hFE z.1.1,
          cornerEnd_apply_range E F .kernelRange .rangeKernel hE hF hEF hFE z.1.2,
          cornerEnd_apply_range E F .kernelRange .kernelRange hE hF hEF hFE z.2.1,
          cornerEnd_apply_range E F .kernelRange .kernelKernel hE hF hEF hFE z.2.2]
        simp
      · apply Subtype.ext
        change cornerEnd E F .kernelKernel
          (z.1.1.1 + z.1.2.1 + z.2.1.1 + z.2.2.1) = z.2.2.1
        simp only [map_add]
        rw [cornerEnd_apply_range E F .kernelKernel .rangeRange hE hF hEF hFE z.1.1,
          cornerEnd_apply_range E F .kernelKernel .rangeKernel hE hF hEF hFE z.1.2,
          cornerEnd_apply_range E F .kernelKernel .kernelRange hE hF hEF hFE z.2.1,
          cornerEnd_apply_range E F .kernelKernel .kernelKernel hE hF hEF hFE z.2.2]
        simp
  map_add' X Y := by
    apply Prod.ext <;> apply Prod.ext <;> apply Subtype.ext <;> simp
  map_smul' c X := by
    apply Prod.ext <;> apply Prod.ext <;> apply Subtype.ext <;> simp

private theorem fourCornerClassAdd_eq_matrix
    (E F : MatrixCarrier (ι := ι))
    (hE : E * E = E) (hF : F * F = F)
    (hEF : E * F = 0) (hFE : F * E = 0) (hEFsum : E + F = 1) :
    Quotient.mk (moduleIsoSetoid ℝ)
        (directSum ℝ
          (directSum ℝ (cornerRangeModule E F .rangeRange hE hF)
            (cornerRangeModule E F .rangeKernel hE hF))
          (directSum ℝ (cornerRangeModule E F .kernelRange hE hF)
            (cornerRangeModule E F .kernelKernel hE hF))) =
      Quotient.mk (moduleIsoSetoid ℝ) (matrixModule ι) := by
  apply Quotient.sound
  exact ⟨(fourCornerEquiv E F hE hF hEF hFE hEFsum).symm.toModuleIso⟩

/-- The four full-matrix Peirce corner ranges sum to the full matrix module in
the existing projective-module `K₀(ℝ)`. The two off-diagonal corners are
included; this theorem makes no `K₀(Matrix ι ι ℝ)` claim. -/
theorem markovMatrixFourCornerK0_split
    [Nontrivial ι] (P G : Matrix ι ι ℝ)
    (hG : IsGroupInverse (1 - P) G) :
    k0Class ℝ (cornerRangeModule (markovRangeIdempotent P G)
      (1 - markovRangeIdempotent P G) .rangeRange
      (markovRangeIdempotent_idempotent P G hG)
      (markovRangeComplement_idempotent P G hG)) +
    k0Class ℝ (cornerRangeModule (markovRangeIdempotent P G)
      (1 - markovRangeIdempotent P G) .rangeKernel
      (markovRangeIdempotent_idempotent P G hG)
      (markovRangeComplement_idempotent P G hG)) +
    k0Class ℝ (cornerRangeModule (markovRangeIdempotent P G)
      (1 - markovRangeIdempotent P G) .kernelRange
      (markovRangeIdempotent_idempotent P G hG)
      (markovRangeComplement_idempotent P G hG)) +
    k0Class ℝ (cornerRangeModule (markovRangeIdempotent P G)
      (1 - markovRangeIdempotent P G) .kernelKernel
      (markovRangeIdempotent_idempotent P G hG)
      (markovRangeComplement_idempotent P G hG)) =
      k0Class ℝ (matrixModule ι) := by
  let E := markovRangeIdempotent P G
  let F := 1 - E
  have hE : E * E = E := by exact markovRangeIdempotent_idempotent P G hG
  have hF : F * F = F := by exact markovRangeComplement_idempotent P G hG
  have hEF : E * F = 0 := by exact markovRange_mul_kernelComplement_eq_zero P G hG
  have hFE : F * E = 0 := by exact markovKernelComplement_mul_range_eq_zero P G hG
  have hsum : E + F = 1 := by dsimp [E, F]; noncomm_ring
  let c₁ : ProjectiveModuleClass ℝ := Quotient.mk _ (cornerRangeModule E F .rangeRange hE hF)
  let c₂ : ProjectiveModuleClass ℝ := Quotient.mk _ (cornerRangeModule E F .rangeKernel hE hF)
  let c₃ : ProjectiveModuleClass ℝ := Quotient.mk _ (cornerRangeModule E F .kernelRange hE hF)
  let c₄ : ProjectiveModuleClass ℝ := Quotient.mk _ (cornerRangeModule E F .kernelKernel hE hF)
  let cM : ProjectiveModuleClass ℝ := Quotient.mk _ (matrixModule ι)
  have hclass := fourCornerClassAdd_eq_matrix E F hE hF hEF hFE hsum
  have hclass' : classAdd ℝ (classAdd ℝ c₁ c₂) (classAdd ℝ c₃ c₄) = cM := by
    change Quotient.mk _ (directSum ℝ
        (directSum ℝ (cornerRangeModule E F .rangeRange hE hF)
          (cornerRangeModule E F .rangeKernel hE hF))
        (directSum ℝ (cornerRangeModule E F .kernelRange hE hF)
          (cornerRangeModule E F .kernelKernel hE hF))) = _
    exact hclass
  change grothendieckMap (ProjectiveModuleClass ℝ) c₁ +
      grothendieckMap (ProjectiveModuleClass ℝ) c₂ +
      grothendieckMap (ProjectiveModuleClass ℝ) c₃ +
      grothendieckMap (ProjectiveModuleClass ℝ) c₄ =
    grothendieckMap (ProjectiveModuleClass ℝ) cM
  calc
    _ = (grothendieckMap (ProjectiveModuleClass ℝ) c₁ +
        grothendieckMap (ProjectiveModuleClass ℝ) c₂) +
        (grothendieckMap (ProjectiveModuleClass ℝ) c₃ +
        grothendieckMap (ProjectiveModuleClass ℝ) c₄) := by abel
    _ = grothendieckMap (ProjectiveModuleClass ℝ) (c₁ + c₂) +
        grothendieckMap (ProjectiveModuleClass ℝ) (c₃ + c₄) := by
          rw [(grothendieckMap (ProjectiveModuleClass ℝ)).map_add,
            (grothendieckMap (ProjectiveModuleClass ℝ)).map_add]
    _ = grothendieckMap (ProjectiveModuleClass ℝ)
        ((c₁ + c₂) + (c₃ + c₄)) :=
          ((grothendieckMap (ProjectiveModuleClass ℝ)).map_add
            (c₁ + c₂) (c₃ + c₄)).symm
    _ = grothendieckMap (ProjectiveModuleClass ℝ) cM :=
      congrArg (grothendieckMap (ProjectiveModuleClass ℝ)) hclass'

end InfoGeometry.QuantumContext.MarkovMatrixFourCornerK0

end
