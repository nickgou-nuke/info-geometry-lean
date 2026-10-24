/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CuntzComplexStarBinaryCoreProjection
import InfoGeometry.Algebra.CuntzComplexStarBinaryCoreMatrixUnits

/-! Integer-degree components in the actual quotient and star-square extraction. -/
noncomputable section
namespace InfoGeometry.Algebra.CuntzComplexStarHomogeneousComponents

open InfoGeometry.Physics.ComplexStarCuntzRedesign
open InfoGeometry.Algebra.CuntzIntegerGrading
open InfoGeometry.Algebra.CuntzComplexStarBinaryGaugeDegreeZero
open InfoGeometry.Algebra.CuntzComplexStarBinaryCoreProjection
open InfoGeometry.Algebra.CuntzComplexStarBinaryCoreMatrixUnits
open InfoGeometry.Algebra.CuntzComplexStarBinaryWordPairMultiplicationBridge
open InfoGeometry.Canonical.CuntzComplexStarBinaryWordPairSpanBridge

def component (d : ℤ) : Carrier →ₗ[ℂ] Carrier where
  toFun x := (delta x).coeff d
  map_add' x y := by simp
  map_smul' c x := by simp

theorem component_wordPair (d : ℤ) (u v : List Bool) :
    component d (complexStarWordPair u v) =
      if (u.length : ℤ) - v.length = d then complexStarWordPair u v else 0 := by
  change (delta (complexStarWordPair u v)).coeff d = _
  rw [delta_wordPair]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem delta_component (d : ℤ) (x : Carrier) :
    delta (component d x) = AddMonoidAlgebra.single d (component d x) := by
  have hx : x ∈ sourceWordPairSpan := by rw [sourceWordPair_span_eq_top]; trivial
  unfold sourceWordPairSpan at hx
  refine Submodule.span_induction (p := fun y _ =>
    delta (component d y) = AddMonoidAlgebra.single d (component d y)) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨⟨u, v⟩, rfl⟩
    change delta (component d (complexStarWordPair u v)) =
      AddMonoidAlgebra.single d (component d (complexStarWordPair u v))
    rw [component_wordPair]
    split_ifs with h
    · rw [delta_wordPair, h]
    · simp only [map_zero, AddMonoidAlgebra.single_zero]
  · simp only [map_zero, AddMonoidAlgebra.single_zero]
  · intro a b _ _ ha hb
    simp only [map_add, ha, hb, AddMonoidAlgebra.single_add]
  · intro c y _ hy
    simp only [map_smul, hy, AddMonoidAlgebra.smul_single]

theorem component_star (d : ℤ) (x : Carrier) :
    component d (star x) = star (component (-d) x) := by
  have hx : x ∈ sourceWordPairSpan := by rw [sourceWordPair_span_eq_top]; trivial
  unfold sourceWordPairSpan at hx
  refine Submodule.span_induction (p := fun y _ =>
    component d (star y) = star (component (-d) y)) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨⟨u, v⟩, rfl⟩
    change component d (star (complexStarWordPair u v)) =
      star (component (-d) (complexStarWordPair u v))
    rw [wordPair_star, component_wordPair, component_wordPair]
    have he : ((v.length : ℤ) - u.length = d) ↔
        ((u.length : ℤ) - v.length = -d) := by omega
    by_cases h : (v.length : ℤ) - u.length = d
    · simp [h, he.mp h, wordPair_star]
    · simp [h, mt he.mpr h]
  · simp
  · intro a b _ _ ha hb
    simp [ha, hb]
  · intro c y _ hy
    simp [hy]

theorem projection_star_mul (x : Carrier) :
    projection (star x * x) =
      (delta x).coeff.sum (fun _d a => star a * a) := by
  change (delta (star x * x)).coeff 0 = _
  rw [map_mul, AddMonoidAlgebra.coeff_mul_apply_right]
  apply Finsupp.sum_congr
  intro d _
  change component (0 - d) (star x) * (delta x).coeff d = _
  rw [component_star]
  simp [component]

end InfoGeometry.Algebra.CuntzComplexStarHomogeneousComponents
end
