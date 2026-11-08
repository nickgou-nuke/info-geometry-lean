/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CuntzComplexStarBinaryGaugeDegreeZero
import InfoGeometry.Canonical.CuntzComplexStarBinaryWordPairSpanBridge

/-! The degree-zero projection onto the equal-length word core of the actual
binary complex-star Cuntz quotient. No positivity or KMS property is claimed.
-/
noncomputable section
namespace InfoGeometry.Algebra.CuntzComplexStarBinaryCoreProjection

open InfoGeometry.Algebra.CuntzIntegerGrading
open InfoGeometry.Algebra.CuntzComplexStarBinaryGaugeDegreeZero
open InfoGeometry.Algebra.CuntzComplexStarBinaryWordPairMultiplicationBridge
open InfoGeometry.Canonical.CuntzComplexStarBinaryWordPairSpanBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliTensorQuotientPrefixMeasureBridge

/-- The equal-length word core, as a submodule of the full quotient. -/
def core : Submodule ℂ Carrier :=
  Submodule.span ℂ {x | ∃ u v : List Bool,
    u.length = v.length ∧ complexStarWordPair u v = x}

/-- Extract the zero degree after applying the existing integer grading. -/
def projection : Carrier →ₗ[ℂ] Carrier := degreeZero.comp delta.toLinearMap

theorem projection_wordPair (u v : List Bool) :
    projection (complexStarWordPair u v) =
      if u.length = v.length then complexStarWordPair u v else 0 :=
  degreeZero_delta_wordPair u v

theorem projection_mem_core (x : Carrier) : projection x ∈ core := by
  have hx : x ∈ sourceWordPairSpan := by rw [sourceWordPair_span_eq_top]; trivial
  unfold sourceWordPairSpan at hx
  refine Submodule.span_induction (p := fun y _ => projection y ∈ core)
    ?_ ?_ ?_ ?_ hx
  · rintro y ⟨⟨u, v⟩, rfl⟩
    change projection (complexStarWordPair u v) ∈ core
    rw [projection_wordPair]
    split_ifs with h
    · exact Submodule.subset_span ⟨u, v, h, rfl⟩
    · exact core.zero_mem
  · simp
  · intro a b _ _ ha hb
    simpa using core.add_mem ha hb
  · intro c y _ hy
    simpa using core.smul_mem c hy

theorem projection_eq_self_of_mem {x : Carrier} (hx : x ∈ core) :
    projection x = x := by
  unfold core at hx
  refine Submodule.span_induction (p := fun y _ => projection y = y)
    ?_ ?_ ?_ ?_ hx
  · rintro y ⟨u, v, huv, rfl⟩
    simp [projection_wordPair, huv]
  · exact map_zero projection
  · intro a b _ _ ha hb
    simp [ha, hb]
  · intro c y _ hy
    simp [hy]

theorem projection_idempotent (x : Carrier) :
    projection (projection x) = projection x :=
  projection_eq_self_of_mem (projection_mem_core x)

theorem projection_one : projection 1 = 1 := by
  simpa [complexStarWordPair, complexStarWord] using projection_wordPair [] []

theorem projection_star (x : Carrier) : projection (star x) = star (projection x) := by
  have hx : x ∈ sourceWordPairSpan := by rw [sourceWordPair_span_eq_top]; trivial
  unfold sourceWordPairSpan at hx
  refine Submodule.span_induction
    (p := fun y _ => projection (star y) = star (projection y)) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨⟨u, v⟩, rfl⟩
    change projection (star (complexStarWordPair u v)) =
      star (projection (complexStarWordPair u v))
    have hs : ∀ a b, star (complexStarWordPair a b) = complexStarWordPair b a := by
      intro a b
      simp [complexStarWordPair, star_mul]
    rw [hs, projection_wordPair, projection_wordPair]
    by_cases h : u.length = v.length
    · simp [h, hs]
    · simp [h, Ne.symm h]
  · simp
  · intro a b _ _ ha hb
    simp [ha, hb]
  · intro c y _ hy
    simp [hy]

/-- The image is exactly the core, not merely contained in it. -/
theorem range_projection : LinearMap.range projection = core := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact projection_mem_core y
  · intro hx
    exact ⟨x, projection_eq_self_of_mem hx⟩

end InfoGeometry.Algebra.CuntzComplexStarBinaryCoreProjection
end
