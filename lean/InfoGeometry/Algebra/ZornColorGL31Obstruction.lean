/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornColorOddDerived

/-! # Why the raw CAR odd space is not the odd space of gl(3|1)

A genuine obstruction to every faithful homogeneous-bracket-preserving map,
not merely failure of one chosen labeling of generators. The domain is the
existing native `SuperMatrix 3 1 R`; the target is the actual Zorn endomorphism
algebra. The proof uses centrality of every CAR odd bracket and an explicit
noncentral odd bracket in gl(3|1).
-/
noncomputable section
namespace InfoGeometry.Algebra.ZornColorOperatorCoordinates
open InfoGeometry.Canonical.GLSupermatrixGradedLie
variable {R : Type*} [CommRing R] [Nontrivial R]

/-- In gl(3|1), [e_{0,3},e_{3,1}]_+ = e_{0,1}, which does not commute with e_{0,0}. -/
theorem gl31_odd_bracket_noncentral :
    ∃ X Y Z : SuperMatrix 3 1 R,
      IsHomogeneous .odd X ∧ IsHomogeneous .odd Y ∧ IsHomogeneous .even Z ∧
      ringSuperbracket .even .even (ringSuperbracket .odd .odd X Y) Z ≠ 0 := by
  let X : SuperMatrix 3 1 R := oddMatrix (Matrix.single 0 0 1) 0
  let Y : SuperMatrix 3 1 R := oddMatrix 0 (Matrix.single 0 1 1)
  let Z : SuperMatrix 3 1 R := evenMatrix (Matrix.single 0 0 1) 0
  refine ⟨X, Y, Z, ⟨_, _, rfl⟩, ⟨_, _, rfl⟩, ⟨_, _, rfl⟩, ?_⟩
  intro h
  have ht := congrArg (fun A : SuperMatrix 3 1 R => A (.inl 0) (.inl 1)) h
  simp [ringSuperbracket, X, Y, Z, oddMatrix, evenMatrix, Matrix.fromBlocks,
    Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single] at ht

/-- No faithful gl(3|1) representation can send its entire odd component into
this six-dimensional raw CAR odd space while preserving homogeneous brackets. -/
theorem not_faithful_gl31_with_CAR_odd
    (F : SuperMatrix 3 1 R →ₗ[R] Op R)
    (hodd : ∀ X, IsHomogeneous .odd X → F X ∈ oddPart)
    (hbracket : ∀ (p q : Parity) (X Y : SuperMatrix 3 1 R),
      IsHomogeneous p X → IsHomogeneous q Y →
      F (ringSuperbracket p q X Y) = ringSuperbracket p q (F X) (F Y)) :
    ¬ Function.Injective F := by
  intro hinj
  obtain ⟨X, Y, Z, hx, hy, hz, hne⟩ := gl31_odd_bracket_noncentral (R := R)
  have hb : IsHomogeneous .even (ringSuperbracket .odd .odd X Y) := by
    simpa only [Parity.odd_add_odd, superbracket_eq_ringSuperbracket] using
      superbracket_preserves_grading .odd .odd X Y hx hy
  apply hne
  apply hinj
  rw [hbracket .even .even _ Z hb hz, map_zero, hbracket .odd .odd X Y hx hy]
  change (F X * F Y + F Y * F X) * F Z - F Z * (F X * F Y + F Y * F X) = 0
  exact sub_eq_zero.mpr (odd_bracket_central (hodd X hx) (hodd Y hy) (F Z)).eq

/-- A classical existential kernel form of the noninjectivity obstruction:
every homogeneous-bracket-preserving linear map into the raw CAR odd sector
kills some nonzero element. This theorem does not identify that element. -/
theorem exists_nonzero_kernel_of_homogeneous_bracket_map_to_CAR_odd
    (F : SuperMatrix 3 1 R →ₗ[R] Op R)
    (hodd : ∀ X, IsHomogeneous .odd X → F X ∈ oddPart)
    (hbracket : ∀ (p q : Parity) (X Y : SuperMatrix 3 1 R),
      IsHomogeneous p X → IsHomogeneous q Y →
      F (ringSuperbracket p q X Y) = ringSuperbracket p q (F X) (F Y)) :
    ∃ X, X ≠ 0 ∧ F X = 0 := by
  by_contra h
  have hzero : ∀ X, F X = 0 → X = 0 := by
    intro X hFX
    by_contra hX
    exact h ⟨X, hX, hFX⟩
  have hinj : Function.Injective F := by
    intro X Y hXY
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hXY, sub_self]
  exact (not_faithful_gl31_with_CAR_odd F hodd hbracket) hinj

end InfoGeometry.Algebra.ZornColorOperatorCoordinates
