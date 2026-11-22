/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornColorGL31Obstruction

/-! Strengthen the non-faithfulness obstruction to an explicit kernel
witness. The obstruction is the nonzero even double bracket detected by the
noncentral odd bracket in `gl(3|1)`. -/
noncomputable section

namespace InfoGeometry.Algebra.ZornColorOperatorCoordinates

open InfoGeometry.Canonical.GLSupermatrixGradedLie
open ZornVectorMatrix

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- Any linear map that sends the full odd component into the raw CAR odd
space and preserves homogeneous brackets kills a specific nonzero element.
Thus the obstruction yields a kernel vector, not just an injectivity
contradiction. -/
theorem bracket_map_has_explicit_nonzero_kernel
    (F : SuperMatrix 3 1 R →ₗ[R] Op R)
    (hodd : ∀ X, IsHomogeneous .odd X → F X ∈ oddPart)
    (hbracket : ∀ (p q : Parity) (X Y : SuperMatrix 3 1 R),
      IsHomogeneous p X → IsHomogeneous q Y →
      F (ringSuperbracket p q X Y) = ringSuperbracket p q (F X) (F Y)) :
    ∃ K : SuperMatrix 3 1 R, K ≠ 0 ∧ F K = 0 := by
  obtain ⟨X, Y, Z, hx, hy, hz, hK⟩ := gl31_odd_bracket_noncentral (R := R)
  let K := ringSuperbracket .even .even (ringSuperbracket .odd .odd X Y) Z
  have hinner : IsHomogeneous .even (ringSuperbracket .odd .odd X Y) := by
    simpa only [Parity.odd_add_odd, superbracket_eq_ringSuperbracket] using
      superbracket_preserves_grading .odd .odd X Y hx hy
  refine ⟨K, hK, ?_⟩
  change F (ringSuperbracket .even .even
    (ringSuperbracket .odd .odd X Y) Z) = 0
  rw [hbracket .even .even _ Z hinner hz,
    hbracket .odd .odd X Y hx hy]
  change (F X * F Y + F Y * F X) * F Z -
    F Z * (F X * F Y + F Y * F X) = 0
  exact sub_eq_zero.mpr (odd_bracket_central (hodd X hx) (hodd Y hy) (F Z)).eq

end InfoGeometry.Algebra.ZornColorOperatorCoordinates
end
