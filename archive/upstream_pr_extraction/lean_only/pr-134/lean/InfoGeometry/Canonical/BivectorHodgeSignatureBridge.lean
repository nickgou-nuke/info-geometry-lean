import Mathlib

/-!
# Bivector Hodge-signature bridge

The square of a Hodge operator is signature data. This owner packages the
two finite algebraic cases separately: square `+1` gives a real involution
(the split-signature self-dual/anti-self-dual situation), while square `-1`
gives an internal complex structure (the Lorentzian bivector situation).
-/

namespace InfoGeometry.Canonical.BivectorHodgeSignatureBridge

noncomputable section

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

structure HodgeSquareData where
  star : E ≃ₗ[ℝ] E
  squareSign : ℝ
  squareSign_sq : squareSign * squareSign = 1
  star_square : ∀ x : E, star (star x) = squareSign • x

theorem star_square_one (H : HodgeSquareData (E := E))
    (hSign : H.squareSign = 1) (x : E) :
    H.star (H.star x) = x := by
  rw [H.star_square, hSign]
  simp

theorem star_square_neg_one (H : HodgeSquareData (E := E))
    (hSign : H.squareSign = -1) (x : E) :
    H.star (H.star x) = -x := by
  rw [H.star_square, hSign]
  simp

theorem split_hodge_is_involution (H : HodgeSquareData (E := E))
    (hSign : H.squareSign = 1) :
    Function.Involutive H.star := by
  intro x
  exact star_square_one H hSign x

theorem lorentzian_hodge_is_complex (H : HodgeSquareData (E := E))
    (hSign : H.squareSign = -1) :
    ∀ x : E, H.star (H.star x) = -x := by
  intro x
  exact star_square_neg_one H hSign x

def selfDualProjector (H : HodgeSquareData (E := E)) : E →ₗ[ℝ] E :=
  (1 / 2 : ℝ) • (LinearMap.id + H.star.toLinearMap)

def antiSelfDualProjector (H : HodgeSquareData (E := E)) : E →ₗ[ℝ] E :=
  (1 / 2 : ℝ) • (LinearMap.id - H.star.toLinearMap)

theorem selfDualProjector_idempotent (H : HodgeSquareData (E := E))
    (hSign : H.squareSign = 1) (x : E) :
    selfDualProjector H (selfDualProjector H x) = selfDualProjector H x := by
  simp [selfDualProjector, H.star_square, hSign, map_smul]
  module

theorem antiSelfDualProjector_idempotent (H : HodgeSquareData (E := E))
    (hSign : H.squareSign = 1) (x : E) :
    antiSelfDualProjector H (antiSelfDualProjector H x) = antiSelfDualProjector H x := by
  simp [antiSelfDualProjector, H.star_square, hSign, map_smul]
  module

theorem hodge_projectors_sum (H : HodgeSquareData (E := E)) (x : E) :
    selfDualProjector H x + antiSelfDualProjector H x = x := by
  simp [selfDualProjector, antiSelfDualProjector]
  module

theorem selfDualProjector_star (H : HodgeSquareData (E := E))
    (hSign : H.squareSign = 1) (x : E) :
    H.star (selfDualProjector H x) = selfDualProjector H x := by
  simp [selfDualProjector, H.star_square, hSign, map_smul]
  module

theorem antiSelfDualProjector_star (H : HodgeSquareData (E := E))
    (hSign : H.squareSign = 1) (x : E) :
    H.star (antiSelfDualProjector H x) = -antiSelfDualProjector H x := by
  simp [antiSelfDualProjector, H.star_square, hSign, map_smul]
  module

theorem hodge_projectors_orthogonal (H : HodgeSquareData (E := E))
    (hSign : H.squareSign = 1) (x : E) :
    selfDualProjector H (antiSelfDualProjector H x) = 0 := by
  simp [selfDualProjector, antiSelfDualProjector, H.star_square, hSign, map_smul]
  module

theorem anti_hodge_projectors_orthogonal (H : HodgeSquareData (E := E))
    (hSign : H.squareSign = 1) (x : E) :
    antiSelfDualProjector H (selfDualProjector H x) = 0 := by
  simp [selfDualProjector, antiSelfDualProjector, H.star_square, hSign, map_smul]
  module

end

end InfoGeometry.Canonical.BivectorHodgeSignatureBridge
