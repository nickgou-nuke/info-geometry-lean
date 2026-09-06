import InfoGeometry.SuperMetriplectic.Axioms
import InfoGeometry.Meta.Architecture

/-!
# Native Schur/Drazin inverse bridge

The former owner converted scalar inverse records over `ℝ`.  The maintained
interface is generic in the noncommutative carrier: inverse laws are fields of
`OperatorSchurDrazinBlock`, and these lemmas merely expose them at the public
boundary.
-/

namespace InfoGeometry.SuperMetriplectic.InverseBridge

open InfoGeometry.Canonical.MoorePenrose
open InfoGeometry.Canonical.Drazin

variable {A : Type*} [Ring A] [StarRing A]

@[rep_depth operator]
theorem block_hasMoorePenroseInverse
    (B : OperatorSchurDrazinBlock A) :
    IsMoorePenroseInverse B.LΘΘ B.penroseElement :=
  B.penrose_is_inverse

@[rep_depth operator]
theorem block_hasDrazinInverse
    (B : OperatorSchurDrazinBlock A) :
    IsDrazinInverse B.LΘΘ B.drazinElement B.index :=
  B.drazin_is_inverse

@[rep_depth operator]
theorem block_drazinProjection_idempotent
    (B : OperatorSchurDrazinBlock A) :
    (B.LΘΘ * B.drazinElement) * (B.LΘΘ * B.drazinElement) =
      B.LΘΘ * B.drazinElement := by
  exact IsDrazinInverse.projection_is_idempotent B.drazin_is_inverse

@[rep_depth operator]
theorem block_drazinComplementaryProjection_idempotent
    (B : OperatorSchurDrazinBlock A) :
    (1 - B.LΘΘ * B.drazinElement) *
        (1 - B.LΘΘ * B.drazinElement) =
      1 - B.LΘΘ * B.drazinElement := by
  exact IsDrazinInverse.complementaryProjection_is_idempotent B.drazin_is_inverse

@[rep_depth operator]
theorem block_penroseRangeProjection_idempotent
    (B : OperatorSchurDrazinBlock A) :
    (B.LΘΘ * B.penroseElement) *
        (B.LΘΘ * B.penroseElement) =
      B.LΘΘ * B.penroseElement := by
  exact IsMoorePenroseInverse.rightProjector_idempotent B.penrose_is_inverse

end InfoGeometry.SuperMetriplectic.InverseBridge
