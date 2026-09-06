import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import InfoGeometry.Canonical.CStarAlgebraStateColimit

/-!
# Pullback of positive normalized functionals

Positive states are transported only along explicit star-algebra homomorphisms.
This file deliberately does not identify unrelated GNS or finite-operator
state carriers.
-/

noncomputable section

namespace InfoGeometry.Modular.PositiveStatePullback

open scoped ComplexOrder
open CStarStateColimit
open CStarStateColimit.Native

universe u

variable {A : Type u} {B : Type u}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def pullback (φ : PositiveState B) (f : A →⋆ₐ[ℂ] B) : PositiveState A :=
  PositiveLinearMap.mk₀
    (φ.toLinearMap.comp f.toLinearMap)
    (by
      intro a ha
      exact φ.map_nonneg
        (starAlgHom_map_nonneg (A := A) (B := B) f ha))

@[simp] theorem pullback_apply
    (φ : PositiveState B) (f : A →⋆ₐ[ℂ] B) (a : A) :
    pullback φ f a = φ (f a) := rfl

theorem pullback_star_mul_self_nonneg
    (φ : PositiveState B) (f : A →⋆ₐ[ℂ] B) (a : A) :
    0 ≤ (pullback φ f (star a * a)).re := by
  exact PositiveState.gns_state_pos (pullback φ f) a

theorem pullback_normalized
    (φ : PositiveState B) (f : A →⋆ₐ[ℂ] B)
    (hφ : φ (1 : B) = 1) :
    pullback φ f (1 : A) = 1 := by
  simpa using hφ

end InfoGeometry.Modular.PositiveStatePullback
