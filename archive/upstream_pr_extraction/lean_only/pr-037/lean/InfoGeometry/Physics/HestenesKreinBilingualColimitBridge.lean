import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Constructions
import InfoGeometry.Physics.HestenesKreinBilingualCarrier
import InfoGeometry.Arithmetic.CyclotomicFiveNPotentGaloisBridge

/-!
# Hestenes--Krein bilingual actions on native filtered colimits

This owner keeps the replacement for an analytic two-sided carrier entirely
inside Mathlib's native `RingCat` filtered colimit.  The colimit carrier is
still only an algebraic carrier: no norm completion, Hilbert structure, or
Morita equivalence is asserted here.
-/

namespace InfoGeometry.Physics.HestenesKreinBilingualColimitBridge

open CategoryTheory CategoryTheory.Limits

universe u

variable {J : Type u} [Category.{u} J] [IsFiltered J]
variable (F : J ⥤ RingCat.{u}) [HasColimit F]

noncomputable section

abbrev ColimitCarrier := (colimit F : RingCat.{u})

theorem colimit_bilingual_left_right_commute
    (a x : ColimitCarrier F) (b : (ColimitCarrier F)ᵐᵒᵖ) :
    bilingualLeftAction a (bilingualRightOppositeAction x b) =
      bilingualRightOppositeAction (bilingualLeftAction a x) b := by
  exact InfoGeometry.Physics.bilingual_left_right_commute a x b

theorem colimit_bilingual_left_assoc
    (a₁ a₂ x : ColimitCarrier F) :
    bilingualLeftAction a₁ (bilingualLeftAction a₂ x) =
      bilingualLeftAction (a₁ * a₂) x := by
  exact InfoGeometry.Physics.bilingualLeftAction_assoc a₁ a₂ x

theorem colimit_ι_bilingual_left
    (j : J) (a x : F.obj j) :
    (colimit.ι F j).hom (bilingualLeftAction a x) =
      bilingualLeftAction ((colimit.ι F j).hom a) ((colimit.ι F j).hom x) := by
  simp [InfoGeometry.Physics.bilingualLeftAction]

theorem colimit_ι_bilingual_left_right_commute
    (j : J) (a x : F.obj j) (b : (F.obj j)ᵐᵒᵖ) :
    bilingualLeftAction ((colimit.ι F j).hom a)
        (bilingualRightOppositeAction ((colimit.ι F j).hom x)
          (MulOpposite.op ((colimit.ι F j).hom (MulOpposite.unop b))) ) =
      bilingualRightOppositeAction
        (bilingualLeftAction ((colimit.ι F j).hom a) ((colimit.ι F j).hom x))
        (MulOpposite.op ((colimit.ι F j).hom (MulOpposite.unop b))) := by
  exact InfoGeometry.Physics.bilingual_left_right_commute
    ((colimit.ι F j).hom a) ((colimit.ι F j).hom x)
      (MulOpposite.op ((colimit.ι F j).hom (MulOpposite.unop b)))

end
end InfoGeometry.Physics.HestenesKreinBilingualColimitBridge

namespace InfoGeometry.Physics.HestenesKreinBilingualColimitBridge

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Arithmetic.CyclotomicFiveNPotentGaloisBridge

universe v

variable {K : Type v} [Category.{v} K] [IsFiltered K]
variable (C : K ⥤ CommRingCat.{v}) [HasColimit C]

noncomputable section

/-- Cyclotomic sixth-potent transport through the native commutative-ring colimit. -/
theorem commRingColimit_six_potent_of_pow_five_eq_one
    (k : K) (x : C.obj k) (hDomain : IsDomain (C.obj k))
    (hx : x ^ 5 = 1) :
    (colimit.ι C k).hom x ^ 6 =
      (colimit.ι C k).hom x := by
  letI := hDomain
  have hstage : x ^ 6 = x := six_potent_of_pow_five_eq_one hx
  simpa using congrArg (colimit.ι C k).hom hstage

/-- Cyclotomic inverse/unit transport with the native colimit unit. -/
theorem commRingColimit_twist_inverse_pair
    (k : K) (x : C.obj k) (hDomain : IsDomain (C.obj k))
    (hx : x ^ 5 = 1) :
    (colimit.ι C k).hom ((x ^ 2) ^ 4) *
        (colimit.ι C k).hom (x ^ 2) = 1 := by
  letI := hDomain
  have hstage : (x ^ 2) ^ 4 * (x ^ 2) = 1 :=
    twist_fourth_mul_twist_eq_one hx
  simpa using congrArg (colimit.ι C k).hom hstage

end
end InfoGeometry.Physics.HestenesKreinBilingualColimitBridge
