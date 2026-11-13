/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.SandwichLocalizationStar
import InfoGeometry.OperatorAlgebra.PeirceSpine.CayleyKernelRegularity

/-!
# Ambient Peirce Cayley action without an on-shell hypothesis

The polynomial norm identity of the existing Peirce owner is applied to the
native two-sided localization of the whole original ring. Three-square star
faithfulness proves injectivity of the ambient embedding. The action itself
does not assume metric idempotence or ambient denominator commutativity.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.SandwichCayley

open InfoGeometry.Algebra.SandwichLocalization

variable {B : Type*} [Ring B] [StarRing B]

/-- The actual shifted Peirce denominator in the original ambient ring. -/
def shift (P A : B) : B := 1 + genV P A (star A)

instance shiftSelfAdjoint (P A : B) [hPs : Fact (star P = P)] :
    Fact (star (shift P A) = shift P A) where
  out := by simp only [shift, star_add, star_one, star_genV hPs.out]

/-- The polynomial Cayley numerator commutes with the denominator, without
requiring an arbitrary ambient numerator to commute with it. -/
theorem numerator_commute (P A : B) (hP : P * P = P) :
    Commute (shift P A) (cayleyKernelNumerator P A (star A)) := by
  have h := genV_commute_of_mem_generated hP A (star A)
    (cayleyKernelNumerator_mem_generated P A (star A))
  exact (Commute.one_left _).add_left h

/-- Three-square faithfulness proves regularity on the right as well as the left. -/
theorem shift_right_injective (P A : B) (hPs : star P = P)
    (hfaith : ∀ X Y Z : B, star X * X + star Y * Y + star Z * Z = 0 → X = 0) :
    Function.Injective (fun X : B => X * shift P A) := by
  intro X Y h
  have hs : star (shift P A) = shift P A := by
    simp only [shift, star_add, star_one, star_genV hPs]
  have hstar : shift P A * star X = shift P A * star Y := by
    simpa only [star_mul, hs] using congrArg star h
  have he := one_add_genV_mul_injective hPs hfaith A hstar
  simpa only [star_star] using congrArg star he

/-- Faithful inclusion of all ambient operators, including noncentral ones. -/
theorem ambient_embedding_injective (P A : B) (hPs : star P = P)
    (hfaith : ∀ X Y Z : B, star X * X + star Y * Y + star Z * Z = 0 → X = 0) :
    Function.Injective (of (shift P A)) :=
  of_injective (shift P A) (one_add_genV_mul_injective hPs hfaith A)
    (shift_right_injective P A hPs hfaith)

/-- The exact two-sided fraction criterion for the submitted Peirce denominator. -/
theorem ambient_fraction_eq_iff (P A : B) (hPs : star P = P)
    (hfaith : ∀ X Y Z : B, star X * X + star Y * Y + star Z * Z = 0 → X = 0)
    (k l k' l' : ℕ) (X Y : B) :
    repr (shift P A) k X l = repr (shift P A) k' Y l' ↔
      shift P A ^ k' * X * shift P A ^ l' = shift P A ^ k * Y * shift P A ^ l :=
  repr_eq_iff_cross (shift P A) (one_add_genV_mul_injective hPs hfaith A)
    (shift_right_injective P A hPs hfaith) k l k' l' X Y

variable (P A : B) [hP : Fact (P * P = P)] [hPs : Fact (star P = P)]

/-- A constructed off-shell Cayley additive equivalence on the full ambient carrier. -/
noncomputable def ambientCayley : Space (shift P A) ≃+ Space (shift P A) :=
  cayleyEquiv (shift P A) (cayleyKernelNumerator P A (star A))
    (numerator_commute P A hP.out)
    (cayleyKernelNumerator_star_products hP.out hPs.out A).1
    (cayleyKernelNumerator_star_products hP.out hPs.out A).2

/-- The requested two-denominator formula at the actual ambient embedding. -/
theorem ambientCayley_of (X : B) :
    ambientCayley P A (of (shift P A) X) =
      repr (shift P A) 1
        (cayleyKernelNumerator P A (star A) * X *
          cayleyKernelNumeratorConj P A (star A)) 1 := by
  change repr (shift P A) (0 + 1)
    (cayleyKernelNumerator P A (star A) * X *
      star (cayleyKernelNumerator P A (star A))) (0 + 1) = _
  rw [star_cayleyKernelNumerator hPs.out]

theorem ambientCayley_star (z : Space (shift P A)) :
    star (ambientCayley P A z) = ambientCayley P A (star z) :=
  cayleyEquiv_star (shift P A) _ _ _ _ z

/-- Both inverse laws belong to the actual constructed equivalence. -/
theorem ambientCayley_inverse (z : Space (shift P A)) :
    (ambientCayley P A).symm (ambientCayley P A z) = z ∧
      ambientCayley P A ((ambientCayley P A).symm z) = z :=
  ⟨(ambientCayley P A).symm_apply_apply z, (ambientCayley P A).apply_symm_apply z⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine.SandwichCayley
