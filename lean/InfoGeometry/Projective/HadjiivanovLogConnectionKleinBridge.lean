import InfoGeometry.Projective.HadjiivanovLogConnectionBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.PuncturedAffineKleinInversionBridge

/-!
# Klein inversion of the algebraic Hadjiivanov logarithmic connection

Laurent inversion is lifted trivially across the finite fiber.  Reversing the
base logarithmic orientation and the residue together gives the algebraic
intertwining law `∇[-H] ι = -ι ∇[H]` on the full tensor section carrier.

This is a finite cochain symmetry.  It is not an analytic CPT, transport, or
holonomy theorem.
-/

namespace InfoGeometry.Projective.HadjiivanovLogConnectionKleinBridge

open scoped TensorProduct
open InfoGeometry.Projective.HadjiivanovLogConnectionBridge
open InfoGeometry.Projective.PuncturedAffineKleinInversionBridge

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Simultaneous sign reversal of the scalar and nilpotent residue parts. -/
def reverseResidue (R : LogResidue V) : LogResidue V where
  weight := -R.weight
  nilpotent := -R.nilpotent
  nilpotent_sq := by
    ext v
    simp [LinearMap.comp_apply, nilpotent_apply_twice R]

@[simp] theorem reverseResidue_weight (R : LogResidue V) :
    (reverseResidue R).weight = -R.weight := rfl

@[simp] theorem reverseResidue_nilpotent (R : LogResidue V) :
    (reverseResidue R).nilpotent = -R.nilpotent := rfl

theorem reverseResidue_involutive (R : LogResidue V) :
    reverseResidue (reverseResidue R) = R := by
  cases R
  simp [reverseResidue]

theorem residueOperator_reverse (R : LogResidue V) :
    residueOperator (reverseResidue R) = -residueOperator R := by
  ext v
  simp [residueOperator]
  abel

/-- Laurent inversion lifted across an unchanged finite fiber. -/
def sectionInversion : LogSection V →ₗ[ℂ] LogSection V :=
  TensorProduct.map inversion.toLinearMap LinearMap.id

@[simp] theorem sectionInversion_tmul
    (f : HadjiivanovLogConnectionBridge.LaurentRing) (v : V) :
    sectionInversion (f ⊗ₜ[ℂ] v) = inversion f ⊗ₜ[ℂ] v := by
  simp [sectionInversion]

/-- The lifted inversion is an involution on every finite algebraic section. -/
theorem sectionInversion_involutive (x : LogSection V) :
    sectionInversion (sectionInversion x) = x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro f v
    rw [sectionInversion_tmul, sectionInversion_tmul, inversion_involutive]
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Klein reversal of the connection on a pure Laurent/fiber tensor. -/
theorem logarithmicConnection_reverse_tmul
    (R : LogResidue V)
    (f : HadjiivanovLogConnectionBridge.LaurentRing) (v : V) :
    logarithmicConnection (reverseResidue R)
        (sectionInversion (f ⊗ₜ[ℂ] v)) =
      -sectionInversion (logarithmicConnection R (f ⊗ₜ[ℂ] v)) := by
  simp only [sectionInversion_tmul, logarithmicConnection_tmul,
    reverseResidue_weight, reverseResidue_nilpotent, map_add]
  rw [logarithmicDifferential_inversion_anticommute]
  simp only [LinearMap.neg_apply, neg_smul, TensorProduct.tmul_add,
    TensorProduct.tmul_neg, TensorProduct.neg_tmul]
  abel

/-- Full-carrier cochain identity `∇[-H] ι = -ι ∇[H]`. -/
theorem logarithmicConnection_reverse (R : LogResidue V) (x : LogSection V) :
    logarithmicConnection (reverseResidue R) (sectionInversion x) =
      -sectionInversion (logarithmicConnection R x) := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · exact logarithmicConnection_reverse_tmul R
  · intro x y hx hy
    simp only [map_add, hx, hy, neg_add_rev]
    abel

theorem logarithmicConnection_reverse_comp (R : LogResidue V) :
    (logarithmicConnection (reverseResidue R)).comp sectionInversion =
      (-sectionInversion).comp (logarithmicConnection R) := by
  apply LinearMap.ext
  intro x
  exact logarithmicConnection_reverse R x

end

end InfoGeometry.Projective.HadjiivanovLogConnectionKleinBridge
