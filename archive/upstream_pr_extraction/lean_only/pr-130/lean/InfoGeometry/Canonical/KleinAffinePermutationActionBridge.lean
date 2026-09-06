import Mathlib
import InfoGeometry.Canonical.KleinPresentedGroup

/-!
# Native affine permutation action for the Klein presentation

This owner packages the affine formulas `x ↦ x + a` and `x ↦ -x` as actual
permutations of `ℝ`.  It proves the Klein conjugation relation and obtains the
corresponding native group homomorphism from the presented Klein group.

No topology, continuity, crossed product, or C*-completion is asserted here.
-/

namespace InfoGeometry.Canonical.KleinAffinePermutationActionBridge

open InfoGeometry.Canonical.KleinPresentedGroup

def affineTranslation (a : ℝ) : Equiv.Perm ℝ :=
  { toFun := fun x => x + a
    invFun := fun x => x - a
    left_inv := by intro x; ring
    right_inv := by intro x; ring }

def affineGlide : Equiv.Perm ℝ :=
  Equiv.neg ℝ

@[simp]
theorem affineTranslation_apply (a x : ℝ) :
    affineTranslation a x = x + a :=
  rfl

@[simp]
theorem affineGlide_apply (x : ℝ) : affineGlide x = -x :=
  rfl

theorem affine_glide_involutive : affineGlide * affineGlide = 1 := by
  ext x
  simp [affineGlide]

theorem affine_translation_mul (a b : ℝ) :
    affineTranslation a * affineTranslation b = affineTranslation (a + b) := by
  ext x
  simp [Equiv.Perm.mul_apply, affineTranslation]
  ring

theorem affine_glide_conjugates_translation (a : ℝ) :
    affineGlide * affineTranslation a * affineGlide⁻¹ =
      affineTranslation (-a) := by
  ext x
  simp [Equiv.Perm.mul_apply, affineGlide, affineTranslation, add_comm]

@[simp]
theorem affineTranslation_inv (a : ℝ) :
    (affineTranslation a)⁻¹ = affineTranslation (-a) := by
  ext x
  simp [affineTranslation]
  ring

def affineKleinRep : KleinGroup →* Equiv.Perm ℝ :=
  kleinRep affineGlide (affineTranslation 1) (by
    simpa using (affine_glide_conjugates_translation 1))

theorem affineKleinRep_generators :
    affineKleinRep (toKlein genA) = affineGlide ∧
    affineKleinRep (toKlein genB) = affineTranslation 1 := by
  exact kleinRep_relator_relation affineGlide (affineTranslation 1) (by
    simpa using (affine_glide_conjugates_translation 1))

theorem affineKleinRep_relator :
    affineKleinRep (toKlein genA) * affineKleinRep (toKlein genB) *
        (affineKleinRep (toKlein genA))⁻¹ =
      (affineKleinRep (toKlein genB))⁻¹ := by
  have h := affineKleinRep_generators
  rw [h.1, h.2]
  simpa using (affine_glide_conjugates_translation 1)

end InfoGeometry.Canonical.KleinAffinePermutationActionBridge
