/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KleinVectorLiftObstruction

/-!
# Projective readback of the corrected six-state unitary lift

The original chosen generators have a nontrivial central defect. The existing
phase correction supplies an ordinary representation. Here its projection is
identified with the original projective representation on the entire presented
group, not only on the generators.

Dependencies: central phase → generator readback → free-group extensionality
→ quotient representation equality. No topological identification is asserted.
-/

noncomputable section
namespace InfoGeometry.Canonical.KleinUnitaryLiftProjection

open ProjectiveUnitary6 KleinPresentedGroup
open KleinSixStateProjectiveMonodromy KleinVectorLiftObstruction

theorem liftedTriality_projective (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    toPU6 (liftedTrialityU6 omega homega) = toPU6 (trialityU6 omega homega) := by
  rw [liftedTrialityU6, map_mul, toPU6_z_eq_one _ phaseIU6_mem_center, one_mul]

/-- Homomorphisms out of the presented Klein group are determined by its two
generators. This uses the existing quotient presentation. -/
theorem klein_hom_ext {G : Type*} [Group G] (f g : KleinGroup →* G)
    (ha : f (toKlein genA) = g (toKlein genA))
    (hb : f (toKlein genB) = g (toKlein genB)) : f = g := by
  have hfree : f.comp toKlein = g.comp toKlein := by
    apply FreeGroup.ext_hom
    intro generator
    cases generator
    · exact ha
    · exact hb
  apply MonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective KleinNormal x
  exact DFunLike.congr_fun hfree y

/-- The corrected lift is a lift of the same projective representation. -/
theorem concreteKleinUnitaryLift_projects (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    toPU6.comp (concreteKleinUnitaryLift omega homega) =
      concreteKleinProjectiveRep omega homega := by
  apply klein_hom_ext
  · simp only [MonoidHom.comp_apply,
      (concreteKleinUnitaryLift_generators omega homega).1,
      (concreteKleinProjectiveRep_generators omega homega).1]
  · simp only [MonoidHom.comp_apply,
      (concreteKleinUnitaryLift_generators omega homega).2,
      (concreteKleinProjectiveRep_generators omega homega).2,
      liftedTriality_projective]

end InfoGeometry.Canonical.KleinUnitaryLiftProjection
end noncomputable section
