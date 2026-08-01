import InfoGeometry.Canonical.CubicJordanOsFilteredTopCatCocone

/-!
# Cubic-norm readout through a native Albert topological colimit

The transition system is intentionally arbitrary.  A cubic-norm readout
descends only when preservation is supplied as an explicit stagewise
compatibility law.  This keeps the colimit statement constructive and avoids
assuming that an unrelated continuous transition map preserves the invariant.
-/

noncomputable section

namespace InfoGeometry.Algebra.CubicJordanOs

open CategoryTheory
open InfoGeometry.Algebra.CubicJordanOs.AlbertMatrix

variable {J : Type} [Category J]

structure NormCubicCompatible
    (S : ContinuousAlbertTransitionSystem J) : Prop where
  map_preserves : ∀ {i j : J} (f : i ⟶ j) (x : AlbertMatrix),
    normCubic (S.map f x) = normCubic x

noncomputable def normCubicCocone
    (S : ContinuousAlbertTransitionSystem J)
    (hS : NormCubicCompatible S) :
    ContinuousAlbertCocone S ℝ where
  ι := fun _ => normCubic
  continuous_ι := fun _ => continuous_normCubic
  ι_comm := by
    intro i j f x
    exact hS.map_preserves f x

noncomputable def normCubicColimitReadout
    (S : ContinuousAlbertTransitionSystem J)
    (hS : NormCubicCompatible S) :
    topologicalColimit S ⟶ TopCat.of ℝ :=
  coconeDescend (normCubicCocone S hS)

theorem normCubicColimitReadout_stage
    (S : ContinuousAlbertTransitionSystem J)
    (hS : NormCubicCompatible S) (i : J) (x : AlbertMatrix) :
    normCubicColimitReadout S hS (topologicalInjection S i x) =
      normCubic x := by
  exact coconeDescend_stage_apply (normCubicCocone S hS) i x

theorem normCubicColimitReadout_stage_eq
    (S : ContinuousAlbertTransitionSystem J)
    (hS : NormCubicCompatible S) (i : J) :
    topologicalInjection S i ≫ normCubicColimitReadout S hS =
      ιTopCatHom (normCubicCocone S hS) i := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  rw [TopCat.comp_app]
  exact normCubicColimitReadout_stage S hS i x

end InfoGeometry.Algebra.CubicJordanOs
