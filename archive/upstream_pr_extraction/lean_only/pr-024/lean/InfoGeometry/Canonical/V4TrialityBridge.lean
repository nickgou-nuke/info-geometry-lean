import Mathlib
import InfoGeometry.Topology.V4RootSystem
import InfoGeometry.Topology.WallpaperKleinBottlePresentation
import InfoGeometry.Topology.Pin55ReflectionGlide
import InfoGeometry.Canonical.V4SemidirectS3Bridge

/-!
# V4TrialityBridge

This file keeps the old V4/triality debt names but replaces the previous
vacuous placeholders with the strongest finite statements that are
actually available in the current repository.

It does **not** claim the full analytic/geometric theorem
`W(D₄) ≅ (ℤ₂³ ⋊ V₄) ⋊ S₃`, nor a Spin(8)/Cl(5,5) representation theorem.
Those stronger statements remain owner-side closure debt.  The closed content
below is:

* the finite Klein-four multiplication/involution fragment from
  `Topology.V4RootSystem`;
* the finite tripotent/trifactor and non-identity-`V₄` triality packet from
  `Topology.V4RootSystem`;
* the imported finite `V₄ ⋊ S₃` semidirect model from
  `Canonical.V4SemidirectS3Bridge`;
* the pointwise wallpaper `pg` Klein-bottle relation and finite Pin-style glide
  square from the topology owners;
* a concrete affine boundary calculation whose defect is
  `(2θ₂ + 2π, 0)`.
-/

noncomputable section

namespace InfoGeometry.Canonical.V4TrialityBridge

/-- Coordinate pair for the minimal affine boundary calculation. -/
abbrev BoundaryCoord := ℝ × ℝ

/-- Coordinatewise difference on the affine boundary chart. -/
def coordSub (p q : BoundaryCoord) : BoundaryCoord :=
  (p.1 - q.1, p.2 - q.2)

/-- The `K` boundary move: translation by `θ₂ + π` in the first coordinate. -/
def boundaryK (θ₂ : ℝ) (p : BoundaryCoord) : BoundaryCoord :=
  (p.1 + θ₂ + Real.pi, p.2)

/-- The `W` boundary move: reflection in the first coordinate. -/
def boundaryW (p : BoundaryCoord) : BoundaryCoord :=
  (-p.1, p.2)

/-- Closed finite replacement for the old Weyl-decomposition placeholder.

This proves only the available finite V₄ fragment: the two sign reflections
compose to point inversion, and every element is an involution.  It is not the
full Weyl-group decomposition. -/
theorem weyl_group_decomposition :
    InfoGeometry.Topology.V4RootSystem.V4Group.W1 *
        InfoGeometry.Topology.V4RootSystem.V4Group.W2 =
      InfoGeometry.Topology.V4RootSystem.V4Group.W12 ∧
      (∀ x : InfoGeometry.Topology.V4RootSystem.V4Group,
        x * x = InfoGeometry.Topology.V4RootSystem.V4Group.I) :=
  ⟨InfoGeometry.Topology.V4RootSystem.varlamov_v4_inversion,
    InfoGeometry.Topology.V4RootSystem.v4_involution⟩

/-- Closed finite replacement for the old `V₄ ⊂ W(D₄)` placeholder.

The theorem states the kernel-checked embedding law for the left `V₄` factor
inside the repository's finite semidirect model `V₄ ⋊ S₃`.  It is not a Spin(8)
or D₄ Weyl representation theorem. -/
theorem v4_as_weyl_subgroup :
    ∀ x y : InfoGeometry.Canonical.V4SemidirectS3Bridge.V4Element,
      InfoGeometry.Canonical.V4SemidirectS3Bridge.inl x *
          InfoGeometry.Canonical.V4SemidirectS3Bridge.inl y =
        InfoGeometry.Canonical.V4SemidirectS3Bridge.inl (x * y) :=
  fun x y => InfoGeometry.Canonical.V4SemidirectS3Bridge.inl_mul x y

/-- The finite `S₃` triality 3-cycle permutes the three non-identity V₄ labels.

This delegates to `V4SemidirectS3Bridge.semidirect_nontrivial_triplet`, the
checked finite semidirect model. -/
theorem triality_permutes_sectors :
    (InfoGeometry.Canonical.TrialitySpin8Permutations.trialityCycle •
        (InfoGeometry.Canonical.V4SemidirectS3Bridge.V4Element.J :
          InfoGeometry.Canonical.V4SemidirectS3Bridge.V4Element),
      InfoGeometry.Canonical.TrialitySpin8Permutations.trialityCycle •
        (InfoGeometry.Canonical.V4SemidirectS3Bridge.V4Element.S :
          InfoGeometry.Canonical.V4SemidirectS3Bridge.V4Element),
      InfoGeometry.Canonical.TrialitySpin8Permutations.trialityCycle •
        (InfoGeometry.Canonical.V4SemidirectS3Bridge.V4Element.JS :
          InfoGeometry.Canonical.V4SemidirectS3Bridge.V4Element)) =
    (InfoGeometry.Canonical.V4SemidirectS3Bridge.V4Element.S,
      InfoGeometry.Canonical.V4SemidirectS3Bridge.V4Element.JS,
      InfoGeometry.Canonical.V4SemidirectS3Bridge.V4Element.J) :=
  InfoGeometry.Canonical.V4SemidirectS3Bridge.semidirect_nontrivial_triplet

/-- Concrete affine boundary defect calculation.

For `K(x,y)=(x+θ₂+π,y)` and `W(x,y)=(-x,y)`, the commutator defect
`K∘W - W∘K` is exactly `(2θ₂+2π,0)`.  This is only the explicit coordinate
calculation named by the old socket, not a full cohomological obstruction theorem. -/
theorem cocycle_as_triality_obstruction (θ₂ : ℝ) (p : BoundaryCoord) :
    coordSub (boundaryK θ₂ (boundaryW p)) (boundaryW (boundaryK θ₂ p)) =
      (2 * θ₂ + 2 * Real.pi, 0) := by
  cases p with
  | mk x y =>
      simp [coordSub, boundaryK, boundaryW]
      ring

/--
Finite bridge packet for the current Varlamov/V₄/trifactor/triality/glide
thread.

This packages only theorem-owned finite identities:
* tripotent/trifactor classification and non-identity `V₄` 3-cycle;
* concrete `pg` wallpaper relation `G T_y G⁻¹ = T_y⁻¹`;
* finite Pin-style glide square in split `(5,5)` coordinates.

It is not a classification theorem for Klein bottles, wallpaper groups,
`Cl(1,1)`, `Pin(5,5)`, or D₄/Spin(8) triality.
-/
theorem varlamov_v4_trifactor_triality_glide_packet
    (p : InfoGeometry.Topology.Wallpaper.Lattice2D)
    (x : InfoGeometry.Topology.Pin55ReflectionGlide.Vec55) :
    InfoGeometry.Topology.V4RootSystem.VarlamovV4TrifactorTrialityStatement ∧
      (InfoGeometry.Topology.WallpaperKleinBottlePresentation.WallpaperGroupPG.kleinBottlePresentation
          InfoGeometry.Topology.Wallpaper.concretePG).glide
        ((InfoGeometry.Topology.WallpaperKleinBottlePresentation.WallpaperGroupPG.kleinBottlePresentation
            InfoGeometry.Topology.Wallpaper.concretePG).yTranslation
          ((InfoGeometry.Topology.WallpaperKleinBottlePresentation.WallpaperGroupPG.kleinBottlePresentation
              InfoGeometry.Topology.Wallpaper.concretePG).glide.symm p)) =
        ((InfoGeometry.Topology.WallpaperKleinBottlePresentation.WallpaperGroupPG.kleinBottlePresentation
            InfoGeometry.Topology.Wallpaper.concretePG).yTranslation.symm p) ∧
      InfoGeometry.Topology.Pin55ReflectionGlide.glide01
          (InfoGeometry.Topology.Pin55ReflectionGlide.glide01 x) =
        InfoGeometry.Topology.Pin55ReflectionGlide.translate1 1 x := by
  exact ⟨InfoGeometry.Topology.V4RootSystem.varlamov_v4_trifactor_triality_packet,
    InfoGeometry.Topology.WallpaperKleinBottlePresentation.concrete_kleinBottlePresentation_relation p,
    InfoGeometry.Topology.Pin55ReflectionGlide.glide01_squared_eq_translate1 x⟩

end InfoGeometry.Canonical.V4TrialityBridge
