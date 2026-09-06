import InfoGeometry.Canonical.Pin55
import InfoGeometry.Canonical.Pin55NativeCover
import InfoGeometry.Canonical.Pin55WeylWallpaper
import InfoGeometry.Canonical.WallpaperKleinBottleCartan
import InfoGeometry.Topology.WallpaperKleinBottlePresentation

/-!
# Finite `Pin(5,5)` to wallpaper quotient bridge

This file packages the finite theorem chain that is actually available in the
repository:

* a split-signature `Pin(5,5)` reflection maps to the `D₅` Weyl reflection;
* that Weyl reflection projects to the wallpaper mirror and affine glide;
* the concrete `pg` wallpaper action satisfies the Klein-bottle relation;
* the eight displayed wallpaper point symmetries are Klein-compatible.

This is a finite quotient bridge, not a full classification theorem for
`O(5,5)`, `Pin(5,5)`, or the wallpaper groups.
-/

noncomputable section

namespace InfoGeometry.Canonical.Pin55WallpaperQuotientBridge

open InfoGeometry.Canonical.Pin55
open InfoGeometry.Canonical.Pin55WeylWallpaper
open InfoGeometry.Canonical.WallpaperKleinBottleCartan
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Topology.Wallpaper
open InfoGeometry.Topology.WallpaperKleinBottlePresentation

theorem alpha12Split_Q55_nonisotropic :
    Q55 alpha12Split ≠ 0 := by
  rw [← quadratic_form_5_5_eq_Q55]
  exact alpha12Split_nonisotropic

noncomputable def alpha12RealPin : RealPin55 :=
  Classical.choose (realPin55OrthogonalAction_surjective
    (quadraticReflectionIsometry alpha12Split
      alpha12Split_Q55_nonisotropic))

theorem realPin55OrthogonalAction_alpha12RealPin :
    realPin55OrthogonalAction alpha12RealPin =
      quadraticReflectionIsometry alpha12Split
        alpha12Split_Q55_nonisotropic := by
  exact Classical.choose_spec (realPin55OrthogonalAction_surjective
    (quadraticReflectionIsometry alpha12Split
      alpha12Split_Q55_nonisotropic))

theorem alpha12RealPin_action_eq_weyl_reflection (v : Cartan5D) :
    (realPin55OrthogonalAction alpha12RealPin
      (v, fun _ => 0)).1 = weyl_reflect v alpha_12 := by
  rw [realPin55OrthogonalAction_alpha12RealPin]
  change (quadraticReflection alpha12Split
      alpha12Split_Q55_nonisotropic (v, fun _ => 0)).1 = _
  rw [quadraticReflection_apply]
  have hpolar :
      QuadraticMap.polar (⇑Q55) (v, fun _ => 0) alpha12Split =
        2 * dot_product v alpha_12 := by
    classical
    have hfilter :
        ({x : Fin 4 | x.succ = 1} : Finset (Fin 4)).card = 1 := by
      native_decide
    simp [QuadraticMap.polar, Q55_apply, alpha12Split, alpha_12,
      dot_product, Fin.sum_univ_succ, hfilter]
    ring_nf
  rw [hpolar]
  have hq : Q55 alpha12Split = 2 := by
    rw [← quadratic_form_5_5_eq_Q55]
    have h20 : (2 : Fin 5) ≠ 0 := by decide
    have h21 : (2 : Fin 5) ≠ 1 := by decide
    have h30 : (3 : Fin 5) ≠ 0 := by decide
    have h31 : (3 : Fin 5) ≠ 1 := by decide
    have h40 : (4 : Fin 5) ≠ 0 := by decide
    have h41 : (4 : Fin 5) ≠ 1 := by decide
    norm_num [quadratic_form_5_5, splitPair55, alpha12Split,
      alpha_12, dot_product, h20, h21, h30, h31, h40, h41]
  rw [hq]
  unfold weyl_reflect
  funext i
  rw [alpha_12_norm_sq]
  by_cases hi0 : i = 0
  · subst i
    simp [alpha12Split, alpha_12]
    ring
  · by_cases hi1 : i = 1
    · subst i
      simp [alpha12Split, alpha_12]
      ring
    · simp [alpha12Split, alpha_12, hi0, hi1]

namespace Pin55D5WallpaperQuotientPacket

theorem pin_to_weyl (v : Torus5D) :
    (orthogonalReflection55 alpha12Split alpha12Split_nonisotropic
      (v, fun _ => 0)).1 =
      weyl_reflect v alpha_12 := by
  simpa using Pin55.alpha12_split_reflection_eq_weyl_reflection v

theorem wallpaper_mirror (v : Torus5D) :
    project_2d (weyl_reflect v alpha_12) = (v 1, v 0) :=
  weyl_projects_to_wallpaper_mirror v

theorem wallpaper_glide (v : Torus5D) :
    project_2d (affine_shift (weyl_reflect v alpha_12)) =
      (v 1 + 1, v 0 + 1) :=
  affine_weyl_projects_to_glide_reflection v

theorem klein_bottle_presentation (p : Lattice2D) :
    concretePG.G (concretePG.T_y (concretePG.G.symm p)) = concretePG.T_y.symm p :=
  concrete_kleinBottlePresentation_relation p

theorem wallpaperD4_compatible :
    ∀ i : Fin 8, IsKleinCompatibleWallpaper (wallpaperD4 i) :=
  wallpaperD4_is_klein_compatible

end Pin55D5WallpaperQuotientPacket

/-- Build the finite quotient packet from the checked owner lemmas. -/
theorem pin55_d5_wallpaper_quotient_packet
    (v : Torus5D) (p : Lattice2D) :
    (orthogonalReflection55 alpha12Split alpha12Split_nonisotropic
      (v, fun _ => 0)).1 =
        weyl_reflect v alpha_12 ∧
      project_2d (weyl_reflect v alpha_12) = (v 1, v 0) ∧
      project_2d (affine_shift (weyl_reflect v alpha_12)) =
        (v 1 + 1, v 0 + 1) ∧
      concretePG.G (concretePG.T_y (concretePG.G.symm p)) = concretePG.T_y.symm p ∧
      (∀ i : Fin 8, IsKleinCompatibleWallpaper (wallpaperD4 i)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa using Pin55.alpha12_split_reflection_eq_weyl_reflection v
  · exact weyl_projects_to_wallpaper_mirror v
  · exact affine_weyl_projects_to_glide_reflection v
  · exact concrete_kleinBottlePresentation_relation p
  · exact wallpaperD4_is_klein_compatible

end InfoGeometry.Canonical.Pin55WallpaperQuotientBridge
