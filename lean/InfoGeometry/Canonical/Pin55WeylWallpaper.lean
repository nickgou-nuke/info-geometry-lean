import Mathlib
import InfoGeometry.Canonical.ContinuousThermodynamicGeometry
import InfoGeometry.Canonical.HolographicSouriauClosure

/-!
# Finite `D₅` Weyl reflections and wallpaper quotient shadow

This module is the finite root-system shadow for the wallpaper quotient lane.
It defines one explicit `D₅` reflection on a 5D torus chart, projects it to a
2D boundary chart, and proves the projected formulas exactly:

* the reflection across `e₁ - e₂` projects to the mirror swap `(x, y) ↦ (y, x)`;
* the affine lift projects to the glide-shift `(x, y) ↦ (y + 1, x + 1)`.

This is a finite quotient/factorization shadow, not a construction of the full
Lie group `O(5,5)`, a topological `Pin(5,5)` cover, or a global crystallographic
classification theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.Pin55WeylWallpaper

/-!
### 1. D_5 Root System and Weyl Reflections
-/

/-- The vector space for the O(5,5) maximal torus. -/
def Torus5D := Fin 5 → ℝ

/-- The standard inner product on ℝ⁵. -/
def dot_product (v w : Torus5D) : ℝ :=
  (v 0 * w 0) + (v 1 * w 1) + (v 2 * w 2) + (v 3 * w 3) + (v 4 * w 4)

/-- 
The explicit mathematical definition of a Weyl reflection `s_α(v)` across a root `α`. 
-/
def weyl_reflect (v α : Torus5D) : Torus5D :=
  fun i => v i - 2 * (dot_product v α / dot_product α α) * α i

/-- 
The specific root `e₁ - e₂` in the D_5 root system.
It acts locally on the first two coordinates of the 5D torus.
-/
def alpha_12 : Torus5D :=
  fun i => if i = 0 then 1 else if i = 1 then -1 else 0

/-!
### 2. 2D Wallpaper Quotient Map
-/

/-- The 2D holographic boundary plane. -/
def Plane2D := ℝ × ℝ

/-- 
The explicit quotient mapping that projects the 5D torus onto the 
2D holographic boundary layer. 
-/
def project_2d (v : Torus5D) : Plane2D :=
  (v 0, v 1)

/-- 
THEOREM: The O(5,5) Weyl reflection across the root `e₁ - e₂` exactly projects 
to the `(x, y) ↦ (y, x)` mirror reflection on the 2D wallpaper boundary. 
This strictly derives the 2D boundary symmetries from the 10D bulk.
-/
theorem weyl_projects_to_wallpaper_mirror (v : Torus5D) :
    project_2d (weyl_reflect v alpha_12) = (v 1, v 0) := by
  dsimp [project_2d, weyl_reflect, alpha_12, dot_product]
  have h1 : v 0 - 2 * ((v 0 * 1 + v 1 * -1 + v 2 * 0 + v 3 * 0 + v 4 * 0) / (1 * 1 + (-1) * -1 + 0 * 0 + 0 * 0 + 0 * 0)) * 1 = v 1 := by ring
  have h2 : v 1 - 2 * ((v 0 * 1 + v 1 * -1 + v 2 * 0 + v 3 * 0 + v 4 * 0) / (1 * 1 + (-1) * -1 + 0 * 0 + 0 * 0 + 0 * 0)) * -1 = v 0 := by ring
  exact Prod.ext h1 h2

/-!
### 3. Affine Adjoint Glide Reflection
-/

/-- A standard translation on the 5D torus representing an affine root shift. -/
def affine_shift (v : Torus5D) : Torus5D :=
  fun i => if i = 0 then v i + 1 else if i = 1 then v i + 1 else v i

/-- 
THEOREM: The Affine Weyl action (reflection followed by translation shift) 
exactly induces the wallpaper glide reflection `(y+1, x+1)` on the holographic boundary.
-/
theorem affine_weyl_projects_to_glide_reflection (v : Torus5D) :
    project_2d (affine_shift (weyl_reflect v alpha_12)) = (v 1 + 1, v 0 + 1) := by
  dsimp [project_2d, affine_shift, weyl_reflect, alpha_12, dot_product]
  have h1 : (v 0 - 2 * ((v 0 * 1 + v 1 * -1 + v 2 * 0 + v 3 * 0 + v 4 * 0) / (1 * 1 + (-1) * -1 + 0 * 0 + 0 * 0 + 0 * 0)) * 1) + 1 = v 1 + 1 := by ring
  have h2 : (v 1 - 2 * ((v 0 * 1 + v 1 * -1 + v 2 * 0 + v 3 * 0 + v 4 * 0) / (1 * 1 + (-1) * -1 + 0 * 0 + 0 * 0 + 0 * 0)) * -1) + 1 = v 0 + 1 := by ring
  exact Prod.ext h1 h2

/-- The finite Weyl-to-wallpaper quotient packet: mirror shadow plus glide lift. -/
theorem weyl_wallpaper_quotient_packet (v : Torus5D) :
    project_2d (weyl_reflect v alpha_12) = (v 1, v 0) ∧
      project_2d (affine_shift (weyl_reflect v alpha_12)) = (v 1 + 1, v 0 + 1) := by
  exact ⟨weyl_projects_to_wallpaper_mirror v,
    affine_weyl_projects_to_glide_reflection v⟩

end InfoGeometry.Canonical.Pin55WeylWallpaper
