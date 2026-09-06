import Mathlib.Tactic
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

/-! Real split-Cartan coordinate space for the D₅ Weyl action. -/
def Torus5D := Fin 5 → ℝ

def Cartan5D := Torus5D

/-- The standard inner product on ℝ⁵. -/
def dot_product (v w : Torus5D) : ℝ :=
  (v 0 * w 0) + (v 1 * w 1) + (v 2 * w 2) + (v 3 * w 3) + (v 4 * w 4)

/-- 
The explicit mathematical definition of a Weyl reflection `s_α(v)` across a root `α`. 
-/
def weyl_reflect (v α : Torus5D) : Torus5D :=
  fun i => v i - 2 * (dot_product v α / dot_product α α) * α i

def IsD5RootReal (α : Cartan5D) : Prop :=
  ∃ (i j : Fin 5) (si sj : ℝ),
    i ≠ j ∧
      (si = 1 ∨ si = -1) ∧
      (sj = 1 ∨ sj = -1) ∧
      α = fun k => if k = i then si else if k = j then sj else 0

/-- 
The specific root `e₁ - e₂` in the D_5 root system.
It acts locally on the first two coordinates of the 5D torus.
-/
def alpha_12 : Torus5D :=
  fun i => if i = 0 then 1 else if i = 1 then -1 else 0

@[simp] theorem alpha_12_norm_sq :
    dot_product alpha_12 alpha_12 = 2 := by
  have h20 : (2 : Fin 5) ≠ 0 := by decide
  have h21 : (2 : Fin 5) ≠ 1 := by decide
  have h30 : (3 : Fin 5) ≠ 0 := by decide
  have h31 : (3 : Fin 5) ≠ 1 := by decide
  have h40 : (4 : Fin 5) ≠ 0 := by decide
  have h41 : (4 : Fin 5) ≠ 1 := by decide
  norm_num [dot_product, alpha_12, h20, h21, h30, h31, h40, h41]

theorem alpha_12_nonisotropic :
    dot_product alpha_12 alpha_12 ≠ 0 := by
  rw [alpha_12_norm_sq]
  norm_num

theorem alpha_12_isD5RootReal : IsD5RootReal alpha_12 := by
  refine ⟨0, 1, 1, -1, by decide, by simp, by simp, ?_⟩
  funext k
  fin_cases k <;> simp [alpha_12]

def beta_12 : Cartan5D :=
  ![1, 1, 0, 0, 0]

theorem beta_12_isD5RootReal : IsD5RootReal beta_12 := by
  refine ⟨0, 1, 1, 1, by decide, by simp, by simp, ?_⟩
  funext k
  fin_cases k <;> simp [beta_12]

theorem weyl_reflect_alpha12_involutive (v : Cartan5D) :
    weyl_reflect (weyl_reflect v alpha_12) alpha_12 = v := by
  funext i
  fin_cases i <;>
    simp [weyl_reflect, alpha_12, dot_product] <;> ring

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

theorem affine_shift_eq_add_beta_12 (v : Cartan5D) :
    affine_shift v = fun i => v i + beta_12 i := by
  funext i
  fin_cases i <;> simp [affine_shift, beta_12]

def wallpaperGlide (p : Plane2D) : Plane2D :=
  (p.2 + 1, p.1 + 1)

@[simp] theorem wallpaperGlide_sq (p : Plane2D) :
    wallpaperGlide (wallpaperGlide p) =
      (p.1 + 2, p.2 + 2) := by
  rcases p with ⟨x, y⟩
  apply Prod.ext <;> simp [wallpaperGlide] <;> ring

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

theorem affine_weyl_projects_to_wallpaperGlide (v : Cartan5D) :
    project_2d (affine_shift (weyl_reflect v alpha_12)) =
      wallpaperGlide (project_2d v) := by
  rw [affine_weyl_projects_to_glide_reflection]
  rfl

/-- The finite Weyl-to-wallpaper quotient packet: mirror shadow plus glide lift. -/
theorem weyl_wallpaper_quotient_packet (v : Torus5D) :
    project_2d (weyl_reflect v alpha_12) = (v 1, v 0) ∧
      project_2d (affine_shift (weyl_reflect v alpha_12)) = (v 1 + 1, v 0 + 1) := by
  exact ⟨weyl_projects_to_wallpaper_mirror v,
    affine_weyl_projects_to_glide_reflection v⟩

end InfoGeometry.Canonical.Pin55WeylWallpaper
