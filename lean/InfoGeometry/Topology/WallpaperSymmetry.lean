import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Wallpaper `pg` symmetry: finite Klein-bottle relation

This module formalizes the elementary algebra behind the `pg` wallpaper group:
a glide reflection squares to a lattice translation and conjugates the transverse
translation to its inverse.

This is the finite group-action relation that underlies the usual Klein-bottle
presentation.  The file does not prove a full quotient-manifold classification,
a Brillouin-zone theorem, or a physical topological-insulator result.
-/

noncomputable section

namespace InfoGeometry.Topology.Wallpaper

/-- The 2D Euclidean plane representing a spatial lattice chart. -/
abbrev Lattice2D := ℝ × ℝ

/-- Unit translation in the `x` direction. -/
def T_x : Lattice2D ≃ Lattice2D where
  toFun p := (p.1 + 1, p.2)
  invFun p := (p.1 - 1, p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

/-- Unit translation in the `y` direction. -/
def T_y : Lattice2D ≃ Lattice2D where
  toFun p := (p.1, p.2 + 1)
  invFun p := (p.1, p.2 - 1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

/-- Glide reflection: translate by `1/2` in `x` and reflect `y`. -/
def G : Lattice2D ≃ Lattice2D where
  toFun p := (p.1 + (1 / 2 : ℝ), -p.2)
  invFun p := (p.1 - (1 / 2 : ℝ), -p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

/-- Concrete `pg` relation: the glide squared is the `x` translation. -/
theorem glide_squared_eq_x_translation (p : Lattice2D) :
    G (G p) = T_x p := by
  ext
  · simp [G, T_x]
    ring
  · simp [G, T_x]

/-- Concrete `pg` relation: the glide inverts the transverse translation. -/
theorem glide_y_translation_commutation (p : Lattice2D) :
    G (T_y p) = T_y.symm (G p) := by
  ext
  · simp [G, T_y]
  · simp [G, T_y]
    ring

/--
An abstract `pg` wallpaper symmetry package.  Its fields are exactly the two
relations above, for any chosen lattice chart action.
-/
structure WallpaperGroupPG where
  T_x : Lattice2D ≃ Lattice2D
  T_y : Lattice2D ≃ Lattice2D
  G : Lattice2D ≃ Lattice2D
  h_glide_squared : ∀ p : Lattice2D, G (G p) = T_x p
  h_commutation : ∀ p : Lattice2D, G (T_y p) = T_y.symm (G p)

/-- The concrete Euclidean `pg` wallpaper package. -/
def concretePG : WallpaperGroupPG where
  T_x := T_x
  T_y := T_y
  G := G
  h_glide_squared := glide_squared_eq_x_translation
  h_commutation := glide_y_translation_commutation

/-- Any `pg` package has the glide-translation commutation relation. -/
theorem pg_generates_klein_bottle_relation (pg : WallpaperGroupPG) (p : Lattice2D) :
    pg.G (pg.T_y p) = pg.T_y.symm (pg.G p) := by
  exact pg.h_commutation p

/--
Pointwise Klein-bottle presentation relation `G T_y G⁻¹ = T_y⁻¹` for any `pg`
package.  This is the group-presentation identity underlying the quotient
picture; it is still not a proof of a full quotient-manifold classification.
-/
theorem pg_conjugates_y_translation_to_inverse (pg : WallpaperGroupPG) (p : Lattice2D) :
    pg.G (pg.T_y (pg.G.symm p)) = pg.T_y.symm p := by
  have h := pg.h_commutation (pg.G.symm p)
  simpa using h

/-- The concrete `pg` action satisfies the glide-translation commutation relation. -/
theorem concrete_pg_generates_klein_bottle_relation (p : Lattice2D) :
    concretePG.G (concretePG.T_y p) = concretePG.T_y.symm (concretePG.G p) := by
  exact pg_generates_klein_bottle_relation concretePG p

/-- The concrete `pg` action satisfies `G T_y G⁻¹ = T_y⁻¹`. -/
theorem concrete_pg_conjugates_y_translation_to_inverse (p : Lattice2D) :
    concretePG.G (concretePG.T_y (concretePG.G.symm p)) = concretePG.T_y.symm p := by
  exact pg_conjugates_y_translation_to_inverse concretePG p

end InfoGeometry.Topology.Wallpaper

end noncomputable section
