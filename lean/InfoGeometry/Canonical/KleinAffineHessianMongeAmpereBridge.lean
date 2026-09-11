import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Affine Klein deck data and a finite Hessian background

This owner records the affine-cover algebra behind the Klein-bottle picture.
It proves the deck relation and affine quasi-periodicity of the quadratic
background potential.  It does not construct a quotient manifold, a global
Monge--Ampère solution, or an automorphy theorem for the completed zeta.
-/

noncomputable section

namespace InfoGeometry.Canonical.KleinAffineHessianMongeAmpere

abbrev CoverPoint := ℝ × ℝ

/-- Horizontal deck translation on the affine universal cover. -/
def affineTranslate (L : ℝ) (p : CoverPoint) : CoverPoint :=
  (p.1 + L, p.2)

/-- Orientation-reversing affine glide. -/
def affineGlide (T : ℝ) (p : CoverPoint) : CoverPoint :=
  (-p.1, p.2 + T)

/-- The inverse glide, used explicitly in the semidirect relation. -/
def affineGlideInv (T : ℝ) (p : CoverPoint) : CoverPoint :=
  (-p.1, p.2 - T)

theorem affine_glide_inverse (T : ℝ) (p : CoverPoint) :
    affineGlide T (affineGlideInv T p) = p := by
  dsimp [affineGlide, affineGlideInv]
  ext <;> ring

/-- The Klein semidirect relation on the affine cover. -/
theorem affine_glide_conjugates_translate (L T : ℝ) (p : CoverPoint) :
    affineGlide T (affineTranslate L (affineGlideInv T p)) =
      affineTranslate (-L) p := by
  dsimp [affineGlide, affineTranslate, affineGlideInv]
  ext <;> ring

/-- The square of the glide is vertical translation by `2T`. -/
theorem affine_glide_square (T : ℝ) (p : CoverPoint) :
    affineGlide T (affineGlide T p) = (p.1, p.2 + 2 * T) := by
  dsimp [affineGlide]
  ext <;> ring

/-- The affine quadratic background potential on the cover. -/
def backgroundPotential (p : CoverPoint) : ℝ :=
  (1 / 2 : ℝ) * (p.1 ^ 2 + p.2 ^ 2)

theorem backgroundPotential_translate_increment (L : ℝ) (p : CoverPoint) :
    backgroundPotential (affineTranslate L p) - backgroundPotential p =
      L * p.1 + (1 / 2 : ℝ) * L ^ 2 := by
  dsimp [backgroundPotential, affineTranslate]
  ring

theorem backgroundPotential_glide_increment (T : ℝ) (p : CoverPoint) :
    backgroundPotential (affineGlide T p) - backgroundPotential p =
      T * p.2 + (1 / 2 : ℝ) * T ^ 2 := by
  dsimp [backgroundPotential, affineGlide]
  ring

/-! The critical axis is a deck-invariant subset, even though its transverse
normal is reversed by the glide. -/

theorem affine_glide_preserves_critical_core (T : ℝ) (p : CoverPoint)
    (hp : p.1 = 0) :
    (affineGlide T p).1 = 0 := by
  dsimp [affineGlide]
  rw [hp, neg_zero]

/-- The constant Hessian background matrix. -/
def backgroundHessian : Matrix (Fin 2) (Fin 2) ℝ := 1

theorem backgroundHessian_det : Matrix.det backgroundHessian = 1 := by
  simp [backgroundHessian]

end InfoGeometry.Canonical.KleinAffineHessianMongeAmpere
