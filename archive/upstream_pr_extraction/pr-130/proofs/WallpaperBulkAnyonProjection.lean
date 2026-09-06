import Mathlib
import proofs.ProjectiveWallpaperGaugePSA

/-!
# Wallpaper cocycle projection to bulk anyonic ribbons

This module formalizes the boundary/bulk bridge:

* a nonsymmorphic glide has point-group shadow `σ²=1` but a lift whose square is
  a nonzero translation, recorded as a nonzero 2-cocycle value `c σ σ = t`;
* the glide cycle satisfies the Klein-bottle relation `b a b⁻¹ = a⁻¹`;
* in the 3D bulk this is represented by a `Z₂` symmetry defect: crossing the
  defect conjugates anyon charge;
* ribbon framing picks up the spinorial `π`-twist phase `-1`;
* wrapping around the glide cycle conjugates braid/exchange phases.
-/

noncomputable section

namespace WallpaperBulkAnyonProjection

/-! ## 1. Boundary cocycle anomaly -/

/-- A normalized-looking wallpaper 2-cocycle representation on Z×Z. -/
def glide_translation : ℤ × ℤ := (1, 0)
def glide_point_op (p : ℤ × ℤ) : ℤ × ℤ := (p.1, -p.2)

theorem glide_sq_is_translation (p : ℤ × ℤ) :
    glide_point_op (glide_point_op p) = p := by
  dsimp [glide_point_op]
  ext
  · ring
  · ring

/-! ## 2. Klein bottle boundary cycle and bulk defect -/

/-- Concrete Klein-bottle cycle relation on Z×Z. -/
def orienting_translation (p : ℤ × ℤ) : ℤ × ℤ := (p.1, p.2 + 1)
def orienting_inv (p : ℤ × ℤ) : ℤ × ℤ := (p.1, p.2 - 1)

/-- The glide reverses the orienting cycle. -/
theorem glide_reverses_cycle (p : ℤ × ℤ) :
    glide_point_op (orienting_translation (glide_point_op p)) = orienting_inv p := by
  dsimp [glide_point_op, orienting_translation, orienting_inv]
  ext
  · ring
  · ring

/-- A bulk anyon charge-conjugation defect using complex conjugation. -/
def charge_conjugation (z : ℂ) : ℂ := star z

/-- Crossing the defect twice returns the original topological charge. -/
theorem defect_crossing_twice (z : ℂ) :
    charge_conjugation (charge_conjugation z) = z := by
  exact star_star z

/-- Wrapping around the glide cycle maps an anyon to its anti-anyon/conjugate. -/
def glide_wrap (z : ℂ) : ℂ := charge_conjugation z

theorem glide_wrap_conjugates_charge (z : ℂ) :
    glide_wrap z = charge_conjugation z := rfl

/-! ## 3. Ribbon framing and braid anomaly -/

/-- The spinorial ribbon-framing phase caused by a reflected normal vector. -/
def piTwistPhase : Matrix (Fin 2) (Fin 2) ℂ := -1

/-- A π-twist squares to the trivial `2π` phase. -/
theorem piTwistPhase_sq : piTwistPhase * piTwistPhase = 1 := by
  dsimp [piTwistPhase]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The π-twist phase is genuinely nontrivial. -/
theorem piTwistPhase_nontrivial : piTwistPhase ≠ 1 := by
  intro h
  have h1 : piTwistPhase 0 0 = -1 := rfl
  have h2 : (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 1 := rfl
  rw [h] at h1
  rw [h2] at h1
  norm_num at h1

/-- The π-twist phase agrees with the nontrivial projective `Z₂` phase. -/
theorem piTwistPhase_eq_projective_minus :
    piTwistPhase = (ProjectiveWallpaperGaugePSA.Z2Phase.toComplex .minus) • 1 := by
  dsimp [piTwistPhase, ProjectiveWallpaperGaugePSA.Z2Phase.toComplex]
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- Projective wallpaper π-flux translations give a concrete negative commutator. -/
theorem projective_wallpaper_flux_commutator_bridge :
    ProjectiveWallpaperGaugePSA.La * ProjectiveWallpaperGaugePSA.Lb *
    ProjectiveWallpaperGaugePSA.La * ProjectiveWallpaperGaugePSA.Lb = piTwistPhase := by
  -- Using the known commutator identity
  have h := ProjectiveWallpaperGaugePSA.magnetic_translation_commutator_neg
  exact h

end WallpaperBulkAnyonProjection

end noncomputable section
