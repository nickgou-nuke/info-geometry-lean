import Mathlib

/-!
# Wallpaper glide isometry atom

Recovered finite affine proof: a glide reflection squared is a translation.
-/

namespace WallpaperIsometry

/-- A point in the Euclidean plane. -/
abbrev Point2D := ℝ × ℝ

/-- Reflection across the `x` axis. -/
def reflectionX (p : Point2D) : Point2D := (p.1, -p.2)

/-- Translation by `a` in the `x` direction. -/
def translation (a : ℝ) (p : Point2D) : Point2D := (p.1 + a, p.2)

/-- Glide reflection: translate by `a`, then reflect. -/
def glideReflection (a : ℝ) (p : Point2D) : Point2D := (p.1 + a, -p.2)

/-- A glide reflection squared is the translation by twice the glide length. -/
theorem glide_sq_is_translation (a : ℝ) :
    (fun p : Point2D => glideReflection a (glideReflection a p)) = translation (2 * a) := by
  funext p
  rcases p with ⟨x, y⟩
  simp [glideReflection, translation]
  ring

/-- The reflection part is an involution. -/
theorem reflectionX_sq : (fun p : Point2D => reflectionX (reflectionX p)) = id := by
  funext p
  rcases p with ⟨x, y⟩
  simp [reflectionX]

end WallpaperIsometry
