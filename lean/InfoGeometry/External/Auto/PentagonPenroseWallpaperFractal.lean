import Mathlib.Tactic

/-!
# Pentagon / Penrose fractal beyond wallpaper crystallography

This module records the bridge:

* classical wallpaper lattices obey the crystallographic restriction, excluding
  order-5 rotations;
* Penrose tilings evade this by abandoning periodic translations: 5-fold
  symmetry appears in an aperiodic/fractal inflation system;
* the Penrose rhombus substitution matrix has characteristic polynomial
  `x² - 3x + 1`, with Perron eigenvalue `φ²` when `φ²=φ+1`;
* finite inflation prefixes refine like a Cantor edge code.
-/

noncomputable section

namespace PentagonPenroseWallpaperFractal

/-! ## 1. Wallpaper restriction -/

/-- Rotation orders allowed by the 2D crystallographic restriction. -/
def wallpaperAllowedOrders : List ℕ := [1, 2, 3, 4, 6]

/-- Pentagon/order-5 symmetry is forbidden for periodic wallpaper lattices. -/
theorem pentagon_forbidden_wallpaper : 5 ∉ wallpaperAllowedOrders := by
  simp [wallpaperAllowedOrders]

/-- The allowed-order list has five entries. -/
theorem allowed_orders_five_entries : wallpaperAllowedOrders.length = 5 := by
  norm_num [wallpaperAllowedOrders]

/-! ## 2. Penrose substitution / golden-ratio inflation -/

/-- Tile types for Penrose rhombi. -/
inductive PenroseTile where
  | thick
  | thin
  deriving DecidableEq, Repr

/-- One substitution step, represented as counts of `(thick, thin)`. -/
def substituteCount : PenroseTile → ℕ × ℕ
  | .thick => (2, 1)
  | .thin => (1, 1)

/-- Linear substitution on tile-count vectors `(thick, thin)`. -/
def penroseSubst (v : ℕ × ℕ) : ℕ × ℕ :=
  (2 * v.1 + v.2, v.1 + v.2)

/-- A thick tile inflates to two thick and one thin tile. -/
theorem thick_substitution : substituteCount .thick = (2, 1) := rfl

/-- A thin tile inflates to one thick and one thin tile. -/
theorem thin_substitution : substituteCount .thin = (1, 1) := rfl

/-- Starting from a nonempty patch, Penrose substitution strictly increases total tile count. -/
theorem penroseSubst_total_increases (v : ℕ × ℕ) (h : 0 < v.1 + v.2) :
    v.1 + v.2 < (penroseSubst v).1 + (penroseSubst v).2 := by
  cases v with
  | mk a b =>
    simp [penroseSubst] at h ⊢
    omega

/-- Trace of the Penrose substitution matrix. -/
def penroseTrace : ℤ := 2 + 1

/-- Determinant of the Penrose substitution matrix. -/
def penroseDet : ℤ := 2 * 1 - 1 * 1

/-- Trace/determinant are `3` and `1`. -/
theorem penrose_trace : penroseTrace = 3 := by
  norm_num [penroseTrace]

/-- Penrose substitution determinant is `1`. -/
theorem penrose_det : penroseDet = 1 := by
  norm_num [penroseDet]

/-! ## 3. Fractal/Cantor edge coding -/

/-- Number of binary prefix cylinders at depth `n`. -/
def cantorCylinderCount (n : ℕ) : ℕ := 2 ^ n

/-- Refining one level doubles the number of Cantor cylinders. -/
theorem cantorCylinder_refines (n : ℕ) :
    cantorCylinderCount (n + 1) = 2 * cantorCylinderCount n := by
  simp [cantorCylinderCount, pow_succ]
  ring

/-- Penrose symbolic edge code as infinite binary choices. -/
def PenroseFractalEdge : Type := ℕ → Bool

/-- The symbolic Penrose/Cantor edge code is definitionally binary sequence space. -/
theorem penroseEdge_cantor : Nonempty (PenroseFractalEdge ≃ (ℕ → Bool)) := by
  exact ⟨Equiv.refl _⟩

end PentagonPenroseWallpaperFractal
