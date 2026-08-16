import Mathlib.Tactic

import InfoGeometry.Arithmetic.RiemannXiCayleyZeroBridge
import InfoGeometry.Arithmetic.RHRealDoubledKreinReformulation
import InfoGeometry.Canonical.KleinBottleWallpaper

/-!
# Completed Xi in homogeneous Hestenes coordinates

This file is the small algebraic commuting square behind the completed-Xi
Cayley coordinate.  It uses the distinguished pair `(s, 1 - s)` rather than
introducing an unrelated projective chart.

The file stops before logarithmic branches, cylinder quotients, and Klein
gluing.  It also makes no assertion about the location of zeta zeros.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.CompletedXiHestenesHomogeneousCoordinates

open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Canonical.KleinBottleWallpaper
open InfoGeometry.Canonical.HolographicSouriauClosure
open InfoGeometry.Arithmetic.RHRealDoubledKreinReformulation
open InfoGeometry.Krein

abbrev HomogeneousCoord : Type := ℂ × ℂ

/-- The distinguished two-lane homogeneous coordinate of `s`. -/
def homogeneousCoord (s : ℂ) : HomogeneousCoord :=
  (s, 1 - s)

/-- Hestenes/Weyl swap of the two homogeneous lanes. -/
def hestenesSwap : HomogeneousCoord → HomogeneousCoord :=
  fun X => (X.2, X.1)

/-- Split Cartan grading on the homogeneous lanes. -/
def hestenesEpsilon : HomogeneousCoord → HomogeneousCoord :=
  fun X => (X.1, -X.2)

/-- Real quarter-turn axis on the homogeneous lanes. -/
def hestenesK : HomogeneousCoord → HomogeneousCoord :=
  fun X => (-X.2, X.1)

/-- Projective ratio of a homogeneous pair. -/
def projectiveRatio (X : HomogeneousCoord) : ℂ :=
  X.1 / X.2

/-- The zeta projective coordinate `τ = s/(1-s)`. -/
def tau (s : ℂ) : ℂ :=
  projectiveRatio (homogeneousCoord s)

/-! ## Native pointwise Hestenes algebra -/

@[simp] theorem hestenesSwap_sq (X : HomogeneousCoord) :
    hestenesSwap (hestenesSwap X) = X := by
  rcases X with ⟨p, q⟩
  rfl

@[simp] theorem hestenesEpsilon_sq (X : HomogeneousCoord) :
    hestenesEpsilon (hestenesEpsilon X) = X := by
  rcases X with ⟨p, q⟩
  simp [hestenesEpsilon]

@[simp] theorem hestenesK_sq (X : HomogeneousCoord) :
    hestenesK (hestenesK X) = (-X.1, -X.2) := by
  rcases X with ⟨p, q⟩
  rfl

theorem hestenesSwap_epsilon_anticommute (X : HomogeneousCoord) :
    hestenesSwap (hestenesEpsilon X) =
      -(hestenesEpsilon (hestenesSwap X)) := by
  rcases X with ⟨p, q⟩
  simp [hestenesSwap, hestenesEpsilon]

theorem projectiveRatio_hestenesEpsilon
    (p q : ℂ) :
    projectiveRatio (hestenesEpsilon (p, q)) =
      -projectiveRatio (p, q) := by
  simpa [projectiveRatio, hestenesEpsilon] using (div_neg p)

theorem hestenesK_eq_swap_epsilon (X : HomogeneousCoord) :
    hestenesK X = hestenesSwap (hestenesEpsilon X) := by
  rfl

/-! ## Projective reconstruction and generic functional descent -/

def projectiveS (X : HomogeneousCoord) : ℂ :=
  X.1 / (X.1 + X.2)

theorem projectiveS_homogeneousCoord (s : ℂ) :
    projectiveS (homogeneousCoord s) = s := by
  simp [projectiveS, homogeneousCoord]

def homogeneousFunction (f : ℂ → ℂ) (X : HomogeneousCoord) : ℂ :=
  f (projectiveS X)

theorem homogeneousFunction_swap_invariant
    (f : ℂ → ℂ)
    (hfunc : ∀ s, f (1 - s) = f s)
    {X : HomogeneousCoord}
    (hX : X.1 + X.2 ≠ 0) :
    homogeneousFunction f (hestenesSwap X) =
      homogeneousFunction f X := by
  unfold homogeneousFunction projectiveS hestenesSwap
  have hX' : X.2 + X.1 ≠ 0 := by
    simpa [add_comm] using hX
  have harg : X.2 / (X.2 + X.1) =
      1 - X.1 / (X.1 + X.2) := by
    apply (div_eq_iff hX').2
    field_simp [hX]
    ring
  rw [harg]
  exact hfunc _

theorem completedXi_homogeneousFunction_swap (X : HomogeneousCoord)
    (hX : X.1 + X.2 ≠ 0) :
    homogeneousFunction riemannXi (hestenesSwap X) =
      homogeneousFunction riemannXi X := by
  exact homogeneousFunction_swap_invariant riemannXi
    (fun s => riemannXi_one_sub s) hX

theorem homogeneousCoord_one_sub (s : ℂ) :
    homogeneousCoord (1 - s) =
      hestenesSwap (homogeneousCoord s) := by
  unfold homogeneousCoord hestenesSwap
  congr 1 <;> ring

theorem tau_eq_cayleyToFugacity (s : ℂ) :
    tau s = cayleyToFugacity s :=
  rfl

theorem tau_one_sub_eq_inv (s : ℂ) :
    tau (1 - s) = (tau s)⁻¹ := by
  simpa [tau] using
    (cayleyToFugacity_one_sub_eq_inv s)

/-- Diagonal determinant-one split-Cartan flow on homogeneous coordinates. -/
def cartanFlow (t : ℝ) : HomogeneousCoord → HomogeneousCoord :=
  fun X =>
    ((Real.exp t : ℂ) * X.1,
      (Real.exp (-t) : ℂ) * X.2)

theorem cartanFlow_apply (t : ℝ) (p q : ℂ) :
    cartanFlow t (p, q) =
      ((Real.exp t : ℂ) * p,
        (Real.exp (-t) : ℂ) * q) :=
  rfl

theorem projectiveRatio_cartanFlow
    (t : ℝ) {p q : ℂ} (hq : q ≠ 0) :
    projectiveRatio (cartanFlow t (p, q)) =
      (Real.exp (2 * t) : ℂ) * projectiveRatio (p, q) := by
  unfold projectiveRatio cartanFlow
  field_simp [hq, ne_of_gt (Real.exp_pos t),
    ne_of_gt (Real.exp_pos (-t))]
  have hexp :
      (Real.exp (-t) : ℂ) * (Real.exp (t * 2) : ℂ) =
        (Real.exp t : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 1
    ring
  calc
    (Real.exp t : ℂ) * p = p * (Real.exp t : ℂ) := by ring
    _ = p * ((Real.exp (-t) : ℂ) * (Real.exp (t * 2) : ℂ)) := by
      rw [hexp]
    _ = p * (Real.exp (-t) : ℂ) * (Real.exp (t * 2) : ℂ) := by
      ring

theorem hestenesSwap_cartanFlow_swap
    (t : ℝ) (X : HomogeneousCoord) :
    hestenesSwap (cartanFlow t (hestenesSwap X)) =
      cartanFlow (-t) X := by
  rcases X with ⟨p, q⟩
  unfold hestenesSwap cartanFlow
  simp [Real.exp_neg]

theorem projectiveRatio_hestenesK
    {p q : ℂ} (hp : p ≠ 0) (hq : q ≠ 0) :
    projectiveRatio (hestenesK (p, q)) =
      -(projectiveRatio (p, q))⁻¹ := by
  unfold projectiveRatio hestenesK
  field_simp [hp, hq]

theorem criticalLine_iff_tau_unitCircle (s : ℂ) :
    OnCriticalLine s ↔
      OnLeeYangCircle (tau s) := by
  simpa [tau_eq_cayleyToFugacity] using
    (criticalLine_iff_cayley_unitCircle s)

theorem completedXi_functional_equation (s : ℂ) :
    riemannXi (1 - s) = riemannXi s :=
  riemannXi_one_sub s

theorem homogeneous_functional_intertwining (s : ℂ) :
    homogeneousCoord (1 - s) =
      hestenesSwap (homogeneousCoord s) :=
  homogeneousCoord_one_sub s

theorem completedXi_homogeneous_closure (s : ℂ) :
    homogeneousCoord (1 - s) =
        hestenesSwap (homogeneousCoord s) ∧
    tau (1 - s) = (tau s)⁻¹ ∧
    riemannXi (1 - s) = riemannXi s := by
  exact ⟨homogeneous_functional_intertwining s,
    tau_one_sub_eq_inv s,
    completedXi_functional_equation s⟩

/-! ## Centered zeta coordinates and the native wallpaper glide -/

abbrev CenteredZetaCoord : Type := ℝ × ℝ

/-- The centered real/imaginary coordinates `s = 1/2 + u + iv`. -/
def centeredZetaCoord (s : ℂ) : CenteredZetaCoord :=
  (s.re - (1 / 2 : ℝ), s.im)

/-- The functional reflection `s ↦ 1 - s` in centered coordinates. -/
theorem centeredZetaCoord_one_sub (s : ℂ) :
    centeredZetaCoord (1 - s) =
      (-((centeredZetaCoord s).1), -((centeredZetaCoord s).2)) := by
  unfold centeredZetaCoord
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
    neg_sub, sub_neg_eq_add]
  ext <;> ring

/-- The critical seam is the zero first coordinate in the centered chart. -/
def centeredCriticalSeam (p : CenteredZetaCoord) : Prop :=
  p.1 = 0

theorem centeredZetaCoord_mem_seam_iff (s : ℂ) :
    centeredCriticalSeam (centeredZetaCoord s) ↔ OnCriticalLine s := by
  unfold centeredCriticalSeam centeredZetaCoord OnCriticalLine
  constructor <;> intro h <;> linarith

/-- The existing wallpaper glide, read in centered zeta coordinates. -/
def zetaWallpaperGlide (p : CenteredZetaCoord) : CenteredZetaCoord :=
  InfoGeometry.Canonical.HolographicSouriauClosure.glide_reflection p

theorem zetaWallpaperGlide_apply (u v : ℝ) :
    zetaWallpaperGlide (u, v) = (-u, v + 1 / 2) := by
  rfl

theorem zetaWallpaperGlide_square (p : CenteredZetaCoord) :
    zetaWallpaperGlide (zetaWallpaperGlide p) = (p.1, p.2 + 1) := by
  exact InfoGeometry.Canonical.HolographicSouriauClosure.glide_reflection_squared p

theorem centeredZetaCoord_glide_readout (s : ℂ) :
    zetaWallpaperGlide (centeredZetaCoord s) =
      (-((centeredZetaCoord s).1), (centeredZetaCoord s).2 + 1 / 2) := by
  rfl

theorem zetaWallpaperGlide_preserves_seam (p : CenteredZetaCoord)
    (hp : centeredCriticalSeam p) :
    centeredCriticalSeam (zetaWallpaperGlide p) := by
  unfold centeredCriticalSeam zetaWallpaperGlide
    InfoGeometry.Canonical.HolographicSouriauClosure.glide_reflection at *
  simp [hp]

def transverseTranslation (a : ℝ) (p : CenteredZetaCoord) : CenteredZetaCoord :=
  (p.1 + a, p.2)

theorem transverseTranslation_zero (p : CenteredZetaCoord) :
    transverseTranslation 0 p = p := by
  rcases p with ⟨u, v⟩
  simp [transverseTranslation]

theorem transverseTranslation_add (a b : ℝ) (p : CenteredZetaCoord) :
    transverseTranslation a (transverseTranslation b p) =
      transverseTranslation (a + b) p := by
  rcases p with ⟨u, v⟩
  simp [transverseTranslation]
  ring

theorem zetaWallpaperGlide_conjugates_transverseTranslation (a : ℝ)
    (p : CenteredZetaCoord) :
    zetaWallpaperGlide (transverseTranslation a (G_inv p)) =
      transverseTranslation (-a) p := by
  rcases p with ⟨u, v⟩
  simp [zetaWallpaperGlide, G_inv,
    InfoGeometry.Canonical.HolographicSouriauClosure.glide_reflection,
    transverseTranslation]
  ring

theorem zetaWallpaperGlide_conjugates_unit_transverseTranslation
    (p : CenteredZetaCoord) :
    zetaWallpaperGlide (transverseTranslation 1 (G_inv p)) =
      transverseTranslation (-1) p := by
  simpa using zetaWallpaperGlide_conjugates_transverseTranslation 1 p

theorem centeredZetaCoord_functional_glide_dictionary (s : ℂ) :
    centeredZetaCoord (1 - s) =
      (-((centeredZetaCoord s).1), -((centeredZetaCoord s).2)) ∧
    zetaWallpaperGlide (centeredZetaCoord s) =
      (-((centeredZetaCoord s).1), (centeredZetaCoord s).2 + 1 / 2) := by
  exact ⟨centeredZetaCoord_one_sub s, centeredZetaCoord_glide_readout s⟩

/-! ## Thin transport into the existing real Hestenes carrier -/

/-- The centered zeta coordinate as an operator on the repository's native
real doubled Hestenes/Krein carrier. -/
noncomputable abbrev centeredHestenesCoordinate
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (s : ℂ) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  hestenesComplexCoordinate E (s - (1 / 2 : ℂ))

theorem centeredHestenesCoordinate_conjugation
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (s : ℂ) :
    modular_j (E := E) * centeredHestenesCoordinate E s * modular_j (E := E) =
      centeredHestenesCoordinate E (star s) := by
  unfold centeredHestenesCoordinate
  rw [hestenesComplexCoordinate_conjugation]
  congr 1
  simp [map_sub]

theorem centeredHestenesCoordinate_antiunitary_reflection
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (s : ℂ) :
    centeredHestenesCoordinate E (1 - star s) =
      hestenesComplexCoordinate E (-(star (s - (1 / 2 : ℂ)))) := by
  unfold centeredHestenesCoordinate
  congr 1
  simp [map_sub]
  ring

end InfoGeometry.Arithmetic.CompletedXiHestenesHomogeneousCoordinates

end
