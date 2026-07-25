import Mathlib.Tactic
import InfoGeometry.Topology.BrillouinKleinGaugeInvariant
import InfoGeometry.Topology.ProjectiveKleinCompactification
import InfoGeometry.Topology.V4RootSystem
import InfoGeometry.Canonical.PhotonicParabolicTransfer
import InfoGeometry.Canonical.WallpaperKleinBottleCartan
import InfoGeometry.Canonical.WallpaperPin55RootCrossSection

/-!
# Brillouin Klein bottle manifold: finite projective-gauge shadow

This module formalizes the exact finite algebra behind the Brillouin Klein
bottle story:

* a `Z₂` projective gauge pair of translations anticommutes, `Tx Ty = - Ty Tx`;
* after quotienting by the central sign, the same pair commutes projectively and
  gives a `V₄`-style shadow;
* the momentum-space glide `(kx,ky) ↦ (kx+1,-ky)` conjugates the vertical
  reciprocal-lattice loop to its inverse, the Klein-bottle relation;
* orientation reversal forces any signed integer Chern readout satisfying
  `c = -c` to vanish;
* the surviving Brillouin-Klein invariant is the existing `Z₂` boundary phase
  invariant.

The file is theorem-safe: it does not construct analytic Bloch bundles, Berry
connections, spectral gaps, edge modes, or a full condensed-matter phase
classification.  Those remain explicit certificate fields.
-/

namespace InfoGeometry.Topology.BrillouinKleinBottleManifold

open Matrix
open InfoGeometry.Topology.BrillouinKleinGauge

abbrev M2Q := Matrix (Fin 2) (Fin 2) ℚ
abbrev KPoint := Fin 2 → ℚ

/-- Horizontal projective translation/gauge generator. -/
def Tx : M2Q :=
  !![0, 1; 1, 0]

/-- Vertical `Z₂` gauge generator. -/
def Ty : M2Q :=
  !![1, 0; 0, -1]

/-- Central fermion/gauge sign. -/
def minusI : M2Q :=
  -1

/-- The projective product channel. -/
def Txy : M2Q := Tx * Ty

/-- The two projective translation generators square to the identity. -/
theorem Tx_sq : Tx * Tx = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Tx, Matrix.mul_apply]

/-- The vertical gauge generator squares to the identity. -/
theorem Ty_sq : Ty * Ty = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Ty, Matrix.mul_apply]

/-- `-I` is central. -/
theorem minusI_central (A : M2Q) : minusI * A = A * minusI := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minusI, Matrix.mul_apply]

/-- The `Z₂` gauge flux: projective translations anticommute. -/
theorem projective_translation_anticommutes :
    Tx * Ty = -(Ty * Tx) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Tx, Ty, Matrix.mul_apply]

/-- Equivalent central-sign form of the anticommutation law. -/
theorem projective_translation_commutes_up_to_minusI :
    Tx * Ty = minusI * (Ty * Tx) := by
  rw [projective_translation_anticommutes]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minusI, Matrix.mul_apply]

/-- Matrix representatives are equivalent after quotienting by the central sign. -/
def ProjectiveSignEq (A B : M2Q) : Prop :=
  B = A ∨ B = -A

/-- The projective quotient turns anticommutation into commutation. -/
theorem projective_translation_commutes_in_quotient :
    ProjectiveSignEq (Tx * Ty) (Ty * Tx) := by
  right
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Tx, Ty, Matrix.mul_apply]

/-- The mixed channel also squares to the central sign. -/
theorem Txy_sq_eq_minusI : Txy * Txy = minusI := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Txy, Tx, Ty, minusI, Matrix.mul_apply]

/-- Hence the mixed channel is an involution projectively. -/
theorem Txy_projective_involution : ProjectiveSignEq (Txy * Txy) 1 := by
  right
  rw [Txy_sq_eq_minusI]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minusI]

/-- Momentum-space glide `(kx,ky) ↦ (kx+1,-ky)` in units where `π = 1`. -/
def glide (p : KPoint) : KPoint :=
  fun i => if i = 0 then p 0 + 1 else -p 1

/-- Its inverse is the same reflection with the opposite horizontal shift. -/
def glideInv (p : KPoint) : KPoint :=
  fun i => if i = 0 then p 0 - 1 else -p 1

/-- Vertical reciprocal-lattice loop. -/
def yLoop (p : KPoint) : KPoint :=
  fun i => if i = 0 then p 0 else p 1 + 2

/-- Inverse vertical reciprocal-lattice loop. -/
def yLoopInv (p : KPoint) : KPoint :=
  fun i => if i = 0 then p 0 else p 1 - 2

/-- The glide inverse is a right inverse. -/
theorem glide_right_inverse (p : KPoint) : glide (glideInv p) = p := by
  ext i
  fin_cases i <;> simp [glide, glideInv]

/-- The glide inverse is a left inverse. -/
theorem glide_left_inverse (p : KPoint) : glideInv (glide p) = p := by
  ext i
  fin_cases i <;> simp [glide, glideInv]

/-- Brillouin Klein relation: the glide conjugates the vertical loop to its inverse. -/
theorem glide_conjugates_yLoop_to_inverse (p : KPoint) :
    glide (yLoop (glideInv p)) = yLoopInv p := by
  ext i
  fin_cases i <;> simp [glide, glideInv, yLoop, yLoopInv] <;> ring

/-- Boundary-word form of the Brillouin Klein-bottle relation. -/
theorem brillouin_klein_boundary_word (p : KPoint) :
    glide (yLoop (glideInv (yLoop p))) = p := by
  rw [glide_conjugates_yLoop_to_inverse]
  ext i
  fin_cases i <;> simp [yLoop, yLoopInv]

/-- A signed Chern readout reversed by the non-orientable glide must vanish. -/
theorem chern_zero_of_orientation_reversal {c : ℤ} (h : c = -c) : c = 0 := by
  omega

/-- The surviving normalized boundary invariant is exactly the existing `Z₂` readout. -/
def brillouinKleinZ2 (gamma0 gammaPi : ℤ) : ℤ :=
  klein_bottle_z2_invariant gamma0 gammaPi

/-- The Brillouin-Klein `Z₂` invariant is stable under even gauge shifts. -/
theorem brillouinKleinZ2_gauge_stable (gamma0 gammaPi n : ℤ) :
    brillouinKleinZ2 (gamma0 + 2 * n) gammaPi = brillouinKleinZ2 gamma0 gammaPi :=
  klein_bottle_invariant_gauge_stable gamma0 gammaPi n

/-- Periodic parabolic transfer on a two-wall cell. -/
theorem parabolic_transfer_periodic_cell_pow (χ₁ χ₂ : ℝ) (n : ℕ) :
    (InfoGeometry.Canonical.PhotonicParabolicTransfer.T χ₁ *
      InfoGeometry.Canonical.PhotonicParabolicTransfer.T χ₂) ^ n =
    InfoGeometry.Canonical.PhotonicParabolicTransfer.T ((n : ℝ) * (χ₁ + χ₂)) := by
  exact InfoGeometry.Canonical.PhotonicParabolicTransfer.T_periodic_cell_pow χ₁ χ₂ n

/--
Theorem-safe certificate for a Bloch/Berry realization.  The analytic content is
supplied by fields; the finite matrix and glide laws above are closed theorems.
-/
structure BrillouinKleinInsulatorCertificate where
  gamma0 : ℤ
  gammaPi : ℤ
  chern : ℤ
  orientation_reverses_chern : chern = -chern
  edgeTwistParity : ℤ
  edgeTwistParity_eq_z2 : edgeTwistParity = brillouinKleinZ2 gamma0 gammaPi

namespace BrillouinKleinInsulatorCertificate

variable (C : BrillouinKleinInsulatorCertificate)

/-- The Chern readout vanishes under the supplied non-orientable orientation reversal. -/
theorem chern_eq_zero : C.chern = 0 :=
  chern_zero_of_orientation_reversal C.orientation_reverses_chern

/-- Edge twist parity is the Brillouin-Klein `Z₂` invariant. -/
theorem edge_twist_eq_z2 : C.edgeTwistParity = brillouinKleinZ2 C.gamma0 C.gammaPi :=
  C.edgeTwistParity_eq_z2

end BrillouinKleinInsulatorCertificate

/-- Closed finite packet tying projective gauge, central sign, glide, and `Z₂` readouts. -/
theorem brillouin_klein_bottle_manifold_packet :
    Tx * Ty = -(Ty * Tx) ∧
    ProjectiveSignEq (Tx * Ty) (Ty * Tx) ∧
    (∀ p : KPoint, glide (yLoop (glideInv p)) = yLoopInv p) ∧
    (∀ p : KPoint, glide (yLoop (glideInv (yLoop p))) = p) ∧
    (∀ gamma0 gammaPi n : ℤ,
      brillouinKleinZ2 (gamma0 + 2 * n) gammaPi = brillouinKleinZ2 gamma0 gammaPi) := by
  exact ⟨projective_translation_anticommutes,
    projective_translation_commutes_in_quotient,
    glide_conjugates_yLoop_to_inverse,
    brillouin_klein_boundary_word,
    brillouinKleinZ2_gauge_stable⟩

/-!
### Wallpaper / D₅ cross-section bridge

The Brillouin Klein bottle momentum packet is compatible with the existing
finite wallpaper and `D₅` cross-section owners.  This stays theorem-safe:
we only package the already verified finite actions and projections.
-/

/-- Momentum-space Klein bottle packet tied to the wallpaper / `D₅` cross-section. -/
theorem brillouin_klein_wallpaper_cross_section_packet :
    (∀ i : Fin 8,
      InfoGeometry.Canonical.WallpaperKleinBottleCartan.IsKleinCompatibleWallpaper
        (InfoGeometry.Canonical.WallpaperKleinBottleCartan.wallpaperD4 i)) ∧
    (∀ g r : Fin 8,
      InfoGeometry.Canonical.WallpaperPin55RootCrossSection.IsWallpaperB2Root
        (InfoGeometry.Canonical.WallpaperPin55RootCrossSection.matVec2
          (InfoGeometry.Canonical.WallpaperKleinBottleCartan.wallpaperD4 g)
          (InfoGeometry.Canonical.WallpaperPin55RootCrossSection.wallpaperB2Root r))) ∧
    (∀ i : Fin 8,
      InfoGeometry.Canonical.WallpaperPin55RootCrossSection.IsD5Root
        (InfoGeometry.Canonical.WallpaperPin55RootCrossSection.pin55LiftOfWallpaperRoot i)) ∧
    (∀ i : Fin 8,
      InfoGeometry.Canonical.WallpaperPin55RootCrossSection.projectRoot2
        (InfoGeometry.Canonical.WallpaperPin55RootCrossSection.pin55LiftOfWallpaperRoot i) =
          InfoGeometry.Canonical.WallpaperPin55RootCrossSection.wallpaperB2Root i) := by
  exact ⟨fun i =>
      InfoGeometry.Canonical.WallpaperKleinBottleCartan.wallpaperD4_is_klein_compatible i,
    fun g r =>
      InfoGeometry.Canonical.WallpaperPin55RootCrossSection.wallpaperD4_preserves_b2_roots g r,
    fun i =>
      InfoGeometry.Canonical.WallpaperPin55RootCrossSection.pin55LiftOfWallpaperRoot_isD5Root i,
    fun i =>
      InfoGeometry.Canonical.WallpaperPin55RootCrossSection.project_pin55LiftOfWallpaperRoot i⟩

end InfoGeometry.Topology.BrillouinKleinBottleManifold
