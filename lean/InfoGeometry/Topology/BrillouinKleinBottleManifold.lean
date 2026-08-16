import Mathlib.Tactic
import InfoGeometry.Topology.BrillouinKleinGaugeInvariant
import InfoGeometry.Topology.ProjectiveKleinCompactification
import InfoGeometry.Topology.V4RootSystem
import InfoGeometry.Canonical.PhotonicParabolicTransfer
import InfoGeometry.Canonical.WallpaperKleinBottleCartan
import InfoGeometry.Canonical.WallpaperPin55RootCrossSection
import InfoGeometry.Canonical.HolographicSouriauReconstruction

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
classification.  Those remain explicit property fields.
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

/-! Projective identification by the central sign. -/

def ProjectiveSignEq (A B : M2Q) : Prop :=
  B = A ∨ B = -A

/-- `ProjectiveSignEq` is compatible with left and right multiplication. -/
theorem ProjectiveSignEq_mul {A B C D : M2Q} (hAB : ProjectiveSignEq A B)
    (hCD : ProjectiveSignEq C D) : ProjectiveSignEq (A * C) (B * D) := by
  rcases hAB with hAB | hAB <;> rcases hCD with hCD | hCD
  · exact Or.inl (by simpa [hAB, hCD])
  · exact Or.inr (by simpa [hAB, hCD, Matrix.mul_apply, mul_neg, neg_mul])
  · exact Or.inr (by simpa [hAB, hCD, Matrix.mul_apply, mul_neg, neg_mul])
  · exact Or.inl (by simpa [hAB, hCD, Matrix.mul_apply])

/-- Equivalent central-sign form of the anticommutation law. -/
theorem projective_translation_commutes_up_to_minusI :
    Tx * Ty = minusI * (Ty * Tx) := by
  rw [projective_translation_anticommutes]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minusI, Matrix.mul_apply]

/-- Setoid for projective identification by central sign. -/
def ProjectiveSignSetoid : Setoid M2Q where
  r := ProjectiveSignEq
  iseqv := ⟨
    by intro A; exact Or.inl rfl,
    by
      intro A B h
      rcases h with h | h
      · exact Or.inl (by simpa [h])
      · exact Or.inr (by simpa [h]),
    by
      intro A B C hAB hBC
      rcases hAB with hAB | hAB
      · simpa [hAB] using hBC
      · rcases hBC with hBC | hBC
        · exact Or.inr (by simpa [hAB] using hBC)
        · exact Or.inl (by simpa [hAB, neg_neg] using hBC)
  ⟩

/-- Projective quotient by `B = A` or `B = -A`. -/
def ProjectiveSignQuotient : Type := Quotient ProjectiveSignSetoid

/-- Canonical class map into the projective quotient. -/
def projectiveSignClass (A : M2Q) : ProjectiveSignQuotient :=
  Quotient.mk _ A

/-- Relation-compatibility of class map. -/
theorem projectiveSignClass_eq {A B : M2Q} (h : ProjectiveSignEq A B) :
    projectiveSignClass A = projectiveSignClass B := by
  exact Quotient.sound h

/-- Bridge: `Tx` is the product `-T * T`, where `T` is the rational Brillouin twist. -/
theorem Ty_eq_brillouinGlide2 : Ty = InfoGeometry.Canonical.HolographicSouriauReconstruction.brillouinGlide2 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [Ty,
    InfoGeometry.Canonical.HolographicSouriauReconstruction.brillouinGlide2]

/-- Bridge: `Txy` is the Brillouin twist matrix. -/
theorem Txy_eq_brillouinTwist2 : Txy = InfoGeometry.Canonical.HolographicSouriauReconstruction.brillouinTwist2 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Txy, Tx, Ty,
      InfoGeometry.Canonical.HolographicSouriauReconstruction.brillouinTwist2]

/-- Bridge: `Tx = T * S` in the `Brillouin` notation (`T=twist`, `S=glide`). -/
theorem Tx_eq_brillouinTwist2_mul_glide2 :
    Tx = InfoGeometry.Canonical.HolographicSouriauReconstruction.brillouinTwist2 *
      InfoGeometry.Canonical.HolographicSouriauReconstruction.brillouinGlide2 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Tx,
      InfoGeometry.Canonical.HolographicSouriauReconstruction.brillouinTwist2,
      InfoGeometry.Canonical.HolographicSouriauReconstruction.brillouinGlide2, Matrix.mul_apply]

/-- The projective quotient turns anticommutation into commutation. -/
theorem projective_translation_commutes_in_quotient :
    ProjectiveSignEq (Tx * Ty) (Ty * Tx) := by
  right
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Tx, Ty, Matrix.mul_apply]

/-- The quotient class form of projective commutation. -/
theorem projective_translation_commutes_in_quotient_class :
    projectiveSignClass (Tx * Ty) = projectiveSignClass (Ty * Tx) := by
  exact projectiveSignClass_eq (projective_translation_commutes_in_quotient)

theorem d8_wallpaperD4_central_sign_identification (i : Fin 8) :
    (InfoGeometry.Canonical.WallpaperKleinBottleCartan.wallpaperD4 i = 1 ∨
      InfoGeometry.Canonical.WallpaperKleinBottleCartan.wallpaperD4 i = -1 ↔
      i = 0 ∨ i = 2) := by
  fin_cases i <;> native_decide

theorem d8_wallpaperD4_Tx_identification :
    InfoGeometry.Canonical.WallpaperKleinBottleCartan.wallpaperD4 5 = Tx := by
  rw [Tx_eq_brillouinTwist2_mul_glide2]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Canonical.WallpaperKleinBottleCartan.wallpaperD4,
      InfoGeometry.Canonical.HolographicSouriauReconstruction.brillouinTwist2,
      InfoGeometry.Canonical.HolographicSouriauReconstruction.brillouinGlide2,
      Matrix.mul_apply, Tx, Ty, Txy]

theorem d8_wallpaperD4_Ty_identification :
    InfoGeometry.Canonical.WallpaperKleinBottleCartan.wallpaperD4 4 = Ty := by
  rw [Ty_eq_brillouinGlide2]
  simp [InfoGeometry.Canonical.WallpaperKleinBottleCartan.wallpaperD4]

theorem d8_wallpaperD4_Txy_identification :
    InfoGeometry.Canonical.WallpaperKleinBottleCartan.wallpaperD4 1 = Txy := by
  rw [Txy_eq_brillouinTwist2]
  simp [InfoGeometry.Canonical.WallpaperKleinBottleCartan.wallpaperD4]

theorem d8_wallpaperD4_projective_representatives (i : Fin 8) :
    projectiveSignClass (InfoGeometry.Canonical.WallpaperKleinBottleCartan.wallpaperD4 i) =
      (if i = 0 ∨ i = 2 then projectiveSignClass (1 : M2Q)
       else if i = 1 ∨ i = 3 then projectiveSignClass Txy
       else if i = 4 ∨ i = 6 then projectiveSignClass Ty
       else projectiveSignClass Tx) := by
  fin_cases i <;>
    simp [InfoGeometry.Canonical.WallpaperKleinBottleCartan.wallpaperD4,
      InfoGeometry.Canonical.HolographicSouriauReconstruction.brillouinTwist2,
      InfoGeometry.Canonical.HolographicSouriauReconstruction.brillouinGlide2,
      Tx, Ty, Txy, ProjectiveSignEq, projectiveSignClass, ProjectiveSignSetoid,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    apply projectiveSignClass_eq <;>
    right <;>
    ext a b <;> fin_cases a <;> fin_cases b <;> norm_num

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

/-- The quotient class form of projective involution of `Txy`. -/
theorem Txy_projective_involution_class :
    projectiveSignClass (Txy * Txy) = projectiveSignClass 1 := by
  exact projectiveSignClass_eq (Txy_projective_involution)

/-- Momentum-space glide `(kx,ky) ↦ (kx+1,-ky)` in units where `π = 1`. -/
def glide (p : KPoint) : KPoint :=
  fun i => if i = 0 then p 0 + 1 else -p 1

/-- Unit horizontal shift in `KPoint`. -/
def horizontalShift (n : ℚ) (p : KPoint) : KPoint :=
  fun i => if i = 0 then p 0 + n else p 1

theorem Ty_mulVec (p : KPoint) :
    Ty.mulVec p = fun i => if i = 0 then p 0 else -p 1 := by
  ext i
  fin_cases i <;> simp [Ty, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail,
    Fin.sum_univ_two]

theorem glide_eq_horizontalShift_one : ∀ p : KPoint,
    glide p = horizontalShift 1 (Ty.mulVec p) := by
  intro p
  ext i
  fin_cases i <;> simp [glide, horizontalShift, Ty_mulVec]

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
Theorem-safe property for a Bloch/Berry realization.  The analytic content is
supplied by fields; the finite matrix and glide laws above are closed theorems.
-/
abbrev BrillouinKleinInsulatorCertificate : Type :=
  Σ' gamma0 : ℤ,
    Σ' gammaPi : ℤ,
      Σ' chern : ℤ,
        Σ' _hchern : chern = -chern,
          Σ' edgeTwistParity : ℤ,
            edgeTwistParity = brillouinKleinZ2 gamma0 gammaPi

namespace BrillouinKleinInsulatorCertificate

variable (C : BrillouinKleinInsulatorCertificate)

abbrev gamma0 : ℤ := C.1

abbrev gammaPi : ℤ := C.2.1

abbrev chern : ℤ := C.2.2.1

abbrev orientation_reverses_chern : C.chern = -C.chern := C.2.2.2.1

abbrev edgeTwistParity : ℤ := C.2.2.2.2.1

abbrev edgeTwistParity_eq_z2 :
  C.edgeTwistParity = brillouinKleinZ2 C.gamma0 C.gammaPi :=
  C.2.2.2.2.2

/-- The Chern readout vanishes under the supplied non-orientable orientation reversal. -/
theorem chern_eq_zero : C.chern = 0 :=
  chern_zero_of_orientation_reversal C.orientation_reverses_chern

/-- Edge twist parity is the Brillouin-Klein `Z₂` invariant. -/
theorem edge_twist_eq_z2 : C.edgeTwistParity = brillouinKleinZ2 C.gamma0 C.gammaPi :=
  C.edgeTwistParity_eq_z2

end BrillouinKleinInsulatorCertificate

end InfoGeometry.Topology.BrillouinKleinBottleManifold
