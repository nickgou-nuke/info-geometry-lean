import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Spatial spinor hydrodynamic readout

The current uses the native complex inner product. Its quotient by the
density is an ordinary regular velocity component only away from zero density.
The estimates below concern this readout and its actual derivative; they do
not posit a wave evolution or a Navier--Stokes reconstruction theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.SpinorHydrodynamicReadout

open scoped InnerProductSpace

/-- The parity and spin indices are retained separately. -/
abbrev ParitySpinor := EuclideanSpace ℂ (Fin 2 × Fin 2)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def density (z : E) : ℝ := ‖z‖ ^ 2

def current (kappa : ℝ) (z v : E) : ℝ := kappa * (inner ℂ z v).im

def readout (kappa : ℝ) (z v : E) : ℝ := current kappa z v / density z

theorem density_eq_inner (z : E) : density z = (inner ℂ z z).re := by
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) z).symm

omit [InnerProductSpace ℂ E] in
theorem density_pos_iff (z : E) : 0 < density z ↔ z ≠ 0 := by
  simp [density, sq_pos_iff]

theorem abs_inner_im_le (z v : E) : |(inner ℂ z v).im| ≤ ‖z‖ * ‖v‖ :=
  (Complex.abs_im_le_norm _).trans (norm_inner_le_norm z v)

theorem abs_inner_re_le (z v : E) : |(inner ℂ z v).re| ≤ ‖z‖ * ‖v‖ :=
  (Complex.abs_re_le_norm _).trans (norm_inner_le_norm z v)

theorem abs_current_le {kappa : ℝ} (hk : 0 ≤ kappa) (z v : E) :
    |current kappa z v| ≤ kappa * ‖z‖ * ‖v‖ := by
  rw [current, abs_mul, abs_of_nonneg hk]
  exact (mul_le_mul_of_nonneg_left (abs_inner_im_le z v) hk).trans_eq (mul_assoc _ _ _).symm

theorem abs_readout_le {kappa : ℝ} (hk : 0 ≤ kappa) {z : E}
    (hz : z ≠ 0) (v : E) :
    |readout kappa z v| ≤ kappa * ‖v‖ / ‖z‖ := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [readout, abs_div, abs_of_nonneg (le_of_lt ((density_pos_iff z).mpr hz))]
  calc
    |current kappa z v| / density z ≤ (kappa * ‖z‖ * ‖v‖) / density z :=
      div_le_div_of_nonneg_right (abs_current_le hk z v) (le_of_lt ((density_pos_iff z).mpr hz))
    _ = kappa * ‖v‖ / ‖z‖ := by
      dsimp [density]
      field_simp

/-- The positive-density current is the real momentum weak expression with
the same vector in both boundary slots. An independent postselection is extra data. -/
theorem readout_eq_same_state_weak_expression (kappa : ℝ) (z v : E) :
    readout kappa z v =
      (inner ℂ z (((-Complex.I) * (kappa : ℂ)) • v) / inner ℂ z z).re := by
  have hd : inner ℂ z z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_pow] using (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) z)
  rw [inner_smul_right, hd, Complex.div_ofReal_re]
  simp [readout, current, density, Complex.mul_re, Complex.mul_im]

def densityRate (z dz : E) : ℝ := 2 * (inner ℂ z dz).re

def currentRate (kappa : ℝ) (z dz v dv : E) : ℝ :=
  kappa * ((inner ℂ z dv).im + (inner ℂ dz v).im)

def readoutRate (kappa : ℝ) (z dz v dv : E) : ℝ :=
  (currentRate kappa z dz v dv * density z - current kappa z v * densityRate z dz) /
    density z ^ 2

theorem hasDerivAt_density {f : ℝ → E} {df : E} {t : ℝ}
    (hf : HasDerivAt f df t) :
    HasDerivAt (fun r => density (f r)) (densityRate (f t) df) t := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hf.inner ℂ hf)
  have hs : (inner ℂ df (f t)).re = (inner ℂ (f t) df).re :=
    inner_re_symm (𝕜 := ℂ) df (f t)
  simpa [Function.comp_def, density_eq_inner, densityRate, Complex.add_re, hs, two_mul] using h

theorem hasDerivAt_current (kappa : ℝ) {f g : ℝ → E} {df dg : E} {t : ℝ}
    (hf : HasDerivAt f df t) (hg : HasDerivAt g dg t) :
    HasDerivAt (fun r => current kappa (f r) (g r))
      (currentRate kappa (f t) df (g t) dg) t := by
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hf.inner ℂ hg)
  simpa [current, currentRate, Complex.add_im] using h.const_mul kappa

theorem hasDerivAt_readout (kappa : ℝ) {f g : ℝ → E} {df dg : E} {t : ℝ}
    (hf : HasDerivAt f df t) (hg : HasDerivAt g dg t) (hz : f t ≠ 0) :
    HasDerivAt (fun r => readout kappa (f r) (g r))
      (readoutRate kappa (f t) df (g t) dg) t := by
  exact (hasDerivAt_current kappa hf hg).div (hasDerivAt_density hf)
    (ne_of_gt ((density_pos_iff (f t)).mpr hz))

end InfoGeometry.Canonical.SpinorHydrodynamicReadout
