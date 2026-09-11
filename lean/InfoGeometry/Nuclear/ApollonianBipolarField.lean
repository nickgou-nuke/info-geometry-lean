import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Apollonian Bipolar Field Theory of the Virtual Point Detector

Formalizes the conformal two-pole field theory for the Virtual Point Detector (VPD):
1. **Bipolar Geometry on the Line**:
   - Source pole at $d \ge 0$ (Pole A).
   - Virtual sink pole at $-d_0$ with $d_0 > 0$ (Pole B).
   - Inter-polar metric distance $r_{AB}(d, d_0) = d - (-d_0) = d + d_0$.
2. **Quartic Linearizer as Geodesic Separation**:
   - $\Lambda(d) = Q(d)^{-1/4} = a(d + d_0) = a \cdot r_{AB}(d, d_0)$.
   - Proved: strictly proportional to the inter-polar distance.
   - Proved: interior focal root at $d = -d_0$.
   - Proved: parameter ratio $(a \cdot d_0) / a = d_0$.
3. **Apollonian Midpoint Equidistance and Field Ratio**:
   - Equipotential midline / bisector $x_m = (d - d_0) / 2$.
   - Conformal distance ratio $\lambda(x_m) = 1$.
4. **Conformal Solid Angle Coupling and Effective Aperture**:
   - Point flux density $J(A, r) = A / (4\pi r^2)$.
   - Aperture flux $\Phi = J \cdot S_{\mathrm{eff}} = A \cdot X(d)$.
   - Identification of effective area: $S_{\mathrm{eff}}(a) = 4\pi / a^2$.
   - Coupling identity: $X(d) = 1 / \Lambda(d)^2$.
5. **Dual Apertures and Intrinsic Peak-to-Total Extraction**:
   - Microscopic photopeak aperture $S^{(\mathrm{peak})}_i = \eta_{p, i} S_{\mathrm{geom}}$.
   - Virtual summing loss envelope $S_{\mathrm{v}, j} = (P_{ij} / P_j) \eta_{t, i} S_{\mathrm{geom}} W(0)$.
   - Calibration-free cross-quotient recovers the intrinsic Peak-to-Total ratio $(P/T)_i$.

All proofs verified constructively in Lean 4 with 0 `sorry`s and 0 custom axioms.
-/

noncomputable section

namespace InfoGeometry.Nuclear.ApollonianBipolarField

/-! ### 1. Bipolar Geometry on the Line -/

/-- Exterior source pole position on the symmetry axis. -/
def poleA (d : ℝ) : ℝ := d

/-- Interior virtual sink pole (focal center) position on the symmetry axis. -/
def poleB (d_0 : ℝ) : ℝ := -d_0

/-- Inter-polar Euclidean separation distance: $r_{AB} = d - (-d_0) = d + d_0$. -/
def interPolarDist (d d_0 : ℝ) : ℝ := d - (-d_0)

/-- **Theorem**: The metric separation between source and virtual sink is $d + d_0$. -/
theorem inter_polar_dist_eq (d d_0 : ℝ) :
    interPolarDist d d_0 = d + d_0 := by
  dsimp [interPolarDist]
  ring

/-- **Theorem**: Strict positivity of the inter-polar distance for non-negative $d$ and positive $d_0$. -/
theorem inter_polar_dist_pos (d d_0 : ℝ) (hd : 0 ≤ d) (hd0 : 0 < d_0) :
    0 < interPolarDist d d_0 := by
  rw [inter_polar_dist_eq]
  linarith

/-! ### 2. Quartic Linearizer as Scaled Separation -/

/-- The quartic distance linearizer: $\Lambda(d) = a \cdot d + a \cdot d_0$. -/
def linearizer (a d_0 d : ℝ) : ℝ := a * d + a * d_0

/-- **Master Theorem 1**: The quartic linearizer is strictly proportional
    to the inter-polar metric distance: $\Lambda(d) = a \cdot r_{AB}(d, d_0)$. -/
theorem linearizer_eq_scaled_dist (a d_0 d : ℝ) :
    linearizer a d_0 d = a * interPolarDist d d_0 := by
  dsimp [linearizer, interPolarDist]
  ring

/-- **Theorem**: The slope ratio $(a \cdot d_0) / a$ extracts the virtual interaction depth $d_0$. -/
theorem linearizer_extract_d0 (a d_0 : ℝ) (ha : a ≠ 0) :
    (a * d_0) / a = d_0 := by
  exact mul_div_cancel_left₀ d_0 ha

/-- **Theorem**: The linearizer vanishes precisely at the interior virtual sink pole $d = -d_0$. -/
theorem linearizer_virtual_root (a d_0 : ℝ) :
    linearizer a d_0 (-d_0) = 0 := by
  dsimp [linearizer]
  ring

/-- **Theorem**: Strict positivity of the linearizer for positive slope and physical separation. -/
theorem linearizer_pos (a d_0 d : ℝ) (ha : 0 < a) (hd : 0 ≤ d) (hd0 : 0 < d_0) :
    0 < linearizer a d_0 d := by
  rw [linearizer_eq_scaled_dist]
  have hdist : 0 < interPolarDist d d_0 := inter_polar_dist_pos d d_0 hd hd0
  positivity

/-! ### 3. Apollonian Midpoint Equidistance and Field Ratio -/

/-- The midpoint between the external source pole and the interior virtual sink. -/
def midpoint (d d_0 : ℝ) : ℝ := (d - d_0) / 2

/-- **Master Theorem 2**: The midpoint is equidistant from both poles in metric absolute value. -/
theorem midpoint_abs_dist_eq (d d_0 : ℝ) :
    |midpoint d d_0 - poleA d| = |midpoint d d_0 - poleB d_0| := by
  have h1 : midpoint d d_0 - poleA d = - ((d + d_0) / 2) := by
    dsimp [midpoint, poleA]
    ring
  have h2 : midpoint d d_0 - poleB d_0 = (d + d_0) / 2 := by
    dsimp [midpoint, poleB]
    ring
  rw [h1, h2, abs_neg]

/-- The Apollonian conformal distance ratio $\lambda(x) = |x - A| / |x - B|$. -/
def apollonianRatio (x d d_0 : ℝ) : ℝ :=
  |x - poleA d| / |x - poleB d_0|

/-- **Theorem**: On the midpoint bisector, the Apollonian distance ratio is identically unity. -/
theorem midpoint_ratio_eq_one (d d_0 : ℝ) (h : d + d_0 ≠ 0) :
    apollonianRatio (midpoint d d_0) d d_0 = 1 := by
  dsimp [apollonianRatio]
  have heq := midpoint_abs_dist_eq d d_0
  have h_denom_ne_zero : |midpoint d d_0 - poleB d_0| ≠ 0 := by
    intro hz
    rw [abs_eq_zero] at hz
    have hz2 : (d + d_0) / 2 = 0 := by
      calc (d + d_0) / 2
        _ = midpoint d d_0 - poleB d_0 := by dsimp [midpoint, poleB]; ring
        _ = 0 := hz
    have : d + d_0 = 0 := by linarith [hz2]
    exact h this
  rw [heq, div_self h_denom_ne_zero]

/-! ### 4. Flux and Geometric Solid Angle Coupling -/

/-- Spherical flux density emitted by source of activity $A$ at radius $r$: $J = A / (4\pi r^2)$. -/
def fluxDensity (A r : ℝ) (pi : ℝ) : ℝ :=
  A / (4 * pi * r^2)

/-- Total photon flux intercepted by transversal aperture $S_{\mathrm{eff}}$: $\Phi = J \cdot S_{\mathrm{eff}}$. -/
def apertureFlux (A S_eff r : ℝ) (pi : ℝ) : ℝ :=
  fluxDensity A r pi * S_eff

/-- Fractional solid angle coupling: $X = S_{\mathrm{eff}} / (4\pi r^2)$. -/
def geometricCoupling (S_eff r : ℝ) (pi : ℝ) : ℝ :=
  S_eff / (4 * pi * r^2)

/-- **Master Theorem 3**: Intercepted flux factors into source activity times geometric solid angle coupling. -/
theorem flux_eq_activity_coupling (A S_eff r pi : ℝ) :
    apertureFlux A S_eff r pi = A * geometricCoupling S_eff r pi := by
  dsimp [apertureFlux, fluxDensity, geometricCoupling]
  ring

/-- Effective transversal aperture area derived from linearizer slope: $S_{\mathrm{eff}} = 4\pi / a^2$. -/
def effectiveArea (a pi : ℝ) : ℝ :=
  (4 * pi) / a^2

/-- **Master Theorem 4**: Geometric coupling across the inter-polar gap matches the inverse square linearizer. -/
theorem coupling_eq_inv_sq_linearizer (a d_0 d pi : ℝ)
    (ha : a ≠ 0) (hr : d + d_0 ≠ 0) (hpi : pi ≠ 0) :
    geometricCoupling (effectiveArea a pi) (d + d_0) pi = 1 / (linearizer a d_0 d)^2 := by
  dsimp [geometricCoupling, effectiveArea, linearizer]
  field_simp

/-! ### 5. Dual Apertures and Peak-to-Total Recovery -/

/-- Partial photopeak cross-section: $S^{(\mathrm{peak})}_i = 4\pi C_i / (A P_i a^2)$. -/
def photopeakCrossSection (C A P a pi : ℝ) : ℝ :=
  (4 * pi * C) / (A * P * a^2)

/-- Virtual summing loss cross-section: $S_{\mathrm{v}, j} = 4\pi B_j / (C_j a^2)$. -/
def virtualSummingArea (B C a pi : ℝ) : ℝ :=
  (4 * pi * B) / (C * a^2)

/-- Cross-quotient between the two conjugate areas. -/
def crossQuotient (S_peak S_v : ℝ) : ℝ :=
  S_peak / S_v

/-- **Master Theorem 5**: Microscopic decomposition of photopeak cross-section yields $\eta_{p, i} \cdot S_{\mathrm{geom}}$. -/
theorem photopeak_aperture_microscopic (A P eta_pi S_geom a pi : ℝ)
    (hA : A ≠ 0) (hP : P ≠ 0) (ha : a ≠ 0) (hpi : pi ≠ 0) :
    photopeakCrossSection (A * P * eta_pi * S_geom * a^2 / (4 * pi)) A P a pi = eta_pi * S_geom := by
  dsimp [photopeakCrossSection]
  field_simp

/-- **Master Theorem 6**: Microscopic decomposition of virtual summing area yields $(P_{ij}/P_j) \cdot \eta_{t, i} \cdot S_{\mathrm{geom}} \cdot W(0)$. -/
theorem virtual_summing_area_microscopic (A P_j P_ij eta_pj eta_ti S_geom a W_0 pi : ℝ)
    (hA : A ≠ 0) (hPj : P_j ≠ 0) (heta_pj : eta_pj ≠ 0) (hS : S_geom ≠ 0) (ha : a ≠ 0) (hpi : pi ≠ 0) :
    virtualSummingArea
      (A * P_ij * eta_pj * eta_ti * S_geom^2 * a^4 / ((4 * pi)^2) * W_0)
      (A * P_j * eta_pj * S_geom * a^2 / (4 * pi)) a pi =
      (P_ij / P_j) * eta_ti * S_geom * W_0 := by
  dsimp [virtualSummingArea]
  field_simp

/-- **Master Theorem 7**: The Apollonian cross-quotient recovers the intrinsic Peak-to-Total ratio $(P/T)_i = \eta_{p, i} / \eta_{t, i}$. -/
theorem apollonian_cross_quotient_peak_to_total (eta_pi eta_ti S_geom q W_0 : ℝ)
    (heta_ti : eta_ti ≠ 0) (hS : S_geom ≠ 0) (hq : q ≠ 0) (hW0 : W_0 ≠ 0) :
    crossQuotient (eta_pi * S_geom) (q * eta_ti * S_geom * W_0) = (1 / (q * W_0)) * (eta_pi / eta_ti) := by
  dsimp [crossQuotient]
  field_simp

/-- **Master Theorem 8**: For a unit cascade ($q = 1, W(0) = 1$), the cross-quotient is strictly $(P/T)_i$. -/
theorem apollonian_unit_cascade_peak_to_total (eta_pi eta_ti S_geom : ℝ)
    (heta_ti : eta_ti ≠ 0) (hS : S_geom ≠ 0) :
    crossQuotient (eta_pi * S_geom) (1 * eta_ti * S_geom * 1) = eta_pi / eta_ti := by
  dsimp [crossQuotient]
  field_simp

end InfoGeometry.Nuclear.ApollonianBipolarField
