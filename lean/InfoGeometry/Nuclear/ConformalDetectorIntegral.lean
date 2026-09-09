import InfoGeometry.Nuclear.ApollonianBipolarField
import InfoGeometry.Nuclear.FocalRapidity

/-!
# Prolate spheroidal focal algebra and the rapidity-weighted volume kernel

The focal convention is `A = (0, 0, c)`, `B = (0, 0, -c)`,
`rA = c * (xi - nu)`, `rB = c * (xi + nu)`.

This module identifies the meridional focal distances, the product conformal
factor, and the exact algebraic rewriting of the specified volume density.
The inverse-square factor is reused from `ApollonianBipolarField.fluxDensity`.

`volumeDensity` is the specified prolate coordinate density. A change-of-variables
integral theorem, a derivative/Jacobian theorem for a chart, refractive-index
identification, photon transport, and an exact VPD reduction are NOT asserted.
Cancellation leaves a focal ratio; it does not give a global boundedness theorem.
-/

noncomputable section

namespace InfoGeometry.Nuclear.Conformal

structure SpheroidalOpticalConfig where
  c : ℝ
  hc_pos : 0 < c

namespace SpheroidalOpticalConfig

/-- Interior prolate coordinates; focal and axial degeneracies are excluded. -/
structure Point where
  xi : ℝ
  nu : ℝ
  hxi : 1 < xi
  hnu : |nu| < 1

namespace Point

def rA (cfg : SpheroidalOpticalConfig) (p : Point) : ℝ :=
  cfg.c * (p.xi - p.nu)

def rB (cfg : SpheroidalOpticalConfig) (p : Point) : ℝ :=
  cfg.c * (p.xi + p.nu)

/-- Squared cylindrical radius of the prolate Cartesian parametrization. -/
def rhoSq (cfg : SpheroidalOpticalConfig) (p : Point) : ℝ :=
  cfg.c ^ 2 * (p.xi ^ 2 - 1) * (1 - p.nu ^ 2)

def rho (cfg : SpheroidalOpticalConfig) (p : Point) : ℝ :=
  Real.sqrt (rhoSq cfg p)

def axial (cfg : SpheroidalOpticalConfig) (p : Point) : ℝ :=
  cfg.c * p.xi * p.nu

/-- Algebraic conformal scale squared, not a physical refractive index. -/
def conformalScaleSq (cfg : SpheroidalOpticalConfig) (p : Point) : ℝ :=
  cfg.c ^ 2 * (p.xi ^ 2 - p.nu ^ 2)

/-- Specified prolate volume-density formula; its chart derivation is separate. -/
def volumeDensity (cfg : SpheroidalOpticalConfig) (p : Point) : ℝ :=
  cfg.c ^ 3 * (p.xi ^ 2 - p.nu ^ 2)

def rapidity (cfg : SpheroidalOpticalConfig) (p : Point) : ℝ :=
  FocalRapidity.rapidity (rA cfg p) (rB cfg p)

/-- Volume-weighted point-flux kernel, using the repository's existing owner. -/
def fluxVolumeKernel (cfg : SpheroidalOpticalConfig) (p : Point) : ℝ :=
  ApollonianBipolarField.fluxDensity 1 (rA cfg p) Real.pi * volumeDensity cfg p

theorem diff_pos (p : Point) : 0 < p.xi - p.nu := by
  have h := (abs_lt.mp p.hnu).2
  linarith [p.hxi]

theorem sum_pos (p : Point) : 0 < p.xi + p.nu := by
  have h := (abs_lt.mp p.hnu).1
  linarith [p.hxi]

theorem rA_pos (cfg : SpheroidalOpticalConfig) (p : Point) : 0 < rA cfg p :=
  mul_pos cfg.hc_pos (diff_pos p)

theorem rB_pos (cfg : SpheroidalOpticalConfig) (p : Point) : 0 < rB cfg p :=
  mul_pos cfg.hc_pos (sum_pos p)

theorem quadric_factor_pos (p : Point) : 0 < p.xi ^ 2 - p.nu ^ 2 := by
  have h := mul_pos (diff_pos p) (sum_pos p)
  nlinarith

theorem rhoSq_pos (cfg : SpheroidalOpticalConfig) (p : Point) : 0 < rhoSq cfg p := by
  have hxi : 0 < p.xi ^ 2 - 1 := by nlinarith [p.hxi, sq_nonneg (p.xi - 1)]
  have hnu : 0 < 1 - p.nu ^ 2 := by
    have h := (sq_lt_one_iff_abs_lt_one p.nu).mpr p.hnu
    linarith
  exact mul_pos (mul_pos (sq_pos_of_pos cfg.hc_pos) hxi) hnu

theorem rho_sq (cfg : SpheroidalOpticalConfig) (p : Point) :
    rho cfg p ^ 2 = rhoSq cfg p :=
  Real.sq_sqrt (le_of_lt (rhoSq_pos cfg p))

/-- Cartesian meridional distance to the focus at `+c`. -/
theorem cartesian_rA_sq (cfg : SpheroidalOpticalConfig) (p : Point) :
    rho cfg p ^ 2 + (axial cfg p - cfg.c) ^ 2 = rA cfg p ^ 2 := by
  rw [rho_sq]
  dsimp [rhoSq, axial, rA]
  ring

/-- Cartesian meridional distance to the focus at `-c`. -/
theorem cartesian_rB_sq (cfg : SpheroidalOpticalConfig) (p : Point) :
    rho cfg p ^ 2 + (axial cfg p + cfg.c) ^ 2 = rB cfg p ^ 2 := by
  rw [rho_sq]
  dsimp [rhoSq, axial, rB]
  ring

theorem focal_sum (cfg : SpheroidalOpticalConfig) (p : Point) :
    rA cfg p + rB cfg p = 2 * cfg.c * p.xi := by
  dsimp [rA, rB]
  ring

theorem focal_difference (cfg : SpheroidalOpticalConfig) (p : Point) :
    rB cfg p - rA cfg p = 2 * cfg.c * p.nu := by
  dsimp [rA, rB]
  ring

theorem focal_product (cfg : SpheroidalOpticalConfig) (p : Point) :
    rA cfg p * rB cfg p = cfg.c ^ 2 * (p.xi ^ 2 - p.nu ^ 2) := by
  dsimp [rA, rB]
  ring

theorem conformalScaleSq_eq_focal_product (cfg : SpheroidalOpticalConfig) (p : Point) :
    conformalScaleSq cfg p = rA cfg p * rB cfg p :=
  (focal_product cfg p).symm

theorem volumeDensity_eq_scale (cfg : SpheroidalOpticalConfig) (p : Point) :
    volumeDensity cfg p = cfg.c * conformalScaleSq cfg p := by
  dsimp [volumeDensity, conformalScaleSq]
  ring

theorem volumeDensity_pos (cfg : SpheroidalOpticalConfig) (p : Point) :
    0 < volumeDensity cfg p :=
  mul_pos (pow_pos cfg.hc_pos 3) (quadric_factor_pos p)

/-- One focal factor cancels, leaving the exact distance ratio. -/
theorem volume_over_rASq_eq_conformal_ratio
    (cfg : SpheroidalOpticalConfig) (p : Point) :
    volumeDensity cfg p / rA cfg p ^ 2 =
      cfg.c * ((p.xi + p.nu) / (p.xi - p.nu)) := by
  dsimp [volumeDensity, rA]
  field_simp [ne_of_gt cfg.hc_pos, ne_of_gt (diff_pos p)]; ring

theorem focal_ratio (cfg : SpheroidalOpticalConfig) (p : Point) :
    rB cfg p / rA cfg p = (p.xi + p.nu) / (p.xi - p.nu) := by
  dsimp [rA, rB]
  field_simp [ne_of_gt cfg.hc_pos, ne_of_gt (diff_pos p)]

theorem conformal_weight_eq_exp_two_rapidity
    (cfg : SpheroidalOpticalConfig) (p : Point) :
    Real.exp (2 * rapidity cfg p) = (p.xi + p.nu) / (p.xi - p.nu) := by
  rw [rapidity, FocalRapidity.exp_two_rapidity (rA_pos cfg p) (rB_pos cfg p)]
  exact focal_ratio cfg p

theorem fluxVolumeKernel_eq_ratio (cfg : SpheroidalOpticalConfig) (p : Point) :
    fluxVolumeKernel cfg p =
      (cfg.c / (4 * Real.pi)) * ((p.xi + p.nu) / (p.xi - p.nu)) := by
  dsimp [fluxVolumeKernel, ApollonianBipolarField.fluxDensity, volumeDensity, rA]
  field_simp [ne_of_gt cfg.hc_pos, ne_of_gt (diff_pos p),
    ne_of_gt Real.pi_pos]; ring

theorem fluxVolumeKernel_eq_exp (cfg : SpheroidalOpticalConfig) (p : Point) :
    fluxVolumeKernel cfg p = (cfg.c / (4 * Real.pi)) * Real.exp (2 * rapidity cfg p) := by
  rw [fluxVolumeKernel_eq_ratio, conformal_weight_eq_exp_two_rapidity]

/-- The same pointwise identity remains valid under an arbitrary scalar weight. -/
theorem weighted_fluxVolumeKernel_eq_exp
    (cfg : SpheroidalOpticalConfig) (p : Point) (w : ℝ) :
    w * fluxVolumeKernel cfg p =
      w * ((cfg.c / (4 * Real.pi)) * Real.exp (2 * rapidity cfg p)) := by
  rw [fluxVolumeKernel_eq_exp]

theorem tanh_rapidity_eq_nu_div_xi (cfg : SpheroidalOpticalConfig) (p : Point) :
    Real.tanh (rapidity cfg p) = p.nu / p.xi := by
  rw [rapidity, FocalRapidity.tanh_rapidity_eq_difference_ratio
    (rA_pos cfg p) (rB_pos cfg p), focal_difference, focal_sum]
  have hxi : p.xi ≠ 0 := by linarith [p.hxi]
  field_simp [ne_of_gt cfg.hc_pos, hxi]

/-- The exact sech envelope in prolate focal coordinates. -/
theorem sech_rapidity_eq_sqrt_ratio (cfg : SpheroidalOpticalConfig) (p : Point) :
    FocalRapidity.sechProfile (rapidity cfg p) =
      Real.sqrt (p.xi ^ 2 - p.nu ^ 2) / p.xi := by
  rw [rapidity, FocalRapidity.sech_rapidity_eq_overlap (rA_pos cfg p) (rB_pos cfg p)]
  rw [FocalRapidity.overlap, focal_product, focal_sum,
    Real.sqrt_mul (sq_nonneg cfg.c), Real.sqrt_sq (le_of_lt cfg.hc_pos)]
  have hxi : p.xi ≠ 0 := by linarith [p.hxi]
  field_simp [ne_of_gt cfg.hc_pos, hxi]

/-- A family approaching a focal boundary while remaining in the open chart. -/
def approachingFocus (eps : ℝ) (h0 : 0 < eps) (h1 : eps < 1) : Point where
  xi := 1 + eps
  nu := 1 - eps
  hxi := by linarith
  hnu := abs_lt.mpr ⟨by linarith, by linarith⟩

/-- The residual focal weight is `1 / eps`: cancellation is not global regularization. -/
theorem approachingFocus_weight (eps : ℝ) (h0 : 0 < eps) (h1 : eps < 1) :
    ((approachingFocus eps h0 h1).xi + (approachingFocus eps h0 h1).nu) /
      ((approachingFocus eps h0 h1).xi - (approachingFocus eps h0 h1).nu) = 1 / eps := by
  dsimp [approachingFocus]
  field_simp [ne_of_gt h0]; ring

end Point
end SpheroidalOpticalConfig
end InfoGeometry.Nuclear.Conformal
