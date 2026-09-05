import InfoGeometry.Geometry.RindlerLapseCalculus
import Mathlib

/-!
# Boltzmann charge sign and one-dimensional electrostatic calculus

The carrier variable eta = (E_F - E_i)/(k_B*T) is dimensionless. These are
Maxwell--Boltzmann model densities, not exact Fermi--Dirac distributions.
Ionized dopants are separate data. An arbitrary mapped logarithmic lapse
potential is not asserted to solve a self-consistent Poisson--Boltzmann problem.
-/

namespace InfoGeometry.Physics.BoltzmannPoissonReconstruction

noncomputable section

open InfoGeometry.Geometry.RindlerLapseCalculus

def electronDensity (ni eta : ℝ) : ℝ := ni * Real.exp eta
def holeDensity (ni eta : ℝ) : ℝ := ni * Real.exp (-eta)
def intrinsicCharge (e ni eta : ℝ) : ℝ :=
  e * (holeDensity ni eta - electronDensity ni eta)

theorem electronDensity_pos (ni eta : ℝ) (hni : 0 < ni) :
    0 < electronDensity ni eta := mul_pos hni (Real.exp_pos _)

theorem holeDensity_pos (ni eta : ℝ) (hni : 0 < ni) :
    0 < holeDensity ni eta := mul_pos hni (Real.exp_pos _)

theorem mass_action (ni eta : ℝ) :
    electronDensity ni eta * holeDensity ni eta = ni ^ 2 := by
  dsimp [electronDensity, holeDensity]
  calc
    _ = ni ^ 2 * (Real.exp eta * Real.exp (-eta)) := by ring
    _ = ni ^ 2 := by rw [← Real.exp_add]; simp

/-- The minus sign is forced by electron charge -e and hole charge +e. -/
theorem intrinsicCharge_eq_neg_sinh (e ni eta : ℝ) :
    intrinsicCharge e ni eta = -2 * e * ni * Real.sinh eta := by
  rw [Real.sinh_eq]
  dsimp [intrinsicCharge, electronDensity, holeDensity]
  ring

theorem intrinsicCharge_odd (e ni eta : ℝ) :
    intrinsicCharge e ni (-eta) = -intrinsicCharge e ni eta := by
  simp [intrinsicCharge, electronDensity, holeDensity]
  ring

theorem intrinsicCharge_zero_iff (e ni eta : ℝ) (he : 0 < e) (hni : 0 < ni) :
    intrinsicCharge e ni eta = 0 ↔ eta = 0 := by
  constructor
  · intro h
    have hs : holeDensity ni eta - electronDensity ni eta = 0 :=
      (mul_eq_zero.mp h).resolve_left he.ne'
    have hd : ni * Real.exp (-eta) = ni * Real.exp eta := sub_eq_zero.mp hs
    have hx : Real.exp (-eta) = Real.exp eta := mul_left_cancel₀ hni.ne' hd
    have ha := Real.exp_injective hx
    linarith
  · rintro rfl
    simp [intrinsicCharge, electronDensity, holeDensity]

theorem intrinsicCharge_neg_of_pos (e ni eta : ℝ)
    (he : 0 < e) (hni : 0 < ni) (heta : 0 < eta) :
    intrinsicCharge e ni eta < 0 := by
  have hlt : Real.exp (-eta) < Real.exp eta := Real.exp_lt_exp.mpr (by linarith)
  have hd : holeDensity ni eta < electronDensity ni eta :=
    mul_lt_mul_of_pos_left hlt hni
  exact mul_neg_of_pos_of_neg he (sub_neg.mpr hd)

theorem intrinsicCharge_pos_of_neg (e ni eta : ℝ)
    (he : 0 < e) (hni : 0 < ni) (heta : eta < 0) :
    0 < intrinsicCharge e ni eta := by
  have h := intrinsicCharge_neg_of_pos e ni (-eta) he hni (by linarith)
  rw [intrinsicCharge_odd] at h
  linarith

theorem hasDerivAt_intrinsicCharge (e ni eta : ℝ) :
    HasDerivAt (intrinsicCharge e ni) (-2 * e * ni * Real.cosh eta) eta := by
  have hf : intrinsicCharge e ni = fun z => -2 * e * ni * Real.sinh z :=
    funext (intrinsicCharge_eq_neg_sinh e ni)
  rw [hf]
  exact (Real.hasDerivAt_sinh eta).const_mul (-2 * e * ni)

def dopedCharge (e ni donors acceptors eta : ℝ) : ℝ :=
  e * (donors - acceptors + holeDensity ni eta - electronDensity ni eta)

theorem dopedCharge_decomposition (e ni donors acceptors eta : ℝ) :
    dopedCharge e ni donors acceptors eta =
      e * (donors - acceptors) - 2 * e * ni * Real.sinh eta := by
  have h := intrinsicCharge_eq_neg_sinh e ni eta
  dsimp [dopedCharge, intrinsicCharge] at *
  linarith

/-- Solving neutrality does not identify a Rindler horizon. -/
theorem neutrality_potential (e ni EF theta phi : ℝ)
    (he : 0 < e) (hni : 0 < ni) (htheta : 0 < theta) :
    intrinsicCharge e ni ((EF + e * phi) / theta) = 0 ↔ phi = -EF / e := by
  rw [intrinsicCharge_zero_iff e ni _ he hni]
  rw [div_eq_zero_iff]
  constructor
  · intro h
    have hn : EF + e * phi = 0 := h.resolve_right htheta.ne'
    apply (eq_div_iff he.ne').2
    linarith
  · intro h
    left
    rw [h]
    field_simp [he.ne'] <;> ring

/-- A constant-charge Poisson profile with two free integration constants. -/
def uniformChargePotential (rho eps c0 c1 x : ℝ) : ℝ :=
  c0 + c1 * x - rho / (2 * eps) * x ^ 2

def uniformChargeField (rho eps c1 x : ℝ) : ℝ := rho / eps * x - c1

theorem hasDerivAt_uniformChargePotential (rho eps c0 c1 x : ℝ) (heps : eps ≠ 0) :
    HasDerivAt (uniformChargePotential rho eps c0 c1)
      (-uniformChargeField rho eps c1 x) x := by
  convert (((hasDerivAt_id x).const_mul c1).const_add c0).sub
    (((hasDerivAt_id x).pow 2).const_mul (rho / (2 * eps))) using 1 <;>
    dsimp [uniformChargePotential, uniformChargeField] <;>
    field_simp [heps] <;> ring

theorem hasDerivAt_uniformChargeField (rho eps c1 x : ℝ) :
    HasDerivAt (uniformChargeField rho eps c1) (rho / eps) x := by
  simpa [uniformChargeField] using
    ((hasDerivAt_id x).const_mul (rho / eps)).sub_const c1

theorem uniformCharge_gauss (rho eps c1 x : ℝ) (heps : eps ≠ 0) :
    eps * deriv (uniformChargeField rho eps c1) x = rho := by
  rw [(hasDerivAt_uniformChargeField rho eps c1 x).deriv]
  field_simp [heps]

theorem uniformCharge_poisson (rho eps c0 c1 x : ℝ) (heps : eps ≠ 0) :
    deriv (deriv (uniformChargePotential rho eps c0 c1)) x = -rho / eps := by
  have hf : deriv (uniformChargePotential rho eps c0 c1) =
      fun y => -uniformChargeField rho eps c1 y := by
    funext y
    exact (hasDerivAt_uniformChargePotential rho eps c0 c1 y heps).deriv
  rw [hf]
  simpa using (hasDerivAt_uniformChargeField rho eps c1 x).neg.deriv

/-- An explicit analogue dictionary: phi = c*log N. It is a chosen model, not an isomorphism. -/
def logarithmicPotential (c a x : ℝ) : ℝ := c * Real.log (lapse a x)
def logarithmicField (c a x : ℝ) : ℝ := -c * stationaryAcceleration a x

theorem hasDerivAt_logarithmicPotential (c a x : ℝ) (hx : lapse a x ≠ 0) :
    HasDerivAt (logarithmicPotential c a) (-logarithmicField c a x) x := by
  convert (hasDerivAt_log_lapse a x hx).const_mul c using 1 <;>
    dsimp [logarithmicPotential, logarithmicField] <;> ring

theorem hasDerivAt_logarithmicField (c a x : ℝ) (hx : lapse a x ≠ 0) :
    HasDerivAt (logarithmicField c a) (c * (stationaryAcceleration a x) ^ 2) x := by
  convert (hasDerivAt_stationaryAcceleration a x hx).const_mul (-c) using 1 <;>
    dsimp [logarithmicField] <;> ring

/-- The electrostatic source of the chosen log-lapse profile is generally nonzero. -/
theorem logarithmicField_gauss_source (eps c a x : ℝ) (hx : lapse a x ≠ 0) :
    eps * deriv (logarithmicField c a) x = eps * c * (stationaryAcceleration a x) ^ 2 := by
  rw [(hasDerivAt_logarithmicField c a x hx).deriv]
  ring

theorem logarithmicField_source_pos (eps c a x : ℝ)
    (heps : 0 < eps) (hc : 0 < c) (ha : 0 < a) (hx : 0 < lapse a x) :
    0 < eps * deriv (logarithmicField c a) x := by
  rw [logarithmicField_gauss_source eps c a x hx.ne']
  have hacc : 0 < stationaryAcceleration a x := div_pos ha hx
  positivity

end
end InfoGeometry.Physics.BoltzmannPoissonReconstruction
