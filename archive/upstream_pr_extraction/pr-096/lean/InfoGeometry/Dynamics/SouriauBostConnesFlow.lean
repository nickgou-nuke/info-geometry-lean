import Mathlib.Tactic
import InfoGeometry.Canonical.CayleyBregmanBridge

/-!
# Souriau--Bost--Connes Flow Corridor

This file isolates the theorem-owned part of the proposed metriplectic-attractor
closure.  It proves the finite algebraic flow-sign facts and the elementary
Cayley geometry, while keeping the analytic Riemann-zeta claims as explicit
premises.

#### BUCKET 1: CLOSED FINITE THEOREMS

* `flow_direction_positive`: a positive dissipation coefficient and a negative
  entropy gradient force the inverse-temperature velocity to be positive.
* `cayley_right_half_plane_normSq_lt`: the Cayley numerator has smaller norm
  square than the denominator on the open right half-plane.
* `cayley_right_half_plane_maps_to_unit_disk`: the Cayley transform maps the
  open right half-plane into the open unit disk.
* `golden_ratio_order_parameter`: the Fibonacci quantum dimension satisfies
  `φ^2 - φ - 1 = 0`.
* `thermal_cayley_absolute_zero_limit`: the repository-owned real thermal
  Cayley coordinate tends to the boundary point `1`.

#### OPEN CLOSURE DEBT

* Prove the real zeta limit `ζ(β) -> 1` from the Dirichlet-series estimate.
* Prove the strict sign of the zeta logarithmic derivative in the desired
  corridor and connect it to `souriauEntropyGradient`.
* Construct the Cantor-boundary accumulation map.  The Cayley theorem here only
  proves the continuous right-half-plane-to-disk geometry.
-/

open scoped Topology

noncomputable section

namespace InfoGeometry.Dynamics.SouriauBostConnesFlow

open Complex
open InfoGeometry.Canonical

/-! ## 1. Metriplectic flow sign -/

/--
The Souriau entropy gradient channel.  In the intended zeta specialization,
`logZetaDerivative β` is `ζ'(β) / ζ(β)`.
-/
def souriauEntropyGradient (logZetaDerivative : ℝ → ℝ) (β : ℝ) : ℝ :=
  logZetaDerivative β

/-- The metriplectic inverse-temperature vector field. -/
def metriplecticFlowField (κ : ℝ) (logZetaDerivative : ℝ → ℝ) (β : ℝ) : ℝ :=
  -κ * souriauEntropyGradient logZetaDerivative β

/--
If the dissipation coefficient is positive and the entropy gradient is negative,
the inverse temperature increases.
-/
theorem flow_direction_positive
    {κ β : ℝ} {logZetaDerivative : ℝ → ℝ}
    (hκ : 0 < κ)
    (hgrad : souriauEntropyGradient logZetaDerivative β < 0) :
    metriplecticFlowField κ logZetaDerivative β > 0 := by
  dsimp [metriplecticFlowField]
  nlinarith [mul_pos hκ (neg_pos.mpr hgrad)]

/-! ## 2. Cayley compactification geometry -/

/-- The centered Cayley transform from the open right half-plane to the disk. -/
def cayleyTransform (s : ℂ) : ℂ :=
  (s - (1 / 2 : ℂ)) / (s + (1 / 2 : ℂ))

/-- The Cayley denominator is nonzero on the open right half-plane. -/
theorem cayley_denominator_ne_zero {s : ℂ} (hreal : 0 < s.re) :
    s + (1 / 2 : ℂ) ≠ 0 := by
  intro h
  have hre : (s + (1 / 2 : ℂ)).re = 0 := by
    simpa using congrArg Complex.re h
  norm_num at hre
  linarith

/--
On the open right half-plane, the Cayley numerator has smaller norm square than
the denominator.
-/
theorem cayley_right_half_plane_normSq_lt (s : ℂ) (hreal : 0 < s.re) :
    Complex.normSq (s - (1 / 2 : ℂ)) < Complex.normSq (s + (1 / 2 : ℂ)) := by
  rw [Complex.normSq_apply, Complex.normSq_apply]
  norm_num
  nlinarith

/-- The centered Cayley transform maps the open right half-plane into the unit disk. -/
theorem cayley_right_half_plane_maps_to_unit_disk (s : ℂ) (hreal : 0 < s.re) :
    ‖cayleyTransform s‖ < 1 := by
  have hlt := cayley_right_half_plane_normSq_lt s hreal
  have hden_ne : s + (1 / 2 : ℂ) ≠ 0 := cayley_denominator_ne_zero hreal
  have hden_pos : 0 < Complex.normSq (s + (1 / 2 : ℂ)) :=
    Complex.normSq_pos.mpr hden_ne
  have hsq :
      ‖cayleyTransform s‖ ^ 2 < (1 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, cayleyTransform, Complex.normSq_div]
    rw [one_pow]
    exact (div_lt_one hden_pos).mpr hlt
  have hnorm_nonneg : 0 ≤ ‖cayleyTransform s‖ := norm_nonneg _
  nlinarith

/-! ## 3. Boundary phases and order parameter -/

/-- The positive Fibonacci braiding phase. -/
def braidingPhasePositive : ℂ :=
  Complex.exp (Complex.I * (4 * Real.pi / 5))

/-- The negative Fibonacci braiding phase. -/
def braidingPhaseNegative : ℂ :=
  Complex.exp (Complex.I * (-2 * Real.pi / 5))

/-- Both boundary braiding phases lie on the unit circle. -/
theorem braiding_phases_unit_norm :
    ‖braidingPhasePositive‖ = 1 ∧ ‖braidingPhaseNegative‖ = 1 := by
  constructor
  · simp [braidingPhasePositive, Complex.norm_exp]
  · simp [braidingPhaseNegative, Complex.norm_exp]

/-- The golden-ratio order parameter satisfies its minimal polynomial. -/
theorem golden_ratio_order_parameter :
    let phi : ℝ := (1 + Real.sqrt 5) / 2
    phi ^ 2 - phi - 1 = 0 := by
  intro phi
  dsimp [phi]
  have hsqrt : (Real.sqrt 5) ^ 2 = (5 : ℝ) := by
    exact Real.sq_sqrt (by norm_num)
  nlinarith

/-! ## 4. Genuine Cayley limit owner; zeta limits remain open -/

/--
The real thermal-ray Cayley coordinate reaches the boundary point `1` at
absolute zero.  This delegates to the existing Cayley owner.
-/
theorem thermal_cayley_absolute_zero_limit :
    Filter.Tendsto Cayley.thermalCayley Filter.atTop (𝓝 (1 : ℝ)) :=
  Cayley.thermalCayley_tendsto_atTop_one

end InfoGeometry.Dynamics.SouriauBostConnesFlow
