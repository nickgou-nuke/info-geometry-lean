import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Boundary Majorana Mass Gap

Finite scalar theorem surface for the boundary Majorana/twistor-knot gap.

This module proves only the controlled finite readouts:

* the boundary gap is the supplied minimum positive singular value of a real
  skew Majorana quadratic form;
* a Pfaffian/index transition forces a zero Pfaffian and hence a gap closing;
* chiral Majorana central charge bookkeeping gives `N_R - N_L = 16` for
  `c_- = 8`;
* the chiral boundary CFT pressure formula specializes to the `E₈` value;
* a Weyl-scaled gap has logarithmic scale response `log Δ = log Δ₀ - φ`.

No Riemann-spectrum theorem, `E₈` representation theorem, or full gravity
theorem is asserted here.
-/

namespace InfoGeometry.Physics.BoundaryMajoranaMassGap

/-! ## 1. Boundary Majorana spectrum and gap -/

/--
Finite Majorana boundary spectrum.

`lambda j` represents the positive singular values of the real skew matrix
`A` in a quadratic Majorana Hamiltonian.  `gap` is supplied as the minimum
nonzero quasiparticle gap readout.
-/
structure BoundaryMajoranaSpectrum (Mode : Type*) where
  lambda : Mode → ℝ
  gap : ℝ
  gap_nonneg : 0 ≤ gap
  gap_le_abs_lambda : ∀ j, gap ≤ |lambda j|
  gap_attained : ∃ j, gap = |lambda j|

namespace BoundaryMajoranaSpectrum

/-- The quasiparticle gap is nonnegative. -/
theorem massGap_nonneg {Mode : Type*} (S : BoundaryMajoranaSpectrum Mode) :
    0 ≤ S.gap :=
  S.gap_nonneg

/-- The gap is bounded by every singular-value magnitude. -/
theorem massGap_le_abs_lambda {Mode : Type*} (S : BoundaryMajoranaSpectrum Mode) (j : Mode) :
    S.gap ≤ |S.lambda j| :=
  S.gap_le_abs_lambda j

/-- The supplied gap is attained by at least one mode. -/
theorem massGap_attained {Mode : Type*} (S : BoundaryMajoranaSpectrum Mode) :
    ∃ j, S.gap = |S.lambda j| :=
  S.gap_attained

end BoundaryMajoranaSpectrum

/-! ## 2. Pfaffian transition obstruction -/

/--
Pfaffian transition package for a finite Majorana boundary path.

`gap_zero_of_pfaffian_zero` is the finite Majorana fact that a zero Pfaffian
means the skew matrix is singular, so at least one singular value and hence
the gap vanishes.  The path/intermediate-value analysis is not hidden here:
the critical point `critical` with zero Pfaffian is explicit data.
-/
structure PfaffianKnotTransition (Path : Type*) where
  pfaffian : Path → ℝ
  gap : Path → ℝ
  critical : Path
  pfaffian_critical_eq_zero : pfaffian critical = 0
  gap_zero_of_pfaffian_zero : ∀ s, pfaffian s = 0 → gap s = 0

namespace PfaffianKnotTransition

/-- At the supplied Pfaffian transition point, the boundary gap closes. -/
theorem critical_gap_closes {Path : Type*} (T : PfaffianKnotTransition Path) :
    T.gap T.critical = 0 :=
  T.gap_zero_of_pfaffian_zero T.critical T.pfaffian_critical_eq_zero

/-- A protected Pfaffian/index transition has some point where the gap closes. -/
theorem topological_transition_forces_gap_closing
    {Path : Type*} (T : PfaffianKnotTransition Path) :
    ∃ s, T.gap s = 0 :=
  ⟨T.critical, T.critical_gap_closes⟩

end PfaffianKnotTransition

/-! ## 3. Chiral Majorana central charge bookkeeping -/

/--
Chiral Majorana boundary central charge.

`netChiral = N_R - N_L` and `cMinus = netChiral / 2`.
-/
structure ChiralMajoranaCentralCharge where
  rightModes : ℝ
  leftModes : ℝ
  netChiral : ℝ
  cMinus : ℝ
  netChiral_eq : netChiral = rightModes - leftModes
  cMinus_eq : cMinus = netChiral / 2

namespace ChiralMajoranaCentralCharge

/-- Chiral central charge is half the net chiral Majorana count. -/
theorem cMinus_eq_half_net (C : ChiralMajoranaCentralCharge) :
    C.cMinus = C.netChiral / 2 :=
  C.cMinus_eq

/-- If `c_- = 8`, the required net chiral Majorana count is `16`. -/
theorem netChiral_eq_sixteen_of_cMinus_eq_eight
    (C : ChiralMajoranaCentralCharge)
    (hE8 : C.cMinus = 8) :
    C.netChiral = 16 := by
  rw [C.cMinus_eq] at hE8
  nlinarith

/-- The `E₈` level-one central-charge condition is `N_R - N_L = 16`. -/
theorem right_minus_left_eq_sixteen_of_cMinus_eq_eight
    (C : ChiralMajoranaCentralCharge)
    (hE8 : C.cMinus = 8) :
    C.rightModes - C.leftModes = 16 := by
  rw [← C.netChiral_eq]
  exact C.netChiral_eq_sixteen_of_cMinus_eq_eight hE8

end ChiralMajoranaCentralCharge

/-! ## 4. Chiral boundary CFT pressure -/

/--
Scalar chiral boundary CFT pressure readout.

The intended formula is `P = π c_- T² / (12 v)`.  At horizon temperature
`T = κ/(2π)`, this becomes `P = c_- κ²/(48π v)`.
-/
structure ChiralBoundaryCFTPressure where
  cMinus : ℝ
  velocity : ℝ
  temperature : ℝ
  kappa : ℝ
  pressure : ℝ
  temperature_eq_horizon : temperature = kappa / (2 * Real.pi)
  pressure_eq : pressure = Real.pi * cMinus * temperature ^ 2 / (12 * velocity)

namespace ChiralBoundaryCFTPressure

/-- Chiral CFT thermal pressure before substituting the horizon temperature. -/
theorem pressure_eq_thermal (P : ChiralBoundaryCFTPressure) :
    P.pressure = Real.pi * P.cMinus * P.temperature ^ 2 / (12 * P.velocity) :=
  P.pressure_eq

/-- Horizon-temperature pressure: `P = c_- κ² / (48πv)`. -/
theorem pressure_eq_horizon (P : ChiralBoundaryCFTPressure) :
    P.pressure = P.cMinus * P.kappa ^ 2 / (48 * Real.pi * P.velocity) := by
  rw [P.pressure_eq, P.temperature_eq_horizon]
  field_simp [Real.pi_ne_zero]
  ring

/-- For `c_- = 8`, the pressure is `κ²/(6πv)`. -/
theorem pressure_eq_E8
    (P : ChiralBoundaryCFTPressure)
    (hE8 : P.cMinus = 8) :
    P.pressure = P.kappa ^ 2 / (6 * Real.pi * P.velocity) := by
  rw [P.pressure_eq_horizon, hE8]
  ring

end ChiralBoundaryCFTPressure

/-! ## 5. Weyl scaling of the boundary gap -/

/--
Weyl scaling of a boundary Majorana gap.

The intended readout is `Δ(φ) = exp(-φ) Δ₀`.
-/
structure WeylGapScaling where
  phi : ℝ
  gap0 : ℝ
  gap : ℝ
  gap0_pos : 0 < gap0
  gap_eq : gap = Real.exp (-phi) * gap0

namespace WeylGapScaling

/-- Weyl scaling keeps the gap positive when the reference gap is positive. -/
theorem gap_pos (W : WeylGapScaling) :
    0 < W.gap := by
  rw [W.gap_eq]
  exact mul_pos (Real.exp_pos _) W.gap0_pos

/-- Logarithmic Weyl gap scaling: `log Δ = log Δ₀ - φ`. -/
theorem log_gap_eq_log_gap0_sub_phi (W : WeylGapScaling) :
    Real.log W.gap = Real.log W.gap0 - W.phi := by
  rw [W.gap_eq]
  rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt W.gap0_pos)]
  rw [Real.log_exp]
  ring

end WeylGapScaling

end InfoGeometry.Physics.BoundaryMajoranaMassGap
