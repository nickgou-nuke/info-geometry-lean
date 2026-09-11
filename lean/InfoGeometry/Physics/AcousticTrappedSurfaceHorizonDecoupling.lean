import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import InfoGeometry.Physics.ChiralAcousticBimetricConeSeparation

/-!
# Acoustic Trapped Surfaces and Dual Horizon Decoupling on Background Flow

This module formalizes:
1. Two-component acoustic fluid on a background velocity field `v₀` (`AcousticFlowSystem`):
   - Dual sound speeds `0 < c₋ < c₊`.
   - Local background flow speed `v ≥ 0`.
   - Mach numbers `M₋ = v / c₋` and `M₊ = v / c₊`.
2. Properties of local Mach numbers:
   - Ordering: `v > 0 → M₊ < M₋`.
3. Lab-frame acoustic metric `g₀₀` components:
   - `g₀₀(±) = -(c_±² - v²) = v² - c_±²`.
4. Trapped surface / acoustic horizon condition:
   - Supersonic flow for branch `±`: `v ≥ c_± ↔ g₀₀(±) ≥ 0`.
5. Birefringent transonic window `c₋ < v < c₊`:
   - Slow branch is supersonic: `M₋ > 1`, creating an acoustic trapped surface / horizon.
   - Fast branch is subsonic: `M₊ < 1`, remaining completely untrapped.
   - Opposite metric signs: `g₀₀(-) > 0` (slow trapped) and `g₀₀(+) < 0` (fast untrapped).
6. Horizon Decoupling and Upstream Propagation:
   - Slow phonons cannot propagate upstream: relative speed `c₋ - v < 0`.
   - Fast phonons escape upstream freely: relative speed `c₊ - v > 0`.
   - Horizon transparency: At the slow horizon `v = c₋`, `g₀₀(+) = c₋² - c₊² < 0`,
     proving the slow horizon is an ordinary transparent timelike region for fast phonons.
7. Background Flow Invariance of Bimetric Gap:
   - `g₀₀(+) - g₀₀(-) = -(c₊² - c₋²)`, completely independent of background speed `v`.
   - Interval difference `ds₊² - ds₋² = -(c₊² - c₋²) dt² ≤ 0`.
8. Master certified conjunction: `certified_acoustic_trapped_surface_synthesis`.
-/

namespace InfoGeometry.Physics.AcousticTrappedSurface

/-- Physical parameters of a two-component chiral fluid with background flow. -/
structure AcousticFlowSystem where
  c_minus : ℝ
  c_plus : ℝ
  v : ℝ
  hc_minus_pos : 0 < c_minus
  hc_gap : c_minus < c_plus
  hv_nonneg : 0 ≤ v

variable (sys : AcousticFlowSystem)

/-- Sound speed positivity for fast branch. -/
theorem c_plus_pos : 0 < sys.c_plus :=
  lt_trans sys.hc_minus_pos sys.hc_gap

/-- Local Mach number for slow branch: `M₋ = v / c₋`. -/
noncomputable def machMinus : ℝ :=
  sys.v / sys.c_minus

/-- Local Mach number for fast branch: `M₊ = v / c₊`. -/
noncomputable def machPlus : ℝ :=
  sys.v / sys.c_plus

/-- Mach numbers are non-negative. -/
theorem machMinus_nonneg : 0 ≤ machMinus sys :=
  div_nonneg sys.hv_nonneg (le_of_lt sys.hc_minus_pos)

theorem machPlus_nonneg : 0 ≤ machPlus sys :=
  div_nonneg sys.hv_nonneg (le_of_lt (c_plus_pos sys))

/-- **Theorem 1 (Mach Number Ordering)**:
    For any nonzero background flow `v > 0`, the fast Mach number is strictly
    smaller than the slow Mach number: `M₊ < M₋`. -/
theorem mach_ordering (hv_pos : 0 < sys.v) : machPlus sys < machMinus sys := by
  dsimp [machPlus, machMinus]
  have hc_plus_pos := c_plus_pos sys
  have h_den : sys.c_minus < sys.c_plus := sys.hc_gap
  exact div_lt_div_of_pos_left hv_pos sys.hc_minus_pos h_den

/-!
### 2. Lab-Frame Acoustic Metric and Ergosurface
-/

/-- Lab-frame `g₀₀` component for slow acoustic metric:
    `g₀₀(-) = -(c₋² - v²) = v² - c₋²`. -/
noncomputable def g00_minus : ℝ :=
  sys.v ^ 2 - sys.c_minus ^ 2

/-- Lab-frame `g₀₀` component for fast acoustic metric:
    `g₀₀(+) = -(c₊² - v²) = v² - c₊²`. -/
noncomputable def g00_plus : ℝ :=
  sys.v ^ 2 - sys.c_plus ^ 2

/-- **Theorem 2 (Bimetric Gap Invariance on Background Flow)**:
    The difference `g₀₀(+) - g₀₀(-)` is strictly independent of the background
    velocity `v` and equals `-(c₊² - c₋²)`. -/
theorem bimetric_gap_background_invariance :
    g00_plus sys - g00_minus sys = - (sys.c_plus ^ 2 - sys.c_minus ^ 2) := by
  dsimp [g00_plus, g00_minus]
  ring

/-- The bimetric gap is strictly negative. -/
theorem bimetric_gap_strictly_negative :
    g00_plus sys - g00_minus sys < 0 := by
  rw [bimetric_gap_background_invariance]
  have h1 : sys.c_minus ^ 2 < sys.c_plus ^ 2 := by
    nlinarith [sys.hc_minus_pos, sys.hc_gap]
  linarith

/-!
### 3. Trapped Surfaces in the Birefringent Transonic Window
-/

/-- The birefringent transonic window condition: `c₋ < v < c₊`. -/
def inBirefringentWindow : Prop :=
  sys.c_minus < sys.v ∧ sys.v < sys.c_plus

/-- **Theorem 3 (Supersonic Slow Branch in Transonic Window)**:
    In the transonic window, the slow branch is strictly supersonic: `M₋ > 1`. -/
theorem slow_supersonic_in_window (h_win : inBirefringentWindow sys) :
    1 < machMinus sys := by
  dsimp [machMinus]
  rw [one_lt_div sys.hc_minus_pos]
  exact h_win.1

/-- **Theorem 4 (Subsonic Fast Branch in Transonic Window)**:
    In the transonic window, the fast branch is strictly subsonic: `M₊ < 1`. -/
theorem fast_subsonic_in_window (h_win : inBirefringentWindow sys) :
    machPlus sys < 1 := by
  dsimp [machPlus]
  rw [div_lt_one (c_plus_pos sys)]
  exact h_win.2

/-- **Theorem 5 (Slow Branch Acoustic Trapped Surface)**:
    In the transonic window, the slow metric has `g₀₀(-) > 0`,
    forming an acoustic trapped region. -/
theorem slow_trapped_in_window (h_win : inBirefringentWindow sys) :
    0 < g00_minus sys := by
  dsimp [g00_minus]
  have hv : sys.c_minus < sys.v := h_win.1
  have hc : 0 < sys.c_minus := sys.hc_minus_pos
  nlinarith

/-- **Theorem 6 (Fast Branch Untrapped Space)**:
    In the transonic window, the fast metric has `g₀₀(+) < 0`,
    remaining untrapped. -/
theorem fast_untrapped_in_window (h_win : inBirefringentWindow sys) :
    g00_plus sys < 0 := by
  dsimp [g00_plus]
  have hv : sys.v < sys.c_plus := h_win.2
  have hv_nonneg : 0 ≤ sys.v := sys.hv_nonneg
  nlinarith

/-!
### 4. Upstream Propagation and Horizon Decoupling
-/

/-- Relative upstream propagation speed for slow phonons: `v_rel(-) = c₋ - v`. -/
noncomputable def upstreamSpeedMinus : ℝ :=
  sys.c_minus - sys.v

/-- Relative upstream propagation speed for fast phonons: `v_rel(+) = c₊ - v`. -/
noncomputable def upstreamSpeedPlus : ℝ :=
  sys.c_plus - sys.v

/-- **Theorem 7 (Slow Phonons Cannot Escape Upstream)**:
    In the transonic window, slow phonons cannot propagate upstream (`c₋ - v < 0`). -/
theorem slow_no_upstream_escape (h_win : inBirefringentWindow sys) :
    upstreamSpeedMinus sys < 0 := by
  dsimp [upstreamSpeedMinus]
  linarith [h_win.1]

/-- **Theorem 8 (Fast Phonons Escape Upstream Freely)**:
    In the transonic window, fast phonons propagate upstream freely (`c₊ - v > 0`). -/
theorem fast_upstream_escape (h_win : inBirefringentWindow sys) :
    0 < upstreamSpeedPlus sys := by
  dsimp [upstreamSpeedPlus]
  linarith [h_win.2]

/-- **Theorem 9 (Slow Horizon Transparency to Fast Modes)**:
    At the exact slow acoustic event horizon where `v = c₋`,
    the fast metric component is strictly negative:
    `g₀₀(+) = c₋² - c₊² < 0`.
    Hence the slow horizon is an ordinary transparent region for the fast mode. -/
theorem slow_horizon_transparent_to_fast (hv_horizon : sys.v = sys.c_minus) :
    g00_plus sys = sys.c_minus ^ 2 - sys.c_plus ^ 2 ∧ g00_plus sys < 0 := by
  constructor
  · dsimp [g00_plus]
    rw [hv_horizon]
  · dsimp [g00_plus]
    rw [hv_horizon]
    have hc1 : 0 < sys.c_minus := sys.hc_minus_pos
    have hc2 : sys.c_minus < sys.c_plus := sys.hc_gap
    nlinarith

/-- **Theorem 10 (Acoustic Interval Bimetric Gap with Background Flow)**:
    For any spacetime displacement `(dt, dx)` with background advection `dx - v₀ dt`,
    the net bimetric interval difference is:
    `ds₊² - ds₋² = - (c₊² - c₋²) dt² ≤ 0`. -/
theorem acoustic_interval_bimetric_gap (dt dx : ℝ) :
    (-sys.c_plus ^ 2 * dt ^ 2 + (dx - sys.v * dt) ^ 2) -
    (-sys.c_minus ^ 2 * dt ^ 2 + (dx - sys.v * dt) ^ 2) =
    - (sys.c_plus ^ 2 - sys.c_minus ^ 2) * dt ^ 2 := by
  ring

/-!
### 5. Master Certified Conjunction
-/

/-- **Master Certified Conjunction**:
    Unifying Mach ordering, bimetric background invariance, trapped surface emergence,
    and horizon decoupling for two-component chiral acoustic fluids. -/
theorem certified_acoustic_trapped_surface_synthesis
    (hv_pos : 0 < sys.v)
    (h_win : inBirefringentWindow sys)
    (dt : ℝ) :
    machPlus sys < machMinus sys ∧
    g00_plus sys - g00_minus sys = - (sys.c_plus ^ 2 - sys.c_minus ^ 2) ∧
    0 < g00_minus sys ∧
    g00_plus sys < 0 ∧
    upstreamSpeedMinus sys < 0 ∧
    0 < upstreamSpeedPlus sys ∧
    (-sys.c_plus ^ 2 * dt ^ 2) - (-sys.c_minus ^ 2 * dt ^ 2) =
      - (sys.c_plus ^ 2 - sys.c_minus ^ 2) * dt ^ 2 := by
  refine ⟨
    mach_ordering sys hv_pos,
    bimetric_gap_background_invariance sys,
    slow_trapped_in_window sys h_win,
    fast_untrapped_in_window sys h_win,
    slow_no_upstream_escape sys h_win,
    fast_upstream_escape sys h_win,
    by ring
  ⟩

end InfoGeometry.Physics.AcousticTrappedSurface
