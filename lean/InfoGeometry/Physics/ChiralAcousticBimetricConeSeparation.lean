import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic

open RealInnerProductSpace

/-!
# Two-Component Chiral Acoustic Bimetric System & Dual Sound Cone Separation

This module formalizes:
1. The chiral acoustic bimetric data `ChiralBimetricData` with sound speeds `0 < c₋ < c₊`.
2. The acoustic quadratic forms `Q₊(dt, dx) = -c₊² dt² + ‖dx‖²` and `Q₋(dt, dx) = -c₋² dt² + ‖dx‖²`.
3. Metric difference identity: `Q₊(dt, dx) - Q₋(dt, dx) = - (c₊² - c₋²) dt²`.
4. Theorem: Causal vectors of the slow cone are strictly timelike in the fast cone:
   `Q₋(dt, dx) ≤ 0 ∧ dt ≠ 0 → Q₊(dt, dx) < 0`.
5. Theorem: Strict null cone separation:
   `dt ≠ 0 → ¬ (Q₋(dt, dx) = 0 ∧ Q₊(dt, dx) = 0)`.
6. Characteristic wave dispersion symbols `P₊(ω, k)` and `P₋(ω, k)`.
7. Theorem: Slow on-shell acoustic modes are strictly evanescent for the fast branch:
   `P₋(ω, k) = 0 ∧ k > 0 → P₊(ω, k) > 0`.
8. The Birefringent Window / Chiral Ergoregion `c₋ < v < c₊`:
   dual opposite signatures `Q₋ > 0` (spacelike) and `Q₊ < 0` (timelike).
9. Dual acoustic horizons: decoupling into trapped and escaping chiral sectors.
-/

/-- The parameters of a two-component chiral acoustic bimetric fluid. -/
structure ChiralBimetricData (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  c_minus : ℝ
  c_plus : ℝ
  hc_minus_pos : 0 < c_minus
  hc_split : c_minus < c_plus

namespace ChiralBimetricData

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (B : ChiralBimetricData E)

/-- Fast sound speed is strictly positive. -/
lemma c_plus_pos : 0 < B.c_plus :=
  lt_trans B.hc_minus_pos B.hc_split

/-- The squared speed gap `c₊² - c₋²` is strictly positive. -/
lemma c_sq_diff_pos : 0 < B.c_plus ^ 2 - B.c_minus ^ 2 := by
  have h1 := B.hc_minus_pos
  have h2 := B.hc_split
  have h3 := B.c_plus_pos
  nlinarith

/-!
### 1. Spacetime Quadratic Forms (Acoustic Intervals)
-/

/-- Acoustic Minkowski quadratic form for the slow branch (-). -/
def Q_minus (dt : ℝ) (dx : E) : ℝ :=
  - (B.c_minus ^ 2) * (dt ^ 2) + inner (𝕜 := ℝ) dx dx

/-- Acoustic Minkowski quadratic form for the fast branch (+). -/
def Q_plus (dt : ℝ) (dx : E) : ℝ :=
  - (B.c_plus ^ 2) * (dt ^ 2) + inner (𝕜 := ℝ) dx dx

/-- **Theorem (Metric Difference Identity)**:
    The difference between the dual acoustic quadratic forms is strictly negative
    for any non-zero time interval. -/
theorem bimetric_gap (dt : ℝ) (dx : E) :
    B.Q_plus dt dx - B.Q_minus dt dx = - (B.c_plus ^ 2 - B.c_minus ^ 2) * dt ^ 2 := by
  dsimp [Q_plus, Q_minus]
  ring

/-!
### 2. Strict Cone Nesting and Null Boundary Separation
-/

/-- **Theorem (Slow Causal Cone is Strictly Fast Timelike)**:
    Any vector that is causal (timelike or null) for the slow metric `g₋`
    is strictly timelike for the fast metric `g₊`, provided `dt ≠ 0`. -/
theorem slow_causal_strictly_fast_timelike (dt : ℝ) (dx : E) (hdt : dt ≠ 0)
    (h_slow : B.Q_minus dt dx ≤ 0) : B.Q_plus dt dx < 0 := by
  have h_gap := B.bimetric_gap dt dx
  have h_c_pos := B.c_sq_diff_pos
  have h_dt_sq : 0 < dt ^ 2 := by
    cases ne_iff_lt_or_gt.mp hdt with
    | inl hneg => nlinarith
    | inr hpos => nlinarith
  have h_sub_neg : - (B.c_plus ^ 2 - B.c_minus ^ 2) * dt ^ 2 < 0 := by
    have : 0 < (B.c_plus ^ 2 - B.c_minus ^ 2) * dt ^ 2 := mul_pos h_c_pos h_dt_sq
    linarith
  linarith

/-- **Main Theorem (Strict Separation of Dual Sound Cones)**:
    The null cones of the two chiral metrics are strictly disjoint away from the origin:
    no non-trivial vector can be simultaneously null for both branches. -/
theorem null_cones_disjoint_outside_origin (dt : ℝ) (dx : E) (hdt : dt ≠ 0) :
    ¬ (B.Q_minus dt dx = 0 ∧ B.Q_plus dt dx = 0) := by
  intro ⟨h_slow, h_fast⟩
  have h_fast_lt := B.slow_causal_strictly_fast_timelike dt dx hdt (by linarith)
  linarith

/-!
### 3. Semiclassical Dispersion Relations and Evanescent Decoupling
-/

/-- Semiclassical acoustic wave operator symbol: `P(ω, k) = - ω² + c² ‖k‖²`. -/
def acousticDispersionSymbol (c : ℝ) (omega : ℝ) (k_norm_sq : ℝ) : ℝ :=
  - (omega ^ 2) + (c ^ 2) * k_norm_sq

/-- Fast branch wave symbol: `P₊(ω, k) = - ω² + c₊² ‖k‖²`. -/
def P_plus (omega : ℝ) (k_norm_sq : ℝ) : ℝ :=
  acousticDispersionSymbol B.c_plus omega k_norm_sq

/-- Slow branch wave symbol: `P₋(ω, k) = - ω² + c₋² ‖k‖²`. -/
def P_minus (omega : ℝ) (k_norm_sq : ℝ) : ℝ :=
  acousticDispersionSymbol B.c_minus omega k_norm_sq

/-- Dispersion symbol gap: `P₊(ω, k) - P₋(ω, k) = (c₊² - c₋²) ‖k‖²`. -/
theorem dispersion_gap (omega : ℝ) (k_norm_sq : ℝ) :
    B.P_plus omega k_norm_sq - B.P_minus omega k_norm_sq =
    (B.c_plus ^ 2 - B.c_minus ^ 2) * k_norm_sq := by
  dsimp [P_plus, P_minus, acousticDispersionSymbol]
  ring

/-- **Theorem (Evanescent Decoupling)**:
    A propagating on-shell sound mode of the slow branch (`P₋ = 0`)
    is strictly off-shell and space-like / evanescent for the fast branch (`P₊ > 0`). -/
theorem slow_on_shell_strictly_fast_evanescent
    (omega : ℝ) (k_norm_sq : ℝ) (hk : 0 < k_norm_sq)
    (h_slow_on_shell : B.P_minus omega k_norm_sq = 0) :
    B.P_plus omega k_norm_sq > 0 := by
  have h_gap := B.dispersion_gap omega k_norm_sq
  have h_c_pos := B.c_sq_diff_pos
  have h_prod_pos : 0 < (B.c_plus ^ 2 - B.c_minus ^ 2) * k_norm_sq := mul_pos h_c_pos hk
  linarith

/-!
### 4. Birefringent Window & Dual Acoustic Horizons
-/

/-- A velocity is inside the birefringent window if it falls between the two sound speeds. -/
def InBirefringentWindow (v : ℝ) : Prop :=
  B.c_minus < v ∧ v < B.c_plus

/-- **Theorem (Dual Opposite Signatures in the Birefringent Window)**:
    In the birefringent window `c₋ < v < c₊`, normalized states have opposite metric signatures:
    strictly spacelike (`> 0`) for the slow branch and strictly timelike (`< 0`) for the fast branch. -/
theorem birefringent_window_opposite_signature (v : ℝ) (hv : B.InBirefringentWindow v) :
    0 < - (B.c_minus ^ 2) + v ^ 2 ∧ - (B.c_plus ^ 2) + v ^ 2 < 0 := by
  have h1 := B.hc_minus_pos
  have h2 := hv.1
  have h3 := hv.2
  have _hv_pos : 0 < v := lt_trans h1 h2
  constructor
  · nlinarith
  · nlinarith

/-- Acoustic horizon structure for a chiral background flow. -/
structure ChiralAcousticHorizon where
  v_flow : ℝ
  h_ergo : B.InBirefringentWindow v_flow

namespace ChiralAcousticHorizon

variable (H : ChiralAcousticHorizon B)

/-- The fluid flow is supersonic with respect to the slow branch. -/
theorem flow_is_slow_supersonic : B.c_minus < H.v_flow :=
  H.h_ergo.1

/-- The fluid flow is subsonic with respect to the fast branch. -/
theorem flow_is_fast_subsonic : H.v_flow < B.c_plus :=
  H.h_ergo.2

/-- **Theorem (Chiral Horizon Decoupling)**:
    In the chiral ergoregion, the slow chiral modes are trapped downstream (`v_flow - c₋ > 0`),
    while the fast chiral modes can escape upstream (`c₊ - v_flow > 0`). -/
theorem dual_horizon_decoupling :
    H.v_flow - B.c_minus > 0 ∧ B.c_plus - H.v_flow > 0 := by
  constructor
  · linarith [H.flow_is_slow_supersonic]
  · linarith [H.flow_is_fast_subsonic]

end ChiralAcousticHorizon

/-- **Master Certified Conjunction for Two-Component Chiral Acoustic Bimetric Cone Separation** -/
theorem certified_chiral_acoustic_bimetric_synthesis
    (dt : ℝ) (dx : E) (hdt : dt ≠ 0)
    (omega : ℝ) (k_norm_sq : ℝ)
    (v : ℝ) (hv : B.InBirefringentWindow v) :
    (¬ (B.Q_minus dt dx = 0 ∧ B.Q_plus dt dx = 0)) ∧
    (B.Q_plus dt dx - B.Q_minus dt dx = - (B.c_plus ^ 2 - B.c_minus ^ 2) * dt ^ 2) ∧
    (B.P_plus omega k_norm_sq - B.P_minus omega k_norm_sq = (B.c_plus ^ 2 - B.c_minus ^ 2) * k_norm_sq) ∧
    (0 < - (B.c_minus ^ 2) + v ^ 2 ∧ - (B.c_plus ^ 2) + v ^ 2 < 0) := by
  refine ⟨B.null_cones_disjoint_outside_origin dt dx hdt,
          B.bimetric_gap dt dx,
          B.dispersion_gap omega k_norm_sq,
          B.birefringent_window_opposite_signature v hv⟩

end ChiralBimetricData
