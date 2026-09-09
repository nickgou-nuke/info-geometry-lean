import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Detector-Specific Geometry, Scale Invariance, and Depth Heterogeneity

Formalizes:
1. **Detector Hardware Parameters**:
   Each detector possesses distinct physical crystal and cryostat dimensions:
   - Canberra GC4018: 40% efficiency, 76 mm endcap, d0 ≈ 36.89 mm
   - ORTEC GEM50P4:  50% efficiency, 83 mm endcap, d0 ≈ 38.12 mm
   - Canberra GC5019: 50% efficiency, 83 mm endcap, crystal 66x59 mm, d0 ≈ 29.35 mm
2. **Three Independent Scale Estimators**:
   - Coincidence scale: S_coinc(d) = X(d) / X(d_ref)
   - Vector projection: q_d = (R^(0)(d) . R^(0)(d_ref)) / ||R^(0)(d_ref)||^2
   - Line-averaged singles: S_singles(d) = (1/N) * sum_i [ R_i^(0)(d) / R_i^(0)(d_ref) ]
3. **Master Equivalence Theorem**:
   Under strict zero-intercept restoration R_i^(0)(d) = C_i * X(d), all three
   scale estimators coincide identically: S_coinc = q_d = S_singles = X(d)/X(d_ref).
4. **Inverse-Square Geometric Law**:
   When X(d) = 1 / (a^2 * (d + d0)^2), the relative scale is identically:
   S(d) = (d_ref + d0)^2 / (d + d0)^2.
5. **Detector Depth Heterogeneity**:
   If d0_A ≠ d0_B, transferring d0_B onto detector A breaks the exact
   inverse-square scale ratio, proving d0 is detector-specific.

All proofs verified with 0 `sorry`s and 0 custom axioms.
-/

namespace InfoGeometry.Probability.DetectorScaleInvariance

noncomputable section

open Real

/-! ### 1. Detector Hardware Specifications -/

/-- Physical parameters of an HPGe detector in a specific cryostat:
    - `crystalDiameter` : Diameter of the active Ge crystal cylinder (mm)
    - `crystalLength`   : Length of the Ge crystal cylinder (mm)
    - `endcapDiameter`  : Outer diameter of the cryostat endcap (mm)
    - `d0`              : Virtual point detector depth from endcap face (mm)
    - `a`               : Distance linearizer slope (mm⁻¹) -/
structure HPGeDetector where
  crystalDiameter : ℝ
  crystalLength   : ℝ
  endcapDiameter  : ℝ
  d0              : ℝ
  a               : ℝ
  hcrystalD_pos   : 0 < crystalDiameter
  hcrystalL_pos   : 0 < crystalLength
  hendcapD_pos    : crystalDiameter < endcapDiameter
  hd0_pos         : 0 < d0
  ha_pos          : 0 < a

/-- Verified Canberra GC5019 detector parameters for Eu-152 acquisition (S/N 1030036, DSA-2000). -/
def canberraGC5019_Eu : HPGeDetector where
  crystalDiameter := 66
  crystalLength   := 59
  endcapDiameter  := 83
  d0              := 29.35
  a               := 0.014654
  hcrystalD_pos   := by norm_num
  hcrystalL_pos   := by norm_num
  hendcapD_pos    := by norm_num
  hd0_pos         := by norm_num
  ha_pos          := by norm_num

/-- Standard reference alias for GC5019. -/
def canberraGC5019 : HPGeDetector := canberraGC5019_Eu

/-- Verified Canberra GC5019 detector parameters for Co-60 acquisition (same GC5019 unit in different year).
    Shares the identical crystal and endcap dimensions; fitted d0 = 36.89 mm accounts for deeper absorption
    and mounting spacer offsets. -/
def canberraGC5019_Co : HPGeDetector where
  crystalDiameter := 66
  crystalLength   := 59
  endcapDiameter  := 83
  d0              := 36.89
  a               := 0.01824
  hcrystalD_pos   := by norm_num
  hcrystalL_pos   := by norm_num
  hendcapD_pos    := by norm_num
  hd0_pos         := by norm_num
  ha_pos          := by norm_num

/-- Historical alias for Co-60 configuration (formerly labeled GC4018). -/
def canberraGC4018 : HPGeDetector := canberraGC5019_Co

/-- Verified ORTEC GEM50P4 detector parameters (50% relative efficiency, 83 mm endcap):
    - Catalog PROFILE C50 benchmark: 68 × 62 mm crystal (±2 mm tolerance) in 83 mm endcap.
    - Literature GEM50P4-83 units: 64.1 mm (arXiv:1409.2479) and 66 mm (arXiv:1601.01450).
    - Fitted virtual summing diameter: D_equiv(583 keV) = 66.90 mm, inside the 64.1–68 mm envelope. -/
def ortecGEM50 : HPGeDetector where
  crystalDiameter := 68
  crystalLength   := 62
  endcapDiameter  := 83
  d0              := 38.12
  a               := 0.01751
  hcrystalD_pos   := by norm_num
  hcrystalL_pos   := by norm_num
  hendcapD_pos    := by norm_num
  hd0_pos         := by norm_num
  ha_pos          := by norm_num

/-! ### 2. Geometric Scale Functions -/

/-- Point-source geometric flux coordinate X(d) = 1 / (a^2 * (d + d0)^2). -/
def geometricFlux (det : HPGeDetector) (d : ℝ) : ℝ :=
  1 / (det.a ^ 2 * (d + det.d0) ^ 2)

/-- Relative coincidence scale between distance d and reference distance d_ref:
    S_coinc(d) = X(d) / X(d_ref). -/
def scaleCoincidence (det : HPGeDetector) (d d_ref : ℝ) : ℝ :=
  geometricFlux det d / geometricFlux det d_ref

/-- **Theorem**: The relative coincidence scale reduces identically to the
    inverse-square effective distance ratio, independent of linearizer slope `a`. -/
theorem scaleCoincidence_eq_distance_ratio (det : HPGeDetector) (d d_ref : ℝ)
    (hd : d + det.d0 ≠ 0) (hd_ref : d_ref + det.d0 ≠ 0) :
    scaleCoincidence det d d_ref = (d_ref + det.d0) ^ 2 / (d + det.d0) ^ 2 := by
  dsimp [scaleCoincidence, geometricFlux]
  have ha : det.a ≠ 0 := ne_of_gt det.ha_pos
  have _ha2 : det.a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have _hd2 : (d + det.d0) ^ 2 ≠ 0 := pow_ne_zero 2 hd
  have _hd_ref2 : (d_ref + det.d0) ^ 2 ≠ 0 := pow_ne_zero 2 hd_ref
  field_simp

/-! ### 3. Multi-Line Zero-Intercept Response Equivalence -/

/-- Restored linear singles response: R_i^(0)(d) = C_i * X(d). -/
def restoredSinglesRate (C_i : ℝ) (X_d : ℝ) : ℝ := C_i * X_d

/-- Line-by-line relative ratio for transition i:
    R_i^(0)(d) / R_i^(0)(d_ref). -/
def lineRatio (C_i : ℝ) (X_d X_ref : ℝ) : ℝ :=
  restoredSinglesRate C_i X_d / restoredSinglesRate C_i X_ref

/-- **Theorem (Single-Line Scale Invariance)**:
    Under strict zero-intercept restoration, the relative line ratio is
    strictly independent of the line's transmission coefficient C_i. -/
theorem lineRatio_eq_scale (C_i X_d X_ref : ℝ) (hCi : C_i ≠ 0) :
    lineRatio C_i X_d X_ref = X_d / X_ref := by
  dsimp [lineRatio, restoredSinglesRate]
  exact mul_div_mul_left X_d X_ref hCi

/-- Two-channel spectrum vector projection slope:
    q_d = (R1*R1_ref + R2*R2_ref) / (R1_ref^2 + R2_ref^2). -/
def vectorSlope2 (C1 C2 X_d X_ref : ℝ) : ℝ :=
  (restoredSinglesRate C1 X_d * restoredSinglesRate C1 X_ref +
   restoredSinglesRate C2 X_d * restoredSinglesRate C2 X_ref) /
  ((restoredSinglesRate C1 X_ref) ^ 2 + (restoredSinglesRate C2 X_ref) ^ 2)

/-- **Theorem (Vector Projection Equivalence)**:
    The spectrum vector projection slope q_d identically equals the
    coincidence scale X_d / X_ref for any positive transmission coefficients. -/
theorem vectorSlope2_eq_scale (C1 C2 X_d X_ref : ℝ)
    (hXref : X_ref ≠ 0) (hC : C1 ^ 2 + C2 ^ 2 ≠ 0) :
    vectorSlope2 C1 C2 X_d X_ref = X_d / X_ref := by
  dsimp [vectorSlope2, restoredSinglesRate]
  have hdenom : (C1 * X_ref) ^ 2 + (C2 * X_ref) ^ 2 = (C1 ^ 2 + C2 ^ 2) * X_ref ^ 2 := by ring
  have hnum : (C1 * X_d) * (C1 * X_ref) + (C2 * X_d) * (C2 * X_ref) = (C1 ^ 2 + C2 ^ 2) * X_d * X_ref := by ring
  rw [hdenom, hnum]
  have hXref2 : X_ref ^ 2 ≠ 0 := pow_ne_zero 2 hXref
  have _hprod : (C1 ^ 2 + C2 ^ 2) * X_ref ^ 2 ≠ 0 := mul_ne_zero hC hXref2
  field_simp

/-- **Master Equivalence Theorem**:
    All three independent scale estimators (coincidence scale, individual line ratios,
    and vector projection slope) identically collapse to X(d)/X(d_ref). -/
theorem scale_estimators_concurrence (C1 C2 X_d X_ref : ℝ)
    (hC1 : C1 ≠ 0) (hC2 : C2 ≠ 0) (hXref : X_ref ≠ 0) :
    lineRatio C1 X_d X_ref = X_d / X_ref ∧
    lineRatio C2 X_d X_ref = X_d / X_ref ∧
    vectorSlope2 C1 C2 X_d X_ref = X_d / X_ref := by
  have hCsq : C1 ^ 2 + C2 ^ 2 ≠ 0 := by
    have h1 : 0 < C1 ^ 2 := sq_pos_of_ne_zero hC1
    have h2 : 0 ≤ C2 ^ 2 := sq_nonneg C2
    linarith
  refine ⟨lineRatio_eq_scale C1 X_d X_ref hC1,
          lineRatio_eq_scale C2 X_d X_ref hC2,
          vectorSlope2_eq_scale C1 C2 X_d X_ref hXref hCsq⟩

/-! ### 4. Detector Depth Heterogeneity -/

/-- **Theorem (Spurious Depth Bias)**:
    If detector A (depth d0_A) is evaluated using detector B's depth (d0_B ≠ d0_A),
    the apparent scale ratio differs from the physical ratio at all non-reference distances. -/
theorem depth_heterogeneity_bias (d0_A d0_B d d_ref : ℝ)
    (hne : d0_A ≠ d0_B) (hdist : d ≠ d_ref)
    (hA : 0 < d + d0_A)
    (hB : 0 < d + d0_B) :
    (d_ref + d0_A) / (d + d0_A) ≠ (d_ref + d0_B) / (d + d0_B) := by
  intro h_eq
  have hA_ne : d + d0_A ≠ 0 := ne_of_gt hA
  have hB_ne : d + d0_B ≠ 0 := ne_of_gt hB
  have hcross : (d_ref + d0_A) * (d + d0_B) = (d_ref + d0_B) * (d + d0_A) := by
    calc
      (d_ref + d0_A) * (d + d0_B) = ((d_ref + d0_A) / (d + d0_A) * (d + d0_A)) * (d + d0_B) := by
        rw [div_mul_cancel₀ (d_ref + d0_A) hA_ne]
      _ = ((d_ref + d0_B) / (d + d0_B) * (d + d0_A)) * (d + d0_B) := by
        rw [h_eq]
      _ = ((d_ref + d0_B) / (d + d0_B) * (d + d0_B)) * (d + d0_A) := by ring
      _ = (d_ref + d0_B) * (d + d0_A) := by
        rw [div_mul_cancel₀ (d_ref + d0_B) hB_ne]
  have hdiff : (d0_A - d0_B) * (d - d_ref) = 0 := by
    linear_combination hcross
  cases mul_eq_zero.mp hdiff with
  | inl h1 =>
    have : d0_A = d0_B := sub_eq_zero.mp h1
    exact hne this
  | inr h2 =>
    have : d = d_ref := sub_eq_zero.mp h2
    exact hdist this

/-! ### 5. Absolute Efficiency and Multi-Daughter Coincidence Activity Reconstruction -/

/-- Absolute full-energy peak efficiency:
    ε_p(E_i, d) = R_i^(0)(d) / (A * Y_i) = (C_i * X_d) / (A * Y_i). -/
def absolutePeakEfficiency (C_i : ℝ) (X_d : ℝ) (A : ℝ) (Y_i : ℝ) : ℝ :=
  (C_i * X_d) / (A * Y_i)

/-- True coincidence-derived activity from the closure slope H = (R1^(0) * R2^(0)) / Q,
    angular correlation factor W, joint cascade yield P12, and individual yields P1, P2:
    A_coinc = H * (W * P12) / (P1 * P2). -/
def coincidenceActivity (H : ℝ) (W : ℝ) (P12 : ℝ) (P1 : ℝ) (P2 : ℝ) : ℝ :=
  H * (W * P12) / (P1 * P2)

/-- **Theorem (Coincidence Absolute Activity Recovery)**:
    When singles rates R1^(0) = A * P1 * ε1, R2^(0) = A * P2 * ε2 and true sum rate
    Q = A * P12 * W * ε1 * ε2 are formed, the closure slope H = (R1*R2)/Q recovers
    the exact physical activity A identically, independent of detector efficiencies. -/
theorem coincidenceActivity_recovers_activity
    (A : ℝ) (P1 P2 P12 W ε1 ε2 : ℝ)
    (hA : A ≠ 0) (hP1 : P1 ≠ 0) (hP2 : P2 ≠ 0) (hP12 : P12 ≠ 0) (hW : W ≠ 0)
    (hε1 : ε1 ≠ 0) (hε2 : ε2 ≠ 0) :
    let R1 := A * P1 * ε1
    let R2 := A * P2 * ε2
    let Q := A * P12 * W * ε1 * ε2
    let H := (R1 * R2) / Q
    coincidenceActivity H W P12 P1 P2 = A := by
  intro R1 R2 Q H
  dsimp [H, Q, R1, R2, coincidenceActivity]
  field_simp

/-- Effective conditional gamma branch under internal conversion coefficient α:
    b_γ = 1 / (1 + α). -/
def photonBranchOfConversion (α : ℝ) : ℝ :=
  1 / (1 + α)

/-- Cascade coincidence activity with internal conversion on the secondary transition:
    When P12 = P1 * b_feed * (1 / (1 + α)), the activity reduces to:
    A = H * (W * b_feed) / (P2 * (1 + α)). -/
theorem coincidenceActivity_with_conversion
    (H W P1 P2 b_feed α : ℝ)
    (hα : 1 + α ≠ 0) (hP1 : P1 ≠ 0) (hP2 : P2 ≠ 0) :
    let P12 := P1 * b_feed * photonBranchOfConversion α
    coincidenceActivity H W P12 P1 P2 = H * (W * b_feed) / (P2 * (1 + α)) := by
  intro P12
  dsimp [coincidenceActivity, P12, photonBranchOfConversion]
  field_simp

/-- Secular equilibrium parent activity:
    A_parent = A_daughter / b_branch. -/
def secularEquilibriumParentActivity (A_daughter : ℝ) (b_branch : ℝ) : ℝ :=
  A_daughter / b_branch

/-- **Theorem (Secular Equilibrium Invariance)**:
    If daughter activity satisfies A_daughter = b_branch * A_parent with b_branch ≠ 0,
    then secularEquilibriumParentActivity recovers A_parent identically. -/
theorem secularEquilibrium_recovers_parent
    (A_parent b_branch : ℝ) (hb : b_branch ≠ 0) :
    secularEquilibriumParentActivity (b_branch * A_parent) b_branch = A_parent := by
  dsimp [secularEquilibriumParentActivity]
  exact mul_div_cancel_left₀ A_parent hb

/-- **Theorem (Multi-Daughter Concordance)**:
    For a parent nuclide decaying into two distinct daughter channels with
    coincidence-derived activities A_1 and A_2:
    if both channels faithfully measure the parent activity (A_1 = A and A_2 = A),
    then their reconstructed activities agree identically: A_1 = A_2. -/
theorem multi_daughter_concordance (A_1 A_2 A : ℝ)
    (h1 : A_1 = A) (h2 : A_2 = A) : A_1 = A_2 := by
  rw [h1, h2]

/-! ### 6. Surprisal Geometric Mean Baseline and Centered Scale Normalization -/

/-- Surprisal (negative log-rate) of an observed rate:
    s(L) = -ln(L / L_unit). -/
def rateSurprisal (L L_unit : ℝ) : ℝ :=
  -Real.log (L / L_unit)

/-- Log-rate coordinate:
    ℓ = ln(L / L_unit). -/
def logRate (L L_unit : ℝ) : ℝ :=
  Real.log (L / L_unit)

/-- Centered gauge shift for a pair of scale shifts (m = 2):
    s_tilde_1 = (s_1 - s_2) / 2
    s_tilde_2 = (s_2 - s_1) / 2. -/
def centeredShift2 (s1 s2 : ℝ) : ℝ × ℝ :=
  ((s1 - s2) / 2, (s2 - s1) / 2)

/-- **Theorem (Zero-Sum Scale Normalization, Geometric-Mean Gauge)**:
    The centered shifts satisfy s_tilde_1 + s_tilde_2 = 0,
    and consequently exp(s_tilde_1) * exp(s_tilde_2) = 1. -/
theorem centeredShift2_sum_zero (s1 s2 : ℝ) :
    (centeredShift2 s1 s2).1 + (centeredShift2 s1 s2).2 = 0 := by
  dsimp [centeredShift2]
  ring

theorem centeredShift2_prod_exp_one (s1 s2 : ℝ) :
    Real.exp (centeredShift2 s1 s2).1 * Real.exp (centeredShift2 s1 s2).2 = 1 := by
  rw [← Real.exp_add]
  have h := centeredShift2_sum_zero s1 s2
  rw [h]
  exact Real.exp_zero

/-- Transported rate under centered gauge shift:
    L_transported = L * exp(-s_tilde). -/
def transportedRate (L s_tilde : ℝ) : ℝ :=
  L * Real.exp (-s_tilde)

/-- **Theorem (Separable Surprisal Deviation Invariance)**:
    For a separable zero-intercept multi-channel system L_ij = C_i * X_j:
    the surprisal deviation relative to the ensemble geometric mean across distances
    is strictly independent of the energy transmission coefficient C_i. -/
theorem separable_surprisal_deviation_independent_of_channel
    (C_i X1 X2 : ℝ) (hCi : 0 < C_i) (hX1 : 0 < X1) (hX2 : 0 < X2) :
    let L1 := C_i * X1
    let L2 := C_i * X2
    let l1 := Real.log L1
    let l2 := Real.log L2
    let mu := (l1 + l2) / 2
    l1 - mu = (Real.log X1 - Real.log X2) / 2 ∧
    l2 - mu = (Real.log X2 - Real.log X1) / 2 := by
  intro L1 L2 l1 l2 mu
  dsimp [L1, L2, l1, l2, mu]
  have hlog1 : Real.log (C_i * X1) = Real.log C_i + Real.log X1 :=
    Real.log_mul (ne_of_gt hCi) (ne_of_gt hX1)
  have hlog2 : Real.log (C_i * X2) = Real.log C_i + Real.log X2 :=
    Real.log_mul (ne_of_gt hCi) (ne_of_gt hX2)
  rw [hlog1, hlog2]
  constructor <;> ring

/-- **Theorem (Log-Rate Scale Collapse)**:
    Under separable transport with centered scale shift s_tilde_j = (ln X_j - ln X_k) / 2,
    the transported log-rates identically equal ln(C_i) + (ln X_1 + ln X_2) / 2,
    achieving complete collapse independent of measurement distance. -/
theorem separable_log_transport_collapse
    (C_i X1 X2 : ℝ) (hCi : 0 < C_i) (hX1 : 0 < X1) (hX2 : 0 < X2) :
    let L1 := C_i * X1
    let L2 := C_i * X2
    let s1 := (Real.log X1 - Real.log X2) / 2
    let s2 := (Real.log X2 - Real.log X1) / 2
    Real.log L1 - s1 = Real.log C_i + (Real.log X1 + Real.log X2) / 2 ∧
    Real.log L2 - s2 = Real.log C_i + (Real.log X1 + Real.log X2) / 2 ∧
    Real.log L1 - s1 = Real.log L2 - s2 := by
  intro L1 L2 s1 s2
  dsimp [L1, L2, s1, s2]
  have hlog1 : Real.log (C_i * X1) = Real.log C_i + Real.log X1 :=
    Real.log_mul (ne_of_gt hCi) (ne_of_gt hX1)
  have hlog2 : Real.log (C_i * X2) = Real.log C_i + Real.log X2 :=
    Real.log_mul (ne_of_gt hCi) (ne_of_gt hX2)
  rw [hlog1, hlog2]
  refine ⟨by ring, by ring, by ring⟩

/-- **Theorem (Residual Vanishing Under Collective Transport)**:
    The residual e_ij = (ln L_ij - mu_i) - s_j vanishes identically
    for all measurement geometries under separable rank-one scaling. -/
theorem separable_transport_residuals_zero
    (C_i X1 X2 : ℝ) (hCi : 0 < C_i) (hX1 : 0 < X1) (hX2 : 0 < X2) :
    let L1 := C_i * X1
    let L2 := C_i * X2
    let l1 := Real.log L1
    let l2 := Real.log L2
    let mu := (l1 + l2) / 2
    let s1 := (Real.log X1 - Real.log X2) / 2
    let s2 := (Real.log X2 - Real.log X1) / 2
    (l1 - mu) - s1 = 0 ∧ (l2 - mu) - s2 = 0 := by
  intro L1 L2 l1 l2 mu s1 s2
  dsimp [L1, L2, l1, l2, mu, s1, s2]
  have hlog1 : Real.log (C_i * X1) = Real.log C_i + Real.log X1 :=
    Real.log_mul (ne_of_gt hCi) (ne_of_gt hX1)
  have hlog2 : Real.log (C_i * X2) = Real.log C_i + Real.log X2 :=
    Real.log_mul (ne_of_gt hCi) (ne_of_gt hX2)
  rw [hlog1, hlog2]
  constructor <;> ring

end
end InfoGeometry.Probability.DetectorScaleInvariance
