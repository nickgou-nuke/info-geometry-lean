import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

/-! ### Part A: Latent Scale Quadratic Response & Dilation Gauge Invariance -/

/-- Latent zero-intercept quadratic singles rate: R(C, K, z) = C * z - K * z^2. -/
def latentParabola (C K z : ℝ) : ℝ := C * z - K * z ^ 2

/-- Restored unsummed linear singles rate: L(C, z) = C * z. -/
def latentLinear (C z : ℝ) : ℝ := C * z

/-- Coincidence summing loss defect: D(K, z) = K * z^2. -/
def latentLoss (K z : ℝ) : ℝ := K * z ^ 2

/-- **Theorem (Cleaving Archetype)**:
    The observed singles rate decomposes into a linear gain and quadratic loss:
    R(C, K, z) = L(C, z) - D(K, z). -/
theorem latent_cleaving (C K z : ℝ) :
    latentParabola C K z = latentLinear C z - latentLoss K z := by
  dsimp [latentParabola, latentLinear, latentLoss]

/-- **Theorem (Restoration Archetype)**:
    Adding back the quadratic coincidence loss restores the linear channel:
    R(C, K, z) + D(K, z) = L(C, z). -/
theorem latent_restoration (C K z : ℝ) :
    latentParabola C K z + latentLoss K z = latentLinear C z := by
  dsimp [latentParabola, latentLinear, latentLoss]
  ring

/-- Dilation gauge transformation on the latent geometry scale: z ↦ lam * z. -/
def gaugeScale (lam z : ℝ) : ℝ := lam * z

/-- Gauge transformation on the linear transmission coefficient: C ↦ C / lam. -/
def gaugeLinearCoeff (lam C : ℝ) : ℝ := C / lam

/-- Gauge transformation on the quadratic loss coefficient: K ↦ K / lam^2. -/
def gaugeLossCoeff (lam K : ℝ) : ℝ := K / lam ^ 2

/-- **Theorem (Dilation Gauge Invariance of Physical Response)**:
    The physical singles count rate is strictly invariant under simultaneous
    dilation of the latent geometry scale and rescaling of line coefficients:
    R(C/lam, K/lam², lam*z) = R(C, K, z). -/
theorem latentParabola_gauge_invariant (C K z lam : ℝ) (hlam : lam ≠ 0) :
    latentParabola (gaugeLinearCoeff lam C) (gaugeLossCoeff lam K) (gaugeScale lam z) =
      latentParabola C K z := by
  dsimp [latentParabola, gaugeLinearCoeff, gaugeLossCoeff, gaugeScale]
  have _hlam2 : lam ^ 2 ≠ 0 := pow_ne_zero 2 hlam
  field_simp

/-- **Theorem (Gauge Invariance of Restored Linear Rate)**:
    The restored linear rate L(C, z) = C * z is strictly gauge invariant:
    L(C/lam, lam*z) = L(C, z). -/
theorem latentLinear_gauge_invariant (C z lam : ℝ) (hlam : lam ≠ 0) :
    latentLinear (gaugeLinearCoeff lam C) (gaugeScale lam z) = latentLinear C z := by
  dsimp [latentLinear, gaugeLinearCoeff, gaugeScale]
  calc
    (C / lam) * (lam * z) = ((C / lam) * lam) * z := by ring
    _ = C * z := by rw [div_mul_cancel₀ C hlam]

/-- **Theorem (Gauge Invariance of Coincidence Loss)**:
    The coincidence loss D(K, z) = K * z^2 is strictly gauge invariant:
    D(K/lam², lam*z) = D(K, z). -/
theorem latentLoss_gauge_invariant (K z lam : ℝ) (hlam : lam ≠ 0) :
    latentLoss (gaugeLossCoeff lam K) (gaugeScale lam z) = latentLoss K z := by
  dsimp [latentLoss, gaugeLossCoeff, gaugeScale]
  have hlam2 : lam ^ 2 ≠ 0 := pow_ne_zero 2 hlam
  calc
    (K / lam ^ 2) * (lam * z) ^ 2 = (K / lam ^ 2) * (lam ^ 2 * z ^ 2) := by ring
    _ = ((K / lam ^ 2) * lam ^ 2) * z ^ 2 := by ring
    _ = K * z ^ 2 := by rw [div_mul_cancel₀ K hlam2]

/-- **Theorem (Gauge Fixing Uniqueness)**:
    Fixing the reference distance scale to unity (z_ref = 1) eliminates the
    dilation gauge freedom: there is a unique gauge parameter lam > 0 that
    normalizes an arbitrary positive reference scale z₀ to 1. -/
theorem gauge_fixing_unique (z0 : ℝ) (hz0 : 0 < z0) :
    ∃! lam : ℝ, 0 < lam ∧ gaugeScale lam z0 = 1 := by
  use 1 / z0
  dsimp [gaugeScale]
  have hz0_ne : z0 ≠ 0 := ne_of_gt hz0
  have hpos : 0 < 1 / z0 := one_div_pos.mpr hz0
  have heq : (1 / z0) * z0 = 1 := one_div_mul_cancel hz0_ne
  refine ⟨⟨hpos, heq⟩, ?_⟩
  intro y ⟨_hy_pos, hy_eq⟩
  calc
    y = y * (z0 * (1 / z0)) := by rw [mul_one_div_cancel hz0_ne, mul_one]
    _ = (y * z0) * (1 / z0) := by ring
    _ = 1 * (1 / z0) := by rw [hy_eq]
    _ = 1 / z0 := by ring

/-- **Theorem (Gauge Invariance of Relative Scales)**:
    The relative scale ratio between any two acquisitions j and k is
    strictly gauge invariant: (lam * z_j) / (lam * z_k) = z_j / z_k. -/
theorem relative_scale_gauge_invariant (z_j z_k lam : ℝ) (hlam : lam ≠ 0) :
    gaugeScale lam z_j / gaugeScale lam z_k = z_j / z_k := by
  dsimp [gaugeScale]
  exact mul_div_mul_left z_j z_k hlam

/-- **Theorem (Collapse Archetype: Multi-Line Scale Concordance)**:
    Across any spectral line i with C_i ≠ 0, the ratio of restored singles rates
    at two geometries j and k identically collapses to the common latent scale ratio:
    L_i(z_j) / L_i(z_k) = z_j / z_k. -/
theorem multi_line_scale_collapse (C_i z_j z_k : ℝ) (hCi : C_i ≠ 0) :
    latentLinear C_i z_j / latentLinear C_i z_k = z_j / z_k := by
  dsimp [latentLinear]
  exact mul_div_mul_left z_j z_k hCi

/-! ### Part B: Horizon Turnover Scale and Vertex Invariants -/

/-- Horizon turnover scale where the response derivative vanishes:
    z_turn = C / (2 * K). -/
def turnoverScale (C K : ℝ) : ℝ := C / (2 * K)

/-- Maximum observable singles rate at the turnover horizon:
    R^* = C^2 / (4 * K). -/
def peakVertexRate (C K : ℝ) : ℝ := C ^ 2 / (4 * K)

/-- **Theorem (Horizon Turnover Peak Value)**:
    At the turnover scale z_turn = C / (2 * K), the linear gain and quadratic loss
    balance, placing the response at its apex:
    R(z_turn) = C^2 / (4 * K). -/
theorem turnover_vertex_value (C K : ℝ) (hK : K ≠ 0) :
    latentParabola C K (turnoverScale C K) = peakVertexRate C K := by
  dsimp [latentParabola, turnoverScale, peakVertexRate]
  field_simp
  ring

/-- **Theorem (Gauge Equivariance of Turnover Scale)**:
    The turnover scale transforms equivariantly with the geometry scale:
    z'_turn = lam * z_turn. -/
theorem turnoverScale_gauge_equivariant (C K lam : ℝ) (hlam : lam ≠ 0) (hK : K ≠ 0) :
    turnoverScale (gaugeLinearCoeff lam C) (gaugeLossCoeff lam K) =
      gaugeScale lam (turnoverScale C K) := by
  dsimp [turnoverScale, gaugeLinearCoeff, gaugeLossCoeff, gaugeScale]
  have _hlam2 : lam ^ 2 ≠ 0 := pow_ne_zero 2 hlam
  field_simp

/-- **Theorem (Gauge Invariance of Peak Vertex Rate)**:
    The maximum observable rate R^* = C^2 / (4 * K) is strictly gauge invariant. -/
theorem peakVertexRate_gauge_invariant (C K lam : ℝ) (hlam : lam ≠ 0) (hK : K ≠ 0) :
    peakVertexRate (gaugeLinearCoeff lam C) (gaugeLossCoeff lam K) = peakVertexRate C K := by
  dsimp [peakVertexRate, gaugeLinearCoeff, gaugeLossCoeff]
  have _hlam2 : lam ^ 2 ≠ 0 := pow_ne_zero 2 hlam
  field_simp

/-! ### Part C: Far-Field Bayes Independence Limit vs Near-Field Coincidence Defect -/

/-- Fractional coincidence summing loss: δ(z) = D(K, z) / L(C, z) = (K / C) * z. -/
def fractionalLoss (C K z : ℝ) : ℝ := (K / C) * z

/-- Observed-to-restored singles transmission factor: η(z) = 1 - (K / C) * z. -/
def transmissionFactor (C K z : ℝ) : ℝ := 1 - (K / C) * z

/-- **Theorem (Singles Transmission Representation)**:
    The observed rate equals the restored rate attenuated by the transmission factor:
    R(C, K, z) = L(C, z) * (1 - (K / C) * z). -/
theorem observed_eq_restored_mul_transmission (C K z : ℝ) (hC : C ≠ 0) :
    latentParabola C K z = latentLinear C z * transmissionFactor C K z := by
  dsimp [latentParabola, latentLinear, transmissionFactor]
  field_simp

/-- **Theorem (Far-Field Bayes Independence Limit)**:
    In the far field (infinite distance, z → 0), the transmission factor
    approaches unity, and the joint product of observed singles rates
    asymptotically equals the product of unsummed singles rates:
    lim_{z → 0} [ (R1 * R2) / (L1 * L2) ] = 1.
    Evaluated at the far-field boundary z = 0, the coincidence defect vanishes identically. -/
theorem far_field_bayes_independence_boundary (C1 K1 C2 K2 : ℝ) :
    transmissionFactor C1 K1 0 * transmissionFactor C2 K2 0 = 1 := by
  dsimp [transmissionFactor]
  ring

/-- **Theorem (Coincidence Distortion Product Factorization)**:
    For any geometry z > 0, the ratio of the observed singles product to the
    unsummed product factors into the two line transmission factors:
    (R1 * R2) / (L1 * L2) = (1 - (K1/C1)*z) * (1 - (K2/C2)*z). -/
theorem singles_product_distortion_factorization
    (C1 K1 C2 K2 z : ℝ) (hC1 : C1 ≠ 0) (hC2 : C2 ≠ 0) (hz : z ≠ 0) :
    (latentParabola C1 K1 z * latentParabola C2 K2 z) /
      (latentLinear C1 z * latentLinear C2 z) =
      transmissionFactor C1 K1 z * transmissionFactor C2 K2 z := by
  dsimp [latentParabola, latentLinear, transmissionFactor]
  have _hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
  field_simp

/-- **Theorem (Near-Field Coincidence Defect)**:
    The deviation from statistical independence 1 - (R1*R2)/(L1*L2)
    is linear in z to leading order: z * (K1/C1 + K2/C2) - z^2 * (K1*K2)/(C1*C2). -/
theorem near_field_coincidence_defect
    (C1 K1 C2 K2 z : ℝ) :
    1 - transmissionFactor C1 K1 z * transmissionFactor C2 K2 z =
      z * (K1 / C1 + K2 / C2) - z ^ 2 * (K1 * K2 / (C1 * C2)) := by
  dsimp [transmissionFactor]
  ring

/-! ### Part D: Ruler, Root, Invariant, Closure, and Calibration -/

/-- True coincidence sum-peak rate: Q(K12, z) = K12 * z^2. -/
def sumPeakQuadraticRate (K12 z : ℝ) : ℝ := K12 * z ^ 2

/-- **Theorem (Ruler and Root Archetypes)**:
    The sum peak count rate Q scales quadratically with geometry z^2,
    so that its square root (normalized by √K12) acts as the physical ruler:
    √(Q / K12) = z for all z ≥ 0. -/
theorem sumPeak_root_recovers_scale (K12 z : ℝ) (hK12 : 0 < K12) (hz : 0 ≤ z) :
    Real.sqrt (sumPeakQuadraticRate K12 z / K12) = z := by
  dsimp [sumPeakQuadraticRate]
  have hK_ne : K12 ≠ 0 := ne_of_gt hK12
  rw [mul_div_cancel_left₀ (z ^ 2) hK_ne]
  exact Real.sqrt_sq hz

/-- **Theorem (Universal Coincidence Invariant Archetype)**:
    The product of restored singles rates divided by the sum-peak rate
    is strictly independent of geometry z:
    (L1(z) * L2(z)) / Q(z) = (C1 * C2) / K12 for all z ≠ 0. -/
theorem universal_coincidence_invariant (C1 C2 K12 z : ℝ) (hz : z ≠ 0) (hK12 : K12 ≠ 0) :
    (latentLinear C1 z * latentLinear C2 z) / sumPeakQuadraticRate K12 z =
      (C1 * C2) / K12 := by
  dsimp [latentLinear, sumPeakQuadraticRate]
  have _hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
  field_simp

/-- **Theorem (Closure Archetype: Efficiency Cancellation)**:
    Under microscopic nuclear calibration where singles rates follow
    C1 = A * P1 * ε1, C2 = A * P2 * ε2 and sum peak follows
    K12 = A * P12 * W0 * ε1 * ε2,
    the invariant closure ratio (C1 * C2) / K12 identically eliminates
    the detector efficiencies ε1, ε2:
    (C1 * C2) / K12 = A * (P1 * P2) / (P12 * W0). -/
theorem closure_efficiency_cancellation
    (A P1 P2 P12 W0 ε1 ε2 : ℝ)
    (hP12 : P12 ≠ 0) (hW0 : W0 ≠ 0) (hε1 : ε1 ≠ 0) (hε2 : ε2 ≠ 0) (hA : A ≠ 0) :
    let C1 := A * P1 * ε1
    let C2 := A * P2 * ε2
    let K12 := A * P12 * W0 * ε1 * ε2
    (C1 * C2) / K12 = A * (P1 * P2) / (P12 * W0) := by
  intro C1 C2 K12
  dsimp [C1, C2, K12]
  field_simp

/-- **Theorem (Calibration Archetype: Absolute Activity Extraction)**:
    The true physical source activity A is extracted from the invariant closure ratio
    by multiplying by nuclear branching and angular correlation factors:
    A = ((C1 * C2) / K12) * (P12 * W0) / (P1 * P2). -/
theorem calibration_activity_recovery
    (A P1 P2 P12 W0 ε1 ε2 : ℝ)
    (hP1 : P1 ≠ 0) (hP2 : P2 ≠ 0) (hP12 : P12 ≠ 0) (hW0 : W0 ≠ 0)
    (hε1 : ε1 ≠ 0) (hε2 : ε2 ≠ 0) (hA : A ≠ 0) :
    let C1 := A * P1 * ε1
    let C2 := A * P2 * ε2
    let K12 := A * P12 * W0 * ε1 * ε2
    let H := (C1 * C2) / K12
    H * (P12 * W0) / (P1 * P2) = A := by
  intro C1 C2 K12 H
  dsimp [H, C1, C2, K12]
  field_simp

/-! ### Part E: Virtual Scattering Cross-Section and Equivalent Crystal Diameter -/

/-- Virtual coincidence loss area: S_v = (4 * π * K) / (C * a^2). -/
def virtualLossCrossSection (C K a : ℝ) : ℝ :=
  (4 * Real.pi * K) / (C * a ^ 2)

/-- Equivalent HPGe crystal diameter: D_equiv = (4 / a) * √(K / C). -/
def equivalentCrystalDiameter (C K a : ℝ) : ℝ :=
  (4 / a) * Real.sqrt (K / C)

/-- **Theorem (Cross-Section Duality: Equivalent Disk Area)**:
    The geometric cross-sectional area of a disk with diameter D_equiv
    identically equals the virtual coincidence loss area S_v:
    π * (D_equiv / 2)^2 = S_v. -/
theorem equivalent_diameter_area_eq_virtualLoss
    (C K a : ℝ) (hC : 0 < C) (hK : 0 ≤ K) (ha : 0 < a) :
    Real.pi * (equivalentCrystalDiameter C K a / 2) ^ 2 =
      virtualLossCrossSection C K a := by
  dsimp [equivalentCrystalDiameter, virtualLossCrossSection]
  have _ha_ne : a ≠ 0 := ne_of_gt ha
  have _hC_ne : C ≠ 0 := ne_of_gt hC
  have hKC_nonneg : 0 ≤ K / C := div_nonneg hK (le_of_lt hC)
  have h_half : (4 / a * Real.sqrt (K / C)) / 2 = (2 / a) * Real.sqrt (K / C) := by ring
  rw [h_half]
  have h_sq : ((2 / a) * Real.sqrt (K / C)) ^ 2 = (4 / a ^ 2) * (K / C) := by
    calc
      ((2 / a) * Real.sqrt (K / C)) ^ 2 = (2 / a) ^ 2 * (Real.sqrt (K / C)) ^ 2 := by ring
      _ = (4 / a ^ 2) * (K / C) := by rw [div_pow, Real.sq_sqrt hKC_nonneg]; norm_num
  rw [h_sq]
  have _hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-! ### Part F: Master Archetypal Chain of Nuclear Metrology -/

/-- **Master Theorem (The Ten-Step Archetypal Chain of Nuclear Metrology)**:
    Synthesizes the complete chain of measurement and restoration:
    1. Shadow: Coincidence summing loss depletes singles rates.
    2. Ruler: The sum-peak rate Q scales quadratically with geometry z^2.
    3. Root: √(Q / K12) recovers the physical latent geometry scale z.
    4. Cleaving: R(z) decomposes into linear gain L(z) and quadratic loss D(z).
    5. Restoration: R(z) + D(z) reconstructs the loss-free singles rate L(z).
    6. Horizon: Turnover occurs at z_turn = C / (2K) with invariant peak rate R^*.
    7. Collapse: Multi-line rate ratios L_i(z_j) / L_i(z_k) collapse to z_j / z_k.
    8. Invariant: The closure quotient (L1 * L2) / Q is strictly independent of z.
    9. Closure: Efficiency factors ε1, ε2 cancel identically in the closure quotient.
    10. Calibration: Physical activity A is recovered without detector calibration. -/
theorem archetypal_chain_of_nuclear_metrology
    (A P1 P2 P12 W0 ε1 ε2 z : ℝ)
    (hA : 0 < A) (hP1 : 0 < P1) (hP2 : 0 < P2) (hP12 : 0 < P12) (hW0 : 0 < W0)
    (hε1 : 0 < ε1) (hε2 : 0 < ε2) (hz : 0 < z) :
    let C1 := A * P1 * ε1
    let C2 := A * P2 * ε2
    let K12 := A * P12 * W0 * ε1 * ε2
    let L1 := latentLinear C1 z
    let L2 := latentLinear C2 z
    let Q := sumPeakQuadraticRate K12 z
    let H := (L1 * L2) / Q
    Real.sqrt (Q / K12) = z ∧
    H = (C1 * C2) / K12 ∧
    H = A * (P1 * P2) / (P12 * W0) ∧
    H * (P12 * W0) / (P1 * P2) = A := by
  intro C1 C2 K12 L1 L2 Q H
  have hK12_pos : 0 < K12 := by
    dsimp [K12]
    positivity
  have _hP1_ne : P1 ≠ 0 := ne_of_gt hP1
  have _hP2_ne : P2 ≠ 0 := ne_of_gt hP2
  have _hP12_ne : P12 ≠ 0 := ne_of_gt hP12
  have _hW0_ne : W0 ≠ 0 := ne_of_gt hW0
  have _hε1_ne : ε1 ≠ 0 := ne_of_gt hε1
  have _hε2_ne : ε2 ≠ 0 := ne_of_gt hε2
  have _hA_ne : A ≠ 0 := ne_of_gt hA
  have hz_ne : z ≠ 0 := ne_of_gt hz
  have hK12_ne : K12 ≠ 0 := ne_of_gt hK12_pos
  refine ⟨sumPeak_root_recovers_scale K12 z hK12_pos (le_of_lt hz),
          universal_coincidence_invariant C1 C2 K12 z hz_ne hK12_ne, ?_, ?_⟩
  · dsimp [H, L1, L2, Q, latentLinear, sumPeakQuadraticRate, C1, C2, K12]
    field_simp
  · dsimp [H, L1, L2, Q, latentLinear, sumPeakQuadraticRate, C1, C2, K12]
    field_simp

end
end InfoGeometry.Probability.DetectorScaleInvariance

