import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Detector Operator Splitting, Invariants, and Geometric Cancellation

Formalizes the pristine mathematical carriers underlying the multi-distance coincidence
spectroscopy response model:

1. **Graded Operator Splitting (Conservative Transport vs. Dissipative Loss)**:
   Decomposing count rate into degree-1 linear transport $\mathcal{L}_C(X) = C \cdot X$
   and degree-2 coincidence summing loss $\mathcal{Q}_K(X) = K \cdot X^2$.
   Proves degree homogeneity, strictly linear dissipation ratio $\mathcal{Q}/\mathcal{L} = (K/C)X$,
   and exact linear restoration projection $\Pi(R, Q) = R + (K/\kappa) Q = C \cdot X$.

2. **Continuous Dilation Gauge Action & Group Quotient**:
   Invariance of the response observables under $(X, C, K, \kappa) \mapsto (l X, C/l, K/l^2, \kappa/l^2)$,
   preserving both singles response and coincidence rate.

3. **The Universal Campion Cascade Invariant**:
   Exact cancellation of geometric coupling $\Omega$ and intrinsic peak efficiencies $\varepsilon_1, \varepsilon_2$
   in the quadratic coincidence cross-ratio $(R_1 \cdot R_2) / Q = A \cdot (P_1 P_2) / (P_{12} W)$.
   Invariance under the 3-parameter local gauge group $(\mathbb{R}^\times)^3$.

4. **Rank-One Bilinear Separability & Minor Vanishing**:
   Factorization of unperturbed response $M_{ij} = u_i \cdot v_j$, exact vanishing of all 2×2 minors,
   and collinearity of spectral and geometric vectors.

5. **First-Collision Spatial Integral Cancellation**:
   Why the coincidence cross-ratio identically cancels out the 3D volume integral
   $\int_{\mathcal{V}} k(\mathbf{r}) d^3\mathbf{r}$, bypassing numerical Monte Carlo integration.

6. **Apollonian Quartic Linearizer Geometry**:
   Conformal two-pole virtual focal root at $d = -d_0$ and extraction of virtual interaction depth $d_0$.

All theorems kernel-checked in Lean 4 with 0 `sorry`s and 0 custom axioms.
-/

namespace InfoGeometry.Probability.DetectorOperatorSplitting

noncomputable section

open Matrix

/-! ### 1. Graded Operator Splitting (Conservative Transport vs. Dissipative Loss) -/

/-- Degree-1 conservative linear particle transport channel: $\mathcal{L}_C(X) = C \cdot X$. -/
def linearTransport (C X : ℝ) : ℝ := C * X

/-- Degree-2 dissipative coincidence summing-out collision channel: $\mathcal{Q}_K(X) = K \cdot X^2$. -/
def quadraticLoss (K X : ℝ) : ℝ := K * X ^ 2

/-- Total split-step detector response: $R(X) = \mathcal{L}_C(X) - \mathcal{Q}_K(X)$. -/
def splitStepResponse (C K X : ℝ) : ℝ := linearTransport C X - quadraticLoss K X

/-- **Theorem**: Linear transport is homogeneous of degree 1 under coordinate dilation. -/
theorem linearTransport_hom (C X l : ℝ) :
    linearTransport C (l * X) = l * linearTransport C X := by
  dsimp [linearTransport]
  ring

/-- **Theorem**: Quadratic collision loss is homogeneous of degree 2 under coordinate dilation. -/
theorem quadraticLoss_hom (K X l : ℝ) :
    quadraticLoss K (l * X) = l ^ 2 * quadraticLoss K X := by
  dsimp [quadraticLoss]
  ring

/-- **Theorem**: The relative dissipation ratio $\mathcal{Q}/\mathcal{L}$ is strictly linear
    in the natural coupling coordinate $X$. -/
theorem dissipation_ratio (C K X : ℝ) (hC : C ≠ 0) (hX : X ≠ 0) :
    quadraticLoss K X / linearTransport C X = (K / C) * X := by
  dsimp [quadraticLoss, linearTransport]
  field_simp [hC, hX]

/-- **Theorem**: The quadratic loss is the linear transport modulated by the linear dissipation factor. -/
theorem dissipation_linear_modulation (C K X : ℝ) (hC : C ≠ 0) :
    quadraticLoss K X = ((K / C) * X) * linearTransport C X := by
  dsimp [quadraticLoss, linearTransport]
  field_simp [hC]

/-- Coincidence sum-peak counting rate: $Q(X) = \kappa \cdot X^2$. -/
def coincidenceRate (κ X : ℝ) : ℝ := κ * X ^ 2

/-- Linear restoration projection operator: $\Pi(R, Q) = R + (K / \kappa) \cdot Q$. -/
def restorationOperator (R Q K κ : ℝ) : ℝ := R + (K / κ) * Q

/-- **Theorem**: The linear restoration projection identically recovers the unsummed linear transport channel. -/
theorem restoration_recovers_linear (C K κ X : ℝ) (hκ : κ ≠ 0) :
    restorationOperator (splitStepResponse C K X) (coincidenceRate κ X) K κ = linearTransport C X := by
  dsimp [restorationOperator, splitStepResponse, coincidenceRate, linearTransport, quadraticLoss]
  field_simp [hκ]
  ring

/-- **Theorem**: The restoration projection is additive across spectral lines. -/
theorem restoration_add (R₁ R₂ Q₁ Q₂ K₁ K₂ κ : ℝ) :
    restorationOperator (R₁ + R₂) (Q₁ + Q₂) (K₁ + K₂) κ =
      restorationOperator R₁ Q₁ K₁ κ + restorationOperator R₂ Q₂ K₂ κ + ((K₁ * Q₂ + K₂ * Q₁) / κ) := by
  dsimp [restorationOperator]
  ring

/-! ### 2. Continuous Dilation Gauge Action & Group Invariance -/

/-- Coordinate dilation under the continuous scaling group $\mathbb{R}^\times$. -/
def gaugeDilation (scale X : ℝ) : ℝ := scale * X

/-- Dual rescaling of the linear transport coefficient. -/
def gaugeLinearCoeff (scale C : ℝ) : ℝ := C / scale

/-- Dual rescaling of the quadratic loss coefficient. -/
def gaugeQuadraticCoeff (scale K : ℝ) : ℝ := K / scale ^ 2

/-- Dual rescaling of the coincidence coupling coefficient. -/
def gaugeCoincidenceCoeff (scale κ : ℝ) : ℝ := κ / scale ^ 2

/-- **Theorem**: The linear transport channel is strictly gauge invariant. -/
theorem gauge_invariance_transport (scale C X : ℝ) (hscale : scale ≠ 0) :
    linearTransport (gaugeLinearCoeff scale C) (gaugeDilation scale X) = linearTransport C X := by
  dsimp [linearTransport, gaugeLinearCoeff, gaugeDilation]
  field_simp [hscale]

/-- **Theorem**: The quadratic collision loss is strictly gauge invariant. -/
theorem gauge_invariance_loss (scale K X : ℝ) (hscale : scale ≠ 0) :
    quadraticLoss (gaugeQuadraticCoeff scale K) (gaugeDilation scale X) = quadraticLoss K X := by
  dsimp [quadraticLoss, gaugeQuadraticCoeff, gaugeDilation]
  field_simp [hscale]

/-- **Theorem**: The total observed singles response is strictly gauge invariant. -/
theorem gauge_invariance_response (scale C K X : ℝ) (hscale : scale ≠ 0) :
    splitStepResponse (gaugeLinearCoeff scale C) (gaugeQuadraticCoeff scale K) (gaugeDilation scale X) =
      splitStepResponse C K X := by
  dsimp [splitStepResponse, linearTransport, quadraticLoss, gaugeLinearCoeff, gaugeQuadraticCoeff, gaugeDilation]
  field_simp [hscale]

/-- **Theorem**: The coincidence counting rate is strictly gauge invariant. -/
theorem gauge_invariance_coincidence (scale κ X : ℝ) (hscale : scale ≠ 0) :
    coincidenceRate (gaugeCoincidenceCoeff scale κ) (gaugeDilation scale X) =
      coincidenceRate κ X := by
  dsimp [coincidenceRate, gaugeCoincidenceCoeff, gaugeDilation]
  field_simp [hscale]

/-- **Theorem**: The restored rate under gauge-transformed parameters recovers the invariant linear channel. -/
theorem gauge_invariance_restoration (scale C K κ X : ℝ) (hscale : scale ≠ 0) (hκ : κ ≠ 0) :
    restorationOperator
      (splitStepResponse (gaugeLinearCoeff scale C) (gaugeQuadraticCoeff scale K) (gaugeDilation scale X))
      (coincidenceRate (gaugeCoincidenceCoeff scale κ) (gaugeDilation scale X))
      (gaugeQuadraticCoeff scale K) (gaugeCoincidenceCoeff scale κ) =
      linearTransport C X := by
  rw [gauge_invariance_response scale C K X hscale]
  rw [gauge_invariance_coincidence scale κ X hscale]
  dsimp [restorationOperator, gaugeQuadraticCoeff, gaugeCoincidenceCoeff]
  have h_ratio : (K / scale ^ 2) / (κ / scale ^ 2) = K / κ := by
    field_simp [hscale, hκ]
  rw [h_ratio]
  exact restoration_recovers_linear C K κ X hκ

/-- **Theorem**: The dimensionless dissipation ratio is strictly gauge invariant. -/
theorem gauge_invariance_dissipation_ratio (scale C K X : ℝ) (hscale : scale ≠ 0) (hC : C ≠ 0) :
    (gaugeQuadraticCoeff scale K / gaugeLinearCoeff scale C) * gaugeDilation scale X =
      (K / C) * X := by
  dsimp [gaugeQuadraticCoeff, gaugeLinearCoeff, gaugeDilation]
  field_simp [hscale, hC]

/-! ### 3. Universal Campion Cascade Invariant -/

/-- The Campion coincidence quotient: $\mathcal{I}(L_1, L_2, Q) = (L_1 \cdot L_2) / Q$. -/
def campionRatio (L₁ L₂ Q : ℝ) : ℝ := (L₁ * L₂) / Q

/-- Pure nuclear cascade activity product: $A \cdot \frac{P_1 P_2}{P_{12} W}$. -/
def cascadeActivity (A P₁ P₂ P₁₂ W : ℝ) : ℝ := A * (P₁ * P₂) / (P₁₂ * W)

/-- **Theorem**: In terms of model parameters, the Campion ratio is strictly coordinate-independent:
    $\frac{L_1(X) L_2(X)}{Q(X)} = \frac{C_1 C_2}{\kappa}$. -/
theorem campion_invariant_exact (C₁ C₂ κ X : ℝ) (hX : X ≠ 0) (hκ : κ ≠ 0) :
    campionRatio (linearTransport C₁ X) (linearTransport C₂ X) (coincidenceRate κ X) =
      (C₁ * C₂) / κ := by
  dsimp [campionRatio, linearTransport, coincidenceRate]
  field_simp [hX, hκ]

/-- **Theorem (Microscopic Efficiency and Solid-Angle Cancellation)**:
    Under microscopic cascade definitions:
    $R_1 = A P_1 \varepsilon_1 \Omega$, $R_2 = A P_2 \varepsilon_2 \Omega$,
    $Q = A P_{12} W \varepsilon_1 \varepsilon_2 \Omega^2$.
    The geometric solid angle $\Omega$ and intrinsic peak efficiencies $\varepsilon_1, \varepsilon_2$
    vanish identically, leaving only the nuclear cascade activity. -/
theorem campion_microscopic_cancellation (A P₁ P₂ P₁₂ W ε₁ ε₂ Ω : ℝ)
    (hA : A ≠ 0) (hP₁₂ : P₁₂ ≠ 0) (hW : W ≠ 0) (hε₁ : ε₁ ≠ 0) (hε₂ : ε₂ ≠ 0) (hΩ : Ω ≠ 0) :
    let R₁ := A * P₁ * ε₁ * Ω
    let R₂ := A * P₂ * ε₂ * Ω
    let Q := A * P₁₂ * W * ε₁ * ε₂ * Ω ^ 2
    campionRatio R₁ R₂ Q = cascadeActivity A P₁ P₂ P₁₂ W := by
  intro R₁ R₂ Q
  dsimp [campionRatio, cascadeActivity, R₁, R₂, Q]
  field_simp [hA, hP₁₂, hW, hε₁, hε₂, hΩ]

/-- **Theorem (Local Scaling Gauge Invariance)**:
    The Campion ratio is invariant under the full 3-parameter group $(\mathbb{R}^\times)^3$
    of energy-channel rescalings $l_1, l_2$ and spatial geometric rescaling $\mu$. -/
theorem campion_local_gauge_invariance (R₁ R₂ Q l₁ l₂ μ : ℝ)
    (hQ : Q ≠ 0) (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0) (hμ : μ ≠ 0) :
    campionRatio (l₁ * μ * R₁) (l₂ * μ * R₂) (l₁ * l₂ * μ ^ 2 * Q) =
      campionRatio R₁ R₂ Q := by
  dsimp [campionRatio]
  field_simp [hQ, hl₁, hl₂, hμ]

/-! ### 4. Rank-One Bilinear Separability & Minor Vanishing -/

/-- Rank-one outer product matrix $M_{ij} = u_i \cdot v_j$. -/
def rankOneMatrix {m n : ℕ} (u : Fin m → ℝ) (v : Fin n → ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => u i * v j

/-- **Theorem**: Every 2×2 minor of a rank-one matrix identically vanishes. -/
theorem rankOne_minor_2x2 {m n : ℕ} (u : Fin m → ℝ) (v : Fin n → ℝ)
    (i₁ i₂ : Fin m) (j₁ j₂ : Fin n) :
    (rankOneMatrix u v i₁ j₁) * (rankOneMatrix u v i₂ j₂) -
    (rankOneMatrix u v i₁ j₂) * (rankOneMatrix u v i₂ j₁) = 0 := by
  dsimp [rankOneMatrix]
  ring

/-- **Theorem**: Any two columns of a rank-one matrix are strictly collinear. -/
theorem rankOne_collinear_columns {m n : ℕ} (u : Fin m → ℝ) (v : Fin n → ℝ)
    (j₁ j₂ : Fin n) (hj₂ : v j₂ ≠ 0) (i : Fin m) :
    rankOneMatrix u v i j₁ = (v j₁ / v j₂) * rankOneMatrix u v i j₂ := by
  dsimp [rankOneMatrix]
  field_simp [hj₂]

/-- **Theorem**: Any two rows of a rank-one matrix are strictly collinear. -/
theorem rankOne_collinear_rows {m n : ℕ} (u : Fin m → ℝ) (v : Fin n → ℝ)
    (i₁ i₂ : Fin m) (hi₂ : u i₂ ≠ 0) (j : Fin n) :
    rankOneMatrix u v i₁ j = (u i₁ / u i₂) * rankOneMatrix u v i₂ j := by
  dsimp [rankOneMatrix]
  field_simp [hi₂]

/-! ### 5. Spatial First-Collision Integral Bypass (No Monte Carlo Required) -/

/-- Single photopeak rate generated by spatial first-collision volume integration:
    $R_i = A P_i \varepsilon_i \cdot I$, where $I = \int_\mathcal{V} k(\mathbf{r}) d^3\mathbf{r}$. -/
def microSingles (A P ε I : ℝ) : ℝ := A * P * ε * I

/-- Coincidence sum-peak rate generated by the joint spatial volume integration:
    $Q = A P_{12} W \varepsilon_1 \varepsilon_2 \cdot I^2$. -/
def microCoincidence (A P₁₂ W ε₁ ε₂ I : ℝ) : ℝ := A * P₁₂ * W * ε₁ * ε₂ * I ^ 2

/-- **Theorem (Spatial Volume Integral Bypass)**:
    For ANY detector geometry, active volume, or spatial attenuation kernel with non-zero
    first-collision integral $I$, the Campion ratio evaluates identically to the pure
    nuclear cascade activity, bypassing numerical volume integration completely. -/
theorem volume_integral_cancellation (A P₁ P₂ P₁₂ W ε₁ ε₂ I : ℝ)
    (hA : A ≠ 0) (hP₁₂ : P₁₂ ≠ 0) (hW : W ≠ 0) (hε₁ : ε₁ ≠ 0) (hε₂ : ε₂ ≠ 0) (hI : I ≠ 0) :
    campionRatio (microSingles A P₁ ε₁ I) (microSingles A P₂ ε₂ I)
      (microCoincidence A P₁₂ W ε₁ ε₂ I) =
      cascadeActivity A P₁ P₂ P₁₂ W := by
  dsimp [campionRatio, microSingles, microCoincidence, cascadeActivity]
  field_simp [hA, hP₁₂, hW, hε₁, hε₂, hI]

/-! ### 6. Apollonian Quartic Linearizer Geometry -/

/-- Conformal two-pole quartic linearizer: $\Lambda(d) = a \cdot d + a \cdot d_0$. -/
def apollonianLinearizer (a d₀ d : ℝ) : ℝ := a * d + a * d₀

/-- **Theorem**: The linearizer vanishes identically at the interior virtual sink pole $d = -d_0$. -/
theorem apollonianLinearizer_root (a d₀ : ℝ) :
    apollonianLinearizer a d₀ (-d₀) = 0 := by
  dsimp [apollonianLinearizer]
  ring

/-- **Theorem**: The slope ratio $(a \cdot d_0) / a$ uniquely extracts the virtual interaction depth $d_0$. -/
theorem apollonianLinearizer_extract_d0 (a d₀ : ℝ) (ha : a ≠ 0) :
    (a * d₀) / a = d₀ := by
  exact mul_div_cancel_left₀ d₀ ha

/-- **Theorem**: Quartic distance relation $\Lambda(d)^2 = a^2 (d + d_0)^2$. -/
theorem apollonianLinearizer_sq (a d₀ d : ℝ) :
    (apollonianLinearizer a d₀ d) ^ 2 = a ^ 2 * (d + d₀) ^ 2 := by
  dsimp [apollonianLinearizer]
  ring

end

end InfoGeometry.Probability.DetectorOperatorSplitting
