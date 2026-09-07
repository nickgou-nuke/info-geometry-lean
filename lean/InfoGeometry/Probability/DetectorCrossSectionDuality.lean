import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Detector Cross-Section Duality and Peak-to-Total Recovery

Formalizes the dual geometric areas of HPGe coincidence spectrometry:
1. **Quartic Linearizer**: $L(d) = a d + b$, root at $-d_0$, extraction $d_0 = b/a$.
2. **Restored Linear Rate**: $L_i = I_i + B_i Q = C_i X$.
3. **Activity Cancellation**: $A = C_i C_j \frac{P_{ij}}{P_i P_j} W_0$ in coincidence coupling.
4. **Restored Photopeak Area**: $S^{(\mathrm{peak})}_i = \frac{4\pi C_i}{A P_i a^2} = \frac{4\pi P_j}{C_j P_{ij} W_0 a^2}$.
5. **Virtual Summing Area**: $S_{\mathrm{v}, j} = \frac{4\pi B_j}{C_j a^2}$.
6. **Dual Cross-Quotient**:
   $\frac{S_i^{(\mathrm{peak})}}{S_{\mathrm{v}, j}} = \frac{P_j}{B_j P_{ij} W_0} = \frac{P_j}{P_{ij}} \frac{\epsilon_{p, i}}{\epsilon_{t, i}}$.
7. **Unit Branching Limit**:
   When $P_j = P_{ij} = 1$, the cross-quotient is strictly $(P/T)_i = \epsilon_{p, i} / \epsilon_{t, i}$.

All proofs verified constructively with 0 `sorry`s and 0 custom axioms.
-/

namespace InfoGeometry.Probability.DetectorCrossSectionDuality

noncomputable section

open Real

/-! ### 1. Quartic Linearizer Geometry -/

/-- The 1D distance linearizer $L(d) = a \cdot d + b$. -/
def linearizer (a b d : ℝ) : ℝ := a * d + b

/-- **Theorem**: The zero-intercept of the linearizer occurs at $d = -d_0$ when $b = a \cdot d_0$. -/
theorem linearizer_root (a d_0 : ℝ) :
    linearizer a (a * d_0) (-d_0) = 0 := by
  dsimp [linearizer]
  ring

/-- **Theorem**: When $a \neq 0$, the ratio $b / a$ extracts the virtual interaction depth $d_0$. -/
theorem linearizer_extract_d0 (a d_0 : ℝ) (ha : a ≠ 0) :
    (a * d_0) / a = d_0 := by
  exact mul_div_cancel_left₀ d_0 ha

/-! ### 2. Restored Linear Response -/

/-- Observed singles response with summing-out deficit: $I_i = C_i X - B_i Q$. -/
def singlesResponse (C B X Q : ℝ) : ℝ := C * X - B * Q

/-- Restored unsummed rate adding back the coincidence loss: $L_i = I_i + B_i Q$. -/
def restoredRate (I B Q : ℝ) : ℝ := I + B * Q

/-- **Theorem**: Adding the quadratic coincidence loss back restores the linear channel $C_i X$. -/
theorem restored_linear_rate (C B X Q : ℝ) :
    restoredRate (singlesResponse C B X Q) B Q = C * X := by
  dsimp [singlesResponse, restoredRate]
  ring

/-! ### 3. Activity Cancellation in Coincidence Normalization -/

/-- Absolute activity derived from the coincidence sum-peak balance $X = \sqrt{Q}$. -/
def derivedActivity (C_i C_j P_i P_j P_ij W_0 : ℝ) : ℝ :=
  C_i * C_j * (P_ij / (P_i * P_j)) * W_0

/-- **Theorem**: Activity cancellation in the coincidence scaling equation. -/
theorem activity_coincidence_relation (C_i C_j P_i P_j P_ij W_0 : ℝ)
    (hPi : P_i ≠ 0) (hPj : P_j ≠ 0) (hPij : P_ij ≠ 0) (hW0 : W_0 ≠ 0) :
    (derivedActivity C_i C_j P_i P_j P_ij W_0) * P_i * P_j / (P_ij * W_0) = C_i * C_j := by
  dsimp [derivedActivity]
  field_simp

/-! ### 4. Restored Photopeak Area and Activity Independence -/

/-- The restored photopeak area $S^{(\mathrm{peak})}_i = \frac{4\pi C_i}{A P_i a^2}$. -/
def photopeakArea (C A P a : ℝ) : ℝ :=
  (4 * Real.pi * C) / (A * P * a ^ 2)

/-- The activity-free representation of the restored photopeak area. -/
def photopeakAreaActivityFree (C_j P_j P_ij W_0 a : ℝ) : ℝ :=
  (4 * Real.pi * P_j) / (C_j * P_ij * W_0 * a ^ 2)

/-- **Theorem**: Substituting the coincidence activity eliminates $A$ and channel $i$ from $S^{(\mathrm{peak})}_i$. -/
theorem photopeakArea_eq_activityFree (C_i C_j P_i P_j P_ij W_0 a : ℝ)
    (hCi : C_i ≠ 0) (hPi : P_i ≠ 0) (hPj : P_j ≠ 0) (hPij : P_ij ≠ 0) (hW0 : W_0 ≠ 0) (ha : a ≠ 0) :
    photopeakArea C_i (derivedActivity C_i C_j P_i P_j P_ij W_0) P_i a =
      photopeakAreaActivityFree C_j P_j P_ij W_0 a := by
  dsimp [photopeakArea, photopeakAreaActivityFree, derivedActivity]
  have _hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-! ### 5. Virtual Coincidence Loss Area -/

/-- The virtual loss area $S_{\mathrm{v}, j} = \frac{4\pi B_j}{C_j a^2}$. -/
def virtualSummingArea (B C a : ℝ) : ℝ :=
  (4 * Real.pi * B) / (C * a ^ 2)

/-! ### 6. Dual Cross-Quotient and Intrinsic Peak-to-Total -/

/-- Cross-quotient between the restored photopeak area of $i$ and virtual summing area of $j$. -/
def crossQuotient (S_peak S_v : ℝ) : ℝ := S_peak / S_v

/-- **Theorem**: The cross-quotient expressed in terms of the fitted polynomial coefficients. -/
theorem cross_quotient_parameter_form (C_j B_j P_j P_ij W_0 a : ℝ)
    (hCj : C_j ≠ 0) (hBj : B_j ≠ 0) (hPij : P_ij ≠ 0) (hW0 : W_0 ≠ 0) (ha : a ≠ 0) :
    crossQuotient (photopeakAreaActivityFree C_j P_j P_ij W_0 a) (virtualSummingArea B_j C_j a) =
      P_j / (B_j * P_ij * W_0) := by
  dsimp [crossQuotient, photopeakAreaActivityFree, virtualSummingArea]
  have _hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **Theorem**: Restored photopeak area evaluates to $\frac{4\pi \epsilon_{p, i}}{a^2}$ under microscopic decomposition. -/
theorem photopeakArea_microscopic (A P_i C_i eps_pi a : ℝ)
    (hCi : C_i = A * P_i * eps_pi) (hA : A ≠ 0) (hPi : P_i ≠ 0) (ha : a ≠ 0) :
    photopeakArea C_i A P_i a = (4 * Real.pi * eps_pi) / a ^ 2 := by
  dsimp [photopeakArea]
  rw [hCi]
  field_simp

/-- Angular response is absorbed in `eps_ti` (or set to unity) in this
decomposition. For a bare total efficiency use the explicit angular theorem below. -/
theorem virtualSummingArea_microscopic (A P_j P_ij eps_pj eps_ti a C_j B_j : ℝ)
    (hCj : C_j = A * P_j * eps_pj)
    (hBj : B_j = A * P_ij * eps_pj * eps_ti)
    (hA : A ≠ 0) (hPj : P_j ≠ 0) (heps_pj : eps_pj ≠ 0) (ha : a ≠ 0) :
    virtualSummingArea B_j C_j a = (4 * Real.pi * (P_ij / P_j) * eps_ti) / a ^ 2 := by
  dsimp [virtualSummingArea]
  rw [hCj, hBj]
  field_simp

/-- **Theorem**: The cross-quotient of microscopic cross-sections recovers the intrinsic Peak-to-Total ratio. -/
theorem crossQuotient_microscopic (eps_pi eps_ti a P_j P_ij : ℝ)
    (hPj : P_j ≠ 0) (hPij : P_ij ≠ 0) (heps_ti : eps_ti ≠ 0) (ha : a ≠ 0) :
    crossQuotient ((4 * Real.pi * eps_pi) / a ^ 2)
      ((4 * Real.pi * (P_ij / P_j) * eps_ti) / a ^ 2) =
      (P_j / P_ij) * (eps_pi / eps_ti) := by
  dsimp [crossQuotient]
  have _hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **Theorem**: In the unit branching limit ($P_j = P_{ij} = 1$), the cross-quotient is strictly $(P/T)_i$. -/
theorem unit_branching_peak_to_total (eps_pi eps_ti a : ℝ)
    (heps_ti : eps_ti ≠ 0) (ha : a ≠ 0) :
    crossQuotient ((4 * Real.pi * eps_pi) / a ^ 2)
      ((4 * Real.pi * (1 / 1) * eps_ti) / a ^ 2) =
      eps_pi / eps_ti := by
  dsimp [crossQuotient]
  have _hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-! ### 7. General Angular Factor Consistency (Peak-Peak vs Peak-Total) -/

/-- **Theorem**: Virtual summing area evaluates to $\frac{4\pi (P_{ij}/P_j) W_{pt} \epsilon_{t, i}}{a^2}$
    under microscopic decomposition with peak-total angular factor $W_{pt}$. -/
theorem virtualSummingArea_microscopic_angular (A P_j P_ij eps_pj eps_ti a C_j B_j W_pt : ℝ)
    (hCj : C_j = A * P_j * eps_pj)
    (hBj : B_j = A * P_ij * eps_pj * eps_ti * W_pt)
    (hA : A ≠ 0) (hPj : P_j ≠ 0) (heps_pj : eps_pj ≠ 0) (ha : a ≠ 0) :
    virtualSummingArea B_j C_j a = (4 * Real.pi * (P_ij / P_j) * W_pt * eps_ti) / a ^ 2 := by
  dsimp [virtualSummingArea]
  rw [hCj, hBj]
  field_simp

/-- **Theorem**: Cross-quotient with peak-total angular correlation $W_{pt}$. -/
theorem crossQuotient_microscopic_angular (eps_pi eps_ti a P_j P_ij W_pt : ℝ)
    (hPj : P_j ≠ 0) (hPij : P_ij ≠ 0) (hWpt : W_pt ≠ 0) (heps_ti : eps_ti ≠ 0) (ha : a ≠ 0) :
    crossQuotient ((4 * Real.pi * eps_pi) / a ^ 2)
      ((4 * Real.pi * (P_ij / P_j) * W_pt * eps_ti) / a ^ 2) =
      (P_j / (P_ij * W_pt)) * (eps_pi / eps_ti) := by
  dsimp [crossQuotient]
  have _hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **Theorem**: Multiplying by conditional branching $P(i\mid j) = P_{ij}/P_j$ and $W_{pt}$
    recovers the intrinsic peak-to-total ratio $(P/T)_i = \epsilon_{p, i} / \epsilon_{t, i}$. -/
theorem peak_to_total_recovery_general (eps_pi eps_ti a P_j P_ij W_pt : ℝ)
    (hPj : P_j ≠ 0) (hPij : P_ij ≠ 0) (hWpt : W_pt ≠ 0) (heps_ti : eps_ti ≠ 0) (ha : a ≠ 0) :
    (P_ij / P_j) * W_pt * crossQuotient ((4 * Real.pi * eps_pi) / a ^ 2)
      ((4 * Real.pi * (P_ij / P_j) * W_pt * eps_ti) / a ^ 2) =
      eps_pi / eps_ti := by
  dsimp [crossQuotient]
  have _hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **Theorem**: General parameter-form $(P/T)_i$ extraction using both peak-peak ($W_{pp}$)
    and peak-total ($W_{pt}$) angular factors. -/
theorem peak_to_total_parameter_form (C_j B_j P_j P_ij W_pp W_pt a : ℝ)
    (hCj : C_j ≠ 0) (hBj : B_j ≠ 0) (hPj : P_j ≠ 0) (hPij : P_ij ≠ 0) (hWpp : W_pp ≠ 0) (ha : a ≠ 0) :
    (P_ij / P_j) * W_pt * crossQuotient (photopeakAreaActivityFree C_j P_j P_ij W_pp a) (virtualSummingArea B_j C_j a) =
      W_pt / (B_j * W_pp) := by
  dsimp [crossQuotient, photopeakAreaActivityFree, virtualSummingArea]
  have _hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **Theorem**: When peak-total and peak-peak angular factors coincide ($W_{pt} = W_{pp}$),
    the recovered peak-to-total ratio is simply $1 / B_j$. -/
theorem peak_to_total_parameter_concordant_angular (C_j B_j P_j P_ij W a : ℝ)
    (hCj : C_j ≠ 0) (hBj : B_j ≠ 0) (hPj : P_j ≠ 0) (hPij : P_ij ≠ 0) (hW : W ≠ 0) (ha : a ≠ 0) :
    (P_ij / P_j) * W * crossQuotient (photopeakAreaActivityFree C_j P_j P_ij W a) (virtualSummingArea B_j C_j a) =
      1 / B_j := by
  dsimp [crossQuotient, photopeakAreaActivityFree, virtualSummingArea]
  have _hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-! ### 8. Theoretical On-Axis Angular Correlation Expansion W(0) -/

/-- The second-order Legendre polynomial $P_2(x) = \frac{1}{2}(3x^2 - 1)$. -/
def legendreP2 (x : ℝ) : ℝ := (3 * x ^ 2 - 1) / 2

/-- The fourth-order Legendre polynomial $P_4(x) = \frac{1}{8}(35x^4 - 30x^2 + 3)$. -/
def legendreP4 (x : ℝ) : ℝ := (35 * x ^ 4 - 30 * x ^ 2 + 3) / 8

/-- **Theorem**: Exact unit boundary of the second Legendre polynomial at $\cos\theta = 1$. -/
theorem legendreP2_one : legendreP2 1 = 1 := by
  dsimp [legendreP2]
  norm_num

/-- **Theorem**: Exact unit boundary of the fourth Legendre polynomial at $\cos\theta = 1$. -/
theorem legendreP4_one : legendreP4 1 = 1 := by
  dsimp [legendreP4]
  norm_num

/-- Unperturbed directional angular correlation function expanded in Legendre polynomials:
    $W(\theta) = 1 + A_{22} P_2(\cos\theta) + A_{44} P_4(\cos\theta)$. -/
def directionalCorrelation (A_22 A_44 cos_theta : ℝ) : ℝ :=
  1 + A_22 * legendreP2 cos_theta + A_44 * legendreP4 cos_theta

/-- Directional angular correlation expansion at θ = 0 up to rank 4:
    $W(0) = 1 + A_{22} + A_{44}$. -/
def angularCorrelationZero (A_22 A_44 : ℝ) : ℝ := 1 + A_22 + A_44

/-- **Theorem**: The on-axis directional correlation at $\cos\theta = 1$ reduces identically
    to $W(0) = 1 + A_{22} + A_{44}$ via exact Legendre evaluation. -/
theorem directionalCorrelation_zero (A_22 A_44 : ℝ) :
    directionalCorrelation A_22 A_44 1 = angularCorrelationZero A_22 A_44 := by
  dsimp [directionalCorrelation, angularCorrelationZero, legendreP2, legendreP4]
  ring

/-- **Theorem**: Exact analytical Biedenharn-Rose on-axis correlation for ⁶⁰Co (4⁺ → 2⁺ → 0⁺).
    $A_{22} = 5/49$, $A_{44} = 4/441$, yielding precisely $W(0) = 10/9$. -/
theorem co60_angular_correlation_exact :
    angularCorrelationZero (5 / 49) (4 / 441) = 10 / 9 := by
  dsimp [angularCorrelationZero]
  norm_num


/-- **Theorem**: Pure E1 on-axis correlation for ¹⁵²Gd (3⁻ → 2⁺ → 0⁺, 778.9 → 344.3 keV).
    $A_{22} = -1/14$, $A_{44} = 0$, yielding precisely $W(0) = 13/14$. -/
theorem eu152_gd_angular_correlation_pureE1 :
    angularCorrelationZero (-1 / 14) 0 = 13 / 14 := by
  dsimp [angularCorrelationZero]
  norm_num

/-- **Theorem**: Pure E1 on-axis correlation for ¹⁵²Sm (2⁻ → 2⁺ → 0⁺, 1408.0 → 121.8 keV).
    $A_{22} = 1/4$, $A_{44} = 0$, yielding precisely $W(0) = 5/4$. -/
theorem eu152_sm_1408_angular_correlation_pureE1 :
    angularCorrelationZero (1 / 4) 0 = 5 / 4 := by
  dsimp [angularCorrelationZero]
  norm_num

/-- **Theorem**: Pure multipole on-axis correlation for ²⁰⁸Tl → ²⁰⁸Pb (5⁻ → 3⁻ → 0⁺, 583.2 → 2614.5 keV).
    $A_{22} = 5/28$, $A_{44} = -1/231$, yielding precisely $W(0) = 155/132$. -/
theorem tl208_angular_correlation_pure :
    angularCorrelationZero (5 / 28) (-1 / 231) = 155 / 132 := by
  dsimp [angularCorrelationZero]
  norm_num

/-! ### 9. Point-by-Point Effective Angular Correlation Inversion W_eff(d) -/

/-- Effective point-by-point angular correlation factor:
    $W_{\mathrm{eff}}(d) = \frac{A_{\mathrm{ref}} Q(d)}{L_1(d) L_2(d)} \frac{P_1 P_2}{P_{12}}$. -/
def effectiveAngularFactor (A_ref Q L1 L2 P1 P2 P12 : ℝ) : ℝ :=
  (A_ref * Q / (L1 * L2)) * (P1 * P2 / P12)

/-- **Theorem**: $W_{\mathrm{eff}}$ is the exact reciprocal of the normalized singles-product ratio:
    $W_{\mathrm{eff}} = \left( \frac{L_1 L_2}{A_{\mathrm{ref}} Q} \frac{P_{12}}{P_1 P_2} \right)^{-1}$. -/
theorem effectiveAngularFactor_eq_reciprocal (A_ref Q L1 L2 P1 P2 P12 : ℝ)
    (hA : A_ref ≠ 0) (hQ : Q ≠ 0) (hL1 : L1 ≠ 0) (hL2 : L2 ≠ 0) (hP1 : P1 ≠ 0) (hP2 : P2 ≠ 0) (hP12 : P12 ≠ 0) :
    effectiveAngularFactor A_ref Q L1 L2 P1 P2 P12 =
      ((L1 * L2 / (A_ref * Q)) * (P12 / (P1 * P2)))⁻¹ := by
  dsimp [effectiveAngularFactor]
  field_simp

/-- **Theorem**: When count rates follow coincidence scaling with geometric efficiencies $\varepsilon_1, \varepsilon_2$,
    the effective angular factor identically recovers the underlying geometric factor $W(d)$. -/
theorem effectiveAngularFactor_recovers_W (A_ref eps1 eps2 W_d P1 P2 P12 : ℝ)
    (hA : A_ref ≠ 0) (heps1 : eps1 ≠ 0) (heps2 : eps2 ≠ 0) (hP1 : P1 ≠ 0) (hP2 : P2 ≠ 0) (hP12 : P12 ≠ 0) :
    effectiveAngularFactor A_ref (A_ref * P12 * eps1 * eps2 * W_d)
      (A_ref * P1 * eps1) (A_ref * P2 * eps2) P1 P2 P12 = W_d := by
  dsimp [effectiveAngularFactor]
  field_simp

end

end InfoGeometry.Probability.DetectorCrossSectionDuality

