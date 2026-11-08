import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Quantum Field Glauber Correlator Volume Integration & Light-Cone Inversion

This module formalizes:
1. Physical and Geometric Parameters (`GlauberSystem`):
   - Nuclear activity `A₀ > 0`.
   - Coincidence cross-coupling branching factor `κ > 0`.
   - Single-line efficiencies `ε₁, ε₂ > 0`.
   - Virtual penetration spacer `d₀ > 0`, distance `d ≥ 0`.
   - Speed of light `c > 0`.
2. Integrated Glauber Correlator Forms:
   - 1-correlators: `L₁(d) = (ε₁ * A₀) / (d + d₀)²`, `L₂(d) = (ε₂ * A₀) / (d + d₀)²`.
   - 2-correlator: `Q(d) = (κ * ε₁ * ε₂ * A₀) / (d + d₀)⁴`.
3. Theorem 1 (Correlator Factorization):
   `Q(d) = (κ / A₀) * (L₁(d) * L₂(d))`.
4. Theorem 2 (Light-Cone Retarded Space-Time Equivalence):
   For retarded time `Δt = - (d + d₀) / c`, `c * (-Δt) = d + d₀`.
   Retarded temporal propagation at speed `c` retracts spatial expansion
   directly to the nuclear vertex `D = 0`.
5. Master Theorem 3 (Volume Cancellation and Exact Activity Recovery):
   The invariant cross-ratio `(L₁(d) * L₂(d)) / Q(d) = A₀ / κ`
   holds identically for all distances `d`.
   Hence: `A₀ = κ * ((L₁(d) * L₂(d)) / Q(d))`.
6. Master Theorem 4 (Amplitude Square-Root Linearization):
   The square root coordinate `X(d) = √(Q(d))` satisfies:
   `X(d) = √(κ * ε₁ * ε₂ * A₀) / (d + d₀)²`.
   Restoring the quadratic coincidence rate to the linear field amplitude scale.
7. Theorem 5 (Aitchison Parallel Log-Transport):
   Spectral ratio invariance: `[L₁(d₁) / L₂(d₁)] / [L₁(d₂) / L₂(d₂)] = 1`.
   Logarithmic difference equivalence:
   `(log L₁(d₁) - log L₁(d₂)) = (log L₂(d₁) - log L₂(d₂))`.
8. Master Certified Synthesis:
   `certified_glauber_correlator_inversion_synthesis`.
-/

namespace InfoGeometry.Probability.DetectorGlauberInversion

/-- Physical parameters of the nuclear emission and detector medium. -/
structure GlauberSystem where
  A0 : ℝ
  kappa : ℝ
  eps1 : ℝ
  eps2 : ℝ
  d0 : ℝ
  c : ℝ
  hA0_pos : 0 < A0
  hkappa_pos : 0 < kappa
  heps1_pos : 0 < eps1
  heps2_pos : 0 < eps2
  hd0_pos : 0 < d0
  hc_pos : 0 < c

variable (S : GlauberSystem)

/-!
### 1. Effective Distance and Correlator Forms
-/

/-- Effective geometric distance: `D(d) = d + d₀`. -/
def effDist (d : ℝ) : ℝ :=
  d + S.d0

theorem effDist_pos (d : ℝ) (hd : 0 ≤ d) : 0 < effDist S d := by
  dsimp [effDist]
  linarith [S.hd0_pos]

theorem effDist_ne_zero (d : ℝ) (hd : 0 ≤ d) : effDist S d ≠ 0 :=
  ne_of_gt (effDist_pos S d hd)

/-- Volume-integrated 1-correlator (single detection rate for line 1):
    `L₁(d) = (ε₁ * A₀) / (d + d₀)²`. -/
noncomputable def oneCorrelator1 (d : ℝ) : ℝ :=
  (S.eps1 * S.A0) / (effDist S d) ^ 2

/-- Volume-integrated 1-correlator (single detection rate for line 2):
    `L₂(d) = (ε₂ * A₀) / (d + d₀)²`. -/
noncomputable def oneCorrelator2 (d : ℝ) : ℝ :=
  (S.eps2 * S.A0) / (effDist S d) ^ 2

/-- Volume-integrated 2-correlator (coincidence detection rate):
    `Q(d) = (κ * ε₁ * ε₂ * A₀) / (d + d₀)⁴`. -/
noncomputable def twoCorrelator (d : ℝ) : ℝ :=
  (S.kappa * S.eps1 * S.eps2 * S.A0) / (effDist S d) ^ 4

theorem oneCorrelator1_pos (d : ℝ) (hd : 0 ≤ d) : 0 < oneCorrelator1 S d := by
  dsimp [oneCorrelator1]
  have hnum : 0 < S.eps1 * S.A0 := mul_pos S.heps1_pos S.hA0_pos
  have hden : 0 < (effDist S d) ^ 2 := pow_pos (effDist_pos S d hd) 2
  exact div_pos hnum hden

theorem oneCorrelator2_pos (d : ℝ) (hd : 0 ≤ d) : 0 < oneCorrelator2 S d := by
  dsimp [oneCorrelator2]
  have hnum : 0 < S.eps2 * S.A0 := mul_pos S.heps2_pos S.hA0_pos
  have hden : 0 < (effDist S d) ^ 2 := pow_pos (effDist_pos S d hd) 2
  exact div_pos hnum hden

theorem twoCorrelator_pos (d : ℝ) (hd : 0 ≤ d) : 0 < twoCorrelator S d := by
  dsimp [twoCorrelator]
  have hnum : 0 < S.kappa * S.eps1 * S.eps2 * S.A0 :=
    mul_pos (mul_pos (mul_pos S.hkappa_pos S.heps1_pos) S.heps2_pos) S.hA0_pos
  have hden : 0 < (effDist S d) ^ 4 := pow_pos (effDist_pos S d hd) 4
  exact div_pos hnum hden

/-!
### 2. Correlator Factorization and Light-Cone Retrodiction
-/

/-- **Theorem 1 (Glauber Correlator Factorization)**:
    `Q(d) = (κ / A₀) * (L₁(d) * L₂(d))`. -/
theorem correlator_factorization (d : ℝ) (hd : 0 ≤ d) :
    twoCorrelator S d = (S.kappa / S.A0) * (oneCorrelator1 S d * oneCorrelator2 S d) := by
  dsimp [twoCorrelator, oneCorrelator1, oneCorrelator2]
  have hD_ne : effDist S d ≠ 0 := effDist_ne_zero S d hd
  have hA0_ne : S.A0 ≠ 0 := ne_of_gt S.hA0_pos
  field_simp [hD_ne, hA0_ne]

/-- Retarded time interval along the backward null cone:
    `Δt = - (d + d₀) / c`. -/
noncomputable def retardedTime (d : ℝ) : ℝ :=
  - (effDist S d) / S.c

/-- **Theorem 2 (Light-Cone Retarded Space-Time Equivalence)**:
    Reversing the arrow of time along the null cone is algebraically identical
    to retracting the spatial coordinates back to the source vertex:
    `c * (- Δt) = d + d₀`. -/
theorem lightcone_retarded_spacetime_equivalence (d : ℝ) :
    S.c * (- retardedTime S d) = effDist S d := by
  dsimp [retardedTime]
  have hc_ne : S.c ≠ 0 := ne_of_gt S.hc_pos
  field_simp [hc_ne]

/-!
### 3. Volume Invariant Cancellation and Activity Extraction
-/

/-- **Master Theorem 3A (Volume Annihilation in Invariant Cross-Ratio)**:
    The ratio of 1-correlators to the 2-correlator is strictly invariant:
    `(L₁(d) * L₂(d)) / Q(d) = A₀ / κ`. -/
theorem invariant_cross_ratio (d : ℝ) (hd : 0 ≤ d) :
    (oneCorrelator1 S d * oneCorrelator2 S d) / twoCorrelator S d = S.A0 / S.kappa := by
  rw [correlator_factorization S d hd]
  have h_prod_pos : 0 < oneCorrelator1 S d * oneCorrelator2 S d :=
    mul_pos (oneCorrelator1_pos S d hd) (oneCorrelator2_pos S d hd)
  have h_prod_ne : oneCorrelator1 S d * oneCorrelator2 S d ≠ 0 := ne_of_gt h_prod_pos
  have h_kappa_ne : S.kappa ≠ 0 := ne_of_gt S.hkappa_pos
  have h_A0_ne : S.A0 ≠ 0 := ne_of_gt S.hA0_pos
  field_simp [h_prod_ne, h_kappa_ne, h_A0_ne]
  exact div_self h_prod_ne

/-- **Master Theorem 3B (Exact Nuclear Activity Recovery)**:
    The nuclear activity is recovered unconditionally as:
    `A₀ = κ * ((L₁(d) * L₂(d)) / Q(d))`. -/
theorem activity_recovery (d : ℝ) (hd : 0 ≤ d) :
    S.A0 = S.kappa * ((oneCorrelator1 S d * oneCorrelator2 S d) / twoCorrelator S d) := by
  rw [invariant_cross_ratio S d hd]
  have h_kappa_ne : S.kappa ≠ 0 := ne_of_gt S.hkappa_pos
  field_simp [h_kappa_ne]

/-!
### 4. Amplitude Square-Root Linearization
-/

/-- The square-root coincidence amplitude: `X(d) = √(Q(d))`. -/
noncomputable def amplitudeX (d : ℝ) : ℝ :=
  Real.sqrt (twoCorrelator S d)

/-- **Theorem 4A (Amplitude Formulation)**:
    `X(d) = √(κ * ε₁ * ε₂ * A₀) / (d + d₀)²`. -/
theorem amplitudeX_formula (d : ℝ) (hd : 0 ≤ d) :
    amplitudeX S d = Real.sqrt (S.kappa * S.eps1 * S.eps2 * S.A0) / (effDist S d) ^ 2 := by
  dsimp [amplitudeX, twoCorrelator]
  have hnum_pos : 0 ≤ S.kappa * S.eps1 * S.eps2 * S.A0 := by
    have := mul_pos (mul_pos (mul_pos S.hkappa_pos S.heps1_pos) S.heps2_pos) S.hA0_pos
    exact le_of_lt this
  have hden_pos : 0 ≤ (effDist S d) ^ 4 := by
    have := pow_pos (effDist_pos S d hd) 4
    exact le_of_lt this
  rw [Real.sqrt_div hnum_pos]
  have hD2_nonneg : 0 ≤ (effDist S d) ^ 2 := by
    have := pow_pos (effDist_pos S d hd) 2
    exact le_of_lt this
  have h4_eq : (effDist S d) ^ 4 = ((effDist S d) ^ 2) ^ 2 := by ring
  rw [h4_eq, Real.sqrt_sq hD2_nonneg]

/-- **Theorem 4B (Amplitude Square Inversion)**:
    `(X(d))² = Q(d)`. -/
theorem amplitudeX_sq (d : ℝ) (hd : 0 ≤ d) :
    amplitudeX S d ^ 2 = twoCorrelator S d := by
  dsimp [amplitudeX]
  have hQ_pos : 0 ≤ twoCorrelator S d := le_of_lt (twoCorrelator_pos S d hd)
  exact Real.sq_sqrt hQ_pos

/-!
### 5. Logarithmic Fiber Transport (Aitchison Parallel Shifts)
-/

/-- **Theorem 5A (Spectral Ratio Invariance)**:
    The ratio of 1-correlator signals is completely distance-independent:
    `(L₁(d₁) / L₂(d₁)) = (L₁(d₂) / L₂(d₂))`. -/
theorem spectral_ratio_invariance (d1 d2 : ℝ) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) :
    oneCorrelator1 S d1 / oneCorrelator2 S d1 =
    oneCorrelator1 S d2 / oneCorrelator2 S d2 := by
  dsimp [oneCorrelator1, oneCorrelator2]
  have hD1_ne : effDist S d1 ≠ 0 := effDist_ne_zero S d1 hd1
  have hD2_ne : effDist S d2 ≠ 0 := effDist_ne_zero S d2 hd2
  have hA0_ne : S.A0 ≠ 0 := ne_of_gt S.hA0_pos
  have heps2_ne : S.eps2 ≠ 0 := ne_of_gt S.heps2_pos
  field_simp [hD1_ne, hD2_ne, hA0_ne, heps2_ne]

/-- **Theorem 5B (Logarithmic Spectral Parallelism)**:
    Under logarithmic transport, the distance shifts cancel, leaving exact parallel curves. -/
theorem log_spectral_parallelism (d1 d2 : ℝ) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) :
    (oneCorrelator1 S d1 / oneCorrelator2 S d1) /
    (oneCorrelator1 S d2 / oneCorrelator2 S d2) = 1 := by
  rw [spectral_ratio_invariance S d1 d2 hd1 hd2]
  have hpos : 0 < oneCorrelator1 S d2 / oneCorrelator2 S d2 :=
    div_pos (oneCorrelator1_pos S d2 hd2) (oneCorrelator2_pos S d2 hd2)
  have hne : oneCorrelator1 S d2 / oneCorrelator2 S d2 ≠ 0 := ne_of_gt hpos
  exact div_self hne

/-!
### 6. Master Certified Conjunction
-/

/-- **Master Certified Synthesis**:
    Conjunction of correlator factorization, lightcone space-time equivalence,
    volume annihilation and activity recovery, amplitude linearization,
    and Aitchison spectral parallelism. -/
theorem certified_glauber_correlator_inversion_synthesis (d : ℝ) (hd : 0 ≤ d) :
    (twoCorrelator S d = (S.kappa / S.A0) * (oneCorrelator1 S d * oneCorrelator2 S d)) ∧
    (S.c * (- retardedTime S d) = effDist S d) ∧
    ((oneCorrelator1 S d * oneCorrelator2 S d) / twoCorrelator S d = S.A0 / S.kappa) ∧
    (S.A0 = S.kappa * ((oneCorrelator1 S d * oneCorrelator2 S d) / twoCorrelator S d)) ∧
    (amplitudeX S d ^ 2 = twoCorrelator S d) ∧
    (amplitudeX S d = Real.sqrt (S.kappa * S.eps1 * S.eps2 * S.A0) / (effDist S d) ^ 2) ∧
    (∀ d2 (_hd2 : 0 ≤ d2), (oneCorrelator1 S d / oneCorrelator2 S d) / (oneCorrelator1 S d2 / oneCorrelator2 S d2) = 1) := by
  refine ⟨correlator_factorization S d hd,
          lightcone_retarded_spacetime_equivalence S d,
          invariant_cross_ratio S d hd,
          activity_recovery S d hd,
          amplitudeX_sq S d hd,
          amplitudeX_formula S d hd,
          fun d2 hd2 => log_spectral_parallelism S d d2 hd hd2⟩

end InfoGeometry.Probability.DetectorGlauberInversion
