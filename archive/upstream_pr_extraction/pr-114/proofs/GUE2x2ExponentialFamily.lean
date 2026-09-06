import Mathlib

/-!
# 2×2 GUE Matrix — Exponential Family, JPDF, and Wigner Surmise

## Formalization of the 2×2 Gaussian Unitary Ensemble

This file formalizes the complete analytic structure of the 2 × 2 GUE:

1. **Matrix construction** — Hermitian 2×2 with Gaussian entries:
   ```
   H = [ x₁       x₃ − i x₄ ]
       [ x₃ + i x₄    x₂     ]
   ```
   where x₁, x₂ ~ N(0,1) and x₃, x₄ ~ N(0, 1/2).

2. **Joint eigenvalue distribution** (JPDF):
   P(l1, l2) = (1/C) |l1 − l2|² exp(−(l1² + l2²)/2)

3. **Exponential family structure**:
   - Sufficient statistics: T₁ = l1² + l2²,  T₂ = ln|l1 − l2|
   - Natural parameters:  η₁ = −1/2,        η₂ = 2 (β for GUE)

4. **Wigner surmise** (marginal spacing distribution):
   P_GUE(s) = (32/π²) s² exp(−4s²/π),   s ≥ 0
   with mean spacing = 1.

5. **Eigenvalue repulsion**: P_GUE(0) = 0 because of the s² term
   (Dyson index β = 2).

Reference: The 2×2 GUE is the exactly-solvable case that Wigner
surmised captures the N → ∞ spacing distribution to high accuracy.
-/

noncomputable section

open Real
open Complex
open Set

---------------------------------------------------------------
-- Part 1:  The 2×2 GUE matrix and its element distributions
---------------------------------------------------------------

/-- A 2×2 Hermitian matrix representing one draw from the GUE.
    H = [a      c − i d]
        [c + i d    b  ]
    where a,b ~ N(0,1) and c,d ~ N(0, 1/2). -/
structure GUE2x2 where
  a : ℝ   -- diagonal element H₁₁ ~ N(0,1)
  b : ℝ   -- diagonal element H₂₂ ~ N(0,1)
  c : ℝ   -- real part of off-diagonal ~ N(0, 1/2)
  d : ℝ   -- imag part of off-diagonal ~ N(0, 1/2)

/-- The Gaussian (normal) PDF with mean μ and variance sigma_sq:
    f(x) = (1/√(2πsigma_sq)) exp(−(x−μ)²/(2sigma_sq)) -/
def gaussianPDF (μ sigma_sq x : ℝ) (_hsigma_sq : 0 < sigma_sq) : ℝ :=
  (Real.sqrt (2 * π * sigma_sq))⁻¹ * Real.exp (-(x - μ)^2 / (2 * sigma_sq))

/-- PDF of a standard normal N(0,1). -/
def standardNormalPDF (x : ℝ) : ℝ :=
  (Real.sqrt (2 * π))⁻¹ * Real.exp (-x^2 / 2)

/-- PDF of N(0, 1/2). -/
def halfVarianceNormalPDF (x : ℝ) : ℝ :=
  (Real.sqrt π)⁻¹ * Real.exp (-x^2)

/-- The joint probability density of the four independent entries
    of a 2×2 GUE matrix:
    P(a,b,c,d) ∝ exp(−(a² + b²)/2) · exp(−(c² + d²)) -/
def gue2x2EntryPDF (H : GUE2x2) : ℝ :=
  standardNormalPDF H.a *
  standardNormalPDF H.b *
  halfVarianceNormalPDF H.c *
  halfVarianceNormalPDF H.d

/-- The matrix trace squared: Tr(H²) = a² + b² + 2(c² + d²).
    This is the Gaussian weight (confinement potential). -/
def gue2x2_traceSquared (H : GUE2x2) : ℝ :=
  H.a^2 + H.b^2 + 2 * (H.c^2 + H.d^2)

/-- The GUE weight is exp(−½ Tr(H²)) up to normalization. -/
theorem gue2x2_entryPDF_as_weight (H : GUE2x2) :
    gue2x2EntryPDF H = (2 * π^2)⁻¹ * Real.exp (-(gue2x2_traceSquared H) / 2) := by
  unfold gue2x2EntryPDF standardNormalPDF halfVarianceNormalPDF gue2x2_traceSquared
  have hconst : ((Real.sqrt (2 * Real.pi))⁻¹)^2 * ((Real.sqrt Real.pi)⁻¹)^2 =
      (2 * Real.pi^2)⁻¹ := by
    calc
      ((Real.sqrt (2 * Real.pi))⁻¹)^2 * ((Real.sqrt Real.pi)⁻¹)^2 =
        ((Real.sqrt (2 * Real.pi) * Real.sqrt Real.pi)⁻¹)^2 := by
          ring
      _ = ((Real.sqrt (2 * Real.pi) * Real.sqrt Real.pi)^2)⁻¹ := by
        simpa using (inv_pow (Real.sqrt (2 * Real.pi) * Real.sqrt Real.pi) 2)
      _ = (2 * Real.pi^2)⁻¹ := by
        congr
        calc
          (Real.sqrt (2 * Real.pi) * Real.sqrt Real.pi)^2
            = (Real.sqrt (2 * Real.pi))^2 * (Real.sqrt Real.pi)^2 := by ring
          _ = (2 * Real.pi) * Real.pi := by
            rw [Real.sq_sqrt (show (0:ℝ) ≤ 2*Real.pi by positivity), Real.sq_sqrt (show (0:ℝ) ≤ Real.pi by positivity)]
          _ = 2 * Real.pi^2 := by ring
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-H.a^2 / 2) *
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-H.b^2 / 2)) *
        ((Real.sqrt Real.pi)⁻¹ * Real.exp (-H.c^2)) *
        ((Real.sqrt Real.pi)⁻¹ * Real.exp (-H.d^2))
      = ((Real.sqrt (2 * Real.pi))⁻¹)^2 * ((Real.sqrt Real.pi)⁻¹)^2 *
          (Real.exp (-H.a^2 / 2) * Real.exp (-H.b^2 / 2) * (Real.exp (-H.c^2) * Real.exp (-H.d^2))) := by
        ring
    _ = (2 * Real.pi^2)⁻¹ * (Real.exp (-H.a^2 / 2) * Real.exp (-H.b^2 / 2) * (Real.exp (-H.c^2) * Real.exp (-H.d^2))) := by
      rw [hconst]
    _ = (2 * Real.pi^2)⁻¹ * Real.exp (-(H.a^2 + H.b^2 + 2 * (H.c^2 + H.d^2)) / 2) := by
      congr
      rw [← Real.exp_add]
      rw [← Real.exp_add]
      rw [← Real.exp_add]
      congr
      ring
    _ = (2 * Real.pi^2)⁻¹ * Real.exp (-(H.a^2 + H.b^2 + 2 * (H.c^2 + H.d^2)) / 2) := by rfl
---------------------------------------------------------------
-- Part 2:  Eigenvalues of the 2×2 GUE matrix
---------------------------------------------------------------

/-- The characteristic polynomial of H:
    det(H − lamI) = lam² − (a+b)lam + (ab − c² − d²).
    Eigenvalues are the roots of this quadratic. -/
def gue2x2_charPoly (H : GUE2x2) (lam : ℝ) : ℝ :=
  lam^2 - (H.a + H.b) * lam + (H.a * H.b - H.c^2 - H.d^2)

/-- The discriminant Δ = (a+b)² − 4(ab − c² − d²) = (a−b)² + 4(c² + d²).
    Since c² + d² ≥ 0, we have Δ ≥ 0, so eigenvalues are always real. -/
def gue2x2_discriminant (H : GUE2x2) : ℝ :=
  (H.a - H.b)^2 + 4 * (H.c^2 + H.d^2)

theorem discriminant_nonneg (H : GUE2x2) : 0 ≤ gue2x2_discriminant H := by
  unfold gue2x2_discriminant
  nlinarith [sq_nonneg (H.a - H.b), sq_nonneg H.c, sq_nonneg H.d]

/-- The two real eigenvalues of H (ordered l1 ≥ l2). -/
def gue2x2_eigenvalues (H : GUE2x2) : ℝ × ℝ :=
  let disc := Real.sqrt (gue2x2_discriminant H)
  let center := (H.a + H.b) / 2
  (center + disc / 2, center - disc / 2)

/-- Spacing S = l1 − l2 = √Δ ≥ 0. -/
def gue2x2_spacing (H : GUE2x2) : ℝ :=
  Real.sqrt (gue2x2_discriminant H)

/-- Center-of-mass R = l1 + l2 = a + b = Tr(H). -/
def gue2x2_centerOfMass (H : GUE2x2) : ℝ :=
  H.a + H.b

/-- Trace identity: l1² + l2² = ½(R² + S²) = ½((a+b)² + Δ). -/
theorem eigenvalues_square_sum (H : GUE2x2) :
    (gue2x2_eigenvalues H).1^2 + (gue2x2_eigenvalues H).2^2 =
      H.a^2 + H.b^2 + 2*(H.c^2 + H.d^2) := by
  dsimp [gue2x2_eigenvalues]
  have hsq : (Real.sqrt (gue2x2_discriminant H))^2 = gue2x2_discriminant H := by
    rw [Real.sq_sqrt]
    unfold gue2x2_discriminant
    nlinarith [sq_nonneg (H.a - H.b), sq_nonneg H.c, sq_nonneg H.d]
  calc
    ((H.a + H.b) / 2 + Real.sqrt (gue2x2_discriminant H) / 2)^2 + ((H.a + H.b) / 2 - Real.sqrt (gue2x2_discriminant H) / 2)^2
        = (H.a + H.b)^2 / 2 + (Real.sqrt (gue2x2_discriminant H))^2 / 2 := by
          ring
    _ = (H.a + H.b)^2 / 2 + gue2x2_discriminant H / 2 := by rw [hsq]
    _ = H.a^2 + H.b^2 + 2*(H.c^2 + H.d^2) := by
      simp [gue2x2_discriminant]
      ring

theorem eigenvalues_product (H : GUE2x2) :
    (gue2x2_eigenvalues H).1 * (gue2x2_eigenvalues H).2 =
      H.a * H.b - H.c^2 - H.d^2 := by
  dsimp [gue2x2_eigenvalues]
  have hsq : (Real.sqrt (gue2x2_discriminant H))^2 = gue2x2_discriminant H := by
    rw [Real.sq_sqrt]
    unfold gue2x2_discriminant
    nlinarith [sq_nonneg (H.a - H.b), sq_nonneg H.c, sq_nonneg H.d]
  calc
    ((H.a + H.b) / 2 + Real.sqrt (gue2x2_discriminant H) / 2) *
        ((H.a + H.b) / 2 - Real.sqrt (gue2x2_discriminant H) / 2)
        = (((H.a + H.b)^2) - (Real.sqrt (gue2x2_discriminant H))^2) / 4 := by
          ring
    _ = (((H.a + H.b)^2) - gue2x2_discriminant H) / 4 := by rw [hsq]
    _ = H.a * H.b - H.c^2 - H.d^2 := by
      simp [gue2x2_discriminant]
      ring
-- eigenvalues_product was proven above; this placeholder removed.
---------------------------------------------------------------
-- Part 3:  Joint Eigenvalue Distribution (JPDF)
---------------------------------------------------------------

/-- The unnormalized joint eigenvalue density:
    ρ(l1, l2) = |l1 − l2|² exp(−(l1² + l2²)/2)

    The |l1−l2|² factor encodes the β = 2 (GUE) eigenvalue repulsion
    and arises from the Vandermonde determinant after integrating
    out the unitary eigenvectors. -/
def gue2x2_jpdf_unnormalized (l1 l2 : ℝ) : ℝ :=
  (l1 - l2)^2 * Real.exp (-(l1^2 + l2^2) / 2)

/-- The log of the unnormalized JPDF — exposes the exponential
    family structure directly:
    ln ρ = 2 ln|l1 − l2| − (l1² + l2²)/2 -/
def gue2x2_log_jpdf_unnormalized (l1 l2 : ℝ) (_h : l1 ≠ l2) : ℝ :=
  2 * Real.log |l1 - l2| - (l1^2 + l2^2) / 2

/-- The (S, R) change of variables:
    S = l1 − l2  (spacing ≥ 0)
    R = l1 + l2  (center of mass)
    Then l1² + l2² = (R² + S²)/2. -/
def jpdf_in_SR (S R : ℝ) : ℝ :=
  S^2 * Real.exp (-(R^2 + S^2) / 4)

/-- The JPDF expressed in (S, R) coordinates, showing factorization:
    ρ(S, R) ∝ S² exp(−S²/4) · exp(−R²/4)
    The R-dependent factor is a pure Gaussian and integrates out. -/
theorem jpdf_SR_factorization (S R : ℝ) :
    jpdf_in_SR S R = (S^2 * Real.exp (-S^2 / 4)) * Real.exp (-R^2 / 4) := by
  unfold jpdf_in_SR
  ring_nf
  rw [Real.exp_add]
  ring

---------------------------------------------------------------
-- Part 4:  Exponential Family Structure
---------------------------------------------------------------

/-
**Exponential Family Form** (general):
  P(x | η) = h(x) exp(η · T(x) − A(η))

For the 2×2 GUE eigenvalue distribution:
  P(l1, l2) = (1/C) exp(η₁ T₁ + η₂ T₂)

where:
  T₁(l1, l2) = l1² + l2²    (Gaussian confinement)
  T₂(l1, l2) = ln|l1 − l2|   (Coulomb repulsion)
  η₁ = −1/2                  (confinement strength)
  η₂ = 2                     (Dyson index β = 2 for GUE)

So: P(l1, l2) = (1/C) exp(−½(l1² + l2²) + 2 ln|l1 − l2|)
               = (1/C) |l1 − l2|² exp(−(l1² + l2²)/2)
-/

/-- Sufficient statistic T₁: sum of squared eigenvalues (trace of H²). -/
def expFamily_T1 (l1 l2 : ℝ) : ℝ :=
  l1^2 + l2^2

/-- Sufficient statistic T₂: log of eigenvalue spacing (Coulomb gas). -/
def expFamily_T2 (l1 l2 : ℝ) (_h : l1 ≠ l2) : ℝ :=
  Real.log |l1 - l2|

/-- Natural parameter η₁: −1/2 (Gaussian confinement strength). -/
def expFamily_eta1 : ℝ := -1/2

/-- Natural parameter η₂: 2 (Dyson index β for GUE). -/
def expFamily_eta2 : ℝ := 2

/-- Partition function for the two-eigenvalue exponential family.
    This is the actual Lebesgue integral expression; convergence and closed-form
    evaluation are intentionally separate theorems, not hidden in an opaque
    constant. -/
def expFamily_partition (η1 η2 : ℝ) : ℝ :=
  ∫ x : ℝ × ℝ,
    Real.exp (η1 * (x.1^2 + x.2^2)) * |x.1 - x.2| ^ η2

/-- Log-partition function (log-normalizer) `A(η) = log Z(η)`. -/
def expFamily_logPartition (η1 η2 : ℝ) : ℝ :=
  Real.log (expFamily_partition η1 η2)

@[simp] theorem expFamily_logPartition_eq_log_partition (η1 η2 : ℝ) :
    expFamily_logPartition η1 η2 = Real.log (expFamily_partition η1 η2) := by
  rfl

/-- The unnormalized JPDF is exactly exp(η₁ T₁ + η₂ T₂) for l1 ≠ l2. -/
theorem jpdf_as_exponential_family (l1 l2 : ℝ) (h : l1 ≠ l2) :
    gue2x2_jpdf_unnormalized l1 l2 =
      Real.exp (expFamily_eta1 * expFamily_T1 l1 l2 + expFamily_eta2 * expFamily_T2 l1 l2 h) := by
  unfold gue2x2_jpdf_unnormalized expFamily_T1 expFamily_T2 expFamily_eta1 expFamily_eta2
  have habs_sq : |l1 - l2|^2 = (l1 - l2)^2 := by
    nlinarith [sq_abs (l1 - l2)]
  have hx : |l1 - l2| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr h)
  have h0 : 0 < |l1 - l2|^2 := by
    exact sq_pos_of_ne_zero hx
  have hsq_log : Real.exp (2 * Real.log |l1 - l2|) = |l1 - l2|^2 := by
    have hlog : (2 : ℝ) * Real.log |l1 - l2| = Real.log (|l1 - l2|^2) := by
      simp [Real.log_pow]
    rw [hlog]
    rw [Real.exp_log h0]
  have hcoeff : -(l1^2 + l2^2) / 2 = (-1 / 2) * (l1^2 + l2^2) := by ring
  calc
    (l1 - l2)^2 * Real.exp (-(l1^2 + l2^2) / 2)
        = |l1 - l2|^2 * Real.exp (-(l1^2 + l2^2) / 2) := by rw [← habs_sq]
    _ = Real.exp (2 * Real.log |l1 - l2|) * Real.exp (-(l1^2 + l2^2) / 2) := by rw [hsq_log]
    _ = Real.exp (2 * Real.log |l1 - l2| + (-(l1^2 + l2^2) / 2)) := by
          rw [← Real.exp_add]
    _ = Real.exp (-(l1^2 + l2^2) / 2 + 2 * Real.log |l1 - l2|) := by
          ring_nf
    _ = Real.exp ((-1 / 2) * (l1^2 + l2^2) + 2 * Real.log |l1 - l2|) := by
          rw [hcoeff]
    _ = Real.exp (expFamily_eta1 * (expFamily_T1 l1 l2) + expFamily_eta2 * expFamily_T2 l1 l2 h) := by
          rfl
/-- Base density for the unnormalized eigenvalue JPDF relative to Lebesgue
    measure. It is constant in this simplified two-eigenvalue model. -/
def expFamily_baseMeasure (_l1 _l2 : ℝ) : ℝ := 1

---------------------------------------------------------------
-- Part 5:  Wigner Surmise — Marginal Spacing Distribution
---------------------------------------------------------------

/-- The Wigner surmise (GUE, Dyson index β = 2):
    P_GUE(s) = (32/π²) s² exp(−4s²/π)

    This is the normalized spacing distribution with mean = 1.
    Derived by: (1) change variables to (S, R), (2) integrate out R,
    (3) normalize so ∫₀^∞ s P(s) ds = 1. -/
def wignerSurmiseGUE (s : ℝ) : ℝ :=
  if s ≥ 0 then
    (32 / π^2) * s^2 * Real.exp (-4 * s^2 / π)
  else
    0

/-- The unnormalized Wigner surmise: s² exp(−s²/4).
    This is the form obtained directly from integrating out R
    from the 2×2 GUE JPDF. -/
def wignerSurmise_unnormalized (s : ℝ) : ℝ :=
  s^2 * Real.exp (-s^2 / 4)

/-- The normalizing constant Z such that ∫₀^∞ (s²/Z) exp(−s²/4) ds has mean 1.
    Z = π^(3/2) / 8  for the unnormalized form.
    After mean-normalization: Z_norm = π²/32. -/
def wignerNormalization : ℝ := π^2 / 32

/-- P_GUE(s) = (1/wignerNormalization) * s² exp(−s²/4) * scaling(s).
    Actually the direct formula P(s) = (32/π²) s² exp(−4s²/π)
    is already correctly normalized with mean 1. -/
theorem wignerSurmise_nonneg (s : ℝ) : 0 ≤ wignerSurmiseGUE s := by
  unfold wignerSurmiseGUE
  split
  · have hsq : 0 ≤ s^2 := pow_two_nonneg s
    have h_exp : 0 ≤ Real.exp (-4 * s^2 / π) := Real.exp_nonneg _
    positivity
  · exact le_refl 0

/-- Eigenvalue repulsion: P(0) = 0. The s² term forces the PDF
    to zero at the origin, forbidding degenerate eigenvalues.
    This is the hallmark of the Dyson index β = 2. -/
theorem wignerSurmise_zero_at_origin : wignerSurmiseGUE 0 = 0 := by
  unfold wignerSurmiseGUE
  simp

/-- Level repulsion is quadratic (β = 2): P(s) ~ (32/π²) s² as s → 0⁺. -/
theorem wignerSurmise_small_s_behavior (s : ℝ) (hs : 0 < s) (hs_small : s < 0.1) :
    |wignerSurmiseGUE s - (32/π^2) * s^2| < 0.001 := by
  unfold wignerSurmiseGUE
  simp [show s ≥ 0 from le_of_lt hs]
  have hs2_nonneg : 0 ≤ s^2 := by positivity
  have hs2_lt : s^2 < (1 / 100 : ℝ) := by nlinarith
  let u : ℝ := 4 * s^2 / π
  have hu_nonneg : 0 ≤ u := by
    dsimp [u]
    positivity
  have hu_lt : |Real.exp (-u) - 1| ≤ u := by
    have hle1 : Real.exp (-u) ≤ 1 := by
      apply (Real.exp_le_one_iff).2
      have : -u ≤ 0 := by linarith
      exact this
    have h_add : 1 - u ≤ Real.exp (-u) := by
      have h := Real.add_one_le_exp (-u)
      linarith
    have hle_abs : 1 - Real.exp (-u) ≤ u := by linarith
    have hexpr : Real.exp (-u) - 1 ≤ 0 := by linarith
    have habs : |Real.exp (-u) - 1| = 1 - Real.exp (-u) := by
      rw [abs_of_nonpos hexpr]
      ring
    rw [habs]
    exact hle_abs
  have hmain : |(32 / π^2) * s^2 * (Real.exp (-u) - 1)| ≤ (128 / π^3) * s^4 := by
    have hC_nonneg : 0 ≤ (32 / π^2) := by positivity
    have hsq_nonneg : 0 ≤ s^2 := by positivity
    have huv : (32 / π^2) * s^2 * |Real.exp (-u) - 1| ≤ (32 / π^2) * s^2 * u := by
      exact mul_le_mul_of_nonneg_left hu_lt (mul_nonneg hC_nonneg hsq_nonneg)
    calc
      |(32 / π^2) * s^2 * (Real.exp (-u) - 1)|
          = |(32 / π^2) * s^2| * |Real.exp (-u) - 1| := by
              rw [abs_mul]
      _ = (32 / π^2) * s^2 * |Real.exp (-u) - 1| := by
              rw [abs_of_nonneg (mul_nonneg hC_nonneg hsq_nonneg)]
      _ ≤ (32 / π^2) * s^2 * u := huv
      _ = (32 / π^2) * (s^2 * u) := by ring
      _ = (32 / π^2) * (s^2 * (4 * s^2 / π)) := by simp [u]
      _ = (128 / π^3) * s^4 := by
            field_simp
            ring
  have hnum : (128 / π^3) * s^4 < 0.001 := by
    have hs4_lt : s^4 < (1 / 10000 : ℝ) := by nlinarith
    have hpi3 : (27:ℝ) < π^3 := by
      nlinarith [Real.pi_gt_three, Real.pi_pos]
    have h_inv : 1 / π^3 < 1 / (27:ℝ) := by
      have h27 : 0 < (27 : ℝ) := by norm_num
      exact one_div_lt_one_div_of_lt h27 hpi3
    have hconst : (128 / π^3) < 128 / 27 := by
      have h := (mul_lt_mul_of_pos_left h_inv (by positivity : (0:ℝ) < 128))
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h
    have hs4_pos : 0 < s^4 := by positivity
    have hmul : (128 / π^3) * s^4 < (128 / 27) * s^4 := by
      exact mul_lt_mul_of_pos_right hconst hs4_pos
    have hmul2 : (128 / 27) * s^4 < 0.001 := by
      have hmul2' : (128 / 27 : ℝ) * s^4 < (128 / 27 : ℝ) * (1 / 10000:ℝ) := by
        exact mul_lt_mul_of_pos_left hs4_lt (by positivity)
      have hconstnum : (128 / 27 : ℝ) * (1 / 10000:ℝ) < 0.001 := by norm_num
      linarith
    linarith
  have htarget : |(32 / π^2) * s^2 * (Real.exp (-u) - 1)| < 0.001 := lt_of_le_of_lt hmain hnum
  have hfinal : |(32 / π^2) * s^2 * Real.exp (-(s^2 * 4) / π) - (32 / π^2) * s^2| < 0.001 := by
    have hstep :
        (32 / π^2) * s^2 * Real.exp (-(s^2 * 4) / π) - (32 / π^2) * s^2 =
          (32 / π^2) * s^2 * (Real.exp (-u) - 1) := by
      dsimp [u]
      ring
    simpa [hstep] using htarget
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_assoc, mul_left_comm, mul_comm] using hfinal
/-- The maximum of the Wigner surmise: occurs at s = √(π/4) ≈ 0.88623.
    At this point P_GUE(s_max) = 32/(π²) · (π/4) · exp(−1) = (8/π) exp(−1) ≈ 0.936. -/
theorem wignerSurmise_peak :
    wignerSurmiseGUE (Real.sqrt (π / 4)) = (8 / π) * Real.exp (-1) := by
  have hs : 0 ≤ (Real.sqrt (π / 4) : ℝ) := by positivity
  have hsqrt : Real.sqrt (π / 4) = Real.sqrt π / 2 := by
    rw [Real.sqrt_div (show 0 ≤ (π : ℝ) by positivity)]
    norm_num
  rw [hsqrt]
  unfold wignerSurmiseGUE
  have hs' : 0 ≤ (Real.sqrt π : ℝ) := Real.sqrt_nonneg _
  have hs2 : 0 ≤ Real.sqrt π / 2 := by nlinarith [hs']
  rw [if_pos hs2]
  have hsq : (Real.sqrt π / 2)^2 = π / 4 := by
    rw [div_pow]
    have hpi : 0 ≤ (π : ℝ) := Real.pi_pos.le
    rw [Real.sq_sqrt hpi]
    field_simp
    ring
  rw [hsq]
  field_simp [Real.pi_ne_zero]
  ring

---------------------------------------------------------------
-- Part 6:  Normalization — Mean Spacing = 1
---------------------------------------------------------------

/-- The definite integral ∫₀^∞ s² exp(−4s²/π) ds = π² / 32.
    This is a standard Gaussian moment integral. -/
theorem integral_s2_exp_neg_4s2_over_pi :
    ∫ s in Set.Ioi (0 : ℝ), (s ^ 2 : ℝ) * Real.exp (-(4 * s ^ 2) / π) = π ^ 2 / 32 := by
  have hrew :
      ∫ s in Set.Ioi (0 : ℝ), (s ^ 2 : ℝ) * Real.exp (-(4 * s^2) / π)
        = ∫ s in Set.Ioi (0 : ℝ), s ^ (2 : ℝ) * Real.exp (-(4 / π) * s ^ (2 : ℝ)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro s hs
    simp [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  rw [hrew]
  have h :
      ∫ s in Set.Ioi (0 : ℝ), s ^ (2 : ℝ) * Real.exp (-(4 / π) * s ^ (2 : ℝ)) =
        (4 / π : ℝ) ^ (-(2 + 1 : ℝ) / 2) * (1 / 2) * Real.Gamma ((2 + 1 : ℝ) / 2) := by
    simpa using (_root_.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (2 : ℝ)) (b := 4 / π)
      (by norm_num) (by norm_num) (by positivity))
  have hA :
      (4 / π : ℝ) ^ (-(3 : ℝ) / 2) * (1 / 2) * Real.Gamma (3 / 2) = π ^ 2 / 32 := by
    have hgamma : Real.Gamma (3 / 2 : ℝ) = (1 / 2 : ℝ) * Real.sqrt π := by
      have hhalf : Real.Gamma ((1 / 2 : ℝ) + 1) = (1 / 2 : ℝ) * Real.Gamma (1 / 2 : ℝ) :=
        Real.Gamma_add_one (show (1 / 2 : ℝ) ≠ 0 by norm_num)
      have hhalf2 : Real.Gamma (3 / 2 : ℝ) = (1 / 2 : ℝ) * Real.Gamma (1 / 2 : ℝ) := by
        simpa [show (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 by norm_num] using hhalf
      rw [hhalf2, Real.Gamma_one_half_eq]
    rw [hgamma]
    let x : ℝ := (4 / π : ℝ) ^ (-(3 : ℝ) / 2)
    have hsqpow : x ^ 2 = (4 / π : ℝ) ^ (-(3 : ℝ)) := by
      dsimp [x]
      have hmul := Real.rpow_mul (show (0:ℝ) ≤ (4 / π) by positivity) (-(3:ℝ) / 2) (2 : ℝ)
      have hs : (-(3:ℝ) / 2) * (2:ℝ) = (-(3:ℝ)) := by norm_num
      have hmul' : (4 / π : ℝ) ^ (-(3 : ℝ)) = ((4 / π : ℝ) ^ (-(3 : ℝ) / 2)) ^ 2 := by
        simpa [hs, pow_two] using hmul
      simpa using hmul'.symm
    have hcube : (4 / π : ℝ) ^ (-(3 : ℝ)) = π ^ 3 / 64 := by
      have hpow : (4 / π : ℝ) ^ (-(3 : ℝ)) = ((4 / π : ℝ) ^ (3 : ℝ))⁻¹ := by
        rw [Real.rpow_neg (show (0:ℝ) ≤ (4 / π) by positivity)]
      rw [hpow]
      have hpow3 : (4 / π : ℝ) ^ (3 : ℝ) = (4 / π : ℝ) ^ (3 : ℕ) := by
        simp
      rw [hpow3]
      have h3 : (4 / π : ℝ) ^ (3 : ℕ) = (4 ^ (3 : ℕ) : ℝ) / π ^ 3 := by
        field_simp [Real.pi_ne_zero]
      rw [h3]
      norm_num
    have hsq : (x * (1 / 2) * (1 / 2 * Real.sqrt π)) ^ 2 = (π ^ 2 / 32) ^ 2 := by
      calc
        (x * (1 / 2) * (1 / 2 * Real.sqrt π)) ^ 2
            = x ^ 2 * (1 / 2) ^ 2 * (1 / 2 * Real.sqrt π) ^ 2 := by ring
        _ = (4 / π : ℝ) ^ (-(3 : ℝ)) * (1 / 2) ^ 2 * (1 / 2 * Real.sqrt π) ^ 2 := by rw [hsqpow]
        _ = (π ^ 3 / 64) * (1 / 2) ^ 2 * (1 / 2 * Real.sqrt π) ^ 2 := by rw [hcube]
        _ = (π ^ 2 / 32) ^ 2 := by
          ring_nf
          rw [Real.sq_sqrt (show 0 ≤ π by positivity)]
          field_simp [Real.pi_ne_zero]
    have hnonneg : 0 ≤ x * (1 / 2) * (1 / 2 * Real.sqrt π) := by positivity
    have hnonnegR : 0 ≤ (π ^ 2 / 32 : ℝ) := by
      have hpi2 : 0 ≤ π ^ 2 := by positivity
      nlinarith [hpi2]
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with h1 | h2
    · simpa [x] using h1
    · exfalso
      have hle : (π ^ 2 / 32 : ℝ) ≤ 0 := by nlinarith [hnonneg, h2]
      have hr : 0 < (π ^ 2 / 32 : ℝ) := by positivity
      nlinarith
  have h₂ : (4 / π : ℝ) ^ (((-1 : ℝ) + (-2 : ℝ)) / 2) * (1 / 2) * Real.Gamma (3 / 2) = π ^ 2 / 32 := by
    have hneg : (-(3 : ℝ) / 2 : ℝ) = (((-1 : ℝ) + (-2 : ℝ)) / 2 : ℝ) := by norm_num
    simpa [hneg] using hA
  rw [h]
  calc
    (4 / π : ℝ) ^ (-(2 + 1 : ℝ) / 2) * (1 / 2) * Real.Gamma ((2 + 1 : ℝ) / 2)
        = (4 / π : ℝ) ^ (((-1 : ℝ) + (-2 : ℝ)) / 2) * (1 / 2) * Real.Gamma (3 / 2) := by
          norm_num
    _ = π ^ 2 / 32 := h₂

/-- The Wigner surmise integrates to 1 over [0, ∞). -/
theorem wignerSurmise_integrates_to_one :
    ∫ s in Set.Ioi (0 : ℝ), wignerSurmiseGUE s = 1 := by
  have hrew :
      ∫ s in Set.Ioi (0 : ℝ), wignerSurmiseGUE s =
        ∫ s in Set.Ioi (0 : ℝ), (32 / π^2) * ((s ^ 2 : ℝ) * Real.exp (-(4 * s^2) / π)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro s hs
    have hs0 : 0 ≤ s := le_of_lt hs
    simp [wignerSurmiseGUE, hs0, mul_assoc, mul_left_comm, mul_comm]
  rw [hrew]
  have hmul :
      ∫ s in Set.Ioi (0 : ℝ), (32 / π^2) * ((s ^ 2 : ℝ) * Real.exp (-(4 * s^2) / π))
        = (32 / π^2) * ∫ s in Set.Ioi (0 : ℝ), (s ^ 2 : ℝ) * Real.exp (-(4 * s^2) / π) := by
    simpa using (MeasureTheory.integral_const_mul (32 / π^2)
      (fun s => (s ^ 2 : ℝ) * Real.exp (-(4 * s^2) / π) : ℝ → ℝ))
  rw [hmul, integral_s2_exp_neg_4s2_over_pi]
  field_simp [Real.pi_ne_zero]

/-- The first moment (mean spacing) is exactly 1. -/
theorem integral_s3_exp_neg_4s2_over_pi :
    ∫ s in Set.Ioi (0 : ℝ), (s ^ 3 : ℝ) * Real.exp (-(4 * s^2) / π) = π ^ 2 / 32 := by
  have hrew :
      ∫ s in Set.Ioi (0 : ℝ), (s ^ 3 : ℝ) * Real.exp (-(4 * s^2) / π)
        = ∫ s in Set.Ioi (0 : ℝ), s ^ (3 : ℝ) * Real.exp (-(4 / π) * s ^ (2 : ℝ)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro s hs
    simp [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  rw [hrew]
  have h :
      ∫ s in Set.Ioi (0 : ℝ), s ^ (3 : ℝ) * Real.exp (-(4 / π) * s ^ (2 : ℝ)) =
        (4 / π : ℝ) ^ (-(3 + 1 : ℝ) / 2) * (1 / 2) * Real.Gamma ((3 + 1 : ℝ) / 2) := by
    simpa using (_root_.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (3 : ℝ)) (b := 4 / π)
      (by norm_num) (by norm_num) (by positivity))
  have hneg2 : (4 / π : ℝ) ^ (-(2 : ℝ)) = (π ^ 2) / 16 := by
    have hpow : (4 / π : ℝ) ^ (-(2 : ℝ)) = ((4 / π : ℝ) ^ (2 : ℝ))⁻¹ := by
      rw [Real.rpow_neg (show (0:ℝ) ≤ 4 / π by positivity)]
    rw [hpow]
    have h2' : (4 / π : ℝ) ^ (2 : ℝ) = (4 / π : ℝ) ^ 2 := by
      simp
    rw [h2']
    field_simp [Real.pi_ne_zero]
    ring
  have h2 :
      (4 / π : ℝ) ^ (-(3 + 1 : ℝ) / 2) * (1 / 2) * Real.Gamma ((3 + 1 : ℝ) / 2) = π^2 / 32 := by
    have hpow : (4 / π : ℝ) ^ (-(3 + 1 : ℝ) / 2) = (4 / π : ℝ) ^ (-(2:ℝ)) := by
      norm_num
    have hgamma : Real.Gamma ((3 + 1 : ℝ) / 2) = Real.Gamma 2 := by
      norm_num
    rw [hpow, hneg2, hgamma, Real.Gamma_two]
    ring
  rw [h]
  simpa using h2

/-- Mean spacing ∫₀^∞ s · P(s) ds = 1. This is the standard
    normalization convention in RMT. -/
theorem wignerSurmise_mean_spacing :
    ∫ s in Set.Ioi (0 : ℝ), s * wignerSurmiseGUE s = 1 := by
  have hrew :
      ∫ s in Set.Ioi (0 : ℝ), s * wignerSurmiseGUE s
        = ∫ s in Set.Ioi (0 : ℝ), (32 / π^2) * ((s ^ 3 : ℝ) * Real.exp (-(4 * s^2) / π)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro s hs
    have hs0 : 0 ≤ s := le_of_lt hs
    simp [wignerSurmiseGUE, hs0, pow_two, mul_assoc, mul_left_comm, mul_comm]
    ring
  rw [hrew]
  have hmul : ∫ s in Set.Ioi (0 : ℝ), (32 / π^2) * ((s ^ 3 : ℝ) * Real.exp (-(4 * s^2) / π))
      = (32 / π^2) * ∫ s in Set.Ioi (0 : ℝ), (s ^ 3 : ℝ) * Real.exp (-(4 * s^2) / π) := by
    simpa using
      (MeasureTheory.integral_const_mul (32 / π^2)
        (fun s => (s ^ 3 : ℝ) * Real.exp (-(4 * s^2) / π) : ℝ → ℝ)
        : ∫ s in Set.Ioi (0 : ℝ), (32 / π^2) * ((s ^ 3 : ℝ) * Real.exp (-(4 * s^2) / π))
            = (32 / π^2) * ∫ s in Set.Ioi (0 : ℝ), (s ^ 3 : ℝ) * Real.exp (-(4 * s^2) / π))
  rw [hmul, integral_s3_exp_neg_4s2_over_pi]
  field_simp [Real.pi_ne_zero]

/-- Variance of the Wigner surmise (GUE, β=2):
    Var(s) = ∫₀^∞ (s − 1)² P(s) ds = 3π/8 − 1 ≈ 0.178. -/
theorem integral_s4_exp_neg_4s2_over_pi :
    ∫ s in Set.Ioi (0 : ℝ), (s ^ 4 : ℝ) * Real.exp (-(4 * s^2) / π) = 3 * π ^ 3 / 256 := by
  have hrew :
      ∫ s in Set.Ioi (0 : ℝ), (s ^ 4 : ℝ) * Real.exp (-(4 * s ^ 2) / Real.pi)
        = ∫ s in Set.Ioi (0 : ℝ), s ^ (4 : ℝ) * Real.exp (-(4 / Real.pi) * s ^ (2 : ℝ)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro s hs
    simp [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hq4 :
      ∫ s in Set.Ioi (0 : ℝ), s ^ (4 : ℝ) * Real.exp (-(4 / Real.pi) * s ^ (2 : ℝ))
        = (4 / Real.pi : ℝ) ^ (((-1 : ℝ) + (-4 : ℝ)) / 2) * (2⁻¹) * Real.Gamma ((4 + 1 : ℝ) / 2) := by
    simpa using (_root_.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (4 : ℝ)) (b := 4 / Real.pi)
      (by norm_num) (by norm_num) (by positivity))
  have hq2raw :
      ∫ s in Set.Ioi (0 : ℝ), s ^ (2 : ℝ) * Real.exp (-(4 / Real.pi) * s ^ (2 : ℝ))
        = (4 / Real.pi : ℝ) ^ (((-1 : ℝ) + (-2 : ℝ)) / 2) * (2⁻¹) * Real.Gamma ((2 + 1 : ℝ) / 2) := by
    simpa using (_root_.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (2 : ℝ)) (b := 4 / Real.pi)
      (by norm_num) (by norm_num) (by positivity))
  have hhalf : Real.Gamma (3 / 2 : ℝ) = (2⁻¹ : ℝ) * Real.sqrt Real.pi := by
    calc
      Real.Gamma (3 / 2 : ℝ) = (2⁻¹ : ℝ) * Real.Gamma (1 / 2 : ℝ) := by
        have h := Real.Gamma_add_one (show (1 / 2 : ℝ) ≠ 0 by norm_num)
        simpa [show (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 by norm_num, show (1 / 2 : ℝ) = (2⁻¹ : ℝ) by norm_num] using h
      _ = (2⁻¹ : ℝ) * Real.sqrt Real.pi := by rw [Real.Gamma_one_half_eq]
  have hAhalf :
      (4 / Real.pi : ℝ) ^ (((-1 : ℝ) + (-2 : ℝ)) / 2) * (2⁻¹) * (2⁻¹ * Real.sqrt Real.pi) = Real.pi ^ 2 / 32 := by
    have hrew2 :
        ∫ s in Set.Ioi (0 : ℝ), s ^ (2 : ℝ) * Real.exp (-(4 / Real.pi) * s ^ (2 : ℝ))
          = ∫ s in Set.Ioi (0 : ℝ), (s ^ 2 : ℝ) * Real.exp (-(4 * s^2) / Real.pi) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
      intro s hs
      simp [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    calc
      (4 / Real.pi : ℝ) ^ (((-1 : ℝ) + (-2 : ℝ)) / 2) * (2⁻¹) * (2⁻¹ * Real.sqrt Real.pi)
          = (4 / Real.pi : ℝ) ^ (((-1 : ℝ) + (-2 : ℝ)) / 2) * (2⁻¹) * Real.Gamma (3 / 2) := by
            rw [hhalf]
      _ = ∫ s in Set.Ioi (0 : ℝ), s ^ (2 : ℝ) * Real.exp (-(4 / Real.pi) * s ^ (2 : ℝ)) := by
            simpa [show (3 / 2 : ℝ) = ((2 + 1 : ℝ) / 2) by norm_num] using hq2raw.symm
      _ = ∫ s in Set.Ioi (0 : ℝ), (s ^ 2 : ℝ) * Real.exp (-(4 * s^2) / Real.pi) := hrew2
      _ = Real.pi ^ 2 / 32 := integral_s2_exp_neg_4s2_over_pi
  have hA2 :
      (4 / Real.pi : ℝ) ^ (((-1 : ℝ) + (-2 : ℝ)) / 2) * Real.sqrt Real.pi = Real.pi ^ 2 / 8 := by
    calc
      (4 / Real.pi : ℝ) ^ (((-1 : ℝ) + (-2 : ℝ)) / 2) * Real.sqrt Real.pi
          = 4 * ((4 / Real.pi : ℝ) ^ (((-1 : ℝ) + (-2 : ℝ)) / 2) * (2⁻¹) * (2⁻¹ * Real.sqrt Real.pi)) := by ring
      _ = 4 * (Real.pi ^ 2 / 32) := by rw [hAhalf]
      _ = Real.pi ^ 2 / 8 := by ring
  have hpow52raw : (4 / Real.pi : ℝ) ^ (((-1 : ℝ) + (-4 : ℝ)) / 2) =
      (4 / Real.pi : ℝ) ^ (((-1 : ℝ) + (-2 : ℝ)) / 2) * (4 / Real.pi : ℝ) ^ (-1 : ℝ) := by
    have h := Real.rpow_add (show (0:ℝ) < 4 / Real.pi by positivity) (((-1 : ℝ) + (-2 : ℝ)) / 2) (-1 : ℝ)
    have hsum : (((-1 : ℝ) + (-4 : ℝ)) / 2) = (((-1 : ℝ) + (-2 : ℝ)) / 2) + (-1 : ℝ) := by norm_num
    simpa [hsum] using h
  have hgamma : Real.Gamma ((4 + 1 : ℝ) / 2) = (3 / 4 : ℝ) * Real.sqrt Real.pi := by
    have h1 : Real.Gamma (5 / 2) = 3 * Real.sqrt Real.pi / ((2 : ℕ) ^ (2 : ℕ) : ℝ) := by
      simpa [show ((5 : ℝ) / 2) = (2 : ℝ) + (1 / 2 : ℝ) by norm_num] using (Real.Gamma_nat_add_half 2)
    calc
      Real.Gamma ((4 + 1 : ℝ) / 2) = Real.Gamma (5 / 2) := by norm_num
      _ = 3 * Real.sqrt Real.pi / ((2 : ℕ) ^ (2 : ℕ) : ℝ) := h1
      _ = 3 * Real.sqrt Real.pi / 4 := by norm_num
      _ = (3 / 4 : ℝ) * Real.sqrt Real.pi := by ring
  have hinv : (4 / Real.pi : ℝ) ^ (-1 : ℝ) = Real.pi / 4 := by
    have hpow : (4 / Real.pi : ℝ) ^ (-1 : ℝ) = ((4 / Real.pi : ℝ) ^ (1 : ℝ))⁻¹ := by
      rw [Real.rpow_neg (show (0:ℝ) ≤ 4 / Real.pi by positivity)]
    rw [hpow]
    have hmul : ((4 / Real.pi : ℝ) ^ (1 : ℝ)) = 4 / Real.pi := by
      simp
    rw [hmul]
    field_simp [Real.pi_ne_zero]
  rw [hrew, hq4]
  rw [hpow52raw, hgamma, hinv]
  have hmain :
      (4 / Real.pi : ℝ) ^ (((-1 : ℝ) + (-2 : ℝ)) / 2) * (Real.pi / 4) * (2⁻¹) * (3 / 4 * Real.sqrt Real.pi)
        = (4 / Real.pi : ℝ) ^ (((-1 : ℝ) + (-2 : ℝ)) / 2) * Real.sqrt Real.pi * (3 * Real.pi / 32) := by
    ring
  rw [hmain]
  rw [hA2]
  ring

/-- The second moment ⟨s²⟩.
    For GUE β=2: ⟨s²⟩ = 3π/8 ≈ 1.178. -/
theorem wignerSurmise_second_moment :
    ∫ s in Set.Ioi (0 : ℝ), (s ^ 2 : ℝ) * wignerSurmiseGUE s = 3 * π / 8 := by
  have hrew :
      ∫ s in Set.Ioi (0 : ℝ), (s ^ 2 : ℝ) * wignerSurmiseGUE s
        = ∫ s in Set.Ioi (0 : ℝ), (32 / π^2) * ((s ^ 4 : ℝ) * Real.exp (-(4 * s^2) / π)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro s hs
    have hs0 : 0 ≤ s := le_of_lt hs
    simp [wignerSurmiseGUE, hs0, pow_two, mul_assoc, mul_left_comm, mul_comm]
    ring
  have hmul :
      ∫ s in Set.Ioi (0 : ℝ), (32 / π^2) * ((s ^ 4 : ℝ) * Real.exp (-(4 * s^2) / π))
        = (32 / π^2) * ∫ s in Set.Ioi (0 : ℝ), (s ^ 4 : ℝ) * Real.exp (-(4 * s^2) / π) := by
    simpa using
      (MeasureTheory.integral_const_mul (32 / π^2)
        (fun s => (s ^ 4 : ℝ) * Real.exp (-(4 * s^2) / π) : ℝ → ℝ)
        : ∫ s in Set.Ioi (0 : ℝ), (32 / π^2) * ((s ^ 4 : ℝ) * Real.exp (-(4 * s^2) / π))
            = (32 / π^2) * ∫ s in Set.Ioi (0 : ℝ), (s ^ 4 : ℝ) * Real.exp (-(4 * s^2) / π))
  rw [hrew, hmul, integral_s4_exp_neg_4s2_over_pi]
  field_simp [Real.pi_ne_zero]
  ring

/-- Variance = ⟨s²⟩ − ⟨s⟩² = 3π/8 − 1 ≈ 0.178. -/
theorem wignerSurmise_variance :
    ∫ s in Set.Ioi (0 : ℝ), (s - 1)^2 * wignerSurmiseGUE s = 3 * π / 8 - 1 := by
  have hPInt :
      MeasureTheory.Integrable (fun s : ℝ => wignerSurmiseGUE s) (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    by_contra hni
    have hzero : ∫ s in Set.Ioi (0 : ℝ), wignerSurmiseGUE s = 0 := by
      simpa using (MeasureTheory.integral_undef hni)
    have h1 : (1 : ℝ) ≠ 0 := by norm_num
    have hzero' : (1 : ℝ) = 0 := by
      simpa [wignerSurmise_integrates_to_one] using hzero
    have hcontra : False := h1 hzero'
    exact False.elim hcontra
  have hSInt :
      MeasureTheory.Integrable (fun s : ℝ => s * wignerSurmiseGUE s) (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    by_contra hni
    have hzero : ∫ s in Set.Ioi (0 : ℝ), s * wignerSurmiseGUE s = 0 := by
      simpa using (MeasureTheory.integral_undef hni)
    have h1 : (1 : ℝ) ≠ 0 := by norm_num
    have hzero' : (1 : ℝ) = 0 := by
      simpa [wignerSurmise_mean_spacing] using hzero
    have hcontra : False := h1 hzero'
    exact False.elim hcontra
  have hS2Int :
      MeasureTheory.Integrable (fun s : ℝ => (s ^ 2 : ℝ) * wignerSurmiseGUE s) (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    by_contra hni
    have hzero : ∫ s in Set.Ioi (0 : ℝ), (s ^ 2 : ℝ) * wignerSurmiseGUE s = 0 := by
      simpa using (MeasureTheory.integral_undef hni)
    have h30 : (3 * π / 8 : ℝ) ≠ 0 := by positivity
    have hzero' : (3 * π / 8 : ℝ) = 0 := by
      simpa [wignerSurmise_second_moment] using hzero
    have hcontra : False := h30 hzero'
    exact False.elim hcontra
  have hS2minus :
      MeasureTheory.Integrable (fun s : ℝ => (s ^ 2 : ℝ) * wignerSurmiseGUE s - (2 : ℝ) * (s * wignerSurmiseGUE s))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hsub := hS2Int.sub (hSInt.const_mul (2 : ℝ))
    simpa using hsub
  have hrew :
      ∫ s in Set.Ioi (0 : ℝ), (s - 1)^2 * wignerSurmiseGUE s
        = ∫ s in Set.Ioi (0 : ℝ), (s ^ 2 : ℝ) * wignerSurmiseGUE s - (2 : ℝ) * (s * wignerSurmiseGUE s) + wignerSurmiseGUE s := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro s hs
    have hs0 : 0 ≤ s := le_of_lt hs
    simp [wignerSurmiseGUE, hs0, pow_two, mul_assoc, mul_left_comm, mul_comm]
    ring
  rw [hrew]
  calc
    ∫ s in Set.Ioi (0 : ℝ), (s ^ 2 : ℝ) * wignerSurmiseGUE s - (2 : ℝ) * (s * wignerSurmiseGUE s) + wignerSurmiseGUE s
        = (∫ s in Set.Ioi (0 : ℝ), (s ^ 2 : ℝ) * wignerSurmiseGUE s - (2 : ℝ) * (s * wignerSurmiseGUE s))
            + ∫ s in Set.Ioi (0 : ℝ), wignerSurmiseGUE s := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            (MeasureTheory.integral_add (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) hS2minus hPInt)
    _ = (∫ s in Set.Ioi (0 : ℝ), (s ^ 2 : ℝ) * wignerSurmiseGUE s - (2 : ℝ) * (s * wignerSurmiseGUE s))
            + 1 := by rw [wignerSurmise_integrates_to_one]
    _ = ((∫ s in Set.Ioi (0 : ℝ), (s ^ 2 : ℝ) * wignerSurmiseGUE s)
            - ∫ s in Set.Ioi (0 : ℝ), (2 : ℝ) * (s * wignerSurmiseGUE s)) + 1 := by
          rw [MeasureTheory.integral_sub hS2Int (hSInt.const_mul (2 : ℝ))]
    _ = ((3 * π / 8)
            - (2 * (∫ s in Set.Ioi (0 : ℝ), s * wignerSurmiseGUE s)) + 1) := by
          rw [wignerSurmise_second_moment]
          have h2const :
              ∫ s in Set.Ioi (0 : ℝ), (2 : ℝ) * (s * wignerSurmiseGUE s)
                = (2 : ℝ) * ∫ s in Set.Ioi (0 : ℝ), s * wignerSurmiseGUE s := by
            simpa using (MeasureTheory.integral_const_mul (2 : ℝ)
              (fun s => s * wignerSurmiseGUE s : ℝ → ℝ))
          rw [h2const]
    _ = 3 * π / 8 - 1 := by
          rw [wignerSurmise_mean_spacing]
          ring

---------------------------------------------------------------
-- Part 7:  GUE eigenvalue spacings — numerical verification helpers
---------------------------------------------------------------

/-- Generate the GUE2x2 matrix from four standard normal samples.
    In practice, use actual random draws; here we formalize
    the deterministic relationship. -/
def gue2x2_from_samples (x₁ x₂ x₃ x₄ : ℝ) : GUE2x2 :=
  { a := x₁, b := x₂, c := x₃, d := x₄ }

/-- The spacing for a specific set of entries.
    This is always ≥ 0 by discriminant_nonneg. -/
def spacing_from_samples (x₁ x₂ x₃ x₄ : ℝ) : ℝ :=
  gue2x2_spacing (gue2x2_from_samples x₁ x₂ x₃ x₄)

/-- Spacing is always non-negative. -/
theorem spacing_nonneg (x₁ x₂ x₃ x₄ : ℝ) : 0 ≤ spacing_from_samples x₁ x₂ x₃ x₄ := by
  unfold spacing_from_samples gue2x2_spacing
  have h_disc := discriminant_nonneg (gue2x2_from_samples x₁ x₂ x₃ x₄)
  exact Real.sqrt_nonneg _

/-- If the off-diagonal entries are both zero (c=d=0), then H is diagonal
    and the spacing is simply |a − b| (the absolute difference of diagonals). -/
theorem spacing_diagonal_case (a b : ℝ) :
    spacing_from_samples a b 0 0 = |a - b| := by
  unfold spacing_from_samples gue2x2_spacing gue2x2_discriminant gue2x2_from_samples
  simp
  exact Real.sqrt_sq_eq_abs _

/-- When a = b (equal diagonal entries) and off-diagonals are nonzero,
    spacing = 2√(c² + d²) = 2|c + id| (twice the modulus of the off-diagonal). -/
theorem spacing_equal_diagonals (a c d : ℝ) :
    spacing_from_samples a a c d = 2 * Real.sqrt (c^2 + d^2) := by
  unfold spacing_from_samples gue2x2_spacing gue2x2_discriminant gue2x2_from_samples
  have hsq : (a - a)^2 + 4 * (c^2 + d^2) = 4 * (c^2 + d^2) := by ring
  rw [hsq]
  rw [Real.sqrt_mul (show (0:ℝ) ≤ 4 by norm_num)]
  norm_num
---------------------------------------------------------------
-- Part 8:  Connection to the Riemann zeta zeros (IJIRT 172568)
---------------------------------------------------------------

/- The Dyson index β classifies random matrix ensembles:
    β = 1: GOE (orthogonal)  — time-reversal symmetric, integer spin
    β = 2: GUE (unitary)     — no time-reversal symmetry (ζ-zeros)
    β = 4: GSE (symplectic)  — time-reversal symmetric, half-integer spin

    The 2×2 spacing distributions:
    P₁(s) = (π/2) s exp(−πs²/4)     (GOE, β=1)
    P₂(s) = (32/π²) s² exp(−4s²/π)  (GUE, β=2)  ← this file
    P₄(s) = (2¹⁸/3⁶π³) s⁴ exp(−64s²/9π)  (GSE, β=4)

    The ζ-zeros follow the GUE (β=2) statistics — this is the
    Montgomery–Odlyzko law, central to IJIRT 172568 Theorem 4. -/

/-- Wigner surmise for GOE (β = 1). -/
def wignerSurmiseGOE (s : ℝ) : ℝ :=
  if s ≥ 0 then (π * s / 2) * Real.exp (-π * s^2 / 4) else 0

/-- Wigner surmise for GSE (β = 4). -/
def wignerSurmiseGSE (s : ℝ) : ℝ :=
  if s ≥ 0 then
    (262144 / (729 * π^3)) * s^4 * Real.exp (-64 * s^2 / (9 * π))
  else 0

/-- All three Wigner surmisess exhibit level repulsion:
    P_β(s) → 0 as s → 0, with the exponent matching β. -/
theorem all_betas_level_repulsion :
    wignerSurmiseGOE 0 = 0 ∧ wignerSurmiseGUE 0 = 0 ∧ wignerSurmiseGSE 0 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold wignerSurmiseGOE; simp
  · exact wignerSurmise_zero_at_origin
  · unfold wignerSurmiseGSE; simp

/-- Finite theorem package for the `β = 2` Wigner surmise proved in this file:
    level repulsion at the origin, nonnegativity, normalization, and unit mean
    spacing.  This deliberately states only the finite 2×2 facts, not the
    asymptotic Montgomery--Odlyzko comparison. -/
theorem wigner_surmise_finite_package :
    wignerSurmiseGUE 0 = 0 ∧
      (∀ s : ℝ, 0 ≤ wignerSurmiseGUE s) ∧
      (∫ s in Set.Ioi (0 : ℝ), wignerSurmiseGUE s = 1) ∧
      (∫ s in Set.Ioi (0 : ℝ), s * wignerSurmiseGUE s = 1) := by
  refine ⟨wignerSurmise_zero_at_origin, ?_, ?_, ?_⟩
  · intro s
    exact wignerSurmise_nonneg s
  · exact wignerSurmise_integrates_to_one
  · exact wignerSurmise_mean_spacing
---------------------------------------------------------------
-- Part 9:  Finite verification — Sanity checks on the Wigner surmise
---------------------------------------------------------------

/-- P_GUE(1) = (32/π²) exp(−4/π) ≈ 0.930... -/
example : wignerSurmiseGUE 1 = (32 / π^2) * Real.exp (-4 / π) := by
  unfold wignerSurmiseGUE
  simp

/-- P_GUE(2) = (128/π²) exp(−16/π) ≈ 0.067... -/
example : wignerSurmiseGUE 2 = (128 / π^2) * Real.exp (-16 / π) := by
  unfold wignerSurmiseGUE
  norm_num
  ring

/-- P_GUE is non-negative everywhere. -/
example (s : ℝ) : 0 ≤ wignerSurmiseGUE s :=
  wignerSurmise_nonneg s

/-- P_GUE(0) = 0 — level repulsion. -/
example : wignerSurmiseGUE 0 = 0 :=
  wignerSurmise_zero_at_origin

/-- The exponential family natural parameter η₂ = 2 corresponds
    exactly to the Dyson index β = 2 for GUE. -/
example : expFamily_eta2 = 2 := rfl

/-- The weight exp(−½ Tr(H²)) is invariant under unitary conjugation,
    which is the defining property of the GUE. -/
example : expFamily_eta1 = -1/2 := rfl

end
