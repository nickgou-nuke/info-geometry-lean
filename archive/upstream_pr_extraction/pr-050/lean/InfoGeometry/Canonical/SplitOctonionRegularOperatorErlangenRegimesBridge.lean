import Mathlib.Tactic
import InfoGeometry.Canonical.ZornRealRegularMultiplicationSpectralBridge
import InfoGeometry.Lie.SplitOctonionLeftRightAssociatorCommutantBridge

/-!
# Erlangen Tri-Regime Classification for Split-Octonion Regular Operators

This owner classifies the regular operators `L_X` and `R_X` into the three real
Erlangen operator regimes according to the discriminant `Δ_X = tr(X)² - 4N(X)`:

1. **Elliptic / Complex Regime (`Δ_X < 0`):**
   Normalized operator `K_X = (2 / √(-Δ_X)) • (L_X - tr(X)/2 I)` squares to `-I`.
2. **Hyperbolic / Para-Complex Regime (`Δ_X > 0`):**
   Normalized operator `J_X = (2 / √(Δ_X)) • (L_X - tr(X)/2 I)` squares to `+I`,
   generating orthogonal idempotent projectors `P_± = (1/2)(I ± J_X)`.
3. **Parabolic / Nilpotent Regime (`Δ_X = 0`):**
   Centered operator `(L_X - tr(X)/2 I)` squares to `0`.

The same threefold classification holds symmetrically for right regular operators `R_X`.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionRegularOperatorErlangenRegimesBridge

open InfoGeometry.Canonical.ZornRealRegularMultiplicationSpectralBridge
open InfoGeometry.Canonical.ZornVectorMatrixExplicit

abbrev Carrier := ZornCoord

theorem smul_comp_smul (c d : ℝ) (T S : Carrier →ₗ[ℝ] Carrier) :
    (c • T) ∘ₗ (d • S) = (c * d) • (T ∘ₗ S) := by
  rw [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]

-- =========================================================================
-- 1. Elliptic / Complex Regime (discriminant < 0)
-- =========================================================================

def complexStructureL (X : Carrier) : Carrier →ₗ[ℝ] Carrier :=
  (2 / Real.sqrt (-discriminant X)) • centeredLeftRegular X

def complexStructureR (X : Carrier) : Carrier →ₗ[ℝ] Carrier :=
  (2 / Real.sqrt (-discriminant X)) • centeredRightRegular X

/-- 🏆 THEOREM: In the elliptic regime, the normalized left operator squares to -I. -/
theorem complexStructureL_sq (X : Carrier) (h : discriminant X < 0) :
    (complexStructureL X) ∘ₗ (complexStructureL X) = -LinearMap.id := by
  dsimp [complexStructureL]
  rw [smul_comp_smul, centeredLeftRegular_square, smul_smul]
  have hpos : 0 < -discriminant X := neg_pos.mpr h
  have hsqrt : (Real.sqrt (-discriminant X)) ^ 2 = -discriminant X :=
    Real.sq_sqrt (le_of_lt hpos)
  have hne : -discriminant X ≠ 0 := ne_of_gt hpos
  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  have hcalc : (2 / Real.sqrt (-discriminant X)) * (2 / Real.sqrt (-discriminant X)) * (discriminant X / 4) = -1 := by
    have h2 : (2 / Real.sqrt (-discriminant X)) * (2 / Real.sqrt (-discriminant X)) = 4 / (Real.sqrt (-discriminant X) ^ 2) := by
      ring
    rw [h2, hsqrt]
    have hneg : discriminant X = -(-discriminant X) := (neg_neg (discriminant X)).symm
    nth_rw 2 [hneg]
    have : (4 / (-discriminant X)) * (-(-discriminant X) / 4) = - ((4 / (-discriminant X)) * ((-discriminant X) / 4)) := by ring
    rw [this]
    have hone : (4 / (-discriminant X)) * ((-discriminant X) / 4) = 1 := by
      rw [div_mul_div_comm, mul_comm (-discriminant X), div_self (mul_ne_zero h4 hne)]
    rw [hone]
  rw [hcalc, neg_one_smul]

/-- 🏆 THEOREM: In the elliptic regime, the normalized right operator squares to -I. -/
theorem complexStructureR_sq (X : Carrier) (h : discriminant X < 0) :
    (complexStructureR X) ∘ₗ (complexStructureR X) = -LinearMap.id := by
  dsimp [complexStructureR]
  rw [smul_comp_smul, centeredRightRegular_square, smul_smul]
  have hpos : 0 < -discriminant X := neg_pos.mpr h
  have hsqrt : (Real.sqrt (-discriminant X)) ^ 2 = -discriminant X :=
    Real.sq_sqrt (le_of_lt hpos)
  have hne : -discriminant X ≠ 0 := ne_of_gt hpos
  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  have hcalc : (2 / Real.sqrt (-discriminant X)) * (2 / Real.sqrt (-discriminant X)) * (discriminant X / 4) = -1 := by
    have h2 : (2 / Real.sqrt (-discriminant X)) * (2 / Real.sqrt (-discriminant X)) = 4 / (Real.sqrt (-discriminant X) ^ 2) := by
      ring
    rw [h2, hsqrt]
    have hneg : discriminant X = -(-discriminant X) := (neg_neg (discriminant X)).symm
    nth_rw 2 [hneg]
    have : (4 / (-discriminant X)) * (-(-discriminant X) / 4) = - ((4 / (-discriminant X)) * ((-discriminant X) / 4)) := by ring
    rw [this]
    have hone : (4 / (-discriminant X)) * ((-discriminant X) / 4) = 1 := by
      rw [div_mul_div_comm, mul_comm (-discriminant X), div_self (mul_ne_zero h4 hne)]
    rw [hone]
  rw [hcalc, neg_one_smul]

-- =========================================================================
-- 2. Hyperbolic / Para-Complex Regime (discriminant > 0)
-- =========================================================================

def paraComplexInvolutionL (X : Carrier) : Carrier →ₗ[ℝ] Carrier :=
  (2 / Real.sqrt (discriminant X)) • centeredLeftRegular X

def paraComplexInvolutionR (X : Carrier) : Carrier →ₗ[ℝ] Carrier :=
  (2 / Real.sqrt (discriminant X)) • centeredRightRegular X

/-- 🏆 THEOREM: In the hyperbolic regime, the normalized left operator squares to +I. -/
theorem paraComplexInvolutionL_sq (X : Carrier) (h : discriminant X > 0) :
    (paraComplexInvolutionL X) ∘ₗ (paraComplexInvolutionL X) = LinearMap.id := by
  dsimp [paraComplexInvolutionL]
  rw [smul_comp_smul, centeredLeftRegular_square, smul_smul]
  have hsqrt : (Real.sqrt (discriminant X)) ^ 2 = discriminant X :=
    Real.sq_sqrt (le_of_lt h)
  have hne : discriminant X ≠ 0 := ne_of_gt h
  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  have hcalc : (2 / Real.sqrt (discriminant X)) * (2 / Real.sqrt (discriminant X)) * (discriminant X / 4) = 1 := by
    have h2 : (2 / Real.sqrt (discriminant X)) * (2 / Real.sqrt (discriminant X)) = 4 / (Real.sqrt (discriminant X) ^ 2) := by
      ring
    rw [h2, hsqrt, div_mul_div_comm, mul_comm (discriminant X), div_self (mul_ne_zero h4 hne)]
  rw [hcalc, one_smul]

/-- 🏆 THEOREM: In the hyperbolic regime, the normalized right operator squares to +I. -/
theorem paraComplexInvolutionR_sq (X : Carrier) (h : discriminant X > 0) :
    (paraComplexInvolutionR X) ∘ₗ (paraComplexInvolutionR X) = LinearMap.id := by
  dsimp [paraComplexInvolutionR]
  rw [smul_comp_smul, centeredRightRegular_square, smul_smul]
  have hsqrt : (Real.sqrt (discriminant X)) ^ 2 = discriminant X :=
    Real.sq_sqrt (le_of_lt h)
  have hne : discriminant X ≠ 0 := ne_of_gt h
  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  have hcalc : (2 / Real.sqrt (discriminant X)) * (2 / Real.sqrt (discriminant X)) * (discriminant X / 4) = 1 := by
    have h2 : (2 / Real.sqrt (discriminant X)) * (2 / Real.sqrt (discriminant X)) = 4 / (Real.sqrt (discriminant X) ^ 2) := by
      ring
    rw [h2, hsqrt, div_mul_div_comm, mul_comm (discriminant X), div_self (mul_ne_zero h4 hne)]
  rw [hcalc, one_smul]

-- Left Hyperbolic Projectors
def projPlusL (X : Carrier) : Carrier →ₗ[ℝ] Carrier :=
  (1 / 2 : ℝ) • (LinearMap.id + paraComplexInvolutionL X)

def projMinusL (X : Carrier) : Carrier →ₗ[ℝ] Carrier :=
  (1 / 2 : ℝ) • (LinearMap.id - paraComplexInvolutionL X)

theorem projPlusL_sq (X : Carrier) (h : discriminant X > 0) :
    (projPlusL X) ∘ₗ (projPlusL X) = projPlusL X := by
  dsimp [projPlusL]
  rw [smul_comp_smul]
  have h1 : (LinearMap.id + paraComplexInvolutionL X) ∘ₗ (LinearMap.id + paraComplexInvolutionL X) =
      (2 : ℝ) • (LinearMap.id + paraComplexInvolutionL X) := by
    rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_add]
    simp only [LinearMap.id_comp, LinearMap.comp_id]
    rw [paraComplexInvolutionL_sq X h]
    calc
      LinearMap.id + paraComplexInvolutionL X + (paraComplexInvolutionL X + LinearMap.id) =
          (LinearMap.id + LinearMap.id) + (paraComplexInvolutionL X + paraComplexInvolutionL X) := by abel
      _ = (2 : ℝ) • LinearMap.id + (2 : ℝ) • paraComplexInvolutionL X := by
        rw [two_smul, two_smul]
      _ = (2 : ℝ) • (LinearMap.id + paraComplexInvolutionL X) := by rw [smul_add]
  rw [h1, smul_smul]
  have : (1 / 2 : ℝ) * (1 / 2 : ℝ) * 2 = 1 / 2 := by ring
  rw [this]

theorem projMinusL_sq (X : Carrier) (h : discriminant X > 0) :
    (projMinusL X) ∘ₗ (projMinusL X) = projMinusL X := by
  dsimp [projMinusL]
  rw [smul_comp_smul]
  have h1 : (LinearMap.id - paraComplexInvolutionL X) ∘ₗ (LinearMap.id - paraComplexInvolutionL X) =
      (2 : ℝ) • (LinearMap.id - paraComplexInvolutionL X) := by
    rw [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.comp_sub]
    simp only [LinearMap.id_comp, LinearMap.comp_id]
    rw [paraComplexInvolutionL_sq X h]
    calc
      LinearMap.id - paraComplexInvolutionL X - (paraComplexInvolutionL X - LinearMap.id) =
          (LinearMap.id + LinearMap.id) - (paraComplexInvolutionL X + paraComplexInvolutionL X) := by abel
      _ = (2 : ℝ) • LinearMap.id - (2 : ℝ) • paraComplexInvolutionL X := by
        rw [two_smul, two_smul]
      _ = (2 : ℝ) • (LinearMap.id - paraComplexInvolutionL X) := by rw [smul_sub]
  rw [h1, smul_smul]
  have : (1 / 2 : ℝ) * (1 / 2 : ℝ) * 2 = 1 / 2 := by ring
  rw [this]

theorem proj_orthogonalL (X : Carrier) (h : discriminant X > 0) :
    (projPlusL X) ∘ₗ (projMinusL X) = 0 := by
  dsimp [projPlusL, projMinusL]
  rw [smul_comp_smul]
  have h1 : (LinearMap.id + paraComplexInvolutionL X) ∘ₗ (LinearMap.id - paraComplexInvolutionL X) = 0 := by
    rw [LinearMap.add_comp, LinearMap.comp_sub, LinearMap.comp_sub]
    simp only [LinearMap.id_comp, LinearMap.comp_id]
    rw [paraComplexInvolutionL_sq X h]
    abel
  rw [h1, smul_zero]

theorem proj_sumL (X : Carrier) :
    projPlusL X + projMinusL X = LinearMap.id := by
  dsimp [projPlusL, projMinusL]
  calc
    (1 / 2 : ℝ) • (LinearMap.id + paraComplexInvolutionL X) +
        (1 / 2 : ℝ) • (LinearMap.id - paraComplexInvolutionL X) =
        (1 / 2 : ℝ) • ((LinearMap.id + paraComplexInvolutionL X) + (LinearMap.id - paraComplexInvolutionL X)) := by
      rw [← smul_add]
    _ = (1 / 2 : ℝ) • ((2 : ℝ) • LinearMap.id) := by
      have : (LinearMap.id + paraComplexInvolutionL X) + (LinearMap.id - paraComplexInvolutionL X) =
          (2 : ℝ) • LinearMap.id := by
        calc
          (LinearMap.id + paraComplexInvolutionL X) + (LinearMap.id - paraComplexInvolutionL X) =
              LinearMap.id + LinearMap.id := by abel
          _ = (2 : ℝ) • LinearMap.id := by rw [two_smul]
      rw [this]
    _ = LinearMap.id := by
      rw [smul_smul]
      have : (1 / 2 : ℝ) * 2 = 1 := by ring
      rw [this, one_smul]

-- Right Hyperbolic Projectors
def projPlusR (X : Carrier) : Carrier →ₗ[ℝ] Carrier :=
  (1 / 2 : ℝ) • (LinearMap.id + paraComplexInvolutionR X)

def projMinusR (X : Carrier) : Carrier →ₗ[ℝ] Carrier :=
  (1 / 2 : ℝ) • (LinearMap.id - paraComplexInvolutionR X)

theorem projPlusR_sq (X : Carrier) (h : discriminant X > 0) :
    (projPlusR X) ∘ₗ (projPlusR X) = projPlusR X := by
  dsimp [projPlusR]
  rw [smul_comp_smul]
  have h1 : (LinearMap.id + paraComplexInvolutionR X) ∘ₗ (LinearMap.id + paraComplexInvolutionR X) =
      (2 : ℝ) • (LinearMap.id + paraComplexInvolutionR X) := by
    rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_add]
    simp only [LinearMap.id_comp, LinearMap.comp_id]
    rw [paraComplexInvolutionR_sq X h]
    calc
      LinearMap.id + paraComplexInvolutionR X + (paraComplexInvolutionR X + LinearMap.id) =
          (LinearMap.id + LinearMap.id) + (paraComplexInvolutionR X + paraComplexInvolutionR X) := by abel
      _ = (2 : ℝ) • LinearMap.id + (2 : ℝ) • paraComplexInvolutionR X := by
        rw [two_smul, two_smul]
      _ = (2 : ℝ) • (LinearMap.id + paraComplexInvolutionR X) := by rw [smul_add]
  rw [h1, smul_smul]
  have : (1 / 2 : ℝ) * (1 / 2 : ℝ) * 2 = 1 / 2 := by ring
  rw [this]

theorem projMinusR_sq (X : Carrier) (h : discriminant X > 0) :
    (projMinusR X) ∘ₗ (projMinusR X) = projMinusR X := by
  dsimp [projMinusR]
  rw [smul_comp_smul]
  have h1 : (LinearMap.id - paraComplexInvolutionR X) ∘ₗ (LinearMap.id - paraComplexInvolutionR X) =
      (2 : ℝ) • (LinearMap.id - paraComplexInvolutionR X) := by
    rw [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.comp_sub]
    simp only [LinearMap.id_comp, LinearMap.comp_id]
    rw [paraComplexInvolutionR_sq X h]
    calc
      LinearMap.id - paraComplexInvolutionR X - (paraComplexInvolutionR X - LinearMap.id) =
          (LinearMap.id + LinearMap.id) - (paraComplexInvolutionR X + paraComplexInvolutionR X) := by abel
      _ = (2 : ℝ) • LinearMap.id - (2 : ℝ) • paraComplexInvolutionR X := by
        rw [two_smul, two_smul]
      _ = (2 : ℝ) • (LinearMap.id - paraComplexInvolutionR X) := by rw [smul_sub]
  rw [h1, smul_smul]
  have : (1 / 2 : ℝ) * (1 / 2 : ℝ) * 2 = 1 / 2 := by ring
  rw [this]

theorem proj_orthogonalR (X : Carrier) (h : discriminant X > 0) :
    (projPlusR X) ∘ₗ (projMinusR X) = 0 := by
  dsimp [projPlusR, projMinusR]
  rw [smul_comp_smul]
  have h1 : (LinearMap.id + paraComplexInvolutionR X) ∘ₗ (LinearMap.id - paraComplexInvolutionR X) = 0 := by
    rw [LinearMap.add_comp, LinearMap.comp_sub, LinearMap.comp_sub]
    simp only [LinearMap.id_comp, LinearMap.comp_id]
    rw [paraComplexInvolutionR_sq X h]
    abel
  rw [h1, smul_zero]

theorem proj_sumR (X : Carrier) :
    projPlusR X + projMinusR X = LinearMap.id := by
  dsimp [projPlusR, projMinusR]
  calc
    (1 / 2 : ℝ) • (LinearMap.id + paraComplexInvolutionR X) +
        (1 / 2 : ℝ) • (LinearMap.id - paraComplexInvolutionR X) =
        (1 / 2 : ℝ) • ((LinearMap.id + paraComplexInvolutionR X) + (LinearMap.id - paraComplexInvolutionR X)) := by
      rw [← smul_add]
    _ = (1 / 2 : ℝ) • ((2 : ℝ) • LinearMap.id) := by
      have : (LinearMap.id + paraComplexInvolutionR X) + (LinearMap.id - paraComplexInvolutionR X) =
          (2 : ℝ) • LinearMap.id := by
        calc
          (LinearMap.id + paraComplexInvolutionR X) + (LinearMap.id - paraComplexInvolutionR X) =
              LinearMap.id + LinearMap.id := by abel
          _ = (2 : ℝ) • LinearMap.id := by rw [two_smul]
      rw [this]
    _ = LinearMap.id := by
      rw [smul_smul]
      have : (1 / 2 : ℝ) * 2 = 1 := by ring
      rw [this, one_smul]

-- =========================================================================
-- 3. Parabolic / Nilpotent Regime (discriminant = 0)
-- =========================================================================

/-- 🏆 THEOREM: In the parabolic regime, the centered left operator is nilpotent of order 2. -/
theorem nilpotentL_sq (X : Carrier) (h : discriminant X = 0) :
    (centeredLeftRegular X) ∘ₗ (centeredLeftRegular X) = 0 := by
  rw [centeredLeftRegular_square, h]
  simp

/-- 🏆 THEOREM: In the parabolic regime, the centered right operator is nilpotent of order 2. -/
theorem nilpotentR_sq (X : Carrier) (h : discriminant X = 0) :
    (centeredRightRegular X) ∘ₗ (centeredRightRegular X) = 0 := by
  rw [centeredRightRegular_square, h]
  simp

-- =========================================================================
-- 4. Trace-Zero Norm-Sign Classification
-- =========================================================================

theorem trace_zero_discriminant (X : Carrier) (htr : zornTrace X = 0) :
    discriminant X = -4 * zornNorm X := by
  dsimp [discriminant]
  rw [htr]
  ring

theorem trace_zero_norm_pos_implies_disc_neg (X : Carrier) (htr : zornTrace X = 0) (hn : zornNorm X > 0) :
    discriminant X < 0 := by
  rw [trace_zero_discriminant X htr]
  nlinarith

theorem trace_zero_norm_neg_implies_disc_pos (X : Carrier) (htr : zornTrace X = 0) (hn : zornNorm X < 0) :
    discriminant X > 0 := by
  rw [trace_zero_discriminant X htr]
  nlinarith

theorem trace_zero_norm_zero_implies_disc_zero (X : Carrier) (htr : zornTrace X = 0) (hn : zornNorm X = 0) :
    discriminant X = 0 := by
  rw [trace_zero_discriminant X htr, hn]
  ring

end InfoGeometry.Canonical.SplitOctonionRegularOperatorErlangenRegimesBridge
