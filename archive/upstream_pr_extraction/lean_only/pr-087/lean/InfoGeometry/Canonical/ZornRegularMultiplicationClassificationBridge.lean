import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import InfoGeometry.Canonical.ZornRealRegularMultiplicationSpectralBridge

/-!
# Zorn Regular Multiplication Classification Bridge

This module establishes the explicit Erlangen classification of Zorn regular
operators into the three canonical geometric regimes based on the sign of the
discriminant $\Delta_X = \operatorname{tr}(X)^2 - 4N(X)$:

1. **Elliptic / Complex Regime ($\Delta_X < 0$):**
   The normalized centered operator
   $$K_X := \frac{2}{\sqrt{-\Delta_X}} \widehat{L}_X$$
   squares to $-I$, defining a genuine real complex structure ($K_X^2 = -I$).

2. **Hyperbolic / Para-Complex Regime ($\Delta_X > 0$):**
   The normalized centered operator
   $$J_X := \frac{2}{\sqrt{\Delta_X}} \widehat{L}_X$$
   squares to $+I$, defining a para-complex product involution ($J_X^2 = I$) and
   inducing complete, orthogonal projection operators $P_\pm = \frac{1}{2}(I \pm J_X)$
   satisfying $P_+ + P_- = I$, $P_+^2 = P_+$, $P_-^2 = P_-$, $P_+ P_- = 0$.

3. **Parabolic / Nilpotent Regime ($\Delta_X = 0$):**
   The centered operator $\widehat{L}_X$ squares to zero:
   $$\widehat{L}_X^2 = 0.$$

Dual theorems hold identically for the right regular operator $\widehat{R}_X$.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornRegularMultiplicationClassificationBridge

open InfoGeometry.Canonical.ZornVectorMatrixExplicit
open InfoGeometry.Canonical.ZornRealRegularMultiplicationSpectralBridge

abbrev Carrier := ZornCoord

/-- Elliptic normalized complex structure for $\Delta_X < 0$ (left regular). -/
def ellipticLeftK (X : Carrier) : Carrier →ₗ[ℝ] Carrier :=
  (2 / Real.sqrt (-discriminant X)) • centeredLeftRegular X

/-- 🏆 THEOREM: Elliptic left regular operator squares to $-I$:
    $K_X^2 = -I$. -/
theorem ellipticLeftK_square (X : Carrier) (h : discriminant X < 0) :
    ellipticLeftK X ∘ₗ ellipticLeftK X = -LinearMap.id := by
  dsimp [ellipticLeftK]
  rw [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
  rw [centeredLeftRegular_square]
  rw [smul_smul]
  have hpos : 0 < -discriminant X := neg_pos.mpr h
  have hsqrt : Real.sqrt (-discriminant X) ^ 2 = -discriminant X :=
    Real.sq_sqrt (le_of_lt hpos)
  have h_scal : (2 / Real.sqrt (-discriminant X)) * (2 / Real.sqrt (-discriminant X)) * (discriminant X / 4) = -1 := by
    calc
      (2 / Real.sqrt (-discriminant X)) * (2 / Real.sqrt (-discriminant X)) * (discriminant X / 4) =
          (4 / (Real.sqrt (-discriminant X) ^ 2)) * (discriminant X / 4) := by ring
      _ = (4 / (-discriminant X)) * (discriminant X / 4) := by rw [hsqrt]
      _ = -1 := by
        have hne : discriminant X ≠ 0 := ne_of_lt h
        field_simp
  rw [h_scal, neg_one_smul]

/-- Hyperbolic normalized involution for $\Delta_X > 0$ (left regular). -/
def hyperbolicLeftJ (X : Carrier) : Carrier →ₗ[ℝ] Carrier :=
  (2 / Real.sqrt (discriminant X)) • centeredLeftRegular X

/-- 🏆 THEOREM: Hyperbolic left regular operator squares to $+I$:
    $J_X^2 = +I$. -/
theorem hyperbolicLeftJ_square (X : Carrier) (h : discriminant X > 0) :
    hyperbolicLeftJ X ∘ₗ hyperbolicLeftJ X = LinearMap.id := by
  dsimp [hyperbolicLeftJ]
  rw [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
  rw [centeredLeftRegular_square]
  rw [smul_smul]
  have hsqrt : Real.sqrt (discriminant X) ^ 2 = discriminant X :=
    Real.sq_sqrt (le_of_lt h)
  have h_scal : (2 / Real.sqrt (discriminant X)) * (2 / Real.sqrt (discriminant X)) * (discriminant X / 4) = 1 := by
    calc
      (2 / Real.sqrt (discriminant X)) * (2 / Real.sqrt (discriminant X)) * (discriminant X / 4) =
          (4 / (Real.sqrt (discriminant X) ^ 2)) * (discriminant X / 4) := by ring
      _ = (4 / discriminant X) * (discriminant X / 4) := by rw [hsqrt]
      _ = 1 := by
        have hne : discriminant X ≠ 0 := ne_of_gt h
        field_simp
  rw [h_scal, one_smul]

/-- 🏆 THEOREM: Parabolic centered left regular operator squares to $0$ for $\Delta_X = 0$:
    $\widehat{L}_X^2 = 0$. -/
theorem parabolicLeft_square (X : Carrier) (h : discriminant X = 0) :
    centeredLeftRegular X ∘ₗ centeredLeftRegular X = 0 := by
  rw [centeredLeftRegular_square, h]
  simp

/-- Elliptic normalized complex structure for $\Delta_X < 0$ (right regular). -/
def ellipticRightK (X : Carrier) : Carrier →ₗ[ℝ] Carrier :=
  (2 / Real.sqrt (-discriminant X)) • centeredRightRegular X

/-- 🏆 THEOREM: Elliptic right regular operator squares to $-I$:
    $K_{R,X}^2 = -I$. -/
theorem ellipticRightK_square (X : Carrier) (h : discriminant X < 0) :
    ellipticRightK X ∘ₗ ellipticRightK X = -LinearMap.id := by
  dsimp [ellipticRightK]
  rw [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
  rw [centeredRightRegular_square]
  rw [smul_smul]
  have hpos : 0 < -discriminant X := neg_pos.mpr h
  have hsqrt : Real.sqrt (-discriminant X) ^ 2 = -discriminant X :=
    Real.sq_sqrt (le_of_lt hpos)
  have h_scal : (2 / Real.sqrt (-discriminant X)) * (2 / Real.sqrt (-discriminant X)) * (discriminant X / 4) = -1 := by
    calc
      (2 / Real.sqrt (-discriminant X)) * (2 / Real.sqrt (-discriminant X)) * (discriminant X / 4) =
          (4 / (Real.sqrt (-discriminant X) ^ 2)) * (discriminant X / 4) := by ring
      _ = (4 / (-discriminant X)) * (discriminant X / 4) := by rw [hsqrt]
      _ = -1 := by
        have hne : discriminant X ≠ 0 := ne_of_lt h
        field_simp
  rw [h_scal, neg_one_smul]

/-- Hyperbolic normalized involution for $\Delta_X > 0$ (right regular). -/
def hyperbolicRightJ (X : Carrier) : Carrier →ₗ[ℝ] Carrier :=
  (2 / Real.sqrt (discriminant X)) • centeredRightRegular X

/-- 🏆 THEOREM: Hyperbolic right regular operator squares to $+I$:
    $J_{R,X}^2 = +I$. -/
theorem hyperbolicRightJ_square (X : Carrier) (h : discriminant X > 0) :
    hyperbolicRightJ X ∘ₗ hyperbolicRightJ X = LinearMap.id := by
  dsimp [hyperbolicRightJ]
  rw [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
  rw [centeredRightRegular_square]
  rw [smul_smul]
  have hsqrt : Real.sqrt (discriminant X) ^ 2 = discriminant X :=
    Real.sq_sqrt (le_of_lt h)
  have h_scal : (2 / Real.sqrt (discriminant X)) * (2 / Real.sqrt (discriminant X)) * (discriminant X / 4) = 1 := by
    calc
      (2 / Real.sqrt (discriminant X)) * (2 / Real.sqrt (discriminant X)) * (discriminant X / 4) =
          (4 / (Real.sqrt (discriminant X) ^ 2)) * (discriminant X / 4) := by ring
      _ = (4 / discriminant X) * (discriminant X / 4) := by rw [hsqrt]
      _ = 1 := by
        have hne : discriminant X ≠ 0 := ne_of_gt h
        field_simp
  rw [h_scal, one_smul]

/-- 🏆 THEOREM: Parabolic centered right regular operator squares to $0$ for $\Delta_X = 0$:
    $\widehat{R}_X^2 = 0$. -/
theorem parabolicRight_square (X : Carrier) (h : discriminant X = 0) :
    centeredRightRegular X ∘ₗ centeredRightRegular X = 0 := by
  rw [centeredRightRegular_square, h]
  simp

/-- Hyperbolic projection operator $P_+ = \frac{1}{2}(I + J_X)$ for $\Delta_X > 0$. -/
def hyperbolicLeftProjectorPlus (X : Carrier) : Carrier →ₗ[ℝ] Carrier :=
  (1 / 2 : ℝ) • (LinearMap.id + hyperbolicLeftJ X)

/-- Hyperbolic projection operator $P_- = \frac{1}{2}(I - J_X)$ for $\Delta_X > 0$. -/
def hyperbolicLeftProjectorMinus (X : Carrier) : Carrier →ₗ[ℝ] Carrier :=
  (1 / 2 : ℝ) • (LinearMap.id - hyperbolicLeftJ X)

/-- 🏆 THEOREM: Completeness of hyperbolic projectors: $P_+ + P_- = I$. -/
theorem hyperbolicLeftProjector_sum (X : Carrier) :
    hyperbolicLeftProjectorPlus X + hyperbolicLeftProjectorMinus X = LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp only [hyperbolicLeftProjectorPlus, hyperbolicLeftProjectorMinus,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.sub_apply]
  rw [← smul_add]
  have : (x + (hyperbolicLeftJ X) x) + (x - (hyperbolicLeftJ X) x) = (2 : ℝ) • x := by
    calc
      (x + (hyperbolicLeftJ X) x) + (x - (hyperbolicLeftJ X) x) =
          (x + x) + ((hyperbolicLeftJ X) x - (hyperbolicLeftJ X) x) := by abel
      _ = (2 : ℝ) • x + 0 := by
        rw [two_smul, sub_self]
      _ = (2 : ℝ) • x := by rw [add_zero]
  rw [this, smul_smul]
  norm_num

/-- 🏆 THEOREM: Idempotency of $P_+$: $P_+^2 = P_+$. -/
theorem hyperbolicLeftProjectorPlus_square (X : Carrier) (h : discriminant X > 0) :
    hyperbolicLeftProjectorPlus X ∘ₗ hyperbolicLeftProjectorPlus X = hyperbolicLeftProjectorPlus X := by
  dsimp [hyperbolicLeftProjectorPlus]
  rw [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
  have h_comp : (LinearMap.id + hyperbolicLeftJ X) ∘ₗ (LinearMap.id + hyperbolicLeftJ X) =
      (2 : ℝ) • (LinearMap.id + hyperbolicLeftJ X) := by
    rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_add]
    rw [LinearMap.id_comp, LinearMap.id_comp, LinearMap.comp_id, hyperbolicLeftJ_square X h]
    have h_re : (LinearMap.id : Carrier →ₗ[ℝ] Carrier) + hyperbolicLeftJ X + (hyperbolicLeftJ X + LinearMap.id) =
        (2 : ℝ) • (LinearMap.id + hyperbolicLeftJ X) := by
      apply LinearMap.ext
      intro x
      simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply]
      have : x + (hyperbolicLeftJ X) x + ((hyperbolicLeftJ X) x + x) = (2 : ℝ) • (x + (hyperbolicLeftJ X) x) := by
        calc
          x + (hyperbolicLeftJ X) x + ((hyperbolicLeftJ X) x + x) =
              (x + x) + ((hyperbolicLeftJ X) x + (hyperbolicLeftJ X) x) := by abel
          _ = (2 : ℝ) • x + (2 : ℝ) • (hyperbolicLeftJ X) x := by rw [two_smul, two_smul]
          _ = (2 : ℝ) • (x + (hyperbolicLeftJ X) x) := by rw [smul_add]
      exact this
    exact h_re
  rw [h_comp, smul_smul]
  norm_num

/-- 🏆 THEOREM: Idempotency of $P_-$: $P_-^2 = P_-$. -/
theorem hyperbolicLeftProjectorMinus_square (X : Carrier) (h : discriminant X > 0) :
    hyperbolicLeftProjectorMinus X ∘ₗ hyperbolicLeftProjectorMinus X = hyperbolicLeftProjectorMinus X := by
  dsimp [hyperbolicLeftProjectorMinus]
  rw [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
  have h_comp : (LinearMap.id - hyperbolicLeftJ X) ∘ₗ (LinearMap.id - hyperbolicLeftJ X) =
      (2 : ℝ) • (LinearMap.id - hyperbolicLeftJ X) := by
    rw [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.comp_sub]
    rw [LinearMap.id_comp, LinearMap.id_comp, LinearMap.comp_id, hyperbolicLeftJ_square X h]
    have h_re : (LinearMap.id : Carrier →ₗ[ℝ] Carrier) - hyperbolicLeftJ X - (hyperbolicLeftJ X - LinearMap.id) =
        (2 : ℝ) • (LinearMap.id - hyperbolicLeftJ X) := by
      apply LinearMap.ext
      intro x
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply]
      have : x - (hyperbolicLeftJ X) x - ((hyperbolicLeftJ X) x - x) = (2 : ℝ) • (x - (hyperbolicLeftJ X) x) := by
        calc
          x - (hyperbolicLeftJ X) x - ((hyperbolicLeftJ X) x - x) =
              (x + x) - ((hyperbolicLeftJ X) x + (hyperbolicLeftJ X) x) := by abel
          _ = (2 : ℝ) • x - (2 : ℝ) • (hyperbolicLeftJ X) x := by rw [two_smul, two_smul]
          _ = (2 : ℝ) • (x - (hyperbolicLeftJ X) x) := by rw [smul_sub]
      exact this
    exact h_re
  rw [h_comp, smul_smul]
  norm_num

/-- 🏆 THEOREM: Orthogonality of $P_+$ and $P_-$: $P_+ \circ P_- = 0$. -/
theorem hyperbolicLeftProjector_orthogonal (X : Carrier) (h : discriminant X > 0) :
    hyperbolicLeftProjectorPlus X ∘ₗ hyperbolicLeftProjectorMinus X = 0 := by
  dsimp [hyperbolicLeftProjectorPlus, hyperbolicLeftProjectorMinus]
  rw [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
  have h_comp : (LinearMap.id + hyperbolicLeftJ X) ∘ₗ (LinearMap.id - hyperbolicLeftJ X) = 0 := by
    rw [LinearMap.add_comp, LinearMap.comp_sub, LinearMap.comp_sub]
    rw [LinearMap.id_comp, LinearMap.id_comp, LinearMap.comp_id, hyperbolicLeftJ_square X h]
    apply LinearMap.ext
    intro x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.zero_apply]
    abel
  rw [h_comp, smul_zero]

end InfoGeometry.Canonical.ZornRegularMultiplicationClassificationBridge
