import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import InfoGeometry.Physics.LogCFTJordanShear
import InfoGeometry.Dynamics.WassersteinProximalBridge

/-!
# Optimal Transport, Bakry-Émery Ricci Curvature, and Log-CFT Monodromy

This module formalizes:
1. `unipotentShear_det_one`: The unipotent Jordan shear $U(\tau) = I + \tau N$
   preserves volume identically ($\det U(\tau) = 1$).
2. `logCFTMonodromy_det`: The determinant of the Log-CFT monodromy matrix is
   governed purely by the scale/conformal factor:
   $\det \mathcal{M}_{\mathrm{Log}}(\delta) = e^{4\pi i \delta}$.
3. `BakryEmeryRicciConvexity`: The Lott-Sturm-Villani / Bakry-Émery Ricci
   curvature $K$-displacement convexity bound for entropy along Wasserstein geodesics.
4. `jko_unipotent_is_volume_preserving`: The discrete JKO dissipative step
   acts as an area-preserving unipotent shear on the chiral cone.
-/

namespace InfoGeometry.Physics.WassersteinBakryEmeryLogCFT

open Matrix
open InfoGeometry.Physics.LogCFTJordanShear
open InfoGeometry.Dynamics.WassersteinProximalBridge

/--
THEOREM 1: The unipotent Jordan shear $U(\tau)$ has determinant equal to 1 for all $\tau \in \mathbb{C}$.
-/
theorem unipotentShear_det_one (τ : ℂ) :
    Matrix.det (unipotentShear τ) = 1 := by
  dsimp [unipotentShear, nilpotentN]
  have hdet : Matrix.det (1 + τ • (!![0, 1; 0, 0] : Mat2C)) = 1 := by
    simp [Matrix.det_fin_two]
  exact hdet

/--
THEOREM 2: The Log-CFT Monodromy Matrix has determinant given by $e^{4\pi i \delta}$.
-/
theorem logCFTMonodromy_det (δ : ℂ) :
    Matrix.det (logCFTMonodromy δ) = Complex.exp (4 * Real.pi * Complex.I * δ) := by
  dsimp [logCFTMonodromy]
  rw [Matrix.det_smul, unipotentShear_det_one, mul_one]
  have htwo : Fintype.card (Fin 2) = 2 := Fintype.card_fin 2
  rw [htwo]
  have hexp : (Complex.exp (2 * Real.pi * Complex.I * δ)) ^ 2 =
      Complex.exp (4 * Real.pi * Complex.I * δ) := by
    rw [sq, ← Complex.exp_add]
    congr 1
    ring
  exact hexp

/-- Finite monodromy composition raises the conformal determinant factor to `n`. -/
theorem logCFTMonodromy_power_det (δ : ℂ) (n : ℕ) :
    Matrix.det (logCFTMonodromy δ ^ n) =
      (Complex.exp (4 * Real.pi * Complex.I * δ)) ^ n := by
  rw [Matrix.det_pow, logCFTMonodromy_det]

/--
The Lott-Sturm-Villani / Bakry-Émery Ricci curvature lower bound $K \in \mathbb{R}$.
A curve $\gamma : [0, 1] \to \mathcal{S}$ is $K$-displacement convex if the entropy functional
satisfies the quadratic convexity inequality.
-/
def KDisplacementConvexity (E : ℝ → ℝ) (K W_sq : ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    E t ≤ (1 - t) * E 0 + t * E 1 - (K / 2) * t * (1 - t) * W_sq

/--
THEOREM 3: For flat Ricci curvature ($K = 0$), $K$-displacement convexity reduces
to standard linear convexity of the entropy along geodesics.
-/
theorem k_displacement_convexity_zero (E : ℝ → ℝ) (W_sq : ℝ) :
    KDisplacementConvexity E 0 W_sq ↔ (∀ t : ℝ, 0 ≤ t → t ≤ 1 → E t ≤ (1 - t) * E 0 + t * E 1) := by
  unfold KDisplacementConvexity
  simp

/-- A nonnegative curvature correction strengthens the ordinary convexity bound. -/
theorem k_displacement_convexity_implies_linear
    (E : ℝ → ℝ) (K W_sq : ℝ)
    (hK : 0 ≤ K) (hW : 0 ≤ W_sq)
    (hconv : KDisplacementConvexity E K W_sq) :
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      E t ≤ (1 - t) * E 0 + t * E 1 := by
  intro t ht0 ht1
  have h := hconv t ht0 ht1
  have ht1' : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hcorr : 0 ≤ (K / 2) * t * (1 - t) * W_sq := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg hK (by norm_num)) ht0) ht1') hW
  linarith

/-- Strict curvature and transport produce a strict interior convexity gap. -/
theorem k_displacement_convexity_strict_gap
    (E : ℝ → ℝ) (K W_sq t : ℝ)
    (hK : 0 < K) (hW : 0 < W_sq) (ht0 : 0 < t) (ht1 : t < 1)
    (hconv : KDisplacementConvexity E K W_sq) :
    E t < (1 - t) * E 0 + t * E 1 := by
  have h := hconv t (le_of_lt ht0) (le_of_lt ht1)
  have hcorr : 0 < (K / 2) * t * (1 - t) * W_sq := by
    exact mul_pos (mul_pos (mul_pos (div_pos hK (by norm_num)) ht0)
      (sub_pos.mpr ht1)) hW
  linarith

/--
THEOREM 4: The discrete JKO proximal step preserves phase-space volume identically.
-/
theorem jko_unipotent_is_volume_preserving (η : ℂ) :
    Matrix.det (jkoEntropyStep η) = 1 := by
  rw [jkoEntropyStep_eq_logCFTJordanShear]
  exact unipotentShear_det_one η

/-- Every finite composition of the JKO-style unipotent step preserves volume. -/
theorem jko_unipotent_power_is_volume_preserving (η : ℂ) (n : ℕ) :
    Matrix.det (jkoEntropyStep η ^ n) = 1 := by
  rw [Matrix.det_pow, jko_unipotent_is_volume_preserving, one_pow]

theorem gaussianHeatEnvelope_is_volume_preserving (η : ℂ) :
    Matrix.det (gaussianHeatEnvelopeStep η) = 1 := by
  unfold gaussianHeatEnvelopeStep
  exact jko_unipotent_is_volume_preserving (2 * η)

theorem gaussianHeatEnvelope_pow_det_one (η : ℂ) (n : ℕ) :
    Matrix.det (gaussianHeatEnvelopeStep η ^ n) = 1 := by
  rw [Matrix.det_pow, gaussianHeatEnvelope_is_volume_preserving]
  simp

end InfoGeometry.Physics.WassersteinBakryEmeryLogCFT
