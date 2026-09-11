import Mathlib.Data.Real.Basic
import Mathlib.Tactic

noncomputable section

/-!
# Section 5.83: Tensor Factorization of Glauber Correlators & Copula Detector Invariance

This module formalizes:
1. Product integration structure `ProductIntegration α` over single and product detector volumes:
   - Scalar homogeneity of 2-integral (`integrate2_smul`).
   - Fubini theorem for tensor product functions: `I₂(f ⊗ g) = I₁(f) * I₁(g)`.
2. Two-point Glauber cross-field `G_cross = κ * (G₁ ⊗ G₂)`.
3. Coincidence count rate `Q = A₀ * I₂(G_cross)`.
4. Theorem 1 (Fubini Tensor Factorization of 2-Point Glauber Correlator):
   `Q = (κ / A₀) * L₁ * L₂`.
5. Copula cross-ratio `copulaCrossRatio = (L₁ * L₂) / Q`.
6. Master Theorem 2 (Detector Volume Annihilation):
   `copulaCrossRatio = A₀ / κ`. Spatial integrals over volume V,
   detector sensitivity η(x), and geometric dilution factors cancel out identically.
7. Master Theorem 3 (Exact Absolute Nuclear Activity Recovery):
   `κ * copulaCrossRatio = A₀`.
8. Master Theorem 4 (Strict Volume and Distance Scale Invariance):
   Rescaling detector response `g ↦ α • g` with `α > 0` leaves the cross-ratio invariant.
9. Master Theorem 5 (Asymmetric Channel Invariance):
   Even under independent variations in the two detector channels (`α₁ ≠ α₂`),
   the copula cross-ratio remains strictly unchanged.
10. Master Certified Synthesis:
    `certified_glauber_tensor_copula_synthesis`.
-/

namespace InfoGeometry.Probability.GlauberTensorCopula

/-- Product integration structure representing integration over single (1D/3D)
    and product (2D/6D) spaces V and V × V. -/
structure ProductIntegration (α : Type*) where
  integrate1 : (α → ℝ) → ℝ
  integrate2 : (α → α → ℝ) → ℝ
  integrate2_smul : ∀ (c : ℝ) (F : α → α → ℝ), integrate2 (fun x y => c * F x y) = c * integrate2 F
  fubini : ∀ (f g : α → ℝ), integrate2 (fun x y => f x * g y) = integrate1 f * integrate1 g

/-- Quantum Glauber detector system over configuration space `α`. -/
structure QuantumGlauberSystem (α : Type*) where
  PI : ProductIntegration α
  /-- True absolute nuclear activity A₀ > 0 -/
  A0 : ℝ
  /-- Cascade coincidence branching factor κ > 0 -/
  kappa : ℝ
  hA0_pos : 0 < A0
  hkappa_pos : 0 < kappa
  /-- Single-point detector response densities η₁(x) G₁(x) and η₂(x) G₂(x) -/
  G1 : α → ℝ
  G2 : α → ℝ
  /-- Strict positivity of single-point volume integrals over the detector -/
  hI1_pos : 0 < PI.integrate1 G1
  hI2_pos : 0 < PI.integrate1 G2

namespace QuantumGlauberSystem

variable {α : Type*} (sys : QuantumGlauberSystem α)

/-!
### 1. Field Forms and Single/Double Counts
-/

/-- Single count rate (1-correlator) for line 1:
    L₁ = A₀ * ∫_V η₁(x) G₁(x) d³x. -/
def L1 : ℝ :=
  sys.A0 * sys.PI.integrate1 sys.G1

/-- Single count rate (1-correlator) for line 2:
    L₂ = A₀ * ∫_V η₂(x) G₂(x) d³x. -/
def L2 : ℝ :=
  sys.A0 * sys.PI.integrate1 sys.G2

/-- Two-point Glauber cross-field in the far wave zone:
    G⁽²⁾(x₁, x₂) = κ * (η₁(x₁) G₁(x₁)) * (η₂(x₂) G₂(x₂)). -/
def G_cross : α → α → ℝ :=
  fun x y => sys.kappa * (sys.G1 x * sys.G2 y)

/-- Coincidence intensity (2-correlator) integrated over V × V:
    Q = A₀ * ∫_{V×V} G⁽²⁾(x₁, x₂) d³x₁ d³x₂. -/
def Q : ℝ :=
  sys.A0 * sys.PI.integrate2 sys.G_cross

/-!
### 2. Fubini Tensor Factorization
-/

/-- **Theorem 1 (Fubini Tensor Factorization of 2-Point Glauber Correlator)**:
    The 2-point volume integral factors exactly into the product of two 1-point integrals:
    Q = (κ / A₀) * L₁ * L₂. -/
theorem Q_fubini_factorization :
    sys.Q = (sys.kappa / sys.A0) * (sys.L1 * sys.L2) := by
  have h_G : sys.G_cross = fun x y => sys.kappa * (sys.G1 x * sys.G2 y) := rfl
  dsimp [Q, L1, L2]
  rw [h_G]
  rw [sys.PI.integrate2_smul]
  rw [sys.PI.fubini sys.G1 sys.G2]
  have hA0_ne : sys.A0 ≠ 0 := ne_of_gt sys.hA0_pos
  field_simp [hA0_ne]

theorem L1_pos : 0 < sys.L1 :=
  mul_pos sys.hA0_pos sys.hI1_pos

theorem L2_pos : 0 < sys.L2 :=
  mul_pos sys.hA0_pos sys.hI2_pos

theorem Q_pos : 0 < sys.Q := by
  rw [sys.Q_fubini_factorization]
  have h_frac : 0 < sys.kappa / sys.A0 := div_pos sys.hkappa_pos sys.hA0_pos
  have h_prod : 0 < sys.L1 * sys.L2 := mul_pos sys.L1_pos sys.L2_pos
  exact mul_pos h_frac h_prod

/-!
### 3. Copula Cross-Ratio and Exact Volume Annihilation
-/

/-- Copula invariant cross-ratio:
    R = (L₁ * L₂) / Q. -/
def copulaCrossRatio : ℝ :=
  (sys.L1 * sys.L2) / sys.Q

/-- **Master Theorem 2 (Exact Detector Volume Annihilation)**:
    In the copula cross-ratio, volume integrals over V, detector efficiencies η(x),
    and distance dilution factors cancel out identically:
    (L₁ * L₂) / Q = A₀ / κ. -/
theorem copula_cross_ratio_invariant :
    sys.copulaCrossRatio = sys.A0 / sys.kappa := by
  dsimp only [copulaCrossRatio]
  rw [sys.Q_fubini_factorization]
  have hA0_ne : sys.A0 ≠ 0 := ne_of_gt sys.hA0_pos
  have hkappa_ne : sys.kappa ≠ 0 := ne_of_gt sys.hkappa_pos
  have hL1_ne : sys.L1 ≠ 0 := ne_of_gt sys.L1_pos
  have hL2_ne : sys.L2 ≠ 0 := ne_of_gt sys.L2_pos
  have hprod_ne : sys.L1 * sys.L2 ≠ 0 := mul_ne_zero hL1_ne hL2_ne
  field_simp [hA0_ne, hkappa_ne, hprod_ne]

/-- **Master Theorem 3 (Nuclear Activity Recovery)**:
    Multiplying the copula cross-ratio by the cascade branching factor κ
    strictly recovers the true absolute nuclear source activity A₀. -/
theorem recovered_activity_exact :
    sys.kappa * sys.copulaCrossRatio = sys.A0 := by
  rw [sys.copula_cross_ratio_invariant]
  have hkappa_ne : sys.kappa ≠ 0 := ne_of_gt sys.hkappa_pos
  exact mul_div_cancel₀ sys.A0 hkappa_ne

/-!
### 4. Geometric and Channel Scale Invariances
-/

/-- Rescaled system under change of crystal volume V or distance d
    with global positive scaling factor α > 0: G₁ ↦ α • G₁, G₂ ↦ α • G₂. -/
def rescaleGeometry (alpha : ℝ) (halpha_pos : 0 < alpha)
    (h_int_smul : ∀ (c : ℝ) (f : α → ℝ), sys.PI.integrate1 (fun x => c * f x) = c * sys.PI.integrate1 f) :
    QuantumGlauberSystem α where
  PI := sys.PI
  A0 := sys.A0
  kappa := sys.kappa
  hA0_pos := sys.hA0_pos
  hkappa_pos := sys.hkappa_pos
  G1 := fun x => alpha * sys.G1 x
  G2 := fun x => alpha * sys.G2 x
  hI1_pos := by
    rw [h_int_smul]
    exact mul_pos halpha_pos sys.hI1_pos
  hI2_pos := by
    rw [h_int_smul]
    exact mul_pos halpha_pos sys.hI2_pos

/-- **Master Theorem 4 (Strict Volume and Distance Scale Invariance)**:
    Scaling volume or distance dilution by any factor α > 0
    leaves the copula cross-ratio strictly invariant. -/
theorem cross_ratio_scale_invariance (alpha : ℝ) (halpha_pos : 0 < alpha)
    (h_int_smul : ∀ (c : ℝ) (f : α → ℝ), sys.PI.integrate1 (fun x => c * f x) = c * sys.PI.integrate1 f) :
    (sys.rescaleGeometry alpha halpha_pos h_int_smul).copulaCrossRatio = sys.copulaCrossRatio := by
  rw [copula_cross_ratio_invariant, copula_cross_ratio_invariant]
  rfl

/-- Asymmetric scaling of the two channels with independent factors α₁ > 0, α₂ > 0. -/
def rescaleAsymmetric (alpha1 alpha2 : ℝ) (h1_pos : 0 < alpha1) (h2_pos : 0 < alpha2)
    (h_int_smul : ∀ (c : ℝ) (f : α → ℝ), sys.PI.integrate1 (fun x => c * f x) = c * sys.PI.integrate1 f) :
    QuantumGlauberSystem α where
  PI := sys.PI
  A0 := sys.A0
  kappa := sys.kappa
  hA0_pos := sys.hA0_pos
  hkappa_pos := sys.hkappa_pos
  G1 := fun x => alpha1 * sys.G1 x
  G2 := fun x => alpha2 * sys.G2 x
  hI1_pos := by
    rw [h_int_smul]
    exact mul_pos h1_pos sys.hI1_pos
  hI2_pos := by
    rw [h_int_smul]
    exact mul_pos h2_pos sys.hI2_pos

/-- **Master Theorem 5 (Asymmetric Channel Invariance)**:
    Even under completely independent variations in the two detector channels (α₁ ≠ α₂),
    the copula cross-ratio remains strictly unchanged. -/
theorem asymmetric_scale_invariance (alpha1 alpha2 : ℝ) (h1_pos : 0 < alpha1) (h2_pos : 0 < alpha2)
    (h_int_smul : ∀ (c : ℝ) (f : α → ℝ), sys.PI.integrate1 (fun x => c * f x) = c * sys.PI.integrate1 f) :
    (sys.rescaleAsymmetric alpha1 alpha2 h1_pos h2_pos h_int_smul).copulaCrossRatio =
    sys.copulaCrossRatio := by
  rw [copula_cross_ratio_invariant, copula_cross_ratio_invariant]
  rfl

/-- **Certified Master Synthesis (Section 5.83)**:
    Unified conjunction of Fubini factorization, copula detector self-annihilation,
    nuclear activity recovery, and symmetric / asymmetric scale invariance. -/
theorem certified_glauber_tensor_copula_synthesis
    (alpha : ℝ) (halpha_pos : 0 < alpha)
    (alpha1 alpha2 : ℝ) (h1_pos : 0 < alpha1) (h2_pos : 0 < alpha2)
    (h_int_smul : ∀ (c : ℝ) (f : α → ℝ), sys.PI.integrate1 (fun x => c * f x) = c * sys.PI.integrate1 f) :
    (sys.Q = (sys.kappa / sys.A0) * (sys.L1 * sys.L2)) ∧
    (sys.copulaCrossRatio = sys.A0 / sys.kappa) ∧
    (sys.kappa * sys.copulaCrossRatio = sys.A0) ∧
    ((sys.rescaleGeometry alpha halpha_pos h_int_smul).copulaCrossRatio = sys.copulaCrossRatio) ∧
    ((sys.rescaleAsymmetric alpha1 alpha2 h1_pos h2_pos h_int_smul).copulaCrossRatio = sys.copulaCrossRatio) := by
  refine ⟨sys.Q_fubini_factorization,
          sys.copula_cross_ratio_invariant,
          sys.recovered_activity_exact,
          sys.cross_ratio_scale_invariance alpha halpha_pos h_int_smul,
          sys.asymmetric_scale_invariance alpha1 alpha2 h1_pos h2_pos h_int_smul⟩

end QuantumGlauberSystem

end InfoGeometry.Probability.GlauberTensorCopula
