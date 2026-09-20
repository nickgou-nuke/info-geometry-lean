import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace DetectorGeometry.TwoPointQuantumFieldGenesis

/-! A small, proof-producing core for the algebraic content of the proposed
causal chain. Physical interpretation is represented by definitions and
assumptions; the theorems below prove only their stated mathematical content. -/

section FieldCorrelation

noncomputable def radiationKernel (r₁ r₂ : ℝ) : ℝ := 1 / (r₁ ^ 2 * r₂ ^ 2)

def volumeJacobian (r₁ r₂ : ℝ) : ℝ := r₁ ^ 2 * r₂ ^ 2

theorem jacobian_mul_radiationKernel (r₁ r₂ : ℝ) (hr₁ : r₁ ≠ 0)
    (hr₂ : r₂ ≠ 0) : volumeJacobian r₁ r₂ * radiationKernel r₁ r₂ = 1 := by
  simp only [volumeJacobian, radiationKernel]
  exact mul_one_div_cancel (mul_ne_zero (pow_ne_zero 2 hr₁) (pow_ne_zero 2 hr₂))

end FieldCorrelation

section MonopoleProjection

def coincidence (ε₁ ε₂ W : ℝ) : ℝ := ε₁ * ε₂ * W

def single (ε₁ : ℝ) : ℝ := ε₁

def coupledEfficiency (k ε₁ : ℝ) : ℝ := k * ε₁

theorem coincidence_eq_quadratic (ε₁ k W : ℝ) :
    coincidence ε₁ (coupledEfficiency k ε₁) W = (k * W) * (single ε₁) ^ 2 := by
  simp [coincidence, coupledEfficiency, single]
  ring

end MonopoleProjection

section SquareRootRankInversion

noncomputable def naturalCoordinate (N : ℝ) : ℝ := Real.sqrt N

noncomputable def canonicalSlope (k W : ℝ) : ℝ := (Real.sqrt (k * W))⁻¹

theorem square_root_linearizes (ε₁ k W : ℝ) (hε₁ : 0 ≤ ε₁) (hk : 0 < k)
    (hW : 0 < W) :
    single ε₁ = canonicalSlope k W *
      naturalCoordinate (coincidence ε₁ (coupledEfficiency k ε₁) W) := by
  have hkw : 0 < k * W := mul_pos hk hW
  have hkw₀ : 0 ≤ k * W := le_of_lt hkw
  have hquad : coincidence ε₁ (coupledEfficiency k ε₁) W = (k * W) * ε₁ ^ 2 :=
    coincidence_eq_quadratic ε₁ k W
  simp only [single, canonicalSlope, naturalCoordinate, hquad]
  rw [Real.sqrt_mul hkw₀, Real.sqrt_sq hε₁]
  have hs : Real.sqrt (k * W) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hkw)
  field_simp

theorem zero_intercept (k W m b : ℝ) (h_ray : ∀ X : ℝ, 0 ≤ X →
    m * X + b = canonicalSlope k W * X) : b = 0 := by
  have h0 := h_ray 0 (le_refl 0)
  simpa using h0

end SquareRootRankInversion

section CausalPoset

inductive Archetype
  | qedCorrelation
  | separability
  | monopoleProjection
  | rankHierarchy
  | squareRootInversion
  deriving DecidableEq, Repr

def causalRank : Archetype → Nat
  | .qedCorrelation => 175
  | .separability => 176
  | .monopoleProjection => 177
  | .rankHierarchy => 178
  | .squareRootInversion => 179

def causallyPrecedes (a b : Archetype) : Prop := causalRank a ≤ causalRank b

theorem causal_refl (a : Archetype) : causallyPrecedes a a := le_rfl

theorem causal_trans {a b c : Archetype} :
    causallyPrecedes a b → causallyPrecedes b c → causallyPrecedes a c := by
  exact Nat.le_trans

theorem canonical_chain :
    causallyPrecedes .qedCorrelation .separability ∧
    causallyPrecedes .separability .monopoleProjection ∧
    causallyPrecedes .monopoleProjection .rankHierarchy ∧
    causallyPrecedes .rankHierarchy .squareRootInversion := by
  norm_num [causallyPrecedes, causalRank]

theorem causal_antisymm {a b : Archetype} :
    causallyPrecedes a b → causallyPrecedes b a → a = b := by
  intro hab hba
  cases a <;> cases b <;> simp [causallyPrecedes, causalRank] at hab hba ⊢

end CausalPoset

end DetectorGeometry.TwoPointQuantumFieldGenesis
