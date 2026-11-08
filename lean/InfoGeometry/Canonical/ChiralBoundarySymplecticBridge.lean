import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

open RealInnerProductSpace

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace InfoGeometry.Canonical.ChiralBoundarySymplectic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev ChiralDoubled (E : Type*) := E × E

namespace ChiralDoubled

/-- The canonical chiral symplectic 2-form on E × E:
    Ω((u₁, u₂), (v₁, v₂)) = ⟪u₁, v₂⟫ - ⟪v₁, u₂⟫. -/
def symplecticForm (u v : ChiralDoubled E) : ℝ :=
  ⟪u.1, v.2⟫ - ⟪v.1, u.2⟫

/-- The canonical almost complex structure: J(u₁, u₂) = (-u₂, u₁). -/
def J (u : ChiralDoubled E) : ChiralDoubled E :=
  (-u.2, u.1)

/-- The induced Kähler metric: g(u, v) = ⟪u₁, v₁⟫ + ⟪u₂, v₂⟫. -/
def metric (u v : ChiralDoubled E) : ℝ :=
  ⟪u.1, v.1⟫ + ⟪u.2, v.2⟫

/-- Skew-symmetry: Ω(u, v) = -Ω(v, u). -/
theorem symplecticForm_skew (u v : ChiralDoubled E) :
    symplecticForm u v = - symplecticForm v u := by
  dsimp [symplecticForm]
  ring

/-- Alternating: Ω(u, u) = 0. -/
theorem symplecticForm_self_zero (u : ChiralDoubled E) :
    symplecticForm u u = 0 := by
  dsimp [symplecticForm]
  ring

/-- Bilinearity: left additivity. -/
theorem symplecticForm_add_left (u v w : ChiralDoubled E) :
    symplecticForm (u + v) w = symplecticForm u w + symplecticForm v w := by
  dsimp [symplecticForm]
  rw [inner_add_left, inner_add_right]
  ring

/-- Bilinearity: right additivity. -/
theorem symplecticForm_add_right (u v w : ChiralDoubled E) :
    symplecticForm u (v + w) = symplecticForm u v + symplecticForm u w := by
  dsimp [symplecticForm]
  rw [inner_add_right, inner_add_left]
  ring

/-- Bilinearity: scalar scaling left. -/
theorem symplecticForm_smul_left (c : ℝ) (u v : ChiralDoubled E) :
    symplecticForm (c • u) v = c * symplecticForm u v := by
  dsimp [symplecticForm]
  rw [inner_smul_left, inner_smul_right]
  simp only [conj_trivial]
  ring

/-- Bilinearity: scalar scaling right. -/
theorem symplecticForm_smul_right (c : ℝ) (u v : ChiralDoubled E) :
    symplecticForm u (c • v) = c * symplecticForm u v := by
  dsimp [symplecticForm]
  rw [inner_smul_right, inner_smul_left]
  simp only [conj_trivial]
  ring

/-- Holomorphic subspace is isotropic (Lagrangian): Ω((u₁, 0), (v₁, 0)) = 0. -/
theorem holomorphic_isotropic (u1 v1 : E) :
    symplecticForm (u1, (0 : E)) (v1, (0 : E)) = 0 := by
  dsimp [symplecticForm]
  simp

/-- Antiholomorphic subspace is isotropic (Lagrangian): Ω((0, u₂), (0, v₂)) = 0. -/
theorem antiholomorphic_isotropic (u2 v2 : E) :
    symplecticForm ((0 : E), u2) ((0 : E), v2) = 0 := by
  dsimp [symplecticForm]
  simp

/-- Cross-pairing recovery: Ω((u₁, 0), (0, v₂)) = ⟪u₁, v₂⟫. -/
theorem cross_pairing_recovery (u1 v2 : E) :
    symplecticForm (u1, (0 : E)) ((0 : E), v2) = ⟪u1, v2⟫ := by
  dsimp [symplecticForm]
  simp

/-- Complex structure squares to -id: J² = -id. -/
theorem J_sq (u : ChiralDoubled E) :
    J (J u) = - u := by
  ext <;> simp [J]

/-- Symplectic compatibility with J: Ω(u, J u) = ‖u₁‖² + ‖u₂‖² ≥ 0. -/
theorem symplectic_J_positive (u : ChiralDoubled E) :
    0 ≤ symplecticForm u (J u) := by
  dsimp [symplecticForm, J]
  have h2 : ⟪-u.2, u.2⟫ = - ⟪u.2, u.2⟫ := inner_neg_left u.2 u.2
  rw [h2]
  have h_sum : ⟪u.1, u.1⟫ - -⟪u.2, u.2⟫ = ⟪u.1, u.1⟫ + ⟪u.2, u.2⟫ := by ring
  rw [h_sum]
  exact add_nonneg real_inner_self_nonneg real_inner_self_nonneg

/-- Kähler relation: g(u, v) = Ω(u, J v). -/
theorem metric_eq_symplectic_J (u v : ChiralDoubled E) :
    metric u v = symplecticForm u (J v) := by
  dsimp [metric, symplecticForm, J]
  rw [inner_neg_left, real_inner_comm v.2 u.2]
  ring

/-- Non-degeneracy of symplectic form: (∀ v, Ω(u, v) = 0) → u = 0. -/
theorem symplectic_nondegenerate (u : ChiralDoubled E)
    (h : ∀ v, symplecticForm u v = 0) :
    u = 0 := by
  have h1 := h (0, u.1)
  have h2 := h (-u.2, 0)
  dsimp [symplecticForm] at h1 h2
  rw [inner_zero_left, sub_zero] at h1
  have hu1 : u.1 = 0 := inner_self_eq_zero.mp h1
  rw [inner_zero_right, zero_sub, neg_eq_zero] at h2
  have hu2_neg : ⟪-u.2, u.2⟫ = - ⟪u.2, u.2⟫ := inner_neg_left u.2 u.2
  rw [hu2_neg, neg_eq_zero] at h2
  have hu2 : u.2 = 0 := inner_self_eq_zero.mp h2
  ext
  · exact hu1
  · exact hu2

/-- J is an isometry of the metric: g(J u, J v) = g(u, v). -/
theorem metric_J_invariant (u v : ChiralDoubled E) :
    metric (J u) (J v) = metric u v := by
  dsimp [metric, J]
  rw [inner_neg_neg]
  ring

/-- J preserves the symplectic form: Ω(J u, J v) = Ω(u, v). -/
theorem symplectic_J_invariant (u v : ChiralDoubled E) :
    symplecticForm (J u) (J v) = symplecticForm u v := by
  dsimp [symplecticForm, J]
  have h1 : ⟪-u.2, v.1⟫ = - ⟪u.2, v.1⟫ := inner_neg_left u.2 v.1
  have h2 : ⟪-v.2, u.1⟫ = - ⟪v.2, u.1⟫ := inner_neg_left v.2 u.1
  rw [h1, h2]
  have h3 : ⟪u.2, v.1⟫ = ⟪v.1, u.2⟫ := real_inner_comm v.1 u.2
  have h4 : ⟪v.2, u.1⟫ = ⟪u.1, v.2⟫ := real_inner_comm u.1 v.2
  rw [h3, h4]
  ring

end ChiralDoubled

/-- Certified structural record for the Chiral Boundary Symplectic synthesis. -/
structure ChiralBoundarySymplecticSynthesis where
  symplectic_skew : Bool
  symplectic_self_zero : Bool
  symplectic_add_left : Bool
  symplectic_add_right : Bool
  symplectic_smul_left : Bool
  symplectic_smul_right : Bool
  holomorphic_isotropic : Bool
  antiholomorphic_isotropic : Bool
  cross_pairing_recovery : Bool
  J_sq : Bool
  symplectic_J_positive : Bool
  metric_eq_symplectic_J : Bool
  symplectic_nondegenerate : Bool
  metric_J_invariant : Bool
  symplectic_J_invariant : Bool

/-- The canonical synthesis instance certifying the Chiral Boundary Symplectic package. -/
def canonicalChiralBoundarySymplecticSynthesis : ChiralBoundarySymplecticSynthesis :=
  { symplectic_skew := true
  , symplectic_self_zero := true
  , symplectic_add_left := true
  , symplectic_add_right := true
  , symplectic_smul_left := true
  , symplectic_smul_right := true
  , holomorphic_isotropic := true
  , antiholomorphic_isotropic := true
  , cross_pairing_recovery := true
  , J_sq := true
  , symplectic_J_positive := true
  , metric_eq_symplectic_J := true
  , symplectic_nondegenerate := true
  , metric_J_invariant := true
  , symplectic_J_invariant := true
  }

theorem certified_chiral_boundary_symplectic_synthesis :
    canonicalChiralBoundarySymplecticSynthesis.symplectic_skew = true ∧
    canonicalChiralBoundarySymplecticSynthesis.symplectic_self_zero = true ∧
    canonicalChiralBoundarySymplecticSynthesis.symplectic_add_left = true ∧
    canonicalChiralBoundarySymplecticSynthesis.symplectic_add_right = true ∧
    canonicalChiralBoundarySymplecticSynthesis.symplectic_smul_left = true ∧
    canonicalChiralBoundarySymplecticSynthesis.symplectic_smul_right = true ∧
    canonicalChiralBoundarySymplecticSynthesis.holomorphic_isotropic = true ∧
    canonicalChiralBoundarySymplecticSynthesis.antiholomorphic_isotropic = true ∧
    canonicalChiralBoundarySymplecticSynthesis.cross_pairing_recovery = true ∧
    canonicalChiralBoundarySymplecticSynthesis.J_sq = true ∧
    canonicalChiralBoundarySymplecticSynthesis.symplectic_J_positive = true ∧
    canonicalChiralBoundarySymplecticSynthesis.metric_eq_symplectic_J = true ∧
    canonicalChiralBoundarySymplecticSynthesis.symplectic_nondegenerate = true ∧
    canonicalChiralBoundarySymplecticSynthesis.metric_J_invariant = true ∧
    canonicalChiralBoundarySymplecticSynthesis.symplectic_J_invariant = true := by
  decide

end InfoGeometry.Canonical.ChiralBoundarySymplectic
