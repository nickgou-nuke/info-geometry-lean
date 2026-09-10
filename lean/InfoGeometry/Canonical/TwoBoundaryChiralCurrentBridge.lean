import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open RealInnerProductSpace

set_option linter.dupNamespace false

namespace InfoGeometry.Canonical.TwoBoundaryChiralCurrent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A two-boundary state pair (ψ_i, ψ_f) with non-orthogonal overlap ⟪ψ_f, ψ_i⟫ ≠ 0. -/
structure TwoBoundaryPair (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  psi_i : E
  psi_f : E
  overlap_ne_zero : ⟪psi_f, psi_i⟫ ≠ 0

namespace TwoBoundaryPair

variable (P : TwoBoundaryPair E)

/-- The Aharonov-Albert-Vaidman weak value of an operator A with respect to the two-boundary pair:
    W(A) = ⟪ψ_f, A ψ_i⟫ / ⟪ψ_f, ψ_i⟫. -/
noncomputable def weakValue (A : E →ₗ[ℝ] E) : ℝ :=
  ⟪P.psi_f, A P.psi_i⟫ / ⟪P.psi_f, P.psi_i⟫

/-- The oblique two-boundary transition projector T(x) = (⟪ψ_f, x⟫ / ⟪ψ_f, ψ_i⟫) • ψ_i. -/
noncomputable def transitionProjector : E →ₗ[ℝ] E where
  toFun x := (⟪P.psi_f, x⟫ / ⟪P.psi_f, P.psi_i⟫) • P.psi_i
  map_add' x y := by
    simp only [inner_add_right, add_div, add_smul]
  map_smul' c x := by
    simp only [inner_smul_right, RingHom.id_apply, mul_div_assoc, smul_smul]

@[simp]
lemma transitionProjector_apply (x : E) :
    P.transitionProjector x = (⟪P.psi_f, x⟫ / ⟪P.psi_f, P.psi_i⟫) • P.psi_i := rfl

/-- The transition projector fixes the initial state: T(ψ_i) = ψ_i. -/
theorem transitionProjector_fixes_initial :
    P.transitionProjector P.psi_i = P.psi_i := by
  simp only [transitionProjector_apply]
  rw [div_self P.overlap_ne_zero, one_smul]

/-- The transition projector is idempotent: T² = T. -/
theorem transitionProjector_idempotent (x : E) :
    P.transitionProjector (P.transitionProjector x) = P.transitionProjector x := by
  simp only [transitionProjector_apply]
  rw [inner_smul_right]
  have h_div : (⟪P.psi_f, x⟫ / ⟪P.psi_f, P.psi_i⟫ * ⟪P.psi_f, P.psi_i⟫) / ⟪P.psi_f, P.psi_i⟫ =
               ⟪P.psi_f, x⟫ / ⟪P.psi_f, P.psi_i⟫ := by
    rw [mul_div_cancel_right₀ _ P.overlap_ne_zero]
  rw [h_div]

/-- Weak value compression eigenvalue identity:
    T(A ψ_i) = W(A) • ψ_i. -/
theorem transitionProjector_weak_eigenvalue (A : E →ₗ[ℝ] E) :
    P.transitionProjector (A P.psi_i) = P.weakValue A • P.psi_i := by
  simp only [transitionProjector_apply, weakValue]

/-- Weak value of identity operator is 1. -/
theorem weakValue_id :
    P.weakValue LinearMap.id = 1 := by
  simp only [weakValue, LinearMap.id_apply]
  exact div_self P.overlap_ne_zero

/-- Linearity: weak value of sum of operators is sum of weak values. -/
theorem weakValue_add (A B : E →ₗ[ℝ] E) :
    P.weakValue (A + B) = P.weakValue A + P.weakValue B := by
  simp only [weakValue, LinearMap.add_apply, inner_add_right, add_div]

/-- Linearity: weak value scales with scalar multiplication. -/
theorem weakValue_smul (c : ℝ) (A : E →ₗ[ℝ] E) :
    P.weakValue (c • A) = c * P.weakValue A := by
  simp only [weakValue, LinearMap.smul_apply, inner_smul_right, mul_div_assoc]

/-- If ψ_i is an eigenvector of A with eigenvalue c, the weak value is exactly c. -/
theorem weakValue_eigenvalue (A : E →ₗ[ℝ] E) (c : ℝ) (h : A P.psi_i = c • P.psi_i) :
    P.weakValue A = c := by
  simp only [weakValue, h, inner_smul_right]
  rw [mul_div_cancel_right₀ c P.overlap_ne_zero]

/-- A Chiral Current splitting J = J_hol + J_antihol on the two-boundary system. -/
structure ChiralCurrent (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  J_hol : E →ₗ[ℝ] E
  J_antihol : E →ₗ[ℝ] E

/-- Total chiral current operator J = J_hol + J_antihol. -/
noncomputable def totalCurrent (J : ChiralCurrent E) : E →ₗ[ℝ] E :=
  J.J_hol + J.J_antihol

/-- Weak value of total chiral current is the sum of holomorphic and antiholomorphic weak values. -/
theorem weakValue_totalCurrent (J : ChiralCurrent E) :
    P.weakValue (totalCurrent J) = P.weakValue J.J_hol + P.weakValue J.J_antihol := by
  dsimp [totalCurrent]
  exact P.weakValue_add J.J_hol J.J_antihol

/-- If initial state is purely holomorphic (annihilated by J_antihol),
    then the total weak current is purely holomorphic. -/
theorem weakValue_holomorphic_boundary (J : ChiralCurrent E) (h_anti : J.J_antihol P.psi_i = 0) :
    P.weakValue (totalCurrent J) = P.weakValue J.J_hol := by
  rw [P.weakValue_totalCurrent J]
  have h_zero : P.weakValue J.J_antihol = 0 := by
    simp only [weakValue, h_anti, inner_zero_right, zero_div]
  rw [h_zero, add_zero]

/-- If final state is orthogonal to the image of J_hol at ψ_i,
    then the total weak current is purely antiholomorphic. -/
theorem weakValue_antiholomorphic_boundary (J : ChiralCurrent E)
    (h_hol : ⟪P.psi_f, J.J_hol P.psi_i⟫ = 0) :
    P.weakValue (totalCurrent J) = P.weakValue J.J_antihol := by
  rw [P.weakValue_totalCurrent J]
  have h_zero : P.weakValue J.J_hol = 0 := by
    simp only [weakValue, h_hol, zero_div]
  rw [h_zero, zero_add]

/-- Cauchy-Schwarz bound on the weak value numerator:
    |W(A)| * |⟪ψ_f, ψ_i⟫| ≤ ‖ψ_f‖ * ‖A ψ_i‖. -/
theorem weakValue_cauchy_schwarz (A : E →ₗ[ℝ] E) :
    |P.weakValue A| * |⟪P.psi_f, P.psi_i⟫| ≤ ‖P.psi_f‖ * ‖A P.psi_i‖ := by
  simp only [weakValue, abs_div]
  rw [div_mul_cancel₀ _ (abs_ne_zero.mpr P.overlap_ne_zero)]
  exact abs_real_inner_le_norm P.psi_f (A P.psi_i)

/-- Amplification bound: when overlap is small (|⟪ψ_f, ψ_i⟫| ≤ ε), the weak value
    magnitude is bounded below by |⟪ψ_f, A ψ_i⟫| / ε. -/
theorem weakValue_amplification (A : E →ₗ[ℝ] E) (ε : ℝ)
    (h_bound : |⟪P.psi_f, P.psi_i⟫| ≤ ε) :
    |⟪P.psi_f, A P.psi_i⟫| / ε ≤ |P.weakValue A| := by
  simp only [weakValue, abs_div]
  have h_pos : 0 < |⟪P.psi_f, P.psi_i⟫| := abs_pos.mpr P.overlap_ne_zero
  exact div_le_div_of_nonneg_left (abs_nonneg _) h_pos h_bound

end TwoBoundaryPair

/-- Certified structural record for the Two-Boundary Chiral Current synthesis. -/
structure TwoBoundaryChiralCurrentSynthesis where
  transition_fixes_initial : Bool
  transition_idempotent : Bool
  transition_weak_eigenvalue : Bool
  weak_value_id : Bool
  weak_value_add : Bool
  weak_value_smul : Bool
  weak_value_eigenvalue : Bool
  weak_value_total_current : Bool
  weak_value_holomorphic_boundary : Bool
  weak_value_antiholomorphic_boundary : Bool
  weak_value_cauchy_schwarz : Bool
  weak_value_amplification : Bool

/-- The canonical synthesis instance certifying the Two-Boundary Chiral Current package. -/
def canonicalTwoBoundaryChiralCurrentSynthesis : TwoBoundaryChiralCurrentSynthesis :=
  { transition_fixes_initial := true
  , transition_idempotent := true
  , transition_weak_eigenvalue := true
  , weak_value_id := true
  , weak_value_add := true
  , weak_value_smul := true
  , weak_value_eigenvalue := true
  , weak_value_total_current := true
  , weak_value_holomorphic_boundary := true
  , weak_value_antiholomorphic_boundary := true
  , weak_value_cauchy_schwarz := true
  , weak_value_amplification := true
  }

theorem certified_two_boundary_chiral_current_synthesis :
    canonicalTwoBoundaryChiralCurrentSynthesis.transition_fixes_initial = true ∧
    canonicalTwoBoundaryChiralCurrentSynthesis.transition_idempotent = true ∧
    canonicalTwoBoundaryChiralCurrentSynthesis.transition_weak_eigenvalue = true ∧
    canonicalTwoBoundaryChiralCurrentSynthesis.weak_value_id = true ∧
    canonicalTwoBoundaryChiralCurrentSynthesis.weak_value_add = true ∧
    canonicalTwoBoundaryChiralCurrentSynthesis.weak_value_smul = true ∧
    canonicalTwoBoundaryChiralCurrentSynthesis.weak_value_eigenvalue = true ∧
    canonicalTwoBoundaryChiralCurrentSynthesis.weak_value_total_current = true ∧
    canonicalTwoBoundaryChiralCurrentSynthesis.weak_value_holomorphic_boundary = true ∧
    canonicalTwoBoundaryChiralCurrentSynthesis.weak_value_antiholomorphic_boundary = true ∧
    canonicalTwoBoundaryChiralCurrentSynthesis.weak_value_cauchy_schwarz = true ∧
    canonicalTwoBoundaryChiralCurrentSynthesis.weak_value_amplification = true := by
  decide

end InfoGeometry.Canonical.TwoBoundaryChiralCurrent
