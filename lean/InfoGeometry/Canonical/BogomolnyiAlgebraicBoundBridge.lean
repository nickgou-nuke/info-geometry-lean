import Mathlib.Algebra.Module.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section

namespace InfoGeometry.Canonical.BogomolnyiAlgebraicBoundBridge

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Structure**: Hodge Two-Form Inner Product & Involution Data Package. -/
structure HodgeTwoFormData (E : Type*) [AddCommGroup E] [Module ℝ E] where
  inner : E → E → ℝ
  star : Module.End ℝ E
  inner_add_left : ∀ x y z, inner (x + y) z = inner x z + inner y z
  inner_add_right : ∀ x y z, inner x (y + z) = inner x y + inner x z
  inner_smul_left : ∀ (r : ℝ) x y, inner (r • x) y = r * inner x y
  inner_smul_right : ∀ (r : ℝ) x y, inner x (r • y) = r * inner x y
  symmetric : ∀ x y, inner x y = inner y x
  positive : ∀ x, 0 ≤ inner x x
  star_sq : star.comp star = LinearMap.id
  star_isometry : ∀ x y, inner (star x) (star y) = inner x y
  star_selfAdjoint : ∀ x y, inner (star x) y = inner x (star y)

/-- **Theorem**: Left Additive Distributivity for Subtraction. -/
theorem inner_sub_left (D : HodgeTwoFormData E) (x y z : E) :
    D.inner (x - y) z = D.inner x z - D.inner y z := by
  rw [sub_eq_add_neg, D.inner_add_left, ← neg_one_smul ℝ y, D.inner_smul_left, neg_one_mul, sub_eq_add_neg]

/-- **Theorem**: Right Additive Distributivity for Subtraction. -/
theorem inner_sub_right (D : HodgeTwoFormData E) (x y z : E) :
    D.inner x (y - z) = D.inner x y - D.inner x z := by
  rw [sub_eq_add_neg, D.inner_add_right, ← neg_one_smul ℝ z, D.inner_smul_right, neg_one_mul, sub_eq_add_neg]

/-- **Definition**: Yang-Mills Energy / Action Scalar Functional S(F) = ⟨F, F⟩. -/
def yangMillsEnergy (D : HodgeTwoFormData E) (F : E) : ℝ :=
  D.inner F F

/-- **Definition**: Topological Instanton Pairing Functional K(F) = ⟨F, ★ F⟩. -/
def topologicalPairing (D : HodgeTwoFormData E) (F : E) : ℝ :=
  D.inner F (D.star F)

/-- **Theorem**: Fundamental Self-Dual Quadratic Expansion ⟨F - ★ F, F - ★ F⟩ = 2 (S(F) - K(F)). -/
theorem norm_sub_star_sq (D : HodgeTwoFormData E) (F : E) :
    D.inner (F - D.star F) (F - D.star F) = 2 * (yangMillsEnergy D F - topologicalPairing D F) := by
  dsimp [yangMillsEnergy, topologicalPairing]
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  have h_star_self : D.inner (D.star F) F = D.inner F (D.star F) := D.star_selfAdjoint F F
  have h_star_iso : D.inner (D.star F) (D.star F) = D.inner F F := D.star_isometry F F
  rw [h_star_self, h_star_iso]
  ring

/-- **Theorem**: Fundamental Anti-Self-Dual Quadratic Expansion ⟨F + ★ F, F + ★ F⟩ = 2 (S(F) + K(F)). -/
theorem norm_add_star_sq (D : HodgeTwoFormData E) (F : E) :
    D.inner (F + D.star F) (F + D.star F) = 2 * (yangMillsEnergy D F + topologicalPairing D F) := by
  dsimp [yangMillsEnergy, topologicalPairing]
  rw [D.inner_add_left, D.inner_add_right, D.inner_add_right]
  have h_star_self : D.inner (D.star F) F = D.inner F (D.star F) := D.star_selfAdjoint F F
  have h_star_iso : D.inner (D.star F) (D.star F) = D.inner F F := D.star_isometry F F
  rw [h_star_self, h_star_iso]
  ring

/-- **Theorem**: Upper Bound K(F) ≤ S(F) for Topological Instanton Pairing. -/
theorem topologicalPairing_le_energy (D : HodgeTwoFormData E) (F : E) :
    topologicalPairing D F ≤ yangMillsEnergy D F := by
  have h_pos := D.positive (F - D.star F)
  have h_eq := norm_sub_star_sq D F
  linarith

/-- **Theorem**: Lower Bound -K(F) ≤ S(F) for Topological Instanton Pairing. -/
theorem neg_topologicalPairing_le_energy (D : HodgeTwoFormData E) (F : E) :
    -topologicalPairing D F ≤ yangMillsEnergy D F := by
  have h_pos := D.positive (F + D.star F)
  have h_eq := norm_add_star_sq D F
  linarith

/-- **Theorem**: Algebraic Bogomolny Bound |K(F)| ≤ S(F) for Two-Form Energy & Topological Instanton Pairing. -/
theorem bogomolnyi_bound (D : HodgeTwoFormData E) (F : E) :
    |topologicalPairing D F| ≤ yangMillsEnergy D F := by
  rw [abs_le]
  constructor
  · have h_neg := neg_topologicalPairing_le_energy D F
    linarith
  · exact topologicalPairing_le_energy D F

/-- **Theorem**: Energy Minimum S(F) = K(F) if and only if Self-Dual ★ F = F. -/
theorem energy_eq_topologicalPairing_iff_selfDual
    (D : HodgeTwoFormData E)
    (h_def : ∀ x, D.inner x x = 0 → x = 0)
    (F : E) :
    yangMillsEnergy D F = topologicalPairing D F ↔ D.star F = F := by
  constructor
  · intro h
    have h_norm : D.inner (F - D.star F) (F - D.star F) = 0 := by
      rw [norm_sub_star_sq, h, sub_self, mul_zero]
    have h_zero : F - D.star F = 0 := h_def (F - D.star F) h_norm
    exact eq_of_sub_eq_zero h_zero |>.symm
  · intro h
    dsimp [yangMillsEnergy, topologicalPairing]
    rw [h]

/-- **Theorem**: Energy Minimum S(F) = -K(F) if and only if Anti-Self-Dual ★ F = -F. -/
theorem energy_eq_neg_topologicalPairing_iff_antiSelfDual
    (D : HodgeTwoFormData E)
    (h_def : ∀ x, D.inner x x = 0 → x = 0)
    (F : E) :
    yangMillsEnergy D F = -topologicalPairing D F ↔ D.star F = -F := by
  constructor
  · intro h
    have h_norm : D.inner (F + D.star F) (F + D.star F) = 0 := by
      rw [norm_add_star_sq, h, neg_add_cancel, mul_zero]
    have h_zero : F + D.star F = 0 := h_def (F + D.star F) h_norm
    exact eq_neg_of_add_eq_zero_right h_zero
  · intro h
    dsimp [yangMillsEnergy, topologicalPairing]
    rw [h, ← neg_one_smul ℝ F, D.inner_smul_right, neg_one_mul, neg_neg]

/-- **Theorem**: Unified Absolute Bogomolny Equality Characterization S(F) = |K(F)| ↔ (★ F = F ∨ ★ F = -F). -/
theorem bogomolnyi_equality_iff_dual
    (D : HodgeTwoFormData E)
    (h_def : ∀ x, D.inner x x = 0 → x = 0)
    (F : E) :
    yangMillsEnergy D F = |topologicalPairing D F| ↔ D.star F = F ∨ D.star F = -F := by
  constructor
  · rcases le_or_gt 0 (topologicalPairing D F) with h_pos | h_neg
    · intro h
      rw [abs_of_nonneg h_pos] at h
      left
      exact (energy_eq_topologicalPairing_iff_selfDual D h_def F).mp h
    · intro h
      rw [abs_of_neg h_neg] at h
      right
      exact (energy_eq_neg_topologicalPairing_iff_antiSelfDual D h_def F).mp h
  · rintro (h1 | h2)
    · have h_eq := (energy_eq_topologicalPairing_iff_selfDual D h_def F).mpr h1
      rw [h_eq]
      dsimp [topologicalPairing, yangMillsEnergy]
      rw [h1]
      exact (abs_of_nonneg (D.positive F)).symm
    · dsimp [topologicalPairing, yangMillsEnergy]
      rw [h2, ← neg_one_smul ℝ F, D.inner_smul_right, neg_one_mul, abs_neg, abs_of_nonneg (D.positive F)]

/-- **Theorem**: Master Algebraic Bogomolny Bound Synthesis.
    Unifies:
    1. Quadratic self-dual expansion ⟨F - ★ F, F - ★ F⟩ = 2 (S(F) - K(F)).
    2. Quadratic anti-self-dual expansion ⟨F + ★ F, F + ★ F⟩ = 2 (S(F) + K(F)).
    3. Algebraic Bogomolny bound |K(F)| ≤ S(F) for Yang-Mills energy S(F) = ⟨F, F⟩ and topological pairing K(F) = ⟨F, ★ F⟩.
    4. Self-dual S(F) = K(F) ↔ ★ F = F and anti-self-dual S(F) = -K(F) ↔ ★ F = -F saturation criteria.
    5. Unified absolute equality characterization S(F) = |K(F)| ↔ (★ F = F ∨ ★ F = -F). -/
theorem master_bogomolnyi_algebraic_bound_synthesis
    (D : HodgeTwoFormData E)
    (h_def : ∀ x, D.inner x x = 0 → x = 0)
    (F : E) :
    (D.inner (F - D.star F) (F - D.star F) = 2 * (yangMillsEnergy D F - topologicalPairing D F)) ∧
    (D.inner (F + D.star F) (F + D.star F) = 2 * (yangMillsEnergy D F + topologicalPairing D F)) ∧
    (|topologicalPairing D F| ≤ yangMillsEnergy D F) ∧
    (yangMillsEnergy D F = topologicalPairing D F ↔ D.star F = F) ∧
    (yangMillsEnergy D F = -topologicalPairing D F ↔ D.star F = -F) ∧
    (yangMillsEnergy D F = |topologicalPairing D F| ↔ D.star F = F ∨ D.star F = -F) := ⟨
  norm_sub_star_sq D F,
  norm_add_star_sq D F,
  bogomolnyi_bound D F,
  energy_eq_topologicalPairing_iff_selfDual D h_def F,
  energy_eq_neg_topologicalPairing_iff_antiSelfDual D h_def F,
  bogomolnyi_equality_iff_dual D h_def F
⟩

end InfoGeometry.Canonical.BogomolnyiAlgebraicBoundBridge
