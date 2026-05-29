import InfoGeometry.Basic
set_option linter.unnecessarySimpa false

open scoped BigOperators ENNReal

namespace InfoGeometry.TransformationGroups

/-!
Canonical Lean4/Mathlib scaffold for transformation-group prior rules.
-/

section Discrete

variable {α : Type*} [Fintype α]

/-- Finite probability vectors (`ℝ`-valued). -/
abbrev FinProb (α : Type*) [Fintype α] := InfoGeometry.FinProb α

/-- Invariance of a prior under a group action. -/
def invariant_under {G : Type*} [Group G] {α : Type*} [Fintype α] [MulAction G α]
    (p : FinProb α) : Prop :=
  ∀ (g : G) (a : α), p (g • a) = p a

/-- Transitivity of a group action. -/
def is_transitive {G : Type*} [Group G] {α : Type*} [MulAction G α] : Prop :=
  ∀ a b : α, ∃ g : G, g • a = b

/-- Invariant + transitive implies all atoms have equal mass. -/
lemma eq_of_invariant_transitive
    {G : Type*} [Group G] [MulAction G α]
    (p : FinProb α)
    (hinv : invariant_under (G := G) p)
    (htrans : is_transitive (G := G) (α := α)) :
    ∀ a b : α, p a = p b := by
  intro a b
  rcases htrans a b with ⟨g, rfl⟩
  simpa using (hinv g a).symm

/-- Uniform value forced by equal-atom condition and normalization. -/
lemma uniform_of_all_eq {α : Type*} [Fintype α] [Nonempty α]
    (p : FinProb α)
    (hall : ∀ a b : α, p a = p b) :
    ∀ a : α, p a = 1 / (Fintype.card α : ℝ≥0∞) := by
  classical
  intro a0
  let c : ℝ≥0∞ := p a0
  have hc : ∀ a : α, p a = c := by
    intro a
    exact hall a a0
  have hsum : (∑ a : α, p a) = (Fintype.card α : ℝ≥0∞) * c := by
    simp [hc, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Fintype.card α : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcard_top : (Fintype.card α : ℝ≥0∞) ≠ ∞ := by
    simpa using (ENNReal.coe_ne_top (r := (Fintype.card α : ℝ≥0)))
  have hsum_one : (∑ a : α, p a) = 1 := by
    simpa [tsum_fintype] using (p.tsum_coe : ∑' a, p a = 1)
  have hcval : c = (Fintype.card α : ℝ≥0∞)⁻¹ := by
    have hEq : (Fintype.card α : ℝ≥0∞) * c = 1 := by
      simpa [hsum] using hsum_one
    have hEq' := congrArg (fun x => (Fintype.card α : ℝ≥0∞)⁻¹ * x) hEq
    -- normalize the card factor
    have hcancel : (Fintype.card α : ℝ≥0∞)⁻¹ * (Fintype.card α : ℝ≥0∞) = 1 := by
      simpa [mul_comm] using (ENNReal.inv_mul_cancel hcard hcard_top)
    -- finish
    have hEq'' : (Fintype.card α : ℝ≥0∞)⁻¹ * (Fintype.card α : ℝ≥0∞) * c =
        (Fintype.card α : ℝ≥0∞)⁻¹ := by
      simpa [mul_assoc] using hEq'
    simpa [hcancel] using hEq''
  calc
    p a0 = c := hc a0
    _ = 1 / (Fintype.card α : ℝ≥0∞) := by
          simpa [div_eq_mul_inv] using hcval

/-- Indifference theorem: invariant + transitive implies uniform prior. -/
theorem uniform_of_transformation_group
    {G : Type*} [Group G] [MulAction G α] [Nonempty α]
    (p : FinProb α)
    (hinv : invariant_under (G := G) p)
    (htrans : is_transitive (G := G) (α := α)) :
    ∀ a : α, p a = 1 / (Fintype.card α : ℝ≥0∞) := by
  apply uniform_of_all_eq (α := α) p
  exact eq_of_invariant_transitive (α := α) (G := G) p hinv htrans

end Discrete

section ContinuousLocationScale

/-- Location invariance: `g(μ + b) = g(μ)` for all `μ,b`. -/
def location_invariant (g : ℝ → ℝ) : Prop :=
  ∀ μ b : ℝ, g (μ + b) = g μ

/-- Location invariance forces `g` to be constant. -/
lemma location_invariant_const {g : ℝ → ℝ} (h : location_invariant g) :
    ∀ μ : ℝ, g μ = g 0 := by
  intro μ
  -- take μ' = 0 and shift by μ
  simpa using (h 0 μ)

/-- Scale invariance: `g(aσ) = (1/a) g(σ)` for all `a>0`, `σ>0`. -/
def scale_invariant (g : ℝ → ℝ) : Prop :=
  ∀ a : ℝ, 0 < a → ∀ σ : ℝ, 0 < σ → g (a * σ) = (1 / a) * g σ

/-- Scale invariance forces `g(σ) = g(1)/σ` on `(0,∞)`. -/
lemma scale_invariant_inv {g : ℝ → ℝ} (h : scale_invariant g) :
    ∀ σ : ℝ, 0 < σ → g σ = (g 1) / σ := by
  intro σ hσ
  have hσ1 := h σ hσ 1 (by positivity : (0 : ℝ) < 1)
  have hmain : g σ = (1 / σ) * g 1 := by
    simpa [one_mul] using hσ1
  calc
    g σ = (1 / σ) * g 1 := hmain
    _ = g 1 / σ := by simp [div_eq_mul_inv, mul_comm]

/-- If `g(σ)=c/σ`, the induced density in `t = log σ` is constant `c`. -/
lemma log_coord_flat (c : ℝ) :
    (fun t : ℝ => Real.exp t * (c / Real.exp t)) = fun _ => c := by
  funext t
  have hne : Real.exp t ≠ 0 := Real.exp_ne_zero t
  calc
    Real.exp t * (c / Real.exp t)
        = Real.exp t * (c * (Real.exp t)⁻¹) := by
            simp [div_eq_mul_inv]
    _ = c * (Real.exp t * (Real.exp t)⁻¹) := by
          ring
    _ = c * 1 := by
          simp [hne]
    _ = c := by
          simp

end ContinuousLocationScale

end InfoGeometry.TransformationGroups
