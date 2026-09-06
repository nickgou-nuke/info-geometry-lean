import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Basic
import InfoGeometry.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Exp

open scoped BigOperators

namespace InfoGeometry.TransformationGroups

/-!
Canonical Lean4/Mathlib scaffold for transformation-group prior rules.
-/

section Discrete

variable {α : Type*} [Fintype α]

/-- Finite probability vectors (`ℝ`-valued). -/
abbrev FinProb (α : Type*) [Fintype α] := InfoGeometry.FinProb α

/-- Invariance of a prior under a group action. -/
def InvariantUnder {G : Type*} [Group G] {α : Type*} [Fintype α] [MulAction G α]
    (p : FinProb α) : Prop :=
  ∀ (g : G) (a : α), p (g • a) = p a

/-- Transitivity of a group action. -/
def IsTransitive {G : Type*} [Group G] {α : Type*} [MulAction G α] : Prop :=
  ∀ a b : α, ∃ g : G, g • a = b

/-- Invariant + transitive implies all atoms have equal mass. -/
lemma eq_of_invariant_transitive
    {G : Type*} [Group G] [MulAction G α]
    (p : FinProb α)
    (hinv : InvariantUnder (G := G) p)
    (htrans : IsTransitive (G := G) (α := α)) :
    ∀ a b : α, p a = p b := by
  intro a b
  rcases htrans a b with ⟨g, rfl⟩
  simpa using (hinv g a).symm

/-- Uniform value forced by equal-atom condition and normalization. -/
lemma uniform_of_all_eq {α : Type*} [Fintype α] [Nonempty α]
    (p : FinProb α)
    (hall : ∀ a b : α, p a = p b) :
    ∀ a : α, p a = 1 / (Fintype.card α : ℝ) := by
  classical
  let a0 : α := Classical.choice (by infer_instance : Nonempty α)
  let c : ℝ := p a0
  have hc : ∀ a : α, p a = c := by
    intro a
    exact hall a a0
  have hsum : (∑ a : α, p a) = (Fintype.card α : ℝ) * c := by
    simp [hc, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcval : c = 1 / (Fintype.card α : ℝ) := by
    have hEq : (Fintype.card α : ℝ) * c = 1 := by
      simpa [hsum] using p.sum_one
    have hEq' : c * (Fintype.card α : ℝ) = 1 := by
      simpa [mul_comm] using hEq
    exact (eq_div_iff hcard).2 hEq'
  intro a
  calc
    p a = c := hc a
    _ = 1 / (Fintype.card α : ℝ) := hcval

/-- Indifference theorem: invariant + transitive implies uniform prior. -/
theorem uniform_of_transformation_group
    {G : Type*} [Group G] [MulAction G α] [Nonempty α]
    (p : FinProb α)
    (hinv : InvariantUnder (G := G) p)
    (htrans : IsTransitive (G := G) (α := α)) :
    ∀ a : α, p a = 1 / (Fintype.card α : ℝ) := by
  apply uniform_of_all_eq (α := α) p
  exact eq_of_invariant_transitive (α := α) (G := G) p hinv htrans

end Discrete

section ContinuousLocationScale

/-- Location invariance: `g(μ + b) = g(μ)` for all `μ,b`. -/
def LocationInvariant (g : ℝ → ℝ) : Prop :=
  ∀ μ b : ℝ, g (μ + b) = g μ

/-- Location invariance forces `g` to be constant. -/
lemma locationInvariant_const {g : ℝ → ℝ} (h : LocationInvariant g) :
    ∀ μ : ℝ, g μ = g 0 := by
  intro μ
  -- take μ' = 0 and shift by μ
  simpa using (h 0 μ)

/-- Scale invariance: `g(aσ) = (1/a) g(σ)` for all `a>0`, `σ>0`. -/
def ScaleInvariant (g : ℝ → ℝ) : Prop :=
  ∀ a : ℝ, 0 < a → ∀ σ : ℝ, 0 < σ → g (a * σ) = (1 / a) * g σ

/-- Scale invariance forces `g(σ) = g(1)/σ` on `(0,∞)`. -/
lemma scaleInvariant_inv {g : ℝ → ℝ} (h : ScaleInvariant g) :
    ∀ σ : ℝ, 0 < σ → g σ = (g 1) / σ := by
  intro σ hσ
  have hσ1 := h σ hσ 1 (by positivity : (0 : ℝ) < 1)
  have hmain : g σ = (1 / σ) * g 1 := by
    simpa [one_mul] using hσ1
  calc
    g σ = (1 / σ) * g 1 := hmain
    _ = g 1 / σ := by simp [div_eq_mul_inv, mul_comm]

/-- If `g(σ)=c/σ`, the induced density in `t = log σ` is constant `c`. -/
lemma logCoord_flat (c : ℝ) :
    (fun t : ℝ => Real.exp t * (c / Real.exp t)) = fun _ => c := by
  funext t
  have hne : Real.exp t ≠ 0 := Real.exp_ne_zero t
  calc
    Real.exp t * (c / Real.exp t)
        = Real.exp t * (c * (Real.exp t)⁻¹) := by simp [div_eq_mul_inv]
    _   = (Real.exp t * c) * (Real.exp t)⁻¹ := by
          simpa using (mul_assoc (Real.exp t) c (Real.exp t)⁻¹).symm
    _   = (c * Real.exp t) * (Real.exp t)⁻¹ := by simp [mul_comm]
        _   = c * (Real.exp t * (Real.exp t)⁻¹) := by simp
    _   = c * 1 := by simp
    _   = c := by simp

end ContinuousLocationScale

end InfoGeometry.TransformationGroups
