import Architect
import InfoGeometry.Basic
import InfoGeometry.KL.Finite

open scoped BigOperators ENNReal NNReal

namespace InfoGeometry.EntropicInference

/-!
# Entropic Inference (Canonical implementation)

This module implements the core identities of entropic inference using the
canonical `FinProb` (alias for `PMF`) structure from `InfoGeometry.Basic`.
-/

/-- Joint distributions on `X × Θ`. -/
abbrev Joint (X Θ : Type*) [Fintype X] [Fintype Θ] := FinProb (X × Θ)

section BayesJeffreyFinite

variable {X Θ : Type*} [Fintype X] [Fintype Θ] [MeasurableSpace X] [MeasurableSpace Θ]

/-- Marginal on `X`. -/
noncomputable def marginal_x (p : Joint X Θ) : FinProb X :=
  p.map Prod.fst

/-- Marginal on `Θ`. -/
noncomputable def marginal_theta (p : Joint X Θ) : FinProb Θ :=
  p.map Prod.snd

/-- Conditional `p(θ | x)`. -/
noncomputable def cond_theta_given_x
    (p : Joint X Θ) (x : X)
    (hx : x ∈ (marginal_x p).support) : FinProb Θ := by
  let s : Set (X × Θ) := {xt | xt.1 = x}
  have h_filter : ∃ a ∈ s, a ∈ p.support := by
    rcases (PMF.mem_support_map_iff Prod.fst p x).1 hx with ⟨a, ha, hfst⟩
    refine ⟨a, ?_, ha⟩
    change a.1 = x
    exact hfst
  exact (p.filter s h_filter).map Prod.snd

/-- Assemble a joint distribution from a marginal on `X` and conditionals on `Θ | X`. -/
noncomputable def assemble (p_x : FinProb X) (p_theta_given_x : X → FinProb Θ) :
    Joint X Θ :=
  p_x.bind (fun x => (p_theta_given_x x).map (fun θ => (x, θ)))

/-- Marginalizing an assembled joint recovers the original marginal `p_x`. -/
theorem marginal_x_assemble (p_x : FinProb X) (p_theta_given_x : X → FinProb Θ) :
    marginal_x (assemble p_x p_theta_given_x) = p_x := by
  rw [marginal_x, assemble, PMF.map_bind]
  simp [PMF.map_comp]



/-- Bayes posterior after observing `x₀`. -/
noncomputable def bayes_posterior
    (q_theta : FinProb Θ) (q_x_given_theta : Θ → FinProb X) (x0 : X)
    (hZ : x0 ∈
      (marginal_x
        (q_theta.bind (fun θ => (q_x_given_theta θ).map (fun x => (x, θ))))).support) :
    FinProb Θ := by
  let joint : Joint X Θ :=
    q_theta.bind (fun θ => (q_x_given_theta θ).map (fun x => (x, θ)))
  exact cond_theta_given_x joint x0 hZ

/-- Jeffrey joint update: replace `x`-marginal by `p_x`, preserve `q(θ | x)`. -/
noncomputable def jeffrey_joint
    (q : Joint X Θ) (p_x : FinProb X)
    (hq : ∀ x, x ∈ (marginal_x q).support) :
    Joint X Θ :=
  assemble p_x (fun x => cond_theta_given_x q x (hq x))

lemma marginal_x_jeffrey_joint
    (q : Joint X Θ) (p_x : FinProb X)
    (hq : ∀ x, x ∈ (marginal_x q).support) :
    marginal_x (jeffrey_joint q p_x hq) = p_x := by
  simpa [jeffrey_joint] using marginal_x_assemble p_x (fun x => cond_theta_given_x q x (hq x))

end BayesJeffreyFinite

section Decompositions

variable {X Θ : Type*} [Fintype X] [Fintype Θ] [MeasurableSpace X] [MeasurableSpace Θ]

/-- Kullback–Leibler divergence on joints. -/
noncomputable def kl (p q : Joint X Θ) : ℝ≥0∞ :=
  InfoGeometry.kl_div (α := X × Θ)
    (p.toMeasure : MeasureTheory.Measure (X × Θ))
    (q.toMeasure : MeasureTheory.Measure (X × Θ))

noncomputable abbrev KL {X Θ : Type*} [Fintype X] [Fintype Θ] [MeasurableSpace X] [MeasurableSpace Θ]
    (p q : Joint X Θ) : ℝ≥0∞ := kl p q

/--
KL chain-rule decomposition:
`KL(p(x,θ) ‖ q(x,θ)) = KL(p(x) ‖ q(x)) + ∑_x p(x) KL(p(θ|x) ‖ q(θ|x))`
-/
theorem kl_chain_rule
    (p q : Joint X Θ)
    (hq : ∀ x : X, x ∈ (marginal_x q).support)
    (hp : ∀ x : X, x ∈ (marginal_x p).support) :
    kl p q =
      InfoGeometry.kl_div (α := X) (marginal_x p).toMeasure (marginal_x q).toMeasure +
      (∑ x : X, (p.map Prod.fst x) *
        InfoGeometry.kl_div (α := Θ)
          (cond_theta_given_x p x (hp x)).toMeasure
          (cond_theta_given_x q x (hq x)).toMeasure) := by
  sorry

/-- Mutual information `I(X;Θ)`. -/
noncomputable def mutual_information (p : Joint X Θ) : ℝ≥0∞ :=
  kl p (assemble (marginal_x p) (fun _ => marginal_theta p))

/-- Dirac distribution at `x`. -/
noncomputable def dirac {α : Type*} (x : α) : FinProb α :=
  PMF.pure x

end Decompositions

end InfoGeometry.EntropicInference
