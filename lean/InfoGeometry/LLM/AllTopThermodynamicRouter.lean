import InfoGeometry.LLM.ThermodynamicSwitching
import InfoGeometry.LLM.RouterFreeEnergyBridge
import InfoGeometry.Meta.Architecture

open scoped BigOperators InnerProductSpace

namespace InfoGeometry.LLM.AllTopThermodynamicRouter

open InfoGeometry.Canonical.MoE
open InfoGeometry.LLM.ThermodynamicSwitching
open InfoGeometry.LLM.RouterFreeEnergyBridge
open InfoGeometry.Thermo.FiniteDiagonal

section AllTopRouter

variable {Tok V : Type*}
variable [Fintype Tok] [DecidableEq Tok]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {n : Nat} [Nonempty (Fin n)]

/--
All-top thermodynamic weight:
every expert is active, so masked routing collapses to canonical normalized routing.
-/
noncomputable def allTopWeight
    (β : ℝ) (x : Tok → V) (i : Tok) (e : ExpertIdx n) : ℝ :=
  maskedNormalizedWeight (n := n) (allTopMask n) β x i e

@[simp, rep_depth transport]
theorem allTopWeight_eq_normalizedWeight
    (β : ℝ) (x : Tok → V) (i : Tok) (e : ExpertIdx n) :
    allTopWeight (n := n) β x i e = normalizedWeights n β x i e := by
  simp [allTopWeight, maskedNormalizedWeight, allTopMask]

/-- In all-top mode, token-local expert weights form a simplex point. -/
@[rep_depth transport]
theorem allTopWeight_sum_one
    (β : ℝ) (x : Tok → V) (i : Tok) :
    ∑ e : ExpertIdx n, allTopWeight (n := n) β x i e = 1 := by
  simpa [allTopWeight] using
    allTop_weights_sum_one (n := n) (β := β) (x := x) (i := i)

/-- All-top weights are exactly finite-diagonal Gibbs weights of the router Hamiltonian. -/
@[rep_depth thermo]
theorem allTopWeight_eq_finiteGibbs
    (β : ℝ) (x : Tok → V) (i : Tok) (e : ExpertIdx n) :
    allTopWeight (n := n) β x i e
      = gibbsWeight (routerHamiltonian n x i) β e := by
  calc
    allTopWeight (n := n) β x i e
        = normalizedWeights n β x i e := allTopWeight_eq_normalizedWeight (n := n) (β := β) (x := x) (i := i) (e := e)
    _ = gibbsWeight (routerHamiltonian n x i) β e := by
          exact normalizedWeights_eq_finite_gibbsWeight (n := n) (β := β) (x := x) (i := i) (e := e)

/-- All-top routed mixture output. -/
noncomputable def allTopMixture
    (layer : MoELayer n V) (β : ℝ) (x : Tok → V) (i : Tok) : V :=
  maskedNormalizedMixture (n := n) layer (allTopMask n) β x i

/-- All-top mixture equals canonical normalized MoE mixture. -/
@[simp, rep_depth transport]
theorem allTopMixture_eq_normalizedMixture
    (layer : MoELayer n V) (β : ℝ) (x : Tok → V) (i : Tok) :
    allTopMixture (n := n) layer β x i = normalizedMixture layer β x i := by
  simpa [allTopMixture] using
    maskedNormalizedMixture_allTop_eq_normalizedMixture
      (n := n) (layer := layer) (β := β) (x := x) (i := i)

/--
All-top entropy decomposition:
`S = β U + ψ` on each token-local expert slice.
-/
@[rep_depth thermo]
theorem allTop_entropy_eq_beta_internal_plus_massieu
    (β : ℝ) (x : Tok → V) (i : Tok) :
    routerEntropy n β x i = β * routerInternalEnergy n β x i + routerMassieu n β x i := by
  exact routerEntropy_eq_beta_internal_plus_massieu (n := n) (β := β) (x := x) (i := i)

/--
All-top free-energy identity:
`βF = -ψ` for nonzero inverse temperature.
-/
@[rep_depth thermo]
theorem allTop_beta_mul_freeEnergy_eq_neg_massieu
    (β : ℝ) (x : Tok → V) (i : Tok) (hβ : β ≠ 0) :
    β * routerFreeEnergy n β x i = -routerMassieu n β x i := by
  exact beta_mul_routerFreeEnergy_eq_neg_routerMassieu
    (n := n) (β := β) (x := x) (i := i) hβ

end AllTopRouter

section CommonKnowledgeCenter

variable {Tok V : Type*}
variable [Fintype Tok] [DecidableEq Tok]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {n : Nat} [Nonempty (Fin n)]

/--
All-top at `β = 0`: every expert receives uniform mass.
This is the canonical common-knowledge center of the router simplex.
-/
@[simp, rep_depth transport]
theorem allTopWeight_beta_zero_uniform
    (x : Tok → V) (i : Tok) (e : ExpertIdx n) :
    allTopWeight (n := n) 0 x i e = (Fintype.card (ExpertIdx n) : ℝ)⁻¹ := by
  rw [allTopWeight_eq_normalizedWeight (n := n) (β := 0) (x := x) (i := i) (e := e)]
  unfold normalizedWeights unnormalizedWeights routerPartition routerEnergy
  simp [Finset.sum_const, Finset.card_univ]

/-- Common-knowledge router weight (uniform all-top center). -/
noncomputable def commonKnowledgeWeight
    (x : Tok → V) (i : Tok) (e : ExpertIdx n) : ℝ :=
  allTopWeight (n := n) 0 x i e

@[simp, rep_depth transport]
theorem commonKnowledgeWeight_eq_uniform
    (x : Tok → V) (i : Tok) (e : ExpertIdx n) :
    commonKnowledgeWeight (n := n) x i e = (Fintype.card (ExpertIdx n) : ℝ)⁻¹ := by
  simp [commonKnowledgeWeight, allTopWeight_beta_zero_uniform (n := n) (x := x) (i := i) (e := e)]

/-- Common-knowledge mixture: all-top thermodynamic router at `β = 0`. -/
noncomputable def commonKnowledgeMixture
    (layer : MoELayer n V) (x : Tok → V) (i : Tok) : V :=
  allTopMixture (n := n) layer 0 x i

/-- Explicit barycenter of expert outputs on the token slice. -/
noncomputable def expertOutputBarycenter
    (layer : MoELayer n V) (x : Tok → V) (i : Tok) : V :=
  (Fintype.card (ExpertIdx n) : ℝ)⁻¹ •
    (∑ e : ExpertIdx n, (layer.experts e).apply (x i))

/--
At `β = 0`, the all-top router output is exactly the expert-output barycenter.
This is the stabilizing center lane ("common knowledge router").
-/
@[rep_depth transport]
theorem commonKnowledgeMixture_eq_expertOutputBarycenter
    (layer : MoELayer n V) (x : Tok → V) (i : Tok) :
    commonKnowledgeMixture (n := n) layer x i = expertOutputBarycenter (n := n) layer x i := by
  unfold commonKnowledgeMixture allTopMixture maskedNormalizedMixture maskedNormalizedWeight
    allTopMask expertOutputBarycenter
  have hUniform :
      ∀ e : ExpertIdx n,
        normalizedWeights n 0 x i e = (Fintype.card (ExpertIdx n) : ℝ)⁻¹ := by
    intro e
    exact allTopWeight_beta_zero_uniform (n := n) (x := x) (i := i) (e := e)
  simp_rw [hUniform]
  rw [Finset.sum_smul]

end CommonKnowledgeCenter

end InfoGeometry.LLM.AllTopThermodynamicRouter
