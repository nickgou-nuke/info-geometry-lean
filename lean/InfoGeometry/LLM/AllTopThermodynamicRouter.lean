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

section OmitAllTopWeightEq

omit [Fintype Tok] [DecidableEq Tok] [NormedSpace ℝ V] [Nonempty (Fin n)]

@[simp, rep_depth transport]
theorem allTopWeight_eq_normalizedWeight
    (β : ℝ) (x : Tok → V) (i : Tok) (e : ExpertIdx n) :
    allTopWeight (n := n) β x i e = normalizedWeights n β x i e := by
  simp [allTopWeight, maskedNormalizedWeight, allTopMask]

end OmitAllTopWeightEq

section OmitAllTopWeightSumOne

omit [Fintype Tok] [DecidableEq Tok] [NormedSpace ℝ V]

/-- In all-top mode, token-local expert weights form a simplex point. -/
@[rep_depth transport]
theorem allTopWeight_sum_one
    (β : ℝ) (x : Tok → V) (i : Tok) :
    ∑ e : ExpertIdx n, allTopWeight (n := n) β x i e = 1 := by
  simpa [allTopWeight] using
    allTop_weights_sum_one (n := n) (β := β) (x := x) (i := i)

end OmitAllTopWeightSumOne

section OmitAllTopWeightFiniteGibbs

omit [Fintype Tok] [DecidableEq Tok] [NormedSpace ℝ V]

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

end OmitAllTopWeightFiniteGibbs

/-- All-top routed mixture output. -/
noncomputable def allTopMixture
    (layer : MoELayer n V) (β : ℝ) (x : Tok → V) (i : Tok) : V :=
  maskedNormalizedMixture (n := n) layer (allTopMask n) β x i

section OmitAllTopMixtureEq

omit [Fintype Tok] [DecidableEq Tok] [Nonempty (Fin n)]

/-- All-top mixture equals canonical normalized MoE mixture. -/
@[simp, rep_depth transport]
theorem allTopMixture_eq_normalizedMixture
    (layer : MoELayer n V) (β : ℝ) (x : Tok → V) (i : Tok) :
    allTopMixture (n := n) layer β x i = normalizedMixture layer β x i := by
  simpa [allTopMixture] using
    maskedNormalizedMixture_allTop_eq_normalizedMixture
      (n := n) (layer := layer) (β := β) (x := x) (i := i)

end OmitAllTopMixtureEq

section OmitAllTopThermoIds

omit [Fintype Tok] [DecidableEq Tok] [NormedSpace ℝ V]

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

end OmitAllTopThermoIds

end AllTopRouter

end InfoGeometry.LLM.AllTopThermodynamicRouter
