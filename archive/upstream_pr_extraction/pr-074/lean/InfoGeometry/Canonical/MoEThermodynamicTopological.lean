import InfoGeometry.Canonical.MixtureOfExperts

/-!
# Finite topological readouts for thermodynamic MoE routing

The algebraic MoE owner defines the router energy, finite partition function,
and normalized Gibbs weights.  This owner adds only their native finite
topology: continuity in the token configuration, a continuous simplex-valued
weight readout, and closed scalar/vector fibers.  No training limit or neural
operator completion is asserted.
-/

namespace InfoGeometry.Canonical.MoE

open scoped BigOperators

noncomputable section

variable {Tok V : Type*} [Fintype Tok] [DecidableEq Tok]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {n : Nat} [Nonempty (Fin n)]

theorem continuous_routerEnergy (i : Tok) (e : ExpertIdx n) :
    Continuous (fun x : Tok → V => routerEnergy n x i e) := by
  unfold routerEnergy
  exact (continuous_norm.comp (continuous_apply i)).add continuous_const

theorem continuous_unnormalizedWeights (β : ℝ) (i : Tok) (e : ExpertIdx n) :
    Continuous (fun x : Tok → V => unnormalizedWeights n β x i e) := by
  unfold unnormalizedWeights
  have hβ : Continuous (fun _ : Tok → V => (-β : ℝ)) := continuous_const
  exact Real.continuous_exp.comp
    (hβ.mul (continuous_routerEnergy (n := n) i e))

theorem continuous_routerPartition (β : ℝ) (i : Tok) :
    Continuous (fun x : Tok → V => routerPartition n β x i) := by
  unfold routerPartition
  apply continuous_finset_sum
  intro e he
  exact continuous_unnormalizedWeights (n := n) β i e

theorem continuous_normalizedWeights (β : ℝ) (i : Tok) (e : ExpertIdx n) :
    Continuous (fun x : Tok → V => normalizedWeights n β x i e) := by
  unfold normalizedWeights
  exact (continuous_unnormalizedWeights (n := n) β i e).div
    (continuous_routerPartition (n := n) β i)
    (fun x => (routerPartition_pos (n := n) β x i).ne')

def normalizedWeightVector (β : ℝ) (i : Tok) :
    (Tok → V) → (ExpertIdx n → ℝ) :=
  fun x e => normalizedWeights n β x i e

theorem continuous_normalizedWeightVector (β : ℝ) (i : Tok) :
    Continuous (normalizedWeightVector (Tok := Tok) (V := V) (n := n) β i) := by
  exact continuous_pi (fun e =>
    continuous_normalizedWeights (Tok := Tok) (V := V) (n := n) β i e)

theorem normalizedWeightVector_sum_one (β : ℝ) (x : Tok → V) (i : Tok) :
    ∑ e : ExpertIdx n, normalizedWeightVector (n := n) β i x e = 1 := by
  simpa [normalizedWeightVector] using
    normalizedWeights_sum_one (n := n) β x i

theorem normalizedWeightVector_nonneg (β : ℝ) (x : Tok → V) (i : Tok)
    (e : ExpertIdx n) :
    0 ≤ normalizedWeightVector (n := n) β i x e := by
  unfold normalizedWeightVector normalizedWeights unnormalizedWeights
  exact div_nonneg (le_of_lt (Real.exp_pos _))
    (le_of_lt (routerPartition_pos (n := n) β x i))

theorem normalizedWeights_levelSet_isClosed (β : ℝ) (i : Tok)
    (e : ExpertIdx n) (c : ℝ) :
    IsClosed {x : Tok → V |
      normalizedWeights n β x i e = c} := by
  change IsClosed
    ((fun x : Tok → V => normalizedWeights n β x i e) ⁻¹' ({c} : Set ℝ))
  exact isClosed_singleton.preimage
    (continuous_normalizedWeights (n := n) β i e)

theorem normalizedWeightVector_fiber_isClosed (β : ℝ) (i : Tok)
    (w : ExpertIdx n → ℝ) :
    IsClosed {x : Tok → V |
      normalizedWeightVector (n := n) β i x = w} := by
  change IsClosed
    ((normalizedWeightVector (n := n) β i) ⁻¹' ({w} : Set (ExpertIdx n → ℝ)))
  exact isClosed_singleton.preimage
    (continuous_normalizedWeightVector (n := n) β i)

theorem continuous_unnormalizedMixture
    (layer : MoELayer n V) (β : ℝ) (i : Tok)
    (happly : ∀ e : ExpertIdx n, Continuous (layer.experts e).apply) :
    Continuous (fun x : Tok → V => unnormalizedMixture layer β x i) := by
  unfold unnormalizedMixture
  apply continuous_finset_sum
  intro e he
  exact (continuous_unnormalizedWeights (n := n) β i e).smul
    ((happly e).comp (continuous_apply i))

theorem continuous_normalizedMixture
    (layer : MoELayer n V) (β : ℝ) (i : Tok)
    (happly : ∀ e : ExpertIdx n, Continuous (layer.experts e).apply) :
    Continuous (fun x : Tok → V => normalizedMixture layer β x i) := by
  unfold normalizedMixture
  apply continuous_finset_sum
  intro e he
  exact (continuous_normalizedWeights (n := n) β i e).smul
    ((happly e).comp (continuous_apply i))

theorem normalizedMixture_norm_sublevel_isClosed
    (layer : MoELayer n V) (β : ℝ) (i : Tok) (c : ℝ)
    (happly : ∀ e : ExpertIdx n, Continuous (layer.experts e).apply) :
    IsClosed {x : Tok → V |
      ‖normalizedMixture layer β x i‖ ≤ c} := by
  change IsClosed
    ((fun x : Tok → V => ‖normalizedMixture layer β x i‖) ⁻¹' Set.Iic c)
  exact isClosed_Iic.preimage
    (continuous_norm.comp (continuous_normalizedMixture layer β i happly))

end
end InfoGeometry.Canonical.MoE
