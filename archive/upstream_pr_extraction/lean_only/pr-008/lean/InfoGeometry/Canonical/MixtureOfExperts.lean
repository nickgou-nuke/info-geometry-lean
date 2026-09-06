import Mathlib

open scoped BigOperators

namespace InfoGeometry.Canonical.MoE

/-!
# Thermodynamic Geometry of Mixture of Experts (MoE)

This module formalizes the Mixture of Experts (MoE) architecture as a 
thermodynamic gauge theory over a vector bundle.

- **Experts**: Sections of the transformation bundle.
- **Router Energy**: The generating potential for expert selection.
- **Unnormalized Switching**: The pre-quantum measure (raw exponentials).
- **Normalization as Gauge Fixing**: Projecting to the probability simplex (Softmax).
- **Convex Mixture**: The routed output is a strictly verified convex 
  combination of the expert manifold.
-/

variable {Tok V : Type*} [Fintype Tok] [DecidableEq Tok]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A finite set of expert networks. -/
abbrev ExpertIdx (n : Nat) := Fin n

/-- An expert is a transformation on the semantic space V. -/
structure Expert (V : Type*) where
  apply : V → V

/-- The MoE layer contains `n` experts. -/
structure MoELayer (n : Nat) (V : Type*) where
  experts : ExpertIdx n → Expert V

section Router

variable (n : Nat) [Nonempty (Fin n)]

set_option linter.unusedVariables false

/-- 
The Router Energy function.
Assigns a thermodynamic energy to each expert for a given token.
Lower energy = higher routing probability.
(In practice, `- dot(W_router, x_i)`).
-/
def routerEnergy (x : Tok → V) (i : Tok) (e : ExpertIdx n) : ℝ :=
  -- Simple geometric surrogate: token magnitude plus expert-dependent offset.
  ‖x i‖ + ((e : ℕ) : ℝ)

/-- 
Unnormalized routing weights (the pre-quantum measure). 
This is the unnormalized Gibbs weight $e^{-\beta E}$.
-/
noncomputable def unnormalizedWeights (β : ℝ) (x : Tok → V) (i : Tok) (e : ExpertIdx n) : ℝ :=
  Real.exp (-β * routerEnergy n x i e)

/-- 
The Partition Function $Z$ for the router at a specific token.
This is the total mass of the unnormalized weights (the gauge scale).
-/
noncomputable def routerPartition (β : ℝ) (x : Tok → V) (i : Tok) : ℝ :=
  ∑ e : Fin n, unnormalizedWeights n β x i e

/-- 
Normalization as Gauge Fixing: 
Projecting the unnormalized weights onto the probability simplex.
This yields the standard Softmax routing probabilities.
-/
noncomputable def normalizedWeights (β : ℝ) (x : Tok → V) (i : Tok) (e : ExpertIdx n) : ℝ :=
  unnormalizedWeights n β x i e / routerPartition n β x i

omit [Fintype Tok] [DecidableEq Tok] [NormedSpace ℝ V] in
/-- 
The Partition Function $Z$ for the router at a specific token.
This is the total mass of the unnormalized weights (the gauge scale).
-/
lemma routerPartition_pos (β : ℝ) (x : Tok → V) (i : Tok) :
    0 < routerPartition n β x i := by
  classical
  unfold routerPartition
  apply Finset.sum_pos
  · intro e _
    exact Real.exp_pos _
  · exact Finset.univ_nonempty

omit [Fintype Tok] [DecidableEq Tok] [NormedSpace ℝ V] in
/-- 
Theorem: The normalized weights form a valid convex combination 
(they sum to 1). This proves the router maps into the probability simplex.
-/
lemma normalizedWeights_sum_one (β : ℝ) (x : Tok → V) (i : Tok) :
    ∑ e : Fin n, normalizedWeights n β x i e = 1 := by
  classical
  unfold normalizedWeights
  let Z := routerPartition n β x i
  have hZ : Z ≠ 0 := (routerPartition_pos n β x i).ne'
  calc
    ∑ e : Fin n, unnormalizedWeights n β x i e / Z
        = ∑ e : Fin n, Z⁻¹ * unnormalizedWeights n β x i e := by
            refine Finset.sum_congr rfl ?_
            intro e _
            rw [div_eq_inv_mul]
    _ = Z⁻¹ * (∑ e : Fin n, unnormalizedWeights n β x i e) := by
          rw [← Finset.mul_sum]
    _ = (∑ e : Fin n, unnormalizedWeights n β x i e) / Z := by
          rw [div_eq_inv_mul]
    _ = Z / Z := rfl
    _ = 1 := div_self hZ

end Router

section Mixture

variable {n : Nat} [Nonempty (Fin n)]

/-- 
The Unnormalized Mixture (Pre-Gauge Fixing).
This is the raw linear combination of expert outputs using the 
unnormalized thermodynamic measure.
-/
noncomputable def unnormalizedMixture 
    (layer : MoELayer n V) (β : ℝ) (x : Tok → V) (i : Tok) : V :=
  ∑ e : Fin n, unnormalizedWeights n β x i e • (layer.experts e).apply (x i)

/-- 
The Normalized Mixture (Post-Gauge Fixing).
This is the standard MoE output: a strict convex combination of experts 
using the simplex-projected Gibbs weights.
-/
noncomputable def normalizedMixture 
    (layer : MoELayer n V) (β : ℝ) (x : Tok → V) (i : Tok) : V :=
  ∑ e : Fin n, normalizedWeights n β x i e • (layer.experts e).apply (x i)

set_option linter.unusedSectionVars false

/-- 
Theorem: Gauge-Fixing the Output.
The final MoE output is exactly the unnormalized mixture scaled down 
by the router's partition function (the gauge scaling factor).
This formalizes the "Conformal/Weyl scaling" equivalence for MoE.
-/
theorem mixture_gauge_reduction 
    (layer : MoELayer n V) (β : ℝ) (x : Tok → V) (i : Tok) :
    normalizedMixture layer β x i = (routerPartition n β x i)⁻¹ • unnormalizedMixture layer β x i := by
  classical
  unfold normalizedMixture unnormalizedMixture normalizedWeights
  calc
    ∑ e : Fin n, (unnormalizedWeights n β x i e / routerPartition n β x i) • (layer.experts e).apply (x i)
      = ∑ e : Fin n, (routerPartition n β x i)⁻¹ •
            (unnormalizedWeights n β x i e • (layer.experts e).apply (x i)) := by
          refine Finset.sum_congr rfl ?_
          intro e _
          rw [div_eq_inv_mul, mul_smul]
    _ = (routerPartition n β x i)⁻¹ •
        ∑ e : Fin n, unnormalizedWeights n β x i e • (layer.experts e).apply (x i) := by
          rw [← Finset.smul_sum]

end Mixture

end InfoGeometry.Canonical.MoE
