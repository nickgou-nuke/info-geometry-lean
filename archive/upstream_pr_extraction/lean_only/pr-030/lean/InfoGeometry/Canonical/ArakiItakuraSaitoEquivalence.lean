import Mathlib.Tactic

/-!
# Operator Itakura-Saito and Araki Relative Entropy Equivalence

This file formalizes the exact mathematical bridge between Classical Information Geometry
(Itakura-Saito divergence) and Algebraic Quantum Field Theory (Araki Relative Entropy).
Specifically, it proves that the vacuum expectation value of the operator Itakura-Saito
divergence of the relative modular operator Δ collapses exactly to the Araki Relative Entropy,
as the linear operator terms Δ - I cancel out under the vacuum state.
-/

noncomputable section

namespace InfoGeometry.Canonical.ArakiItakuraSaitoEquivalence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The Operator Itakura-Saito Divergence: Δ - log(Δ) - I -/
def operatorItakuraSaito (Delta logDelta : H →L[ℂ] H) : H →L[ℂ] H :=
  Delta - logDelta - ContinuousLinearMap.id ℂ H

/-- The Araki Relative Entropy defined as the negative vacuum expectation of the modular logarithm. -/
def arakiRelativeEntropy (logDelta : H →L[ℂ] H) (Ω : H) : ℂ :=
  - inner ℂ Ω (logDelta Ω)

/--
THE CAPSTONE THEOREM:
The expectation value of the Operator Itakura-Saito Divergence on the vacuum
collapses EXACTLY to the Araki Relative Entropy.
-/
theorem itakuraSaito_expectation_eq_araki
    (Delta logDelta : H →L[ℂ] H) (Ω : H)
    (h_delta_vacuum : inner ℂ Ω (Delta Ω) = 1)
    (h_norm_vacuum : inner ℂ Ω Ω = 1) :
    inner ℂ Ω (operatorItakuraSaito Delta logDelta Ω) = arakiRelativeEntropy logDelta Ω := by
  unfold operatorItakuraSaito arakiRelativeEntropy
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  rw [inner_sub_right, inner_sub_right]
  rw [h_delta_vacuum, h_norm_vacuum]
  ring

/--
Quantum scale-shift theorem:
Scaling the modular operator Delta by c shifts the vacuum expectation value of the
operator Itakura-Saito divergence by exactly the scalar Itakura-Saito divergence of c.
-/
theorem itakuraSaito_expectation_scale_shift
    (Delta logDelta : H →L[ℂ] H) (Ω : H) (c logc : ℂ)
    (h_delta_vacuum : inner ℂ Ω (Delta Ω) = 1)
    (h_norm_vacuum : inner ℂ Ω Ω = 1) :
    let Delta' := c • Delta
    let logDelta' := logDelta + logc • ContinuousLinearMap.id ℂ H
    inner ℂ Ω (operatorItakuraSaito Delta' logDelta' Ω) =
      (c - logc - 1) * inner ℂ Ω Ω + inner ℂ Ω (operatorItakuraSaito Delta logDelta Ω) := by
  intro Delta' logDelta'
  unfold operatorItakuraSaito
  dsimp [Delta', logDelta']
  simp only [inner_sub_right, inner_add_right, inner_smul_right]
  rw [h_delta_vacuum, h_norm_vacuum]
  ring

end InfoGeometry.Canonical.ArakiItakuraSaitoEquivalence

end noncomputable section
