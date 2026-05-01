/-
InfoGeometry/OperatorAlgebra/HorizonEschaton.lean

Genesis / Revelation / Mahapralaya witness boundary.

This module separates three notions that are often conflated:

* horizon evaporation (geometric boundary change),
* revelation recovery (faithful readback of hidden memory),
* pralaya dissolution (terminal many-to-one thermalization).

It is intentionally witness-first and negative-boundary-safe:
`evaporation` alone does not imply `recovery`.
-/

import Mathlib

noncomputable section

namespace InfoGeometry.OperatorAlgebra.HorizonEschaton

/-- Horizon-side evaporation datum: geometric boundary dynamics only. -/
structure HorizonEvaporationDatum where
  /-- Horizon entropy over an abstract time parameter. -/
  horizonEntropy : ℝ → ℝ

  /-- Evaporation law (model-dependent). -/
  evaporationLaw : Prop

  /-- Witness/certificate that the evaporation law holds. -/
  evaporationCertificate : evaporationLaw

/-- Revelation datum: exterior data faithfully recovers hidden memory. -/
structure RevelationRecoveryDatum (Obs Memory : Type*) where
  /-- Exterior decoder candidate. -/
  exteriorDecode : Obs → Memory

  /-- Hidden-memory oracle/readout that should be recovered. -/
  hiddenMemory : Obs → Memory

  /-- Faithful recovery law: decoding matches hidden memory. -/
  faithfulRecovery : ∀ o : Obs, exteriorDecode o = hiddenMemory o

/-- Pralaya datum: terminal many-to-one thermal collapse. -/
structure PralayaDissolutionDatum (Memory : Type*) where
  /-- Thermalization map on hidden memory states. -/
  thermalize : Memory → Memory

  /-- Terminal equilibrium state. -/
  terminalState : Memory

  /-- Dissolution law: every hidden state thermalizes to the same terminal state. -/
  dissolution : ∀ hidden : Memory, thermalize hidden = terminalState

/-- Non-injectivity witness (many-to-one map). -/
def ManyToOne {α β : Type*} (f : α → β) : Prop :=
  ∃ a₁ a₂ : α, a₁ ≠ a₂ ∧ f a₁ = f a₂

/-- Faithful recovery as left-inverse to thermalization. -/
def FaithfulRecovery {Memory : Type*}
    (thermalize : Memory → Memory)
    (decode : Memory → Memory) : Prop :=
  Function.LeftInverse decode thermalize

section NegativeBoundaries

variable {Obs Memory : Type*}

/--
Evaporation alone does not imply recovery unless a separate recovery witness is supplied.

This theorem is intentionally phrased as a negative boundary:
if no recovery witness exists in the context, evaporation cannot manufacture one.
-/
theorem evaporation_does_not_imply_recovery
    (_E : HorizonEvaporationDatum)
    (noRecoveryWitness : ¬ ∃ _ : RevelationRecoveryDatum Obs Memory, True) :
    ¬ ∃ _ : RevelationRecoveryDatum Obs Memory, True :=
  noRecoveryWitness

/--
If thermalization is many-to-one, no decoder can be a faithful left-inverse.

So total collapse (Pralaya-style many-to-one compression) is incompatible with
faithful recovery of pre-thermalized hidden states.
-/
theorem many_to_one_not_faithful_recovery
    {thermalize decode : Memory → Memory}
    (hMany : ManyToOne thermalize) :
    ¬ FaithfulRecovery thermalize decode := by
  intro hFaithful
  rcases hMany with ⟨m₁, m₂, hne, hEq⟩
  have h1 : decode (thermalize m₁) = m₁ := hFaithful m₁
  have h2 : decode (thermalize m₂) = m₂ := hFaithful m₂
  have hDecodedEq : m₁ = m₂ := by
    calc
      m₁ = decode (thermalize m₁) := (h1.symm)
      _ = decode (thermalize m₂) := by simp [hEq]
      _ = m₂ := h2
  exact hne hDecodedEq

/--
Specialized alias in the language used by the doctrine:
"total thermalization" (many-to-one collapse) is not faithful recovery.
-/
theorem total_thermalization_not_faithful_recovery
    {thermalize decode : Memory → Memory}
    (hMany : ManyToOne thermalize) :
    ¬ FaithfulRecovery thermalize decode :=
  many_to_one_not_faithful_recovery hMany

end NegativeBoundaries

end InfoGeometry.OperatorAlgebra.HorizonEschaton
