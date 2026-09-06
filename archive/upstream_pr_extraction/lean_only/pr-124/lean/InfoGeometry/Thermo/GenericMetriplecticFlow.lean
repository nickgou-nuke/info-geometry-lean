import Mathlib

/-!
# Finite GENERIC/metriplectic flow laws

This owner supplies the missing state/covector layer above the existing
Onsager bilinear-form package.  The reversible operator is skew with respect
to covector evaluation, the dissipative operator is symmetric and positive,
and the Hamiltonian/entropy Casimir conditions are explicit hypotheses.
No indefinite Krein form is used as a positivity witness.
-/

noncomputable section

namespace InfoGeometry.Thermo.GenericMetriplecticFlow

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

abbrev Covector (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  V →ₗ[ℝ] ℝ

structure System (V : Type*) [AddCommGroup V] [Module ℝ V] where
  dH : Covector V
  dS : Covector V
  L : Covector V →ₗ[ℝ] V
  M : Covector V →ₗ[ℝ] V
  L_skew : ∀ (α β : Covector V), α (L β) = - β (L α)
  L_entropy_casimir : L dS = 0
  M_symmetric : ∀ (α β : Covector V), α (M β) = β (M α)
  M_hamiltonian_casimir : M dH = 0
  M_nonneg : ∀ (α : Covector V), 0 ≤ α (M α)

namespace System

variable (S : System V)

def flow : V := S.L S.dH + S.M S.dS

theorem reversible_hamiltonian_rate :
    S.dH (S.L S.dH) = 0 := by
  have h := S.L_skew S.dH S.dH
  linarith

theorem reversible_entropy_rate :
    S.dS (S.L S.dH) = 0 := by
  have h := S.L_skew S.dS S.dH
  rw [S.L_entropy_casimir] at h
  simpa using h

theorem dissipative_hamiltonian_rate :
    S.dH (S.M S.dS) = 0 := by
  rw [S.M_symmetric, S.M_hamiltonian_casimir]
  simp

theorem energy_rate :
    S.dH S.flow = 0 := by
  dsimp [flow]
  rw [map_add, S.reversible_hamiltonian_rate,
    S.dissipative_hamiltonian_rate, add_zero]

theorem entropy_rate_eq_dissipative :
    S.dS S.flow = S.dS (S.M S.dS) := by
  dsimp [flow]
  rw [map_add, S.reversible_entropy_rate, zero_add]

theorem entropy_rate_nonneg :
    0 ≤ S.dS S.flow := by
  rw [S.entropy_rate_eq_dissipative]
  exact S.M_nonneg S.dS

end System

end InfoGeometry.Thermo.GenericMetriplecticFlow
