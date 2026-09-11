import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

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

/-- The four linear maps determine a system; its law fields are propositions. -/
@[ext] theorem ext {T : System V} (hH : S.dH = T.dH) (hS : S.dS = T.dS)
    (hL : S.L = T.L) (hM : S.M = T.M) : S = T := by
  cases S
  cases T
  simp_all

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

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- Change coordinates on a GENERIC system. Covectors pull back along the
inverse equivalence; the two operators push forward vectors and pull back
their covector arguments. -/
def transport (e : V ≃ₗ[ℝ] W) : System W where
  dH := S.dH.comp e.symm.toLinearMap
  dS := S.dS.comp e.symm.toLinearMap
  L := e.toLinearMap.comp (S.L.comp e.toLinearMap.dualMap)
  M := e.toLinearMap.comp (S.M.comp e.toLinearMap.dualMap)
  L_skew := by
    intro α β
    exact S.L_skew (α.comp e.toLinearMap) (β.comp e.toLinearMap)
  L_entropy_casimir := by
    have h : (S.dS.comp e.symm.toLinearMap).comp e.toLinearMap = S.dS := by
      ext x
      simp
    change e (S.L ((S.dS.comp e.symm.toLinearMap).comp e.toLinearMap)) = 0
    rw [h, S.L_entropy_casimir, map_zero]
  M_symmetric := by
    intro α β
    exact S.M_symmetric (α.comp e.toLinearMap) (β.comp e.toLinearMap)
  M_hamiltonian_casimir := by
    have h : (S.dH.comp e.symm.toLinearMap).comp e.toLinearMap = S.dH := by
      ext x
      simp
    change e (S.M ((S.dH.comp e.symm.toLinearMap).comp e.toLinearMap)) = 0
    rw [h, S.M_hamiltonian_casimir, map_zero]
  M_nonneg := by
    intro α
    exact S.M_nonneg (α.comp e.toLinearMap)

/-- The vector field transforms covariantly under a linear change of state
coordinates, including both reversible and dissipative summands. -/
theorem transport_flow (e : V ≃ₗ[ℝ] W) :
    (S.transport e).flow = e S.flow := by
  have hH : (S.dH.comp e.symm.toLinearMap).comp e.toLinearMap = S.dH := by
    ext x
    simp
  have hS : (S.dS.comp e.symm.toLinearMap).comp e.toLinearMap = S.dS := by
    ext x
    simp
  change e (S.L ((S.dH.comp e.symm.toLinearMap).comp e.toLinearMap)) +
      e (S.M ((S.dS.comp e.symm.toLinearMap).comp e.toLinearMap)) =
    e (S.L S.dH + S.M S.dS)
  rw [hH, hS, map_add]

/-- Identity coordinates leave all four defining maps unchanged. -/
@[simp] theorem transport_refl :
    S.transport (LinearEquiv.refl ℝ V) = S := by
  apply System.ext <;> ext x <;> rfl

/-- Coordinate changes compose, with contravariant covector transport and
covariant vector transport in both operator lanes. -/
theorem transport_trans {U : Type*} [AddCommGroup U] [Module ℝ U]
    (e : V ≃ₗ[ℝ] W) (f : W ≃ₗ[ℝ] U) :
    (S.transport e).transport f = S.transport (e.trans f) := by
  apply System.ext <;> ext x <;> rfl

/-- Reversing a coordinate change recovers the original system, not merely
its scalar energy and entropy rates. -/
@[simp] theorem transport_symm (e : V ≃ₗ[ℝ] W) :
    (S.transport e).transport e.symm = S := by
  rw [transport_trans]
  have h : e.trans e.symm = LinearEquiv.refl ℝ V := by
    ext x
    simp
  rw [h, transport_refl]

end System

end InfoGeometry.Thermo.GenericMetriplecticFlow
