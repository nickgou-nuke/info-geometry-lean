/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NoncommRing

/-!
# Modular Phase Separation, Klein-Bottle Twist, and Boundary $\mathrm{Cl}(1,1)$ Majorana Structure

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * Krein grading symmetry (`IsKreinSymmetry`), odd operators (`IsOddOperator`),
    graded Krein supertrace (`supertrace`), and commutant submodule (`ModularCommutant`).
- BUCKET 2 (Deconfabulation):
  * Eliminated the `TomitaPhaseSeparationPacket` wrapper structure and `ModularReflection`
    `Prop`-def wrapper; all algebraic and trace properties are proved constructively over a
    commutative ring `R` with `Invertible (2 : R)` and a free finite-rank `R`-module `M`,
    with zero wrapper structures, zero `sorry`s, and zero custom axioms.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `odd_operator_zero_of_grading_one` and `odd_operator_zero_of_grading_neg_one`.
  * `modular_phase_separation`: non-vanishing Krein supertrace of a commutator forces
    non-trivial grading (`Γ ≠ ±1`) and non-commutation (`B ∉ ModularCommutant A`).
  * `clifford_bivector_square_eq_neg_one`: proves directly on `Module.End R M` that
    $(J_\Delta \mathcal{T})^2 = -1$, $J_\Delta \mathcal{T} J_\Delta = -\mathcal{T}$, and
    $\mathcal{T} J_\Delta \mathcal{T} = -J_\Delta$ from $J_\Delta^2 = 1$,
    $\mathcal{T}^2 = 1$, and $J_\Delta \mathcal{T} = -\mathcal{T} J_\Delta$.
-/

namespace InfoGeometry.GrandUnification.ModularPhaseSeparation

open LinearMap

variable {R M : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]

/-! ### 1. Krein Symmetry and Chiral Gradings -/

/-- An operator is a Krein-Chiral symmetry if it acts as an involution on the space. -/
abbrev IsKreinSymmetry (Γ : Module.End R M) : Prop :=
  Γ * Γ = 1

/-- An operator is 'odd' relative to the Krein grading if it perfectly anti-commutes with Γ. -/
abbrev IsOddOperator (Γ A : Module.End R M) : Prop :=
  Γ * A = - (A * Γ)

/-- The Graded Krein Supertrace over the endomorphism algebra. -/
noncomputable def supertrace (Γ X : Module.End R M) : R :=
  LinearMap.trace R M (Γ * X)

/-! ### 2. The Triviality Bounds -/

/-- Any odd operator with respect to the trivial grading `Γ = 1` vanishes identically. -/
lemma odd_operator_zero_of_grading_one (Γ A : Module.End R M)
    (h_odd : IsOddOperator Γ A) (h_one : Γ = 1) : A = 0 := by
  unfold IsOddOperator at h_odd
  rw [h_one, mul_one, one_mul] at h_odd
  have h_add : A + A = 0 := by
    calc A + A = -A + A := by nth_rw 1 [h_odd]
         _ = 0 := neg_add_cancel A
  have h_two : (2 : R) • A = 0 := by
    calc (2 : R) • A = (1 + 1 : R) • A := by norm_num
         _ = (1 : R) • A + (1 : R) • A := add_smul 1 1 A
         _ = A + A := by rw [one_smul]
         _ = 0 := h_add
  calc A = (1 : R) • A := by rw [one_smul]
       _ = (⅟(2 : R) * 2) • A := by rw [invOf_mul_self]
       _ = ⅟(2 : R) • ((2 : R) • A) := by rw [mul_smul]
       _ = ⅟(2 : R) • (0 : Module.End R M) := by rw [h_two]
       _ = 0 := smul_zero _

/-- Any odd operator with respect to the negative trivial grading `Γ = -1` vanishes identically. -/
lemma odd_operator_zero_of_grading_neg_one (Γ A : Module.End R M)
    (h_odd : IsOddOperator Γ A) (h_neg_one : Γ = -1) : A = 0 := by
  unfold IsOddOperator at h_odd
  rw [h_neg_one, neg_mul, mul_neg, one_mul, mul_one, neg_neg] at h_odd
  have h_add : A + A = 0 := by
    calc A + A = -A + A := by nth_rw 1 [← h_odd]
         _ = 0 := neg_add_cancel A
  have h_two : (2 : R) • A = 0 := by
    calc (2 : R) • A = (1 + 1 : R) • A := by norm_num
         _ = (1 : R) • A + (1 : R) • A := add_smul 1 1 A
         _ = A + A := by rw [one_smul]
         _ = 0 := h_add
  calc A = (1 : R) • A := by rw [one_smul]
       _ = (⅟(2 : R) * 2) • A := by rw [invOf_mul_self]
       _ = ⅟(2 : R) • ((2 : R) • A) := by rw [mul_smul]
       _ = ⅟(2 : R) • (0 : Module.End R M) := by rw [h_two]
       _ = 0 := smul_zero _

/-! ### 3. Algebra (Ego) & Commutant (Anima) Modular Partition -/

/-- The Commutant (Anima) of an operator algebra block.
    Defines the set of all endomorphisms that commute with a given target operator. -/
def ModularCommutant (A : Module.End R M) : Submodule R (Module.End R M) where
  carrier := {X | X * A = A * X}
  zero_mem' := by dsimp; rw [zero_mul, mul_zero]
  add_mem' := by
    intro X Y hX hY; dsimp at *
    rw [add_mul, mul_add, hX, hY]
  smul_mem' := by
    intro c X hX; dsimp at *
    ext v
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.map_smul]
    have h_eval : (X * A) v = (A * X) v := by rw [hX]
    simp only [Module.End.mul_apply] at h_eval
    rw [h_eval]

/-! ### 4. The Modular Phase Separation Theorem -/

/-- Theorem: The presence of a non-trivial local spinning anomaly breaks the
    ambient vacuum symmetry, separating the architecture into an algebra and its commutant. -/
theorem modular_phase_separation
    (Γ A B : Module.End R M)
    (h_odd_A : IsOddOperator Γ A)
    (h_anomaly : supertrace Γ (A * B - B * A) ≠ 0) :
    Γ ≠ 1 ∧ Γ ≠ -1 ∧ (B ∈ ModularCommutant A → False) := by
  constructor
  · intro h_one
    have hA_zero := odd_operator_zero_of_grading_one Γ A h_odd_A h_one
    rw [hA_zero, zero_mul, mul_zero, sub_zero] at h_anomaly
    have h_str_zero : supertrace Γ (0 : Module.End R M) = 0 := by
      unfold supertrace; rw [mul_zero, map_zero]
    exact h_anomaly h_str_zero
  · constructor
    · intro h_neg_one
      have hA_zero := odd_operator_zero_of_grading_neg_one Γ A h_odd_A h_neg_one
      rw [hA_zero, zero_mul, mul_zero, sub_zero] at h_anomaly
      have h_str_zero : supertrace Γ (0 : Module.End R M) = 0 := by
        unfold supertrace; rw [mul_zero, map_zero]
      exact h_anomaly h_str_zero
    · intro h_comm
      dsimp [ModularCommutant] at h_comm
      have h_sub_zero : A * B - B * A = 0 := by rw [h_comm, sub_self]
      rw [h_sub_zero] at h_anomaly
      have h_str_zero : supertrace Γ (0 : Module.End R M) = 0 := by
        unfold supertrace; rw [mul_zero, map_zero]
      exact h_anomaly h_str_zero

/-! ### 5. Boundary $\mathrm{Cl}(1,1)$ Majorana Bivector Theorem (Wrapper-Free) -/

omit [Invertible (2 : R)] in
/-- **Boundary $\mathrm{Cl}(1,1)$ Majorana Bivector Theorem:**
For any modular reflection involution $J_\Delta \in \mathrm{End}_R(M)$ ($J_\Delta^2 = 1$)
and Majorana Möbius twist $\mathcal{T} \in \mathrm{End}_R(M)$ ($\mathcal{T}^2 = 1$) that
anti-commute ($J_\Delta \mathcal{T} = -\mathcal{T} J_\Delta$), the pair $(J_\Delta, \mathcal{T})$
generates a real Clifford algebra $\mathrm{Cl}(1,1)$ whose composite boundary bivector
$B = J_\Delta \mathcal{T}$ satisfies:
1. $J_\Delta \mathcal{T} J_\Delta = -\mathcal{T}$ and $\mathcal{T} J_\Delta \mathcal{T} = -J_\Delta$;
2. $(J_\Delta \mathcal{T}) (J_\Delta \mathcal{T}) = -1$ (endogenous symplectic complex structure
   born from two real Majorana involutions). -/
theorem clifford_bivector_square_eq_neg_one
    (J_Δ 𝒯 : Module.End R M)
    (hJ : IsKreinSymmetry J_Δ)
    (hT : IsKreinSymmetry 𝒯)
    (hJT : IsOddOperator J_Δ 𝒯) :
    J_Δ * 𝒯 * J_Δ = - 𝒯 ∧
    𝒯 * J_Δ * 𝒯 = - J_Δ ∧
    (J_Δ * 𝒯) * (J_Δ * 𝒯) = -1 := by
  have hJTJ : J_Δ * 𝒯 * J_Δ = - 𝒯 := by
    calc
      J_Δ * 𝒯 * J_Δ = (-(𝒯 * J_Δ)) * J_Δ := by rw [hJT]
      _ = -(𝒯 * (J_Δ * J_Δ)) := by noncomm_ring
      _ = -(𝒯 * 1) := by rw [hJ]
      _ = - 𝒯 := by rw [mul_one]
  have hTJT : 𝒯 * J_Δ * 𝒯 = - J_Δ := by
    have hTJ : 𝒯 * J_Δ = - (J_Δ * 𝒯) := by
      calc
        𝒯 * J_Δ = -(-(𝒯 * J_Δ)) := (neg_neg _).symm
        _ = - (J_Δ * 𝒯) := by rw [← hJT]
    calc
      𝒯 * J_Δ * 𝒯 = (-(J_Δ * 𝒯)) * 𝒯 := by rw [hTJ]
      _ = -(J_Δ * (𝒯 * 𝒯)) := by noncomm_ring
      _ = -(J_Δ * 1) := by rw [hT]
      _ = - J_Δ := by rw [mul_one]
  have hBiv : (J_Δ * 𝒯) * (J_Δ * 𝒯) = -1 := by
    calc
      (J_Δ * 𝒯) * (J_Δ * 𝒯) = (J_Δ * 𝒯 * J_Δ) * 𝒯 := by noncomm_ring
      _ = (- 𝒯) * 𝒯 := by rw [hJTJ]
      _ = - (𝒯 * 𝒯) := neg_mul 𝒯 𝒯
      _ = -1 := by rw [hT]
  exact ⟨hJTJ, hTJT, hBiv⟩

end InfoGeometry.GrandUnification.ModularPhaseSeparation
