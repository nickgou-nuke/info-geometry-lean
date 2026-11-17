/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.DoubledAdjoint
import InfoGeometry.Krein.InternalPhaseGram

/-!
# The internal phase form as an observable commutator

The carrier is the canonical real Hilbert space `DoubledSpace E`; the phase
operator is the existing `complex_i`.  For Hilbert-self-adjoint operators
commuting with this phase operator, the phase pairing of their fluctuations
is one half of the expectation of their ordered commutator against `I ψ`.

The identity allows arbitrary real centering shifts.  No normalization,
canonical commutation relation, or indefinite probability form is assumed.
Normalization is relevant when a shift is interpreted as an expectation.
The finite-family theorem changes observable coefficients while retaining
every ordered operator product.
-/

noncomputable section

namespace InfoGeometry.Krein.PhaseLinearObservableCommutator

open InfoGeometry.Krein.InternalPhaseGram (phase_pair_neg_swap phase_pair_self_zero)
open scoped InnerProductSpace BigOperators

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => DoubledEnd E
local notation "Iop" => complex_i (E := E)

/-- The fluctuation vector for an explicit real centering shift. -/
def centeredVector (A : EndH) (a : ℝ) (ψ : H₂) : H₂ :=
  A ψ - a • ψ

/-- A self-adjoint observable that preserves the internal phase has zero
phase pairing with the state in its expectation slot. -/
theorem phase_pair_observable_self_zero
    (A : EndH) (hA : IsSelfAdjoint A)
    (hAI : A.comp Iop = (Iop).comp A) (ψ : H₂) :
    ⟪Iop ψ, A ψ⟫_ℝ = 0 := by
  have hcomm : A (Iop ψ) = Iop (A ψ) :=
    congrArg (fun T : EndH => T ψ) hAI
  have hsym : ⟪Iop ψ, A ψ⟫_ℝ = ⟪Iop (A ψ), ψ⟫_ℝ := by
    calc
      ⟪Iop ψ, A ψ⟫_ℝ = ⟪A (Iop ψ), ψ⟫_ℝ :=
        (hA.isSymmetric (Iop ψ) ψ).symm
      _ = ⟪Iop (A ψ), ψ⟫_ℝ := by rw [hcomm]
  have hskew := phase_pair_neg_swap ψ (A ψ)
  linarith

/-- Real centering shifts do not change the phase pairing of self-adjoint,
phase-preserving observables. -/
theorem phase_pair_centered_eq
    (A B : EndH) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAI : A.comp Iop = (Iop).comp A)
    (hBI : B.comp Iop = (Iop).comp B)
    (a b : ℝ) (ψ : H₂) :
    ⟪Iop (centeredVector A a ψ), centeredVector B b ψ⟫_ℝ =
      ⟪Iop (A ψ), B ψ⟫_ℝ := by
  have hA0 : ⟪Iop (A ψ), ψ⟫_ℝ = 0 := by
    rw [phase_pair_neg_swap, phase_pair_observable_self_zero A hA hAI ψ, neg_zero]
  have hB0 := phase_pair_observable_self_zero B hB hBI ψ
  have hψ0 := phase_pair_self_zero ψ
  simp only [centeredVector, map_sub, map_smul, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, hA0, hB0, hψ0,
    mul_zero, sub_zero]

/-- The real phase pairing reads the actual ordered commutator. -/
theorem twice_phase_pair_eq_commutator
    (A B : EndH) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAI : A.comp Iop = (Iop).comp A)
    (hBI : B.comp Iop = (Iop).comp B) (ψ : H₂) :
    2 * ⟪Iop (A ψ), B ψ⟫_ℝ =
      ⟪Iop ψ, (A.comp B - B.comp A) ψ⟫_ℝ := by
  have hcommA : A (Iop ψ) = Iop (A ψ) :=
    congrArg (fun T : EndH => T ψ) hAI
  have hcommB : B (Iop ψ) = Iop (B ψ) :=
    congrArg (fun T : EndH => T ψ) hBI
  have hAB : ⟪Iop ψ, A (B ψ)⟫_ℝ = ⟪Iop (A ψ), B ψ⟫_ℝ := by
    calc
      ⟪Iop ψ, A (B ψ)⟫_ℝ = ⟪A (Iop ψ), B ψ⟫_ℝ :=
        (hA.isSymmetric (Iop ψ) (B ψ)).symm
      _ = ⟪Iop (A ψ), B ψ⟫_ℝ := by rw [hcommA]
  have hBA : ⟪Iop ψ, B (A ψ)⟫_ℝ = -⟪Iop (A ψ), B ψ⟫_ℝ := by
    calc
      ⟪Iop ψ, B (A ψ)⟫_ℝ = ⟪B (Iop ψ), A ψ⟫_ℝ :=
        (hB.isSymmetric (Iop ψ) (A ψ)).symm
      _ = ⟪Iop (B ψ), A ψ⟫_ℝ := by rw [hcommB]
      _ = -⟪Iop (A ψ), B ψ⟫_ℝ := phase_pair_neg_swap (B ψ) (A ψ)
  simp only [sub_apply, ContinuousLinearMap.comp_apply,
    inner_sub_right, hAB, hBA]
  ring

/-- Arbitrarily centered real fluctuations retain the same commutator
expectation.  This is the bridge consumed by the uncertainty owner. -/
theorem twice_centered_phase_pair_eq_commutator
    (A B : EndH) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAI : A.comp Iop = (Iop).comp A)
    (hBI : B.comp Iop = (Iop).comp B)
    (a b : ℝ) (ψ : H₂) :
    2 * ⟪Iop (centeredVector A a ψ), centeredVector B b ψ⟫_ℝ =
      ⟪Iop ψ, (A.comp B - B.comp A) ψ⟫_ℝ := by
  rw [phase_pair_centered_eq A B hA hB hAI hBI a b ψ]
  exact twice_phase_pair_eq_commutator A B hA hB hAI hBI ψ

/-- Observable-coordinate mixing transforms the full ordered commutator
tensor by a double coefficient sum.  No two observables are assumed to
commute, and no signature is imposed on the coordinate indices. -/
theorem commutator_linearCombinations
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → EndH) (B : κ → EndH) (r : ι → ℝ) (s : κ → ℝ) :
    (∑ i, r i • A i).comp (∑ j, s j • B j) -
        (∑ j, s j • B j).comp (∑ i, r i • A i) =
      ∑ i, ∑ j, (r i * s j) • ((A i).comp (B j) - (B j).comp (A i)) := by
  have hforward :
      (∑ i, r i • A i).comp (∑ j, s j • B j) =
        ∑ i, ∑ j, (r i * s j) • (A i).comp (B j) := by
    rw [ContinuousLinearMap.finsetSum_comp]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ContinuousLinearMap.comp_finsetSum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul]
  have hbackward :
      (∑ j, s j • B j).comp (∑ i, r i • A i) =
        ∑ i, ∑ j, (r i * s j) • (B j).comp (A i) := by
    calc
      _ = ∑ j, ∑ i, (s j * r i) • (B j).comp (A i) := by
        rw [ContinuousLinearMap.finsetSum_comp]
        apply Finset.sum_congr rfl
        intro j hj
        rw [ContinuousLinearMap.comp_finsetSum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul]
      _ = ∑ i, ∑ j, (s j * r i) • (B j).comp (A i) := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [mul_comm (s j) (r i)]
  rw [hforward, hbackward, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  exact (smul_sub (r i * s j) ((A i).comp (B j)) ((B j).comp (A i))).symm

end InfoGeometry.Krein.PhaseLinearObservableCommutator
