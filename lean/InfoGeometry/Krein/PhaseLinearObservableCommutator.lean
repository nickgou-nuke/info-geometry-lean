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
operator may be any bounded real operator with an alternating phase pairing.
The historical `complex_i` APIs specialize the generic identities without
assuming a square law. For Hilbert-self-adjoint operators
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

/-- The skew Hilbert adjoint gives the alternating phase pairing directly.
The phase square is irrelevant to this identity. -/
theorem phase_pair_neg_swap_of_star_eq_neg
    (P : EndH) (hPstar : star P = -P) (x y : H₂) :
    ⟪P x, y⟫_ℝ = -⟪P y, x⟫_ℝ := by
  calc
    ⟪P x, y⟫_ℝ = ⟪x, (star P) y⟫_ℝ := (P.adjoint_inner_right x y).symm
    _ = -⟪P y, x⟫_ℝ := by
      rw [hPstar]
      simp only [ContinuousLinearMap.neg_apply, inner_neg_right,
        real_inner_comm x (P y)]

/-- A self-adjoint observable commuting with any skew phase has zero
phase pairing with its state. -/
theorem phase_pair_observable_self_zero_of_phase
    (P : EndH)
    (hPskew : ∀ x y : H₂, ⟪P x, y⟫_ℝ = -⟪P y, x⟫_ℝ)
    (A : EndH) (hA : IsSelfAdjoint A)
    (hAP : A.comp P = P.comp A) (ψ : H₂) :
    ⟪P ψ, A ψ⟫_ℝ = 0 := by
  have hcomm : A (P ψ) = P (A ψ) :=
    congrArg (fun T : EndH => T ψ) hAP
  have hsym : ⟪P ψ, A ψ⟫_ℝ = ⟪P (A ψ), ψ⟫_ℝ := by
    calc
      ⟪P ψ, A ψ⟫_ℝ = ⟪A (P ψ), ψ⟫_ℝ :=
        (hA.isSymmetric (P ψ) ψ).symm
      _ = ⟪P (A ψ), ψ⟫_ℝ := by rw [hcomm]
  have hskew := hPskew ψ (A ψ)
  linarith

/-- Arbitrary real shifts preserve the pairing for any skew phase
commuting with both self-adjoint observables. -/
theorem phase_pair_centered_eq_of_phase
    (P : EndH)
    (hPskew : ∀ x y : H₂, ⟪P x, y⟫_ℝ = -⟪P y, x⟫_ℝ)
    (A B : EndH) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAP : A.comp P = P.comp A) (hBP : B.comp P = P.comp B)
    (a b : ℝ) (ψ : H₂) :
    ⟪P (centeredVector A a ψ), centeredVector B b ψ⟫_ℝ =
      ⟪P (A ψ), B ψ⟫_ℝ := by
  have hA0 : ⟪P (A ψ), ψ⟫_ℝ = 0 := by
    rw [hPskew, phase_pair_observable_self_zero_of_phase P hPskew A hA hAP ψ,
      neg_zero]
  have hB0 := phase_pair_observable_self_zero_of_phase P hPskew B hB hBP ψ
  have hψ0 := InternalPhaseGram.phase_pair_self_zero_of_neg_swap P hPskew ψ
  simp only [centeredVector, map_sub, map_smul, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, hA0, hB0, hψ0,
    mul_zero, sub_zero]

/-- The ordered commutator identity requires skew pairing, self-adjointness,
and phase commutation, but no phase square or normalization assumption. -/
theorem twice_phase_pair_eq_commutator_of_phase
    (P : EndH)
    (hPskew : ∀ x y : H₂, ⟪P x, y⟫_ℝ = -⟪P y, x⟫_ℝ)
    (A B : EndH) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAP : A.comp P = P.comp A) (hBP : B.comp P = P.comp B) (ψ : H₂) :
    2 * ⟪P (A ψ), B ψ⟫_ℝ =
      ⟪P ψ, (A.comp B - B.comp A) ψ⟫_ℝ := by
  have hcommA : A (P ψ) = P (A ψ) :=
    congrArg (fun T : EndH => T ψ) hAP
  have hcommB : B (P ψ) = P (B ψ) :=
    congrArg (fun T : EndH => T ψ) hBP
  have hAB : ⟪P ψ, A (B ψ)⟫_ℝ = ⟪P (A ψ), B ψ⟫_ℝ := by
    calc
      ⟪P ψ, A (B ψ)⟫_ℝ = ⟪A (P ψ), B ψ⟫_ℝ :=
        (hA.isSymmetric (P ψ) (B ψ)).symm
      _ = ⟪P (A ψ), B ψ⟫_ℝ := by rw [hcommA]
  have hBA : ⟪P ψ, B (A ψ)⟫_ℝ = -⟪P (A ψ), B ψ⟫_ℝ := by
    calc
      ⟪P ψ, B (A ψ)⟫_ℝ = ⟪B (P ψ), A ψ⟫_ℝ :=
        (hB.isSymmetric (P ψ) (A ψ)).symm
      _ = ⟪P (B ψ), A ψ⟫_ℝ := by rw [hcommB]
      _ = -⟪P (A ψ), B ψ⟫_ℝ := hPskew (B ψ) (A ψ)
  simp only [sub_apply, ContinuousLinearMap.comp_apply,
    inner_sub_right, hAB, hBA]
  ring

/-- The actual commutator readout is twice the arbitrarily shifted
phase pairing for any admissible real phase. -/
theorem twice_centered_phase_pair_eq_commutator_of_phase
    (P : EndH)
    (hPskew : ∀ x y : H₂, ⟪P x, y⟫_ℝ = -⟪P y, x⟫_ℝ)
    (A B : EndH) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAP : A.comp P = P.comp A) (hBP : B.comp P = P.comp B)
    (a b : ℝ) (ψ : H₂) :
    2 * ⟪P (centeredVector A a ψ), centeredVector B b ψ⟫_ℝ =
      ⟪P ψ, (A.comp B - B.comp A) ψ⟫_ℝ := by
  rw [phase_pair_centered_eq_of_phase P hPskew A B hA hB hAP hBP a b ψ]
  exact twice_phase_pair_eq_commutator_of_phase P hPskew A B hA hB hAP hBP ψ

/-- A self-adjoint observable that preserves the internal phase has zero
phase pairing with the state in its expectation slot. -/
theorem phase_pair_observable_self_zero
    (A : EndH) (hA : IsSelfAdjoint A)
    (hAI : A.comp Iop = (Iop).comp A) (ψ : H₂) :
    ⟪Iop ψ, A ψ⟫_ℝ = 0 := by
  exact phase_pair_observable_self_zero_of_phase Iop
    (fun u v => phase_pair_neg_swap u v) A hA hAI ψ

/-- Real centering shifts do not change the phase pairing of self-adjoint,
phase-preserving observables. -/
theorem phase_pair_centered_eq
    (A B : EndH) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAI : A.comp Iop = (Iop).comp A)
    (hBI : B.comp Iop = (Iop).comp B)
    (a b : ℝ) (ψ : H₂) :
    ⟪Iop (centeredVector A a ψ), centeredVector B b ψ⟫_ℝ =
      ⟪Iop (A ψ), B ψ⟫_ℝ := by
  exact phase_pair_centered_eq_of_phase Iop
    (fun u v => phase_pair_neg_swap u v) A B hA hB hAI hBI a b ψ

/-- The real phase pairing reads the actual ordered commutator. -/
theorem twice_phase_pair_eq_commutator
    (A B : EndH) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAI : A.comp Iop = (Iop).comp A)
    (hBI : B.comp Iop = (Iop).comp B) (ψ : H₂) :
    2 * ⟪Iop (A ψ), B ψ⟫_ℝ =
      ⟪Iop ψ, (A.comp B - B.comp A) ψ⟫_ℝ := by
  exact twice_phase_pair_eq_commutator_of_phase Iop
    (fun u v => phase_pair_neg_swap u v) A B hA hB hAI hBI ψ

/-- Arbitrarily centered real fluctuations retain the same commutator
expectation.  This is the bridge consumed by the uncertainty owner. -/
theorem twice_centered_phase_pair_eq_commutator
    (A B : EndH) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAI : A.comp Iop = (Iop).comp A)
    (hBI : B.comp Iop = (Iop).comp B)
    (a b : ℝ) (ψ : H₂) :
    2 * ⟪Iop (centeredVector A a ψ), centeredVector B b ψ⟫_ℝ =
      ⟪Iop ψ, (A.comp B - B.comp A) ψ⟫_ℝ := by
  exact twice_centered_phase_pair_eq_commutator_of_phase Iop
    (fun u v => phase_pair_neg_swap u v) A B hA hB hAI hBI a b ψ

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
    simp only [ContinuousLinearMap.finsetSum_comp,
      ContinuousLinearMap.comp_finsetSum, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_smul, smul_smul]
  have hbackward :
      (∑ j, s j • B j).comp (∑ i, r i • A i) =
        ∑ i, ∑ j, (r i * s j) • (B j).comp (A i) := by
    simp only [ContinuousLinearMap.finsetSum_comp,
      ContinuousLinearMap.comp_finsetSum, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_smul, smul_smul]
    rw [Finset.sum_comm]
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
