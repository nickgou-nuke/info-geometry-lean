/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.TripotentIntegerGrading
import Mathlib.Algebra.Ring.Action.ConjAct

/-!
# Actual grade transport and composite-generator cancellation

Algebra automorphisms transporting `S` transport its native homogeneous
submodules. Reversing `S` reverses the integer degree; an arbitrary reversing
unit suffices, with no assumption that its square is one. This does not
classify the full normalizer of degree zero.

For inhomogeneous factors, centralization by their product is equivalent to
vanishing of each sum of terms of a fixed nonzero total degree. Individual
products in such a sum need not vanish.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.TripotentGradeTransport

open InfoGeometry.Physics.Algebra
open InfoGeometry.Core.TripotentAdjoint

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The existing homogeneous submodules are covariant under an actual
algebra automorphism, including when the grading element moves. -/
theorem algEquiv_mem_adGrade_iff (f : A ≃ₐ[ℝ] A) (S X : A) (k : ℤ) :
    f X ∈ adGrade (f S) k ↔ X ∈ adGrade S k := by
  rw [mem_adGrade_iff, mem_adGrade_iff]
  have heq : adOp (f S) (f X) = f (adOp S X) := by simp [adOp]
  rw [heq, ← map_smul f (k : ℝ) X]
  exact f.injective.eq_iff

/-- A stationary grading element gives grade preservation for any actual
algebra automorphism. This implication requires no analytic generator. -/
theorem fixed_algEquiv_mem_adGrade_iff (f : A ≃ₐ[ℝ] A) {S : A}
    (hf : f S = S) (X : A) (k : ℤ) :
    f X ∈ adGrade S k ↔ X ∈ adGrade S k := by
  simpa only [hf] using algEquiv_mem_adGrade_iff f S X k

/-- Replacing the grader by its negative reverses the integer degree. -/
theorem mem_adGrade_neg_grader_iff (S X : A) (k : ℤ) :
    X ∈ adGrade (-S) k ↔ X ∈ adGrade S (-k) := by
  rw [mem_adGrade_iff, mem_adGrade_iff]
  have heq : adOp (-S) X = -adOp S X := by simp [adOp]; abel
  rw [heq, Int.cast_neg, neg_smul]
  exact neg_eq_iff_eq_neg

/-- A reversing algebra automorphism identifies the two opposite grades. -/
theorem reversing_algEquiv_mem_iff (f : A ≃ₐ[ℝ] A) {S : A}
    (hf : f S = -S) (X : A) (k : ℤ) :
    f X ∈ adGrade S (-k) ↔ X ∈ adGrade S k := by
  rw [← mem_adGrade_neg_grader_iff, ← hf]
  exact algEquiv_mem_adGrade_iff f S X k

/-- The previous identification is equality of native mapped submodules,
not only a forward inclusion. -/
theorem reversing_algEquiv_map_adGrade (f : A ≃ₐ[ℝ] A) {S : A}
    (hf : f S = -S) (k : ℤ) :
    (adGrade S k).map f.toLinearMap = adGrade S (-k) := by
  ext Y
  obtain ⟨X, rfl⟩ := f.surjective Y
  constructor
  · rintro ⟨Z, hZ, hZX⟩
    have hZX' : Z = X := f.injective hZX
    subst Z
    exact (reversing_algEquiv_mem_iff f hf X k).mpr hZ
  · intro hX
    exact ⟨X, (reversing_algEquiv_mem_iff f hf X k).mp hX, rfl⟩

/-- Conjugation by a genuine unit as a native algebra equivalence. -/
def unitConjugation (u : Aˣ) : A ≃ₐ[ℝ] A :=
  MulSemiringAction.toAlgEquiv ℝ A (ConjAct.toConjAct u)

/-- Commutation of an actual unit with `S` makes its conjugation preserve
every grade. A unit obtained from a spectral construction can use this
algebraic conclusion once that construction has proved commutation. -/
theorem commuting_unit_preserves_adGrade (u : Aˣ) {S : A}
    (hu : Commute (u : A) S) (X : A) (k : ℤ) :
    unitConjugation u X ∈ adGrade S k ↔ X ∈ adGrade S k := by
  apply fixed_algEquiv_mem_adGrade_iff
  change (u : A) * S * (↑u⁻¹ : A) = S
  rw [hu.eq]
  simp [mul_assoc]

/-- Anticommutation of a unit and the grader gives actual grade reversal. -/
theorem anticommuting_unit_map_adGrade (u : Aˣ) {S : A}
    (hu : (u : A) * S + S * (u : A) = 0) (k : ℤ) :
    (adGrade S k).map (unitConjugation u).toLinearMap = adGrade S (-k) := by
  apply reversing_algEquiv_map_adGrade
  have heq : (u : A) * S = -(S * (u : A)) := eq_neg_iff_add_eq_zero.mpr hu
  change (u : A) * S * (↑u⁻¹ : A) = -S
  rw [heq]
  simp [mul_assoc]

/-- A reversing unit cannot centralize a nonzero grader in a real algebra. -/
theorem anticommuting_unit_not_commute (u : Aˣ) {S : A} (hS : S ≠ 0)
    (hu : (u : A) * S + S * (u : A) = 0) : ¬Commute (u : A) S := by
  intro hc
  have htwo : (2 : ℝ) • ((u : A) * S) = 0 := by
    simpa only [two_smul, ← hc.eq] using hu
  have hprod : (u : A) * S = 0 :=
    (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  apply hS
  have h := congrArg (fun X : A => (↑u⁻¹ : A) * X) hprod
  simpa [mul_assoc] using h

/-- A sum form of the existing five-projector reconstruction. -/
theorem sum_fiveGradeProjector (S X : A) :
    ∑ k : FiveGrade, fiveGradeProjector S k X = X := by
  have hu : (Finset.univ : Finset FiveGrade) =
      {.negTwo, .negOne, .zero, .posOne, .posTwo} := by decide
  have hrec := fiveGrade_recompose_decompose S X
  change fiveGradeProjector S .negTwo X + fiveGradeProjector S .negOne X +
    fiveGradeProjector S .zero X + fiveGradeProjector S .posOne X +
    fiveGradeProjector S .posTwo X = X at hrec
  simpa [hu, add_assoc] using hrec

/-- Each term in a component product has exactly its sum degree. -/
theorem fiveGradeProjector_product_components {S : A} (hS : S * S * S = S)
    (J K : A) (i j k : FiveGrade) :
    fiveGradeProjector S k (fiveGradeProjector S i J * fiveGradeProjector S j K) =
      if fiveGradeValue i + fiveGradeValue j = fiveGradeValue k then
        fiveGradeProjector S i J * fiveGradeProjector S j K else 0 := by
  by_cases hsum : fiveGradeValue i + fiveGradeValue j = fiveGradeValue k
  · rw [if_pos hsum]
    exact (mem_fiveGradeRange_iff_projector_fixed hS k).mp
      (mul_mem_fiveGradeRange hS hsum ⟨J, rfl⟩ ⟨K, rfl⟩)
  · rw [if_neg hsum]
    apply fiveGradeProjector_eq_zero_of_eigen_ne hS
      (Module.End.mem_eigenspace_iff.mp
        (mul_mem_eigenspace_add
          (by rw [← fiveGradeRange_eq_eigenspace hS]; exact ⟨J, rfl⟩)
          (by rw [← fiveGradeRange_eq_eigenspace hS]; exact ⟨K, rfl⟩)))
    intro heq
    apply hsum
    have hreal : (fiveGradeValue i : ℝ) + (fiveGradeValue j : ℝ) =
        (fiveGradeValue k : ℝ) := heq.symm
    exact_mod_cast hreal

/-- Actual component expansion of an inhomogeneous product. -/
theorem fiveGradeProjector_mul_expansion {S : A} (hS : S * S * S = S)
    (J K : A) (k : FiveGrade) :
    fiveGradeProjector S k (J * K) =
      ∑ i : FiveGrade, ∑ j : FiveGrade,
        if fiveGradeValue i + fiveGradeValue j = fiveGradeValue k then
          fiveGradeProjector S i J * fiveGradeProjector S j K else 0 := by
  calc
    fiveGradeProjector S k (J * K) = fiveGradeProjector S k
        ((∑ i : FiveGrade, fiveGradeProjector S i J) *
          (∑ j : FiveGrade, fiveGradeProjector S j K)) := by
      rw [sum_fiveGradeProjector, sum_fiveGradeProjector]
    _ = ∑ i : FiveGrade, ∑ j : FiveGrade,
        fiveGradeProjector S k (fiveGradeProjector S i J * fiveGradeProjector S j K) := by
      simp only [Finset.sum_mul, Finset.mul_sum, map_sum]
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact fiveGradeProjector_product_components hS J K i j k

/-- Centralization means all four nonzero homogeneous components vanish. -/
theorem commute_iff_nonzero_components_vanish {S H : A} (hS : S * S * S = S) :
    Commute S H ↔ ∀ k : FiveGrade, k ≠ .zero → fiveGradeProjector S k H = 0 := by
  constructor
  · intro hc k hk
    have heig : LieAlgebra.ad ℝ A S H = (0 : ℝ) • H := by
      change S * H - H * S = (0 : ℝ) • H
      rw [hc.eq, sub_self, zero_smul]
    apply fiveGradeProjector_eq_zero_of_eigen_ne hS heig k
    cases k <;> first | contradiction | norm_num [fiveGradeValue]
  · intro hz
    have hrec := fiveGrade_recompose_decompose S H
    change fiveGradeProjector S .negTwo H + fiveGradeProjector S .negOne H +
      fiveGradeProjector S .zero H + fiveGradeProjector S .posOne H +
      fiveGradeProjector S .posTwo H = H at hrec
    have hzero : fiveGradeProjector S .zero H = H := by
      simpa only [hz .negTwo (by decide), hz .negOne (by decide),
        hz .posOne (by decide), hz .posTwo (by decide), zero_add, add_zero] using hrec
    have heig := mem_fiveGradeRange_implies_adjoint_eigen hS .zero (x := H)
      ((mem_fiveGradeRange_iff_projector_fixed hS .zero).mpr hzero)
    change S * H - H * S = (fiveGradeValue .zero : ℝ) • H at heig
    change S * H = H * S
    simpa only [fiveGradeValue, Int.cast_zero, zero_smul, sub_eq_zero] using heig

/-- The composite criterion groups terms by total degree, allowing
cancellation within a degree. It does not force individual products to vanish. -/
theorem commute_product_iff_grouped_sums_vanish {S : A} (hS : S * S * S = S)
    (J K : A) :
    Commute S (J * K) ↔ ∀ k : FiveGrade, k ≠ .zero →
      (∑ i : FiveGrade, ∑ j : FiveGrade,
        if fiveGradeValue i + fiveGradeValue j = fiveGradeValue k then
          fiveGradeProjector S i J * fiveGradeProjector S j K else 0) = 0 := by
  rw [commute_iff_nonzero_components_vanish hS]
  simp only [fiveGradeProjector_mul_expansion hS]

end InfoGeometry.OperatorAlgebra.TripotentGradeTransport
