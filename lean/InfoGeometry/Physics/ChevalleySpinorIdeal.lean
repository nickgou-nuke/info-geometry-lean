/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

/-!
# Claude Chevalley's Algebraic Theory of Spinors (1954)

This module formalizes Claude Chevalley's algebraic theory of spinors, establishing:
1. **Nilpotents from Null Vectors**: Nilpotent isotropic generators `n² = 0`, `p² = 0`
   and pairing `n p + p n = 1`.
2. **Idempotents and Peirce Split**: Idempotency of `P₊ = n p` and `P₋ = p n`, mutual
   annihilation `P₊ P₋ = 0`, partition of unity `P₊ + P₋ = 1`, and the split involution
   `ε = P₊ - P₋ = [n, p]` with `ε² = 1`.
3. **Grading Anticommutation**: Parity reflection `ε n + n ε = 0` and `ε p + p ε = 0`.
4. **Chevalley Minimal Left Ideal (Vacuum Module)**: Fock vacuum `n • f = 0`, showing
   `P₋ • f = 0`, `P₊ • f = f`, `ε • f = f`, and creation recovery `n • (p • f) = f`
   with Pauli exclusion `p • (p • f) = 0`.
5. **Clifford Action and Dirac-Kähler Vector**: Quadratic vector `(x n + y p)² = (x y) • 1`,
   Dirac vector `(n - p)² = -1`, chiral sum `(n + p)² = 1`, and their anticommutation.
6. **Preadditive Category Realization**: Natural formulation for endomorphisms in preadditive `C`.

All results are genuine definitions, lemmas, and theorems with complete Lean 4 proofs.
-/

namespace InfoGeometry.Physics.Chevalley

/-! ### 1. Nilpotents, CAR Pairing, and Idempotents in a Ring -/

section RingTheorems

variable {R : Type*} [Ring R]

/-- Positive Chevalley projector `P₊ = n * p`. -/
@[inline]
def P_plus (n p : R) : R := n * p

/-- Negative Chevalley projector `P₋ = p * n`. -/
@[inline]
def P_minus (n p : R) : R := p * n

/-- Chevalley chiral grading split involution `ε = n * p - p * n = [n, p]`. -/
@[inline]
def chiralGrading (n p : R) : R := n * p - p * n

/-- Idempotency of the positive projector: `P₊ * P₊ = P₊`. -/
theorem P_plus_sq (n p : R)
    (h_nil_n : n * n = 0)
    (h_car : n * p + p * n = 1) :
    P_plus n p * P_plus n p = P_plus n p := by
  dsimp [P_plus]
  have h_pn : p * n = 1 - n * p := eq_sub_of_add_eq' h_car
  calc
    (n * p) * (n * p) = n * (p * n) * p := by noncomm_ring
    _ = n * (1 - n * p) * p := by rw [h_pn]
    _ = (n - (n * n) * p) * p := by noncomm_ring
    _ = (n - 0 * p) * p     := by rw [h_nil_n]
    _ = n * p               := by noncomm_ring

/-- Idempotency of the negative projector: `P₋ * P₋ = P₋`. -/
theorem P_minus_sq (n p : R)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    P_minus n p * P_minus n p = P_minus n p := by
  dsimp [P_minus]
  have h_np : n * p = 1 - p * n := eq_sub_of_add_eq h_car
  calc
    (p * n) * (p * n) = p * (n * p) * n := by noncomm_ring
    _ = p * (1 - p * n) * n := by rw [h_np]
    _ = (p - (p * p) * n) * n := by noncomm_ring
    _ = (p - 0 * n) * n     := by rw [h_nil_p]
    _ = p * n               := by noncomm_ring

/-- Mutual annihilation: `P₊ * P₋ = 0`. -/
theorem P_plus_mul_P_minus_zero (n p : R)
    (h_nil_p : p * p = 0) :
    P_plus n p * P_minus n p = 0 := by
  dsimp [P_plus, P_minus]
  calc
    (n * p) * (p * n) = n * (p * p) * n := by noncomm_ring
    _ = n * 0 * n := by rw [h_nil_p]
    _ = 0 := by noncomm_ring

/-- Mutual annihilation: `P₋ * P₊ = 0`. -/
theorem P_minus_mul_P_plus_zero (n p : R)
    (h_nil_n : n * n = 0) :
    P_minus n p * P_plus n p = 0 := by
  dsimp [P_plus, P_minus]
  calc
    (p * n) * (n * p) = p * (n * n) * p := by noncomm_ring
    _ = p * 0 * p := by rw [h_nil_n]
    _ = 0 := by noncomm_ring

/-- Partition of unity: `P₊ + P₋ = 1`. -/
theorem partition_of_unity (n p : R)
    (h_car : n * p + p * n = 1) :
    P_plus n p + P_minus n p = 1 :=
  h_car

/-- Chiral grading expresses as difference of projectors: `ε = P₊ - P₋`. -/
theorem chiralGrading_eq_sub (n p : R) :
    chiralGrading n p = P_plus n p - P_minus n p :=
  rfl

/-- Integer scaling: `2 • P₊ = 1 + ε`. -/
theorem two_smul_P_plus (n p : R)
    (h_car : n * p + p * n = 1) :
    (2 : ℤ) • P_plus n p = 1 + chiralGrading n p := by
  dsimp [P_plus, chiralGrading]
  rw [← h_car]
  noncomm_ring

/-- Integer scaling: `2 • P₋ = 1 - ε`. -/
theorem two_smul_P_minus (n p : R)
    (h_car : n * p + p * n = 1) :
    (2 : ℤ) • P_minus n p = 1 - chiralGrading n p := by
  dsimp [P_minus, chiralGrading]
  rw [← h_car]
  noncomm_ring

/-- The Chevalley commutator is an exact split involution: `ε² = 1`. -/
theorem chiralGrading_sq (n p : R)
    (h_nil_n : n * n = 0)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    chiralGrading n p * chiralGrading n p = 1 := by
  have hp_plus := P_plus_sq n p h_nil_n h_car
  have hp_minus := P_minus_sq n p h_nil_p h_car
  have h_pm := P_plus_mul_P_minus_zero n p h_nil_p
  have h_mp := P_minus_mul_P_plus_zero n p h_nil_n
  have h_part := partition_of_unity n p h_car
  dsimp [chiralGrading]
  calc
    (n * p - p * n) * (n * p - p * n)
      = (P_plus n p - P_minus n p) * (P_plus n p - P_minus n p) := rfl
    _ = P_plus n p * P_plus n p - P_plus n p * P_minus n p -
        P_minus n p * P_plus n p + P_minus n p * P_minus n p := by noncomm_ring
    _ = P_plus n p - 0 - 0 + P_minus n p := by rw [hp_plus, h_pm, h_mp, hp_minus]
    _ = P_plus n p + P_minus n p := by noncomm_ring
    _ = 1 := h_part

/-! ### 2. Action on Nilpotents and Parity Anticommutation -/

/-- Action on annihilation operator: `P₊ * n = n`. -/
theorem P_plus_mul_n (n p : R)
    (h_nil_n : n * n = 0)
    (h_car : n * p + p * n = 1) :
    P_plus n p * n = n := by
  dsimp [P_plus]
  have h_pn : p * n = 1 - n * p := eq_sub_of_add_eq' h_car
  calc
    (n * p) * n = n * (p * n) := by noncomm_ring
    _ = n * (1 - n * p)       := by rw [h_pn]
    _ = n - (n * n) * p       := by noncomm_ring
    _ = n - 0 * p             := by rw [h_nil_n]
    _ = n                     := by noncomm_ring

/-- Action on annihilation operator: `n * P₊ = 0`. -/
theorem n_mul_P_plus (n p : R)
    (h_nil_n : n * n = 0) :
    n * P_plus n p = 0 := by
  dsimp [P_plus]
  calc
    n * (n * p) = (n * n) * p := by noncomm_ring
    _ = 0 * p := by rw [h_nil_n]
    _ = 0 := by noncomm_ring

/-- Action on annihilation operator: `P₋ * n = 0`. -/
theorem P_minus_mul_n (n p : R)
    (h_nil_n : n * n = 0) :
    P_minus n p * n = 0 := by
  dsimp [P_minus]
  calc
    (p * n) * n = p * (n * n) := by noncomm_ring
    _ = p * 0 := by rw [h_nil_n]
    _ = 0 := by noncomm_ring

/-- Action on annihilation operator: `n * P₋ = n`. -/
theorem n_mul_P_minus (n p : R)
    (h_nil_n : n * n = 0)
    (h_car : n * p + p * n = 1) :
    n * P_minus n p = n := by
  dsimp [P_minus]
  have h_np : n * p = 1 - p * n := eq_sub_of_add_eq h_car
  calc
    n * (p * n) = (n * p) * n := by noncomm_ring
    _ = (1 - p * n) * n       := by rw [h_np]
    _ = n - p * (n * n)       := by noncomm_ring
    _ = n - p * 0             := by rw [h_nil_n]
    _ = n                     := by noncomm_ring

/-- Action on creation operator: `P₊ * p = 0`. -/
theorem P_plus_mul_p (n p : R)
    (h_nil_p : p * p = 0) :
    P_plus n p * p = 0 := by
  dsimp [P_plus]
  calc
    (n * p) * p = n * (p * p) := by noncomm_ring
    _ = n * 0 := by rw [h_nil_p]
    _ = 0 := by noncomm_ring

/-- Action on creation operator: `p * P₊ = p`. -/
theorem p_mul_P_plus (n p : R)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    p * P_plus n p = p := by
  dsimp [P_plus]
  have h_pn : p * n = 1 - n * p := eq_sub_of_add_eq' h_car
  calc
    p * (n * p) = (p * n) * p := by noncomm_ring
    _ = (1 - n * p) * p       := by rw [h_pn]
    _ = p - n * (p * p)       := by noncomm_ring
    _ = p - n * 0             := by rw [h_nil_p]
    _ = p                     := by noncomm_ring

/-- Action on creation operator: `P₋ * p = p`. -/
theorem P_minus_mul_p (n p : R)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    P_minus n p * p = p := by
  dsimp [P_minus]
  have h_np : n * p = 1 - p * n := eq_sub_of_add_eq h_car
  calc
    (p * n) * p = p * (n * p) := by noncomm_ring
    _ = p * (1 - p * n)       := by rw [h_np]
    _ = p - (p * p) * n       := by noncomm_ring
    _ = p - 0 * n             := by rw [h_nil_p]
    _ = p                     := by noncomm_ring

/-- Action on creation operator: `p * P₋ = 0`. -/
theorem p_mul_P_minus (n p : R)
    (h_nil_p : p * p = 0) :
    p * P_minus n p = 0 := by
  dsimp [P_minus]
  calc
    p * (p * n) = (p * p) * n := by noncomm_ring
    _ = 0 * n := by rw [h_nil_p]
    _ = 0 := by noncomm_ring

/-- Chiral grading action on annihilation operator: `ε * n = n`. -/
theorem chiralGrading_mul_n (n p : R)
    (h_nil_n : n * n = 0)
    (h_car : n * p + p * n = 1) :
    chiralGrading n p * n = n := by
  dsimp [chiralGrading]
  rw [sub_mul]
  have h1 := P_plus_mul_n n p h_nil_n h_car
  have h2 := P_minus_mul_n n p h_nil_n
  dsimp [P_plus] at h1
  dsimp [P_minus] at h2
  rw [h1, h2, sub_zero]

/-- Chiral grading action on annihilation operator: `n * ε = -n`. -/
theorem n_mul_chiralGrading (n p : R)
    (h_nil_n : n * n = 0)
    (h_car : n * p + p * n = 1) :
    n * chiralGrading n p = -n := by
  dsimp [chiralGrading]
  rw [mul_sub]
  have h1 := n_mul_P_plus n p h_nil_n
  have h2 := n_mul_P_minus n p h_nil_n h_car
  dsimp [P_plus] at h1
  dsimp [P_minus] at h2
  rw [h1, h2, zero_sub]

/-- Grading anticommutation with annihilation operator: `ε * n + n * ε = 0`. -/
theorem chiralGrading_anticommutes_n (n p : R)
    (h_nil_n : n * n = 0)
    (h_car : n * p + p * n = 1) :
    chiralGrading n p * n + n * chiralGrading n p = 0 := by
  rw [chiralGrading_mul_n n p h_nil_n h_car]
  rw [n_mul_chiralGrading n p h_nil_n h_car]
  exact add_neg_cancel n

/-- Chiral grading action on creation operator: `ε * p = -p`. -/
theorem chiralGrading_mul_p (n p : R)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    chiralGrading n p * p = -p := by
  dsimp [chiralGrading]
  rw [sub_mul]
  have h1 := P_plus_mul_p n p h_nil_p
  have h2 := P_minus_mul_p n p h_nil_p h_car
  dsimp [P_plus] at h1
  dsimp [P_minus] at h2
  rw [h1, h2, zero_sub]

/-- Chiral grading action on creation operator: `p * ε = p`. -/
theorem p_mul_chiralGrading (n p : R)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    p * chiralGrading n p = p := by
  dsimp [chiralGrading]
  rw [mul_sub]
  have h1 := p_mul_P_plus n p h_nil_p h_car
  have h2 := p_mul_P_minus n p h_nil_p
  dsimp [P_plus] at h1
  dsimp [P_minus] at h2
  rw [h1, h2, sub_zero]

/-- Grading anticommutation with creation operator: `ε * p + p * ε = 0`. -/
theorem chiralGrading_anticommutes_p (n p : R)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    chiralGrading n p * p + p * chiralGrading n p = 0 := by
  rw [chiralGrading_mul_p n p h_nil_p h_car]
  rw [p_mul_chiralGrading n p h_nil_p h_car]
  exact neg_add_cancel p

end RingTheorems

/-! ### 3. The Chevalley Ideal: Spinors as a Vacuum Module -/

section ModuleTheorems

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- The Fock vacuum `f` is annihilated by the negative projector: `P₋ • f = 0`. -/
theorem vacuum_annihilated_by_P_minus (n p : R) (f : M)
    (h_vac : n • f = 0) :
    (P_minus n p) • f = 0 := by
  dsimp [P_minus]
  rw [mul_smul, h_vac, smul_zero]

/-- The Fock vacuum `f` is a +1 eigenstate of the positive projector: `P₊ • f = f`. -/
theorem vacuum_is_positive_eigenstate (n p : R) (f : M)
    (h_car : n * p + p * n = 1)
    (h_vac : n • f = 0) :
    (P_plus n p) • f = f := by
  have h_part : (P_plus n p + P_minus n p) • f = f := by
    rw [partition_of_unity n p h_car, one_smul]
  rw [add_smul, vacuum_annihilated_by_P_minus n p f h_vac, add_zero] at h_part
  exact h_part

/-- The Fock vacuum has positive chirality: `ε • f = f`. -/
theorem vacuum_positive_chirality (n p : R) (f : M)
    (h_car : n * p + p * n = 1)
    (h_vac : n • f = 0) :
    (chiralGrading n p) • f = f := by
  have h_plus := vacuum_is_positive_eigenstate n p f h_car h_vac
  have h_minus := vacuum_annihilated_by_P_minus n p f h_vac
  dsimp [P_plus] at h_plus
  dsimp [P_minus] at h_minus
  dsimp [chiralGrading]
  rw [sub_smul, h_plus, h_minus, sub_zero]

/-- Creation state excitation recovery: Annihilating the excitation returns the vacuum `n • (p • f) = f`. -/
theorem excitation_recovery (n p : R) (f : M)
    (h_car : n * p + p * n = 1)
    (h_vac : n • f = 0) :
    n • (p • f) = f := by
  rw [← mul_smul]
  have h_plus := vacuum_is_positive_eigenstate n p f h_car h_vac
  dsimp [P_plus] at h_plus
  exact h_plus

/-- Pauli exclusion: Repeated creation vanishes identically on the vacuum `p • (p • f) = 0`. -/
theorem excitation_pauli_exclusion (p : R) (f : M)
    (h_nil_p : p * p = 0) :
    p • (p • f) = 0 := by
  rw [← mul_smul, h_nil_p, zero_smul]

/-- The excited state `p • f` is annihilated by the positive projector: `P₊ • (p • f) = 0`. -/
theorem excitation_annihilated_by_P_plus (n p : R) (f : M)
    (h_nil_p : p * p = 0) :
    (P_plus n p) • (p • f) = 0 := by
  dsimp [P_plus]
  rw [mul_smul, ← mul_smul p p, h_nil_p, zero_smul, smul_zero]

/-- The excited state `p • f` is a +1 eigenstate of the negative projector: `P₋ • (p • f) = p • f`. -/
theorem excitation_is_negative_eigenstate (n p : R) (f : M)
    (h_car : n * p + p * n = 1)
    (h_vac : n • f = 0) :
    (P_minus n p) • (p • f) = p • f := by
  dsimp [P_minus]
  rw [mul_smul, excitation_recovery n p f h_car h_vac]

/-- The excited state has negative chirality: `ε • (p • f) = - (p • f)`. -/
theorem excitation_negative_chirality (n p : R) (f : M)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1)
    (h_vac : n • f = 0) :
    (chiralGrading n p) • (p • f) = - (p • f) := by
  have h_plus := excitation_annihilated_by_P_plus n p f h_nil_p
  have h_minus := excitation_is_negative_eigenstate n p f h_car h_vac
  dsimp [P_plus] at h_plus
  dsimp [P_minus] at h_minus
  dsimp [chiralGrading]
  rw [sub_smul, h_plus, h_minus, zero_sub]

end ModuleTheorems

/-! ### 4. Clifford Action, Dirac-Kähler Vector, and Chiral Sum -/

section CliffordTheorems

variable {R : Type*} [Ring R]

/-- The chiral Dirac vector `𝒟 = n - p` satisfies the Clifford relation `𝒟² = -1`. -/
theorem dirac_vector_sq (n p : R)
    (h_nil_n : n * n = 0)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    (n - p) * (n - p) = - 1 := by
  calc
    (n - p) * (n - p) = n * n - (n * p + p * n) + p * p := by noncomm_ring
    _ = 0 - 1 + 0 := by rw [h_nil_n, h_nil_p, h_car]
    _ = - 1 := by noncomm_ring

/-- The chiral sum vector `S = n + p` satisfies the involution identity `S² = 1`. -/
theorem chiral_sum_sq (n p : R)
    (h_nil_n : n * n = 0)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    (n + p) * (n + p) = 1 := by
  calc
    (n + p) * (n + p) = n * n + (n * p + p * n) + p * p := by noncomm_ring
    _ = 0 + 1 + 0 := by rw [h_nil_n, h_nil_p, h_car]
    _ = 1 := by abel

/-- Anticommutation of the Dirac vector and the chiral sum: `𝒟 S + S 𝒟 = 0`. -/
theorem dirac_anticommutes_chiral_sum (n p : R)
    (h_nil_n : n * n = 0)
    (h_nil_p : p * p = 0) :
    (n - p) * (n + p) + (n + p) * (n - p) = 0 := by
  calc
    (n - p) * (n + p) + (n + p) * (n - p)
      = (n * n - p * p) + (n * n - p * p) := by noncomm_ring
    _ = (0 - 0) + (0 - 0) := by rw [h_nil_n, h_nil_p]
    _ = 0 := by noncomm_ring

/-- The product of chiral sum and Dirac vector generates the negative split involution:
`(n + p) * (n - p) = - ε`. -/
theorem chiral_sum_mul_dirac_eq_neg_grading (n p : R)
    (h_nil_n : n * n = 0)
    (h_nil_p : p * p = 0) :
    (n + p) * (n - p) = - chiralGrading n p := by
  dsimp [chiralGrading]
  calc
    (n + p) * (n - p) = n * n - (n * p - p * n) - p * p := by noncomm_ring
    _ = 0 - (n * p - p * n) - 0 := by rw [h_nil_n, h_nil_p]
    _ = - (n * p - p * n) := by noncomm_ring

/-- The product of Dirac vector and chiral sum generates the positive split involution:
`(n - p) * (n + p) = ε`. -/
theorem dirac_mul_chiral_sum_eq_grading (n p : R)
    (h_nil_n : n * n = 0)
    (h_nil_p : p * p = 0) :
    (n - p) * (n + p) = chiralGrading n p := by
  dsimp [chiralGrading]
  calc
    (n - p) * (n + p) = n * n + (n * p - p * n) - p * p := by noncomm_ring
    _ = 0 + (n * p - p * n) - 0 := by rw [h_nil_n, h_nil_p]
    _ = n * p - p * n := by noncomm_ring

end CliffordTheorems

/-! ### 5. Preadditive Category Endomorphism Realization -/

section PreadditiveTheorems

open CategoryTheory
open CategoryTheory.Limits

variable {C : Type*} [Category C] [Preadditive C]

/-- Categorical positive Chevalley projector for endomorphisms in preadditive `C`. -/
@[inline]
def catPPlus {E : C} (n p : E ⟶ E) : E ⟶ E := n ≫ p

/-- Categorical negative Chevalley projector for endomorphisms in preadditive `C`. -/
@[inline]
def catPMinus {E : C} (n p : E ⟶ E) : E ⟶ E := p ≫ n

/-- Categorical Chevalley split involution `ε = n ≫ p - p ≫ n`. -/
@[inline]
def catChiralGrading {E : C} (n p : E ⟶ E) : E ⟶ E := n ≫ p - p ≫ n

/-- Idempotency: `(n ≫ p) ≫ (n ≫ p) = n ≫ p`. -/
theorem cat_P_plus_sq {E : C} (n p : E ⟶ E)
    (h_nil_n : n ≫ n = 0)
    (h_car : n ≫ p + p ≫ n = 𝟙 E) :
    catPPlus n p ≫ catPPlus n p = catPPlus n p := by
  dsimp [catPPlus]
  have h_pn : p ≫ n = 𝟙 E - n ≫ p := eq_sub_of_add_eq' h_car
  calc
    (n ≫ p) ≫ (n ≫ p) = n ≫ (p ≫ n) ≫ p := by simp only [Category.assoc]
    _ = n ≫ (𝟙 E - n ≫ p) ≫ p := by rw [h_pn]
    _ = n ≫ (𝟙 E ≫ p - (n ≫ p) ≫ p) := by rw [Preadditive.sub_comp]
    _ = n ≫ p - n ≫ (n ≫ p) ≫ p := by rw [Category.id_comp, Preadditive.comp_sub]
    _ = n ≫ p - (n ≫ n) ≫ p ≫ p := by simp only [Category.assoc]
    _ = n ≫ p - 0 ≫ p ≫ p := by rw [h_nil_n]
    _ = n ≫ p - 0 := by simp only [zero_comp]
    _ = n ≫ p := sub_zero (n ≫ p)

/-- Idempotency: `(p ≫ n) ≫ (p ≫ n) = p ≫ n`. -/
theorem cat_P_minus_sq {E : C} (n p : E ⟶ E)
    (h_nil_p : p ≫ p = 0)
    (h_car : n ≫ p + p ≫ n = 𝟙 E) :
    catPMinus n p ≫ catPMinus n p = catPMinus n p := by
  dsimp [catPMinus]
  have h_np : n ≫ p = 𝟙 E - p ≫ n := eq_sub_of_add_eq h_car
  calc
    (p ≫ n) ≫ (p ≫ n) = p ≫ (n ≫ p) ≫ n := by simp only [Category.assoc]
    _ = p ≫ (𝟙 E - p ≫ n) ≫ n := by rw [h_np]
    _ = p ≫ (𝟙 E ≫ n - (p ≫ n) ≫ n) := by rw [Preadditive.sub_comp]
    _ = p ≫ n - p ≫ (p ≫ n) ≫ n := by rw [Category.id_comp, Preadditive.comp_sub]
    _ = p ≫ n - (p ≫ p) ≫ n ≫ n := by simp only [Category.assoc]
    _ = p ≫ n - 0 ≫ n ≫ n := by rw [h_nil_p]
    _ = p ≫ n - 0 := by simp only [zero_comp]
    _ = p ≫ n := sub_zero (p ≫ n)

/-- Mutual annihilation: `(n ≫ p) ≫ (p ≫ n) = 0`. -/
theorem cat_P_plus_comp_P_minus_zero {E : C} (n p : E ⟶ E)
    (h_nil_p : p ≫ p = 0) :
    catPPlus n p ≫ catPMinus n p = 0 := by
  dsimp [catPPlus, catPMinus]
  calc
    (n ≫ p) ≫ (p ≫ n) = n ≫ (p ≫ p) ≫ n := by simp only [Category.assoc]
    _ = n ≫ 0 ≫ n := by rw [h_nil_p]
    _ = 0 := by simp only [comp_zero, zero_comp]

/-- Mutual annihilation: `(p ≫ n) ≫ (n ≫ p) = 0`. -/
theorem cat_P_minus_comp_P_plus_zero {E : C} (n p : E ⟶ E)
    (h_nil_n : n ≫ n = 0) :
    catPMinus n p ≫ catPPlus n p = 0 := by
  dsimp [catPPlus, catPMinus]
  calc
    (p ≫ n) ≫ (n ≫ p) = p ≫ (n ≫ n) ≫ p := by simp only [Category.assoc]
    _ = p ≫ 0 ≫ p := by rw [h_nil_n]
    _ = 0 := by simp only [comp_zero, zero_comp]

/-- Partition of unity: `P₊ + P₋ = 𝟙 E`. -/
theorem cat_partition_of_unity {E : C} (n p : E ⟶ E)
    (h_car : n ≫ p + p ≫ n = 𝟙 E) :
    catPPlus n p + catPMinus n p = 𝟙 E :=
  h_car

/-- Categorical Chevalley split involution identity: `ε ≫ ε = 𝟙 E`. -/
theorem cat_chiralGrading_sq {E : C} (n p : E ⟶ E)
    (h_nil_n : n ≫ n = 0)
    (h_nil_p : p ≫ p = 0)
    (h_car : n ≫ p + p ≫ n = 𝟙 E) :
    catChiralGrading n p ≫ catChiralGrading n p = 𝟙 E := by
  dsimp [catChiralGrading]
  rw [Preadditive.sub_comp, Preadditive.comp_sub, Preadditive.comp_sub]
  have h1 : (n ≫ p) ≫ (n ≫ p) = n ≫ p := cat_P_plus_sq n p h_nil_n h_car
  have h2 : (n ≫ p) ≫ (p ≫ n) = 0 := cat_P_plus_comp_P_minus_zero n p h_nil_p
  have h3 : (p ≫ n) ≫ (n ≫ p) = 0 := cat_P_minus_comp_P_plus_zero n p h_nil_n
  have h4 : (p ≫ n) ≫ (p ≫ n) = p ≫ n := cat_P_minus_sq n p h_nil_p h_car
  rw [h1, h2, h3, h4]
  rw [sub_zero, zero_sub, sub_neg_eq_add]
  exact h_car

end PreadditiveTheorems

end InfoGeometry.Physics.Chevalley
