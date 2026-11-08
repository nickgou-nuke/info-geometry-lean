import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BitWordSimplexFaceCancellation

/-!
# Sign cancellation for alternating simplex faces

This owner isolates the scalar sign calculation used when two different
orders of deleting faces are paired in a double coboundary sum.
-/

namespace InfoGeometry.Canonical.BitWordSimplexSignCancellation

theorem neg_one_pow_add_succ_cancel {R : Type*} [Ring R] (i j : ℕ) :
    (-1 : R) ^ (i + j) + (-1 : R) ^ (j + i + 1) = 0 := by
  have h : j + i + 1 = i + j + 1 := by omega
  rw [h, pow_succ]
  noncomm_ring

theorem neg_one_pow_smul_pair_cancel {R M : Type*} [Ring R]
    [AddCommGroup M] [Module R M] (i j : ℕ) (x : M) :
    (-1 : R) ^ (i + j) • x + (-1 : R) ^ (j + i + 1) • x = 0 := by
  rw [← add_smul, neg_one_pow_add_succ_cancel i j, zero_smul]

theorem neg_one_pow_smul_pair_cancel_of_eq {R M : Type*} [Ring R]
    [AddCommGroup M] [Module R M] (i j : ℕ) (x y : M) (hxy : x = y) :
    (-1 : R) ^ (i + j) • x + (-1 : R) ^ (j + i + 1) • y = 0 := by
  rw [hxy]
  exact neg_one_pow_smul_pair_cancel (R := R) (M := M) i j y

theorem nested_face_signed_pair_cancel {n : ℕ} {R M α : Type*}
    [Ring R] [AddCommGroup M] [Module R M]
    (c : (Fin n → α) → M) (σ : Fin (n + 2) → α)
    (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (-1 : R) ^ (i.1 + j.1) •
        c (σ ∘ (fun x => (i.succAbove j).succAbove
          ((j.predAbove i).succAbove x))) +
      (-1 : R) ^ (j.1 + i.1 + 1) •
        c (σ ∘ (fun x => i.succAbove (j.succAbove x))) = 0 := by
  have hfaces :=
    InfoGeometry.Canonical.BitWordSimplexFaceCancellation.nested_succAbove_swap_comp
      (fun x => σ x) i j
  have hvalue :
      c (σ ∘ (fun x => (i.succAbove j).succAbove
        ((j.predAbove i).succAbove x))) =
        c (σ ∘ (fun x => i.succAbove (j.succAbove x))) := by
    congr 1
  exact neg_one_pow_smul_pair_cancel_of_eq (R := R) (M := M)
    i.1 j.1 _ _ hvalue

end InfoGeometry.Canonical.BitWordSimplexSignCancellation
