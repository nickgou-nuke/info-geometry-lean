/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Tensor.RankMinimalTensorTrain
import InfoGeometry.Tensor.ExactTensorTrain

/-!
# Successive tensor unfoldings and the explicit prefix/suffix matricization

The recursive minimal-train construction groups prefix rows as nested pairs.
This file supplies the actual row equivalences identifying those rows with
a prefix word. Native `Matrix.rank_submatrix` transports rank along the
proved reindexing. The only cast on the word domain exchanges the equal
length expressions `m + k` and `k + m`; it does not permute coordinates.
-/

namespace InfoGeometry.Tensor.TensorTrainMatricization

open InfoGeometry.Tensor.RankMinimalTensorTrain

universe u

/-- Direct prefix/suffix matricization with the supplied incoming row. -/
def prefixMatricize {K : Type u} {q m k : ℕ} {σ : Type}
    (C : Matrix σ (Fin (m + k) → Fin q) K) :
    Matrix (σ × (Fin k → Fin q)) (Fin m → Fin q) K :=
  Matrix.of fun row suffix =>
    C row.1 ((Fin.append row.2 suffix) ∘ Fin.cast (Nat.add_comm m k))

/-- Prepending commutes with a cast between equal tail lengths. -/
theorem cons_comp_cast {α : Type*} {m n : ℕ} (h : m = n) (a : α)
    (tail : Fin n → α) :
    (Fin.cons a tail) ∘ Fin.cast (congrArg Nat.succ h) =
      Fin.cons a (tail ∘ Fin.cast h) := by
  cases h
  rfl

section Field

variable {K : Type u} [Field K]

/-- The recursive rank invariant equals the native rank of the explicit
prefix/suffix matrix, after a proved equivalence of prefix row indices. -/
theorem cutRank_eq_prefixMatricize_rank (q m k : ℕ) :
    ∀ (σ : Type) (C : Matrix σ (Fin (m + k) → Fin q) K),
      cutRank q (m + k) σ C
          ⟨k, Nat.lt_succ_of_le (Nat.le_add_left k m)⟩ =
        (prefixMatricize (q := q) (m := m) (k := k) C).rank := by
  induction k with
  | zero =>
      intro σ C
      rw [Fin.mk_zero, cutRank_zero]
      let e : σ ≃ σ × (Fin 0 → Fin q) :=
        { toFun := fun a => (a, Fin.elim0)
          invFun := Prod.fst
          left_inv := fun _ => rfl
          right_inv := fun p => by
            apply Prod.ext
            · rfl
            · exact Subsingleton.elim _ _ }
      have hMatrix :
          (prefixMatricize (q := q) (m := m) (k := 0) C).submatrix
            e (Equiv.refl (Fin m → Fin q)) = C := by
        ext a word
        simp [prefixMatricize, e, Function.comp_def]
      have hRank := Matrix.rank_submatrix
        (prefixMatricize (q := q) (m := m) (k := 0) C)
        e (Equiv.refl (Fin m → Fin q))
      rw [hMatrix] at hRank
      exact hRank
  | succ k ih =>
      intro σ C
      change cutRank q (m + k + 1) σ C
        (Fin.succ ⟨k, Nat.lt_succ_of_le (Nat.le_add_left k m)⟩) = _
      rw [cutRank_succ, ih]
      let e : ((σ × Fin q) × (Fin k → Fin q)) ≃
          (σ × (Fin (k + 1) → Fin q)) :=
        (Equiv.prodAssoc σ (Fin q) (Fin k → Fin q)).trans
          (Equiv.prodCongr (Equiv.refl σ)
            (Fin.consEquiv (fun _ : Fin (k + 1) => Fin q)))
      have hMatrix :
          (prefixMatricize (q := q) (m := m) (k := k + 1) C).submatrix
              e (Equiv.refl (Fin m → Fin q)) =
            prefixMatricize (q := q) (m := m) (k := k) (advance C) := by
        ext row suffix
        rcases row with ⟨⟨a, b⟩, prefixWord⟩
        change C a ((Fin.append (Fin.cons b prefixWord) suffix) ∘
            Fin.cast (Nat.add_comm m (k + 1))) =
          C a (Fin.cons b ((Fin.append prefixWord suffix) ∘
            Fin.cast (Nat.add_comm m k)))
        apply congrArg (C a)
        rw [Fin.append_cons]
        change (Fin.cons b (Fin.append prefixWord suffix)) ∘
            Fin.cast (congrArg Nat.succ (Nat.add_comm m k)) = _
        exact cons_comp_cast (Nat.add_comm m k) b (Fin.append prefixWord suffix)
      have hRank := Matrix.rank_submatrix
        (prefixMatricize (q := q) (m := m) (k := k + 1) C)
        e (Equiv.refl (Fin m → Fin q))
      rw [hMatrix] at hRank
      exact hRank

/-- For scalar tensors, the incoming singleton row disappears under an
explicit equivalence, giving the existing `Fin.append` matricization. -/
theorem cutRank_scalar_eq_matricize_rank (q m k : ℕ)
    (c : (Fin (m + k) → Fin q) → K) :
    cutRank q (m + k) (Fin 1) (Matrix.of fun _ word => c word)
        ⟨k, Nat.lt_succ_of_le (Nat.le_add_left k m)⟩ =
      (ExactTensorTrain.matricize (k := k) (m := m)
        (fun word => c (word ∘ Fin.cast (Nat.add_comm m k)))).rank := by
  rw [cutRank_eq_prefixMatricize_rank]
  let e : (Fin k → Fin q) ≃ Fin 1 × (Fin k → Fin q) :=
    { toFun := fun prefixWord => (0, prefixWord)
      invFun := Prod.snd
      left_inv := fun _ => rfl
      right_inv := fun p => by
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · rfl }
  have hMatrix :
      (prefixMatricize (q := q) (m := m) (k := k)
        (Matrix.of fun (_ : Fin 1) word => c word)).submatrix
          e (Equiv.refl (Fin m → Fin q)) =
        ExactTensorTrain.matricize (k := k) (m := m)
          (fun word => c (word ∘ Fin.cast (Nat.add_comm m k))) := rfl
  have hRank := Matrix.rank_submatrix
    (prefixMatricize (q := q) (m := m) (k := k)
      (Matrix.of fun (_ : Fin 1) word => c word))
    e (Equiv.refl (Fin m → Fin q))
  rw [hMatrix] at hRank
  exact hRank.symm

/-- Four local coefficient labels give the same sharp dimension bound for
the actual successive unfolding ranks used by the compatible train. -/
theorem scalar_four_letter_cutRank_le (m k : ℕ)
    (c : (Fin (m + k) → Fin 4) → K) :
    cutRank 4 (m + k) (Fin 1) (Matrix.of fun _ word => c word)
        ⟨k, Nat.lt_succ_of_le (Nat.le_add_left k m)⟩ ≤ 4 ^ min k m := by
  rw [cutRank_scalar_eq_matricize_rank]
  exact ExactTensorTrain.four_letter_matricize_rank_le _

end Field

end InfoGeometry.Tensor.TensorTrainMatricization
