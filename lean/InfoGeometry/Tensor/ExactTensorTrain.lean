/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Exact finite tensor trains and their cut-rank obstruction

An open-boundary train is evaluated by an ordered product of local matrices.
The bond carrier is fixed across the sites; the boundary row and column can
be absorbed into the first and last cores when there is at least one site.

Every finite coefficient tensor has an explicit exact realization using its
full words as bond states. This construction uses only zero, one, addition,
and ordered multiplication, so it also applies to noncommutative semirings.
It is an existence construction with `card ι ^ n` states, not a compression
algorithm or a claim of minimal bond dimension.

Over a field, every cut matricization factors through the actual bond space.
Its native matrix rank is therefore a lower bound on that bond dimension.
Simultaneously realizing all minimal cut ranks is a separate theorem target.
-/

namespace InfoGeometry.Tensor.ExactTensorTrain

open scoped BigOperators

section OrderedContraction

variable {B ι σ : Type*} [Semiring B] [Fintype σ] [DecidableEq σ]

/-- Open-boundary contraction with the cores multiplied in site order. -/
def eval {n : ℕ} (left : Matrix Unit σ B)
    (core : Fin n → ι → Matrix σ σ B) (right : Matrix σ Unit B)
    (word : Fin n → ι) : B :=
  (left * (List.ofFn fun i => core i (word i)).prod * right) () ()

/-- Splitting at a cut preserves the order of every coefficient product. -/
theorem eval_append {k m : ℕ} (left : Matrix Unit σ B)
    (core : Fin (k + m) → ι → Matrix σ σ B) (right : Matrix σ Unit B)
    (u : Fin k → ι) (v : Fin m → ι) :
    eval left core right (Fin.append u v) =
      ((left * (List.ofFn fun i : Fin k => core (Fin.castAdd m i) (u i)).prod) *
        ((List.ofFn fun i : Fin m => core (Fin.natAdd k i) (v i)).prod * right)) () () := by
  simp only [eval, List.ofFn_add, List.prod_append,
    Fin.append_left', Fin.append_right, Matrix.mul_assoc]

/-- Ordered diagonal products reduce to ordered products of their entries. -/
theorem prod_diagonal_ofFn (n : ℕ) (d : Fin n → σ → B) :
    (List.ofFn fun i => Matrix.diagonal (d i)).prod =
      Matrix.diagonal (fun s => (List.ofFn fun i => d i s).prod) := by
  calc
    _ = Matrix.diagonal (List.ofFn d).prod := by
      simpa only [List.map_ofFn] using
        (map_list_prod (Matrix.diagonalRingHom σ B) (List.ofFn d)).symm
    _ = _ := by
      apply congrArg Matrix.diagonal
      funext s
      simp only [Pi.list_prod_apply, List.map_ofFn]

end OrderedContraction

section ExactConstruction

variable {B ι : Type*} [Semiring B] [Fintype ι] [DecidableEq ι]

/-- A local physical-index test on the finite full-word bond space. -/
def wordSelector {n : ℕ} (i : Fin n) (a : ι) :
    Matrix (Fin n → ι) (Fin n → ι) B :=
  Matrix.diagonal (fun word => if word i = a then 1 else 0)

/-- All local coordinate tests select exactly one full word. -/
theorem prod_coordinate_indicators (n : ℕ) :
    ∀ w x : Fin n → ι,
      (List.ofFn fun i => if w i = x i then (1 : B) else 0).prod =
        if w = x then 1 else 0 := by
  induction n with
  | zero =>
      intro w x
      have h : w = x := funext fun i => Fin.elim0 i
      simp [h]
  | succ n ih =>
      intro w x
      rw [List.ofFn_succ, List.prod_cons, ih]
      by_cases hzero : w 0 = x 0
      · by_cases htail : (fun i : Fin n => w i.succ) = (fun i => x i.succ)
        · have h : w = x := by
            funext i
            exact Fin.cases hzero (fun j => congrFun htail j) i
          simp [hzero, htail, h]
        · have h : w ≠ x := fun h =>
            htail (congrArg (fun f : Fin (n + 1) → ι => fun i : Fin n => f i.succ) h)
          simp [hzero, htail, h]
      · have h : w ≠ x := fun h => hzero (congrFun h 0)
        simp [hzero, h]

/-- The selector cores multiply to the one-word diagonal projection. -/
theorem wordSelector_product {n : ℕ} (x : Fin n → ι) :
    (List.ofFn fun i => wordSelector (B := B) i (x i)).prod =
      Matrix.diagonal (fun w => if w = x then (1 : B) else 0) := by
  unfold wordSelector
  rw [prod_diagonal_ofFn]
  apply congrArg Matrix.diagonal
  funext w
  exact prod_coordinate_indicators n w x

/-- Constructive exact reconstruction. The coefficient tensor occurs once,
in the final boundary column; no coefficient products are commuted. -/
theorem eval_full_word_train {n : ℕ} (c : (Fin n → ι) → B) (x : Fin n → ι) :
    eval (fun _ _ => 1) (wordSelector (B := B)) (fun w _ => c w) x = c x := by
  unfold eval
  rw [wordSelector_product]
  simp [Matrix.mul_apply, Matrix.diagonal, ite_mul]

/-- Every finite coefficient tensor admits an exact open-boundary train.
The displayed witnesses use the actual full-word bond space. -/
theorem exists_exact_train {n : ℕ} (c : (Fin n → ι) → B) :
    ∃ left : Matrix Unit (Fin n → ι) B,
      ∃ core : Fin n → ι → Matrix (Fin n → ι) (Fin n → ι) B,
        ∃ right : Matrix (Fin n → ι) Unit B,
          ∀ x, eval left core right x = c x := by
  exact ⟨fun _ _ => 1, wordSelector, fun w _ => c w, eval_full_word_train c⟩

end ExactConstruction

/-- The coefficient tensor read as a matrix at the cut after `k` sites. -/
def matricize {B ι : Type*} {k m : ℕ} (c : (Fin (k + m) → ι) → B) :
    Matrix (Fin k → ι) (Fin m → ι) B :=
  Matrix.of fun u v => c (Fin.append u v)

section CutFactorization

variable {B ι σ : Type*} [Semiring B] [Fintype σ] [DecidableEq σ]

/-- The two partial contractions are an actual native matrix factorization
of the cut matricization, over an arbitrary noncommutative semiring. -/
theorem matricize_eval_eq_mul {k m : ℕ} (left : Matrix Unit σ B)
    (core : Fin (k + m) → ι → Matrix σ σ B) (right : Matrix σ Unit B) :
    matricize (k := k) (m := m) (eval left core right) =
      (Matrix.of fun u j => (left *
        (List.ofFn fun i : Fin k => core (Fin.castAdd m i) (u i)).prod) () j) *
      (Matrix.of fun j v => ((List.ofFn fun i : Fin m => core (Fin.natAdd k i) (v i)).prod *
        right) j ()) := by
  ext u v
  change eval left core right (Fin.append u v) = _
  rw [eval_append]
  rfl

end CutFactorization

section FieldRank

variable {K ι σ : Type*} [Field K] [Fintype ι] [Fintype σ] [DecidableEq σ]

/-- No train can have a bond smaller than the native rank of its cut matrix.
This rank theorem is deliberately stated over a field. -/
theorem matricize_eval_rank_le {k m : ℕ} (left : Matrix Unit σ K)
    (core : Fin (k + m) → ι → Matrix σ σ K) (right : Matrix σ Unit K) :
    (matricize (k := k) (m := m) (eval left core right)).rank ≤ Fintype.card σ := by
  rw [matricize_eval_eq_mul]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

/-- Both physical sides bound the rank of an arbitrary cut matricization. -/
theorem matricize_rank_le {k m : ℕ} (c : (Fin (k + m) → ι) → K) :
    (matricize (k := k) (m := m) c).rank ≤
      min (Fintype.card ι ^ k) (Fintype.card ι ^ m) := by
  apply le_min
  · simpa using Matrix.rank_le_card_height (matricize (k := k) (m := m) c)
  · simpa using Matrix.rank_le_card_width (matricize (k := k) (m := m) c)

/-- The four Clifford coefficient labels give the familiar finite cut bound. -/
theorem four_letter_matricize_rank_le {k m : ℕ}
    (c : (Fin (k + m) → Fin 4) → K) :
    (matricize (k := k) (m := m) c).rank ≤ 4 ^ min k m := by
  rcases le_total k m with h | h
  · simpa [min_eq_left h] using
      Matrix.rank_le_card_height (matricize (k := k) (m := m) c)
  · simpa [min_eq_right h] using
      Matrix.rank_le_card_width (matricize (k := k) (m := m) c)

/-- A strict cut-rank obstruction rules out every choice of cores on the
proposed bond space, not only the explicit full-word construction. -/
theorem ne_eval_of_card_lt_rank {k m : ℕ} (c : (Fin (k + m) → ι) → K)
    (h : Fintype.card σ < (matricize (k := k) (m := m) c).rank)
    (left : Matrix Unit σ K) (core : Fin (k + m) → ι → Matrix σ σ K)
    (right : Matrix σ Unit K) : c ≠ eval left core right := by
  intro heq
  rw [heq] at h
  exact (not_lt_of_ge (matricize_eval_rank_le left core right)) h

end FieldRank

end InfoGeometry.Tensor.ExactTensorTrain
