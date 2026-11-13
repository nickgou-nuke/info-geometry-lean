/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.MatrixRankFactorization
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Compatible exact tensor trains with varying minimal bond dimensions

The physical alphabet is `Fin q`. A train stores actual finite rectangular
cores and a terminal boundary vector, with no factorization or rank claims
stored as fields. Its coefficient matrix is computed by ordered contraction.

`advance` moves the next physical index to the row side of a native matrix.
`cutRank` repeatedly applies that operation and takes native `Matrix.rank` at
the requested cut. Prefix rows are left-associated tuples in physical order.

Successive factorizations through the actual column-space range construct
one compatible train. A left inverse of each inclusion proves that all later
residual unfolding ranks equal the original unfolding ranks. Consequently,
every positive bond of the constructed train attains the corresponding cut
rank, and every other exact train has at least that bond dimension.

Zero-dimensional bonds are permitted. The supplied input boundary dimension
is not claimed to be minimal. The terminal boundary vector may be absorbed
into the last physical core when there is at least one site; the usual
internal cuts are therefore covered without a positivity convention.
-/

namespace InfoGeometry.Tensor.RankMinimalTensorTrain

open scoped BigOperators Kronecker
open InfoGeometry.Algebra.MatrixRankFactorization

universe u

/-- Finite train data with varying bond dimensions and no proof fields. -/
inductive Train (K : Type u) (q : ℕ) : ℕ → ℕ → Type u
  | nil {r : ℕ} (boundary : Fin r → K) : Train K q 0 r
  | cons {n r s : ℕ} (core : Fin q → Matrix (Fin r) (Fin s) K)
      (tail : Train K q n s) : Train K q (n + 1) r

namespace Train

/-- Ordered contraction, retaining the incoming bond as the matrix row. -/
def coeff {K : Type u} [Semiring K] {q : ℕ} :
    {n r : ℕ} → Train K q n r → Matrix (Fin r) (Fin n → Fin q) K :=
  fun {_ _} T =>
    Train.rec (motive := fun n r _ => Matrix (Fin r) (Fin n → Fin q) K)
      (fun {_} boundary => Matrix.of fun a _ => boundary a)
      (fun {_ _ _} core _ ih => Matrix.of fun a word =>
        ∑ j, core (word 0) a j * ih j (fun i => word i.succ))
      T

/-- The actual dimension of the incoming bond and each successive bond. -/
def bond {K : Type u} {q : ℕ} :
    {n r : ℕ} → Train K q n r → Fin (n + 1) → ℕ :=
  fun {_ _} T =>
    Train.rec (motive := fun n _ _ => Fin (n + 1) → ℕ)
      (fun {r} _ _ => r)
      (fun {_ r _} _ _ ih => Fin.cases r ih)
      T

@[simp] theorem bond_zero {K : Type u} {q n r : ℕ} (T : Train K q n r) :
    T.bond 0 = r := by
  cases T <;> rfl

@[simp] theorem bond_cons_succ {K : Type u} {q n r s : ℕ}
    (core : Fin q → Matrix (Fin r) (Fin s) K) (tail : Train K q n s)
    (k : Fin (n + 1)) : (Train.cons core tail).bond k.succ = tail.bond k := rfl

/-- The actual terminal boundary vector, indexed by the final bond. -/
def terminalBoundary {K : Type u} {q : ℕ} :
    {n r : ℕ} → (T : Train K q n r) → Fin (T.bond (Fin.last n)) → K :=
  fun {_ _} T =>
    Train.rec (motive := fun n _ T => Fin (T.bond (Fin.last n)) → K)
      (fun {_} boundary => boundary)
      (fun {_ _ _} _ _ ih => ih)
      T

/-- Absorb the terminal vector into the last actual core, in multiplication
order. A positive-length train then ends at a one-dimensional unit boundary.
An empty train is unchanged because it has no core into which to absorb its
boundary. Earlier cores and bond dimensions remain unchanged. -/
def absorbTerminalBoundary {K : Type u} [Semiring K] {q : ℕ} :
    {n r : ℕ} → Train K q n r → Train K q n r :=
  fun {_ _} T =>
    Train.rec (motive := fun n r _ => Train K q n r)
      (fun {_} boundary => .nil boundary)
      (fun {n _ _} core tail ih =>
        match n, tail, ih with
        | 0, .nil boundary, _ =>
            .cons (fun a => Matrix.of fun i (_ : Fin 1) =>
              ∑ j, core a i j * boundary j) (.nil fun _ : Fin 1 => 1)
        | _ + 1, _, normalized => .cons core normalized)
      T

@[simp] theorem absorbTerminalBoundary_nil {K : Type u} [Semiring K] {q r : ℕ}
    (boundary : Fin r → K) :
    absorbTerminalBoundary (Train.nil (q := q) boundary) = Train.nil boundary := rfl

/-- Ordered contraction is preserved, including for the empty chain. -/
@[simp] theorem absorbTerminalBoundary_coeff {K : Type u} [Semiring K] {q : ℕ} :
    ∀ {n r : ℕ} (T : Train K q n r), (absorbTerminalBoundary T).coeff = T.coeff
  | 0, _, .nil _ => rfl
  | 1, _, .cons core (.nil boundary) => by
      ext a word
      change (∑ _ : Fin 1, (∑ j, core (word 0) a j * boundary j) * 1) =
        ∑ j, core (word 0) a j * boundary j
      simp
  | n + 2, _, .cons core tail => by
      ext a word
      change (∑ j, core (word 0) a j *
        (absorbTerminalBoundary tail).coeff j (fun i => word i.succ)) =
          ∑ j, core (word 0) a j * tail.coeff j (fun i => word i.succ)
      rw [absorbTerminalBoundary_coeff tail]

/-- Every bond before the final boundary is preserved; the index zero case
includes the supplied incoming boundary dimension. -/
@[simp] theorem absorbTerminalBoundary_bond_castSucc
    {K : Type u} [Semiring K] {q : ℕ} :
    ∀ {n r : ℕ} (T : Train K q n r) (k : Fin n),
      (absorbTerminalBoundary T).bond k.castSucc = T.bond k.castSucc
  | 0, _, .nil _, k => Fin.elim0 k
  | 1, _, .cons core (.nil boundary), k => by
      have hk : k = 0 := Subsingleton.elim _ _
      subst k
      rfl
  | n + 2, _, .cons core tail, k => by
      refine Fin.cases ?_ (fun j => ?_) k
      · rfl
      · exact absorbTerminalBoundary_bond_castSucc tail j

/-- A nonempty normalized train has final bond dimension one. -/
@[simp] theorem absorbTerminalBoundary_bond_last
    {K : Type u} [Semiring K] {q : ℕ} :
    ∀ {n r : ℕ} (T : Train K q (n + 1) r),
      (absorbTerminalBoundary T).bond (Fin.last (n + 1)) = 1
  | 0, _, .cons _ (.nil _) => rfl
  | n + 1, _, .cons _ tail => absorbTerminalBoundary_bond_last tail

/-- The actual final vector of a nonempty normalized train is the unit. -/
@[simp] theorem absorbTerminalBoundary_terminalBoundary
    {K : Type u} [Semiring K] {q : ℕ} :
    ∀ {n r : ℕ} (T : Train K q (n + 1) r),
      (absorbTerminalBoundary T).terminalBoundary = 1
  | 0, _, .cons _ (.nil _) => rfl
  | n + 1, _, .cons _ tail => absorbTerminalBoundary_terminalBoundary tail

/-- With no physical core, replacing a scalar boundary by the unit preserves
its coefficient exactly when that scalar already equals one. -/
theorem nil_scalar_coeff_eq_unit_iff {K : Type u} [Semiring K] {q : ℕ} (a : K) :
    (Train.nil (q := q) (fun _ : Fin 1 => a)).coeff =
      (Train.nil (q := q) (fun _ : Fin 1 => (1 : K))).coeff ↔ a = 1 := by
  constructor
  · intro h
    exact congrArg (fun M : Matrix (Fin 1) (Fin 0 → Fin q) K => M 0 Fin.elim0) h
  · rintro rfl
    rfl

end Train

/-- Move one physical coordinate from the column side to the row side. -/
def advance {K : Type u} {q n : ℕ} {σ : Type}
    (C : Matrix σ (Fin (n + 1) → Fin q) K) :
    Matrix (σ × Fin q) (Fin n → Fin q) K :=
  Matrix.of fun ab word => C ab.1 (Fin.cons ab.2 word)

/-- Native matrix rank after moving exactly the specified prefix to the row
side. Every value is the rank of an actual finite matrix, not a new tensor
rank notion. -/
noncomputable def cutRank {K : Type u} [Field K] (q : ℕ) :
    (n : ℕ) → (σ : Type) →
      Matrix σ (Fin n → Fin q) K → Fin (n + 1) → ℕ
  | 0, _, C, _ => C.rank
  | n + 1, σ, C, k => Fin.cases C.rank
      (fun j => cutRank q n (σ × Fin q) (advance C) j) k

@[simp] theorem cutRank_zero {K : Type u} [Field K] (q n : ℕ)
    (σ : Type) (C : Matrix σ (Fin n → Fin q) K) :
    cutRank q n σ C 0 = C.rank := by
  cases n <;> rfl

@[simp] theorem cutRank_succ {K : Type u} [Field K] (q n : ℕ)
    (σ : Type) (C : Matrix σ (Fin (n + 1) → Fin q) K)
    (k : Fin (n + 1)) :
    cutRank q (n + 1) σ C k.succ = cutRank q n (σ × Fin q) (advance C) k := rfl

/-- The next-index reshape preserves the ordered coefficient products over
an arbitrary semiring. -/
theorem advance_mul {K : Type u} [Semiring K] {q n : ℕ}
    {a s : Type} [Fintype s]
    (L : Matrix a s K) (R : Matrix s (Fin (n + 1) → Fin q) K) :
    advance (L * R) = (L ⊗ₖ (1 : Matrix (Fin q) (Fin q) K)) * advance R := by
  exact reshape_mul_eq_kronecker_mul L
    (Matrix.of fun j (p : Fin q × (Fin n → Fin q)) => R j (Fin.cons p.1 p.2))

/-- Each cut of an arbitrary train has an explicit first-core factorization. -/
theorem advance_coeff_cons {K : Type u} [Semiring K] {q n r s : ℕ}
    (core : Fin q → Matrix (Fin r) (Fin s) K) (tail : Train K q n s) :
    advance (Train.cons core tail).coeff =
      (Matrix.of fun ab j => core ab.2 ab.1 j : Matrix (Fin r × Fin q) (Fin s) K) *
        tail.coeff := by
  ext ab word
  rcases ab with ⟨a, b⟩
  simp [advance, Train.coeff, Matrix.mul_apply]

section Field

variable {K : Type u} [Field K]

/-- Left multiplication cannot increase any later unfolding rank. -/
theorem cutRank_mul_le (q n : ℕ) :
    ∀ (a s : Type) [Fintype s]
      (L : Matrix a s K) (R : Matrix s (Fin n → Fin q) K) (k : Fin (n + 1)),
      cutRank q n a (L * R) k ≤ cutRank q n s R k := by
  induction n with
  | zero =>
      intro a s _ L R k
      exact Matrix.rank_mul_le_right L R
  | succ n ih =>
      intro a s _ L R k
      refine Fin.cases ?_ (fun j => ?_) k
      · rw [cutRank_zero, cutRank_zero]
        exact Matrix.rank_mul_le_right L R
      · rw [cutRank_succ, cutRank_succ, advance_mul]
        exact ih (a × Fin q) (s × Fin q)
          (L ⊗ₖ (1 : Matrix (Fin q) (Fin q) K)) (advance R) j

/-- A proved left inverse preserves all later unfolding ranks, not merely
the rank of the first two-factor decomposition. -/
theorem cutRank_mul_eq_of_left_inverse (q n : ℕ)
    {a s : Type} [Fintype a] [Fintype s] [DecidableEq s]
    (L : Matrix a s K) (Q : Matrix s a K) (hQL : Q * L = 1)
    (R : Matrix s (Fin n → Fin q) K) (k : Fin (n + 1)) :
    cutRank q n a (L * R) k = cutRank q n s R k := by
  apply le_antisymm (cutRank_mul_le q n a s L R k)
  have hRecover : Q * (L * R) = R := by
    rw [← Matrix.mul_assoc, hQL, Matrix.one_mul]
  simpa only [hRecover] using cutRank_mul_le q n s a Q (L * R) k

/-- Every actual variable-bond train obeys the native rank lower bound at
every cut, including its supplied boundary dimensions. -/
theorem cutRank_coeff_le_bond {q : ℕ} :
    ∀ {n r : ℕ} (T : Train K q n r) (k : Fin (n + 1)),
      cutRank q n (Fin r) T.coeff k ≤ T.bond k
  | _, r, .nil boundary, k => by
      change (Train.coeff (Train.nil (q := q) boundary)).rank ≤ r
      simpa using Matrix.rank_le_card_height (Train.coeff (Train.nil (q := q) boundary))
  | _, _, .cons core tail, k => by
      refine Fin.cases ?_ (fun j => ?_) k
      · rw [cutRank_zero, Train.bond_zero]
        simpa using Matrix.rank_le_card_height (Train.coeff (Train.cons core tail))
      · rw [cutRank_succ, Train.bond_cons_succ, advance_coeff_cons]
        exact (cutRank_mul_le _ _ _ _ _ tail.coeff j).trans
          (cutRank_coeff_le_bond tail j)

/-- Successive range-basis factorizations construct one compatible train
attaining every positive cut rank. The original tensor and all its
correlations are reconstructed exactly. -/
theorem exists_rank_minimal_train (q n : ℕ) :
    ∀ (r : ℕ) (C : Matrix (Fin r) (Fin n → Fin q) K),
      ∃ T : Train K q n r, T.coeff = C ∧
        ∀ k : Fin n, T.bond k.succ = cutRank q n (Fin r) C k.succ := by
  classical
  induction n with
  | zero =>
      intro r C
      refine ⟨Train.nil (fun a => C a Fin.elim0), ?_, ?_⟩
      · ext a word
        exact congrArg (C a) (Subsingleton.elim _ _)
      · intro k
        exact Fin.elim0 k
  | succ n ih =>
      intro r C
      let M := advance C
      obtain ⟨L, R, Q, hLR, hQL⟩ := exists_rank_factorization_with_left_inverse M
      obtain ⟨tail, htail, hminimal⟩ := ih M.rank R
      let core : Fin q → Matrix (Fin r) (Fin M.rank) K :=
        fun b => Matrix.of fun a j => L (a, b) j
      refine ⟨Train.cons core tail, ?_, ?_⟩
      · ext a word
        change (∑ j, L (a, word 0) j * tail.coeff j (fun i => word i.succ)) = C a word
        rw [htail]
        change (L * R) (a, word 0) (fun i => word i.succ) = C a word
        rw [hLR]
        change C a (Fin.cons (word 0) (fun i => word i.succ)) = C a word
        exact congrArg (C a) (Fin.cons_self_tail word)
      · intro k
        refine Fin.cases ?_ (fun j => ?_) k
        · rw [Train.bond_cons_succ, Train.bond_zero, cutRank_succ, cutRank_zero]
        · rw [Train.bond_cons_succ, hminimal j, cutRank_succ]
          change cutRank q n (Fin M.rank) R j.succ =
            cutRank q n (Fin r × Fin q) M j.succ
          conv_rhs => rw [← hLR]
          exact (cutRank_mul_eq_of_left_inverse q n L Q hQL R j.succ).symm

/-- Simultaneous minimality against every other exact train follows from
the constructed equalities and the generic cut-rank lower bound. -/
theorem exists_bondwise_minimal_exact_train (q n r : ℕ)
    (C : Matrix (Fin r) (Fin n → Fin q) K) :
    ∃ T : Train K q n r, T.coeff = C ∧
      ∀ S : Train K q n r, S.coeff = C →
        ∀ k : Fin n, T.bond k.succ ≤ S.bond k.succ := by
  obtain ⟨T, hT, hminimal⟩ := exists_rank_minimal_train q n r C
  refine ⟨T, hT, ?_⟩
  intro S hS k
  rw [hminimal k, ← hS]
  exact cutRank_coeff_le_bond S k.succ

end Field

end InfoGeometry.Tensor.RankMinimalTensorTrain
