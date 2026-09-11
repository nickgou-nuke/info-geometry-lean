import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite words and path weights

Finite words are the primitive layer for the n-ary tree.  A depth-`k` word is
`Fin k → Fin n`, so its cardinality is exactly `n ^ k`.  Infinite boundary
objects and completions are intentionally outside this owner.
-/

namespace InfoGeometry.Categorical.FiniteWordPathWeights

/-- The finite n-ary words at depth `k`. -/
abbrev Word (n k : ℕ) := Fin k → Fin n

/-- A finite word of successor length is a shorter word together with its
terminal letter. -/
def wordSuccEquiv (n k : ℕ) :
    Word n (k + 1) ≃ Word n k × Fin n where
  toFun w := (fun i => w i.castSucc, w (Fin.last k))
  invFun p := fun i => Fin.lastCases p.2 (fun j => p.1 j) i
  left_inv w := by
    funext i
    refine Fin.lastCases ?_ ?_ i
    · simp
    · intro j
      simp only [Fin.lastCases_castSucc]
  right_inv p := by
    rcases p with ⟨w, a⟩
    apply Prod.ext
    · funext i
      simp only [Fin.lastCases_castSucc]
    · simp

theorem word_cardinality_successor_product (n k : ℕ) :
    Fintype.card (Word n (k + 1)) =
      Fintype.card (Word n k) * Fintype.card (Fin n) :=
  by
    simpa [Fintype.card_prod, Fintype.card_fin] using
      Fintype.card_congr (wordSuccEquiv n k)

theorem word_cardinality (n k : ℕ) :
    Fintype.card (Word n k) = n ^ k := by
  simp [Word]

theorem word_cardinality_zero (n : ℕ) :
    Fintype.card (Word n 0) = 1 := by
  simp

theorem word_cardinality_successor (n k : ℕ) :
    Fintype.card (Word n (k + 1)) = n * Fintype.card (Word n k) := by
  rw [word_cardinality, word_cardinality]
  simp [pow_succ, Nat.mul_comm]

section FiniteLevelWeights

/-- The product of one edge weight along a finite word. -/
def wordWeight {R : Type*} [CommMonoid R]
    (r : Fin n → R) (w : Word n k) : R :=
  ∏ i, r (w i)

/-- A successor-depth path weight splits into its prefix weight and terminal
letter weight.  This is the finite tree-composition law used by the level
recurrence below; it makes no claim about an infinite boundary or a tensor
category. -/
theorem wordWeight_wordSuccEquiv {R : Type*} [CommMonoid R]
    (r : Fin n → R) (w : Word n (k + 1)) :
    wordWeight r w =
      wordWeight r (wordSuccEquiv n k w).1 * r (wordSuccEquiv n k w).2 := by
  unfold wordWeight
  rw [Fin.prod_univ_castSucc]
  rfl

/-- The total weight of all words at a fixed finite depth. -/
def levelWeightSum {R : Type*} [CommSemiring R]
    (r : Fin n → R) (k : ℕ) : R :=
  ∑ w : Word n k, wordWeight r w

theorem levelWeightSum_eq_pow {R : Type*} [CommSemiring R]
    (r : Fin n → R) (k : ℕ) :
    levelWeightSum r k = (∑ a : Fin n, r a) ^ k := by
  classical
  unfold levelWeightSum wordWeight
  symm
  simpa only [Finset.sum_univ_pi] using
    (Finset.sum_pow' (s := (Finset.univ : Finset (Fin n))) (f := r) k)

theorem levelWeightSum_succ {R : Type*} [CommSemiring R]
    (r : Fin n → R) (k : ℕ) :
    levelWeightSum r (k + 1) =
      levelWeightSum r k * ∑ a : Fin n, r a := by
  rw [levelWeightSum_eq_pow, levelWeightSum_eq_pow, pow_succ]

/-- The successor-level partition sum is the explicit finite tree reindexing
of prefix weights times terminal-letter weights. -/
theorem levelWeightSum_succ_wordSuccEquiv {R : Type*} [CommSemiring R]
    (r : Fin n → R) (k : ℕ) :
    levelWeightSum r (k + 1) =
      ∑ w : Word n k, ∑ a : Fin n, wordWeight r w * r a := by
  calc
    levelWeightSum r (k + 1) =
        ∑ p : Word n k × Fin n,
          wordWeight r ((wordSuccEquiv n k).symm p) := by
      unfold levelWeightSum
      rw [← (wordSuccEquiv n k).sum_comp]
      simp
    _ = ∑ w : Word n k, ∑ a : Fin n,
          wordWeight r ((wordSuccEquiv n k).symm (w, a)) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ w : Word n k, ∑ a : Fin n, wordWeight r w * r a := by
      apply Finset.sum_congr rfl
      intro w _
      apply Finset.sum_congr rfl
      intro a _
      simpa using
        (wordWeight_wordSuccEquiv r ((wordSuccEquiv n k).symm (w, a)))

end FiniteLevelWeights

/-- Additive path coordinate obtained by summing one contribution per edge. -/
def additivePath {R : Type*} [AddMonoid R]
    (τ : Fin n → R) (w : List (Fin n)) : R :=
  (w.map τ).sum

theorem additivePath_append {R : Type*} [AddMonoid R]
    (τ : Fin n → R) (u v : List (Fin n)) :
    additivePath τ (u ++ v) = additivePath τ u + additivePath τ v := by
  simp [additivePath, List.map_append, List.sum_append]

/-- Multiplicative path weight obtained by multiplying one edge weight per
letter. -/
def multiplicativePath {R : Type*} [Monoid R]
    (r : Fin n → R) (w : List (Fin n)) : R :=
  (w.map r).prod

theorem multiplicativePath_append {R : Type*} [Monoid R]
    (r : Fin n → R) (u v : List (Fin n)) :
    multiplicativePath r (u ++ v) =
      multiplicativePath r u * multiplicativePath r v := by
  simp [multiplicativePath, List.map_append, List.prod_append]

theorem additivePath_cons {R : Type*} [AddMonoid R]
    (τ : Fin n → R) (a : Fin n) (w : List (Fin n)) :
    additivePath τ (a :: w) = τ a + additivePath τ w := by
  simp [additivePath]

theorem multiplicativePath_cons {R : Type*} [Monoid R]
    (r : Fin n → R) (a : Fin n) (w : List (Fin n)) :
    multiplicativePath r (a :: w) = r a * multiplicativePath r w := by
  simp [multiplicativePath]

/-- The positive real logarithmic branch turns multiplicative path weights into
the additive surprisal/path coordinate. -/
noncomputable def logarithmicPath (r : Fin n → ℝ) (w : List (Fin n)) : ℝ :=
  additivePath (fun a => -Real.log (r a)) w

theorem logarithmicPath_append
    (r : Fin n → ℝ) (u v : List (Fin n)) :
    logarithmicPath r (u ++ v) =
      logarithmicPath r u + logarithmicPath r v := by
  exact additivePath_append (fun a => -Real.log (r a)) u v

theorem logarithmicPath_eq_neg_log_multiplicativePath
    (r : Fin n → ℝ) (hr : ∀ a, 0 < r a) (w : List (Fin n)) :
    logarithmicPath r w = -Real.log (multiplicativePath r w) := by
  have hprod : ∀ v : List (Fin n), 0 < multiplicativePath r v := by
    intro v
    induction v with
    | nil => simp [multiplicativePath]
    | cons a v ih =>
        simpa [multiplicativePath] using mul_pos (hr a) ih
  induction w with
  | nil => simp [logarithmicPath, additivePath, multiplicativePath]
  | cons a w ih =>
      change -Real.log (r a) + logarithmicPath r w =
        -Real.log (r a * multiplicativePath r w)
      rw [Real.log_mul (hr a).ne' (hprod w).ne']
      rw [ih]
      ring

end InfoGeometry.Categorical.FiniteWordPathWeights
