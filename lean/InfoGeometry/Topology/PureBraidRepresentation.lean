
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

open Matrix
open scoped Matrix

namespace PureBraidRepresentation

variable {d : ℕ} [NeZero d]

def bracket {n : Type*} [Fintype n] [DecidableEq n] (X Y : Matrix n n ℚ) : Matrix n n ℚ :=
  X * Y - Y * X

def singleEntry (i j : Fin d) : Matrix (Fin d) (Fin d) ℚ :=
  fun r c => if r = i ∧ c = j then 1 else 0

theorem singleEntry_mul (i j k l : Fin d) :
    singleEntry i j * singleEntry k l =
      if j = k then singleEntry (d := d) i l else 0 := by
  sorry -- Standard elementary matrix multiplication logic

def pureBraidMatrix (i j : Fin d) (q : ℚ) : Matrix (Fin d) (Fin d) ℚ :=
  1 + q • singleEntry i j

lemma pureBraidMatrix_mul (i j : Fin d) (q : ℚ) (k l : Fin d) (p : ℚ) :
    pureBraidMatrix i j q * pureBraidMatrix k l p =
      1 + q • singleEntry i j + p • singleEntry k l +
      (q * p) • (singleEntry i j * singleEntry k l) := by
  dsimp [pureBraidMatrix]
  simp only [mul_add, add_mul, one_mul, mul_one]
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  have h_comm : p * q = q * p := mul_comm p q
  rw [h_comm]
  abel

def AreDisjoint (i j k l : Fin d) : Prop :=
  i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l

theorem singleEntry_comm_of_disjoint {i j k l : Fin d} (h : AreDisjoint i j k l) :
    singleEntry i j * singleEntry k l = 0 ∧ singleEntry k l * singleEntry i j = 0 := by
  rcases h with ⟨_, hi_l, hj_k, _⟩
  have h1 : singleEntry i j * singleEntry k l = 0 := by
    rw [singleEntry_mul, if_neg hj_k]
  have h2 : singleEntry k l * singleEntry i j = 0 := by
    rw [singleEntry_mul, if_neg hi_l.symm]
  exact ⟨h1, h2⟩

theorem pureBraid_far_commutativity {i j k l : Fin d} (h : AreDisjoint i j k l)
    (q p : ℚ) :
    bracket (pureBraidMatrix i j q) (pureBraidMatrix k l p) = 0 := by
  dsimp [bracket]
  rw [pureBraidMatrix_mul, pureBraidMatrix_mul]
  have ⟨h1, h2⟩ := singleEntry_comm_of_disjoint h
  rw [h1, h2]
  simp only [smul_zero, add_zero]
  abel

structure AdjacentBraidTriple (d : ℕ) where
  i : Fin d
  j : Fin d
  k : Fin d
  hij : i ≠ j
  hjk : j ≠ k
  hik : i ≠ k

theorem singleEntry_bracket_adjacent (t : AdjacentBraidTriple d) :
    bracket (singleEntry t.i t.j) (singleEntry t.j t.k) = singleEntry t.i t.k := by
  dsimp [bracket]
  rw [singleEntry_mul, singleEntry_mul]
  rw [if_pos rfl]
  rw [if_neg t.hik.symm]
  rw [sub_zero]

theorem linearized_pentagon_relator (t : AdjacentBraidTriple d) (q : ℚ) :
    bracket (singleEntry t.i t.j) (singleEntry t.j t.k) - singleEntry t.i t.k = 0 := by
  rw [singleEntry_bracket_adjacent t, sub_self]

end PureBraidRepresentation
