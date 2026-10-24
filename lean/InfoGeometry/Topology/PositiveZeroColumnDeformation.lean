/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.PositiveGrassmannianAmplituhedronTopological

/-! # A positive deformation of the zero-column matrix-chart face

All statements concern finite real matrices, not a quotient Grassmannian.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Canonical Matrix

variable {n : ℕ}

/-- The ordered two-column determinant, allowing equal endpoints. -/
def columnMinor₂ (C : Matrix (Fin 2) (Fin n) ℝ) (i j : Fin n) : ℝ :=
  C 0 i * C 1 j - C 0 j * C 1 i

theorem hasPositiveMaximalMinors_iff_columnMinor₂
    (C : Matrix (Fin 2) (Fin n) ℝ) :
    HasPositiveMaximalMinors C ↔ ∀ i j, i < j → 0 < columnMinor₂ C i j := by
  constructor
  · intro h i j hij
    have hs : StrictMono (![i, j] : Fin 2 → Fin n) := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    have hp := h _ hs
    change 0 < Matrix.det (Matrix.of fun a b => C a (![i, j] b)) at hp
    rw [Matrix.det_fin_two] at hp
    simpa [columnMinor₂] using hp
  · intro h s hs
    change 0 < Matrix.det (Matrix.of fun i j => C i (s j))
    rw [Matrix.det_fin_two]
    exact h (s 0) (s 1) (hs (by decide))

/-- Append a positive multiple of the last column minus the first column. -/
def appendPositiveColumn₂ (C : Matrix (Fin 2) (Fin (n + 2)) ℝ) (ε : ℝ) :
    Matrix (Fin 2) (Fin (n + 2 + 1)) ℝ :=
  fun i j => if hj : j.val < n + 2 then C i ⟨j.val, hj⟩
    else ε * (C i (Fin.last (n + 1)) - C i 0)

@[simp] theorem appendPositiveColumn₂_zero (C : Matrix (Fin 2) (Fin (n + 2)) ℝ) :
    appendPositiveColumn₂ C 0 = appendZeroColumn₂ C := by
  ext i j
  by_cases hj : j.val < n + 2 <;> simp [appendPositiveColumn₂, appendZeroColumn₂, hj]

theorem columnMinor₂_appendPositive_last
    (C : Matrix (Fin 2) (Fin (n + 2)) ℝ) (ε : ℝ) (j : Fin (n + 2)) :
    columnMinor₂ (appendPositiveColumn₂ C ε) j.castSucc (Fin.last (n + 2)) =
      ε * (columnMinor₂ C j (Fin.last (n + 1)) + columnMinor₂ C 0 j) := by
  simp [columnMinor₂, appendPositiveColumn₂, j.isLt]
  ring

theorem appendPositiveColumn₂_positive
    (C : Matrix (Fin 2) (Fin (n + 2)) ℝ)
    (hC : HasPositiveMaximalMinors C) {ε : ℝ} (hε : 0 < ε) :
    HasPositiveMaximalMinors (appendPositiveColumn₂ C ε) := by
  rw [hasPositiveMaximalMinors_iff_columnMinor₂] at hC ⊢
  intro i j hij
  have hi : i.val < n + 2 := by have := j.isLt; change i.val < j.val at hij; omega
  by_cases hj : j.val < n + 2
  · simpa [columnMinor₂, appendPositiveColumn₂, hi, hj] using
      hC ⟨i.val, hi⟩ ⟨j.val, hj⟩ hij
  · have hjlast : j = Fin.last (n + 2) := by apply Fin.ext; simp; omega
    let i' : Fin (n + 2) := ⟨i.val, hi⟩
    have hi' : i = i'.castSucc := by rfl
    rw [hjlast, hi', columnMinor₂_appendPositive_last]
    apply mul_pos hε
    by_cases hfirst : i' = 0
    · rw [hfirst]
      simpa [columnMinor₂] using hC 0 (Fin.last (n + 1)) (by change 0 < n + 1; omega)
    · have h0i : (0 : Fin (n + 2)) < i' := by
        apply Fin.pos_iff_ne_zero.mpr hfirst
      have hleft : 0 ≤ columnMinor₂ C i' (Fin.last (n + 1)) := by
        rcases (Fin.le_last i').eq_or_lt with heq | hlt
        · simp [heq, columnMinor₂]
        · exact (hC _ _ hlt).le
      exact add_pos_of_nonneg_of_pos hleft (hC _ _ h0i)

theorem continuous_appendPositiveColumn₂ (C : Matrix (Fin 2) (Fin (n + 2)) ℝ) :
    Continuous (appendPositiveColumn₂ C) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold appendPositiveColumn₂
  split_ifs <;> fun_prop

theorem appendZeroColumn₂_mem_closure_positive
    (C : Matrix (Fin 2) (Fin (n + 2)) ℝ) (hC : HasPositiveMaximalMinors C) :
    appendZeroColumn₂ C ∈ closure (positiveGrassmannianInterior (k := 2) (n := n + 3)) := by
  have hm : Set.MapsTo (appendPositiveColumn₂ C) (Set.Ioi 0)
      (positiveGrassmannianInterior (k := 2) (n := n + 3)) := by
    intro ε hε
    exact appendPositiveColumn₂_positive C hC hε
  have hz : (0 : ℝ) ∈ closure (Set.Ioi 0) := by simp
  simpa using hm.closure (continuous_appendPositiveColumn₂ C) hz

theorem appendZeroColumn₂_mem_frontier_positive
    (C : Matrix (Fin 2) (Fin (n + 2)) ℝ) (hC : HasPositiveMaximalMinors C) :
    appendZeroColumn₂ C ∈ frontier (positiveGrassmannianInterior (k := 2) (n := n + 3)) := by
  rw [frontier, isOpen_positiveGrassmannianInterior.interior_eq]
  exact ⟨appendZeroColumn₂_mem_closure_positive C hC,
    appendZeroColumn₂_not_mem_positiveGrassmannianInterior (n + 2) (by omega) C⟩

end InfoGeometry.Topology
