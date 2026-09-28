import Mathlib.Algebra.Lie.SerreConstruction

/-!
# The E₁₀ generalized Cartan matrix and its Serre presentation

The diagram used here is the simply-laced tree with arms of lengths `1`, `2`, and `6`
at its trivalent vertex.  This file supplies the missing finite Cartan data to Mathlib's
generic Serre construction.  It does not claim a root-system classification, a hyperbolicity
criterion, a denominator formula, or a representation theorem.
-/

namespace InfoGeometry.Lie.E10

/-- The nine edges of the simply-laced E₁₀ diagram, with vertices numbered `0` through `9`.
The central vertex is `0`; the three arms are `0—1`, `0—2—3`, and
`0—4—5—6—7—8—9`.
-/
def edges : List (Nat × Nat) :=
  [(0, 1), (0, 2), (2, 3), (0, 4), (4, 5), (5, 6), (6, 7), (7, 8), (8, 9)]

theorem edges_length : edges.length = 9 := by
  decide

/-- Adjacency in the E₁₀ diagram.  `min`/`max` make the edge representation unoriented. -/
def Adjacent (i j : Fin 10) : Prop :=
  (min i.val j.val, max i.val j.val) ∈ edges

instance (i j : Fin 10) : Decidable (Adjacent i j) := by
  unfold Adjacent
  infer_instance

theorem adjacent_comm (i j : Fin 10) : Adjacent i j ↔ Adjacent j i := by
  simp [Adjacent, min_comm, max_comm]

/-- The simply-laced E₁₀ generalized Cartan matrix. -/
def cartanMatrix : Matrix (Fin 10) (Fin 10) ℤ := fun i j =>
  if i = j then 2 else if Adjacent i j then -1 else 0

@[simp] theorem cartanMatrix_diag (i : Fin 10) : cartanMatrix i i = 2 := by
  simp [cartanMatrix]

theorem cartanMatrix_symmetric (i j : Fin 10) :
    cartanMatrix i j = cartanMatrix j i := by
  by_cases hij : i = j
  · subst j
    simp [cartanMatrix]
  · have hji : j ≠ i := Ne.symm hij
    rw [cartanMatrix, cartanMatrix, if_neg hij, if_neg hji]
    by_cases hadj : Adjacent i j
    · have hji' : Adjacent j i := (adjacent_comm i j).mp hadj
      simp [hadj, hji']
    · have hji' : ¬ Adjacent j i := fun h => hadj ((adjacent_comm i j).mpr h)
      simp [hadj, hji']

theorem cartanMatrix_offdiag_nonpos {i j : Fin 10} (hij : i ≠ j) :
    cartanMatrix i j ≤ 0 := by
  rw [cartanMatrix, if_neg hij]
  by_cases hadj : Adjacent i j <;> simp [hadj]

theorem cartanMatrix_offdiag_eq_zero_iff {i j : Fin 10} (hij : i ≠ j) :
    cartanMatrix i j = 0 ↔ ¬ Adjacent i j := by
  rw [cartanMatrix, if_neg hij]
  by_cases hadj : Adjacent i j <;> simp [hadj]

/-- Mathlib's Serre quotient for the E₁₀ Cartan matrix, over `ℚ`.

This is the Lie algebra presented by generators `Hᵢ`, `Eᵢ`, `Fᵢ` and the Serre relations
encoded by `Matrix.ToLieAlgebra`; it is not a finite-dimensional matrix realization.
-/
noncomputable abbrev SerreAlgebra := Matrix.ToLieAlgebra ℚ cartanMatrix

end InfoGeometry.Lie.E10
