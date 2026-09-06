import Mathlib

noncomputable section

namespace InfoGeometry.Algebra.CuntzKriegerAdjacencyBridge

/-- **Definition**: Cuntz-Krieger Algebra O_A Generators for Adjacency Matrix A (n x n).
    S_i* S_i = ∑_{j} A(i, j) S_j S_j*, and S_i* S_j = 0 for i ≠ j. -/
structure CuntzKriegerGenerators (n : ℕ) (R : Type*) [Ring R] where
  A : Fin n → Fin n → R
  S : Fin n → R
  Sstar : Fin n → R
  ck_relation : ∀ i : Fin n, Sstar i * S i = (Finset.univ : Finset (Fin n)).sum (fun j => A i j * (S j * Sstar j))
  ortho : ∀ i j : Fin n, i ≠ j → Sstar i * S j = 0

namespace CuntzKriegerGenerators

variable {n : ℕ} {R : Type*} [Ring R] (g : CuntzKriegerGenerators n R)

/-- Projection Operator P_j = S_j S_j*. -/
def proj (j : Fin n) : R := g.S j * g.Sstar j

/-- **Theorem**: Cuntz-Krieger Partial Isometry Identity.
    S_i* S_i = ∑_{j} A(i, j) P_j. -/
theorem partial_isometry_eq (i : Fin n) :
    g.Sstar i * g.S i = (Finset.univ : Finset (Fin n)).sum (fun j => g.A i j * g.proj j) :=
  g.ck_relation i

/-- **Theorem**: Forbidden Transition Annihilation.
    If A(i, j) = 0, then multiplying by P_j on the right annihilates the transition. -/
theorem forbidden_transition_annihilation (i j : Fin n) (hA : g.A i j = 0) :
    g.A i j * g.proj j = 0 := by
  dsimp [proj]
  rw [hA, zero_mul]

end CuntzKriegerGenerators

/-- **Theorem**: Master Cuntz-Krieger Adjacency Constraint Synthesis.
    Unifies:
    1. Cuntz-Krieger partial isometry relation S_i* S_i = ∑_{j} A(i, j) P_j.
    2. Distinct range orthogonality S_i* S_j = 0 for i ≠ j.
    3. Forbidden transition annihilation A(i, j) = 0 → A(i, j) P_j = 0. -/
theorem master_cuntz_krieger_adjacency_synthesis
    {n : ℕ} {R : Type*} [Ring R] (g : CuntzKriegerGenerators n R) (i j : Fin n) (h : i ≠ j) (hA : g.A i j = 0) :
    (g.Sstar i * g.S i = (Finset.univ : Finset (Fin n)).sum (fun k => g.A i k * g.proj k)) ∧
    (g.Sstar i * g.S j = 0) ∧
    (g.A i j * g.proj j = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact g.partial_isometry_eq i
  · exact g.ortho i j h
  · exact g.forbidden_transition_annihilation i j hA

end InfoGeometry.Algebra.CuntzKriegerAdjacencyBridge
