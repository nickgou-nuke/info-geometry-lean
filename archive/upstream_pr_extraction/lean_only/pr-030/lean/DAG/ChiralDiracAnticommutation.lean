import Mathlib
import DAG.TwoComplex

/-!
# Chiral Dirac Anticommutation — ΓD + DΓ = 0

Proves the fundamental anticommutation relation for the graph Dirac
operator on the TwoComplex. Uses Mathlib's `Matrix` with explicit
Cell constructors for nodes (zero), edges (one), and faces (two).

## Theorem

ΓD + DΓ = 0 for any boundary matrices B1 = ∂₁, B2 = ∂₂.

The parity is +1 for nodes/faces, -1 for edges. Since every nonzero
block of D connects cells of opposite parity, the sum cancels.
-/

namespace DAG.ChiralDiracAnticommutation

open DAG

/--
Total graded state space: `zero` = nodes, `one` = edges, `two` = faces.
-/
inductive Cell (n0 n1 n2 : ℕ)
  | zero : Fin n0 → Cell n0 n1 n2
  | one  : Fin n1 → Cell n0 n1 n2
  | two  : Fin n2 → Cell n0 n1 n2

deriving instance DecidableEq, Fintype for Cell

def cellParity {n0 n1 n2 : ℕ} : Cell n0 n1 n2 → ℝ
  | Cell.zero _ => 1
  | Cell.one  _ => -1
  | Cell.two  _ => 1

/--
Γ = diag(+1 on nodes, -1 on edges, +1 on faces).
Since Γ is diagonal, (ΓD)ij = Γii * Dij and (DΓ)ij = Dij * Γjj.
The product at (i,j) is Dij * (Γii + Γjj).
-/
def chiralGamma {n0 n1 n2 : ℕ} : Matrix (Cell n0 n1 n2) (Cell n0 n1 n2) ℝ :=
  λ i j => if i = j then cellParity i else 0

/--
D = [0 δ₀ 0; ∂₁ 0 δ₁; 0 ∂₂ 0]
with B1 = ∂₁ (node→edge) and B2 = ∂₂ (edge→face).
-/
def diracOp {n0 n1 n2 : ℕ}
  (B1 : Matrix (Fin n0) (Fin n1) ℝ)
  (B2 : Matrix (Fin n1) (Fin n2) ℝ) : Matrix (Cell n0 n1 n2) (Cell n0 n1 n2) ℝ
  | Cell.zero i, Cell.one j  => B1 i j
  | Cell.one i,  Cell.zero j => B1 j i
  | Cell.one i,  Cell.two j  => B2 i j
  | Cell.two i,  Cell.one j  => B2 j i
  | _, _ => 0

/--
**Theorem**: ΓD + DΓ = 0.

Proof by cases on the Cell constructors. For every (i,j):
  (ΓD + DΓ)ij = Dij * (Γii + Γjj)

When i=j, Dij = 0 (D has zero diagonal blocks), so the product is 0.
When i≠j, D is nonzero only for adjacent cell types (zero↔one, one↔two).
In those cases Γii + Γjj = parity(i) + parity(j) = 1 + (-1) = 0.
-/
theorem dirac_anticommutes_gamma {n0 n1 n2 : ℕ}
  (B1 : Matrix (Fin n0) (Fin n1) ℝ) (B2 : Matrix (Fin n1) (Fin n2) ℝ) :
  chiralGamma * diracOp B1 B2 + diracOp B1 B2 * chiralGamma = 0 := by
  ext i j
  unfold chiralGamma diracOp
  -- Compute (ΓD)ij = Γii * Dij and (DΓ)ij = Dij * Γjj
  -- Use Matrix.mul_apply to expand the product
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.zero_apply]
  -- Now we have: (Σ_k Γik * Dkj) + (Σ_k Dik * Γkj) = 0
  -- Since Γ is diagonal, Γik = 0 when i≠k and Γkj = 0 when k≠j
  -- So only the k=i term in the first sum and k=j term in the second survive:
  -- Γii * Dij + Dij * Γjj = Dij * (Γii + Γjj)
  -- And we verify that for all (i,j), this is 0.
  cases i <;> cases j <;> simp [cellParity]

end DAG.ChiralDiracAnticommutation
