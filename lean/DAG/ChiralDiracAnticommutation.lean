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

def cellEquivSum {n0 n1 n2 : ℕ} :
    Cell n0 n1 n2 ≃ (Fin n0 ⊕ (Fin n1 ⊕ Fin n2)) where
  toFun
    | Cell.zero i => Sum.inl i
    | Cell.one i => Sum.inr (Sum.inl i)
    | Cell.two i => Sum.inr (Sum.inr i)
  invFun
    | Sum.inl i => Cell.zero i
    | Sum.inr (Sum.inl i) => Cell.one i
    | Sum.inr (Sum.inr i) => Cell.two i
  left_inv := by
    intro x
    cases x <;> rfl
  right_inv := by
    intro x
    cases x with
    | inl i => rfl
    | inr x => cases x <;> rfl

theorem cell_card {n0 n1 n2 : ℕ} :
    Fintype.card (Cell n0 n1 n2) = n0 + n1 + n2 := by
  rw [Fintype.card_congr (cellEquivSum (n0 := n0) (n1 := n1) (n2 := n2))]
  simp [Nat.add_assoc]

noncomputable def cellEightEightEquivFin16 :
    Cell 8 8 0 ≃ Fin 16 := by
  simpa using (Fintype.equivFin (Cell 8 8 0))

def cellEightEightFunctionEquiv :
    (Cell 8 8 0 → ℝ) ≃ₗ[ℝ] ((Fin 8 → ℝ) × (Fin 8 → ℝ)) where
  toFun f := (fun i => f (Cell.zero i), fun i => f (Cell.one i))
  invFun p := fun c => match c with
    | Cell.zero i => p.1 i
    | Cell.one i => p.2 i
    | Cell.two i => Fin.elim0 i
  left_inv := by
    intro f
    funext c
    cases c with
    | zero i => rfl
    | one i => rfl
    | two i => exact Fin.elim0 i
  right_inv := by
    intro p
    rcases p with ⟨p, q⟩
    rfl
  map_add' f g := by
    ext i <;> rfl
  map_smul' c f := by
    ext i <;> rfl

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

/-! The grading is an involution on the complete finite cell carrier. -/
theorem chiralGamma_sq {n0 n1 n2 : ℕ} :
  chiralGamma (n0 := n0) (n1 := n1) (n2 := n2) *
      chiralGamma (n0 := n0) (n1 := n1) (n2 := n2) = 1 := by
  ext i j
  unfold chiralGamma
  simp only [Matrix.mul_apply, Matrix.one_apply]
  cases i <;> cases j <;> simp [cellParity]

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

/-! The chiral trace of the finite off-diagonal Dirac operator vanishes. -/
theorem chiralGamma_trace_mul_dirac_zero {n0 n1 n2 : ℕ}
    (B1 : Matrix (Fin n0) (Fin n1) ℝ)
    (B2 : Matrix (Fin n1) (Fin n2) ℝ) :
  Matrix.trace
      (chiralGamma (n0 := n0) (n1 := n1) (n2 := n2) * diracOp B1 B2) = 0 := by
  unfold Matrix.trace chiralGamma diracOp
  simp [Matrix.mul_apply, cellParity]

/-! A reusable finite-dimensional trace consequence of an involutive grading. -/
theorem trace_mul_zero_of_involutive_anticommute
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Γ D : Matrix ι ι ℝ)
    (hodd : Γ * D + D * Γ = 0) :
    Matrix.trace (Γ * D) = 0 := by
  have hanti : D * Γ = -(Γ * D) := by
    apply eq_neg_of_add_eq_zero_left
    simpa [add_comm] using hodd
  have htrace : Matrix.trace (D * Γ) = Matrix.trace (Γ * D) :=
    Matrix.trace_mul_comm D Γ
  rw [hanti] at htrace
  have htrace' : -(Matrix.trace (Γ * D)) = Matrix.trace (Γ * D) := by
    simpa using htrace
  linarith

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

/-! Complete finite readout for the graded Dirac carrier. -/

theorem finite_chiral_dirac_capstone {n0 n1 n2 : ℕ}
    (B1 : Matrix (Fin n0) (Fin n1) ℝ)
    (B2 : Matrix (Fin n1) (Fin n2) ℝ) :
    chiralGamma (n0 := n0) (n1 := n1) (n2 := n2) *
          chiralGamma (n0 := n0) (n1 := n1) (n2 := n2) = 1 ∧
      chiralGamma * diracOp B1 B2 + diracOp B1 B2 * chiralGamma = 0 ∧
      Matrix.trace (chiralGamma * diracOp B1 B2) = 0 :=
  ⟨chiralGamma_sq,
    dirac_anticommutes_gamma B1 B2,
    chiralGamma_trace_mul_dirac_zero B1 B2⟩

end DAG.ChiralDiracAnticommutation
