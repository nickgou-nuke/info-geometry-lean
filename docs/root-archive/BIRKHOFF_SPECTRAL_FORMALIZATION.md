# Steepest Descent on Birkhoff Polytope with Spectral Norm
## Multi-System Formalization & Codebase Weakness Audit

**Source**: https://leloykun.github.io/ponder/steepest-descent-doubly-stochastic/
**Author**: Franz Louis Cesista (2026-01-04)

---

## 1. MATHEMATICAL CONTENT SUMMARY

### Core Objects
| Object | Definition | Key Property |
|--------|------------|--------------|
| **Birkhoff polytope** $\mathcal{B}_n$ | $\{W \in \mathbb{R}^{n \times n} \mid W\mathbf{1}=\mathbf{1}, W^\top\mathbf{1}=\mathbf{1}, W \geq 0\}$ | Convex polytope, not a smooth manifold (has boundaries/corners) |
| **Spectral norm** $\|\cdot\|_{2\to 2}$ | $\|A\|_{2\to 2} = \sigma_{\max}(A)$ | LMO: $\texttt{LMO}(G) = -\texttt{msign}(G) = -UV^\top$ for SVD $G=U\Sigma V^\top$ |
| **Tangent space** (interior) $T_W\mathcal{B}_n^+$ | $\{A \mid A\mathbf{1}=0, A^\top\mathbf{1}=0\}$ | Zero row/column sums |
| **Tangent cone** (boundary) $T_W\mathcal{B}_n$ | $\{A \mid A\mathbf{1}=0, A^\top\mathbf{1}=0, A_{ij} \geq 0 \text{ where } W_{ij}=0\}$ | Inward-only movement on zero entries |
| **Matrix sign** $\texttt{msign}(G)$ | $UV^\top$ for SVD $G=U\Sigma V^\top$ | LMO for spectral norm |

### Optimization Framework
1. **Primal**: $A^*_t = \arg\min_{A \in T_{W_t}\mathcal{B}_n} \langle G_t, A \rangle$ s.t. $\|A\|_{2\to 2} \leq \eta$
2. **Dual ascent** on $K^\dagger = \mathbb{R}^n \times \mathbb{R}^n \times \mathbb{R}_-^{|\{(i,j):W_{ij}=0\}|}$
3. **Retraction**: Dykstra's algorithm (metric projection), not Sinkhorn-Knopp (entropic projection)

### Dual Ascent Updates
```
A^j = -η · msign(G_t + S₁1^⊤ + 1S₂^⊤ + S₃ ⊙ M)
S₁^{j+1} = S₁^j + σ · A^j 1
S₂^{j+1} = S₂^j + σ · (A^j)^⊤ 1
S₃^{j+1} = min((S₃^j + σ · (A^j ⊙ M)) ⊙ M, 0)
```
where $M_{ij} = 1$ if $W_{ij}=0$, else $0$.

---

## 2. 8-SYSTEM FORMALIZATION

### 2.1 Lean 4 (Mathlib4) - `lean/InfoGeometry/Optimization/BirkhoffSpectral.lean`

```lean
/-- Steepest Descent on Birkhoff Polytope with Spectral Norm -/
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.LinearAlgebra.Matrix.SVD
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Optimization.Convex.Basic

open Matrix

/- 1. Birkhoff Polytope -/
structure BirkhoffPolytope (n : ℕ) (R : Type*) [OrderedSemiring R] where
  carrier : Matrix (Fin n) (Fin n) R
  row_sum : ∀ i, ∑ j, carrier i j = 1
  col_sum : ∀ j, ∑ i, carrier i j = 1
  nonneg : ∀ i j, 0 ≤ carrier i j

/- 2. Spectral Norm LMO -/
def msign {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (G.svd).1.mul (G.svd).2.transpose

def LMO_spectral {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  -msign G

/- 3. Tangent Cone -/
def tangentCone {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  { A : Matrix (Fin n) (Fin n) ℝ |
      (∑ j, A i j = 0) ∧ (∑ i, A i j = 0) ∧
      ∀ i j, W i j = 0 → 0 ≤ A i j }

/- 4. Dual Ascent State -/
structure DualAscentState {n : ℕ} where
  S₁ : Matrix (Fin n) (Fin 1) ℝ
  S₂ : Matrix (Fin 1) (Fin n) ℝ
  S₃ : Matrix (Fin n) (Fin n) ℝ

/- 5. Dual Ascent Step -/
def dualAscentStep {n : ℕ} (η σ : ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    (M : Matrix (Fin n) (Fin n) Bool) (state : DualAscentState n) : DualAscentState n :=
  let A := -η • LMO_spectral (G + state.S₁.mul (1 : Matrix (Fin n) (Fin 1) ℝ).transpose
                                + (1 : Matrix (Fin 1) (Fin n) ℝ).transpose.mul state.S₂
                                + state.S₃.mul M.toMatrix)
  { S₁ := state.S₁ + σ • A.mul (1 : Matrix (Fin n) (Fin 1) ℝ),
    S₂ := state.S₂ + σ • A.transpose.mul (1 : Matrix (Fin 1) (Fin n) ℝ),
    S₃ := Matrix.of fun i j => min ((state.S₃ i j + σ * (A i j * M i j.toReal)) * M i j.toReal) 0 }

/- 6. Dykstra's Algorithm for Metric Projection -/
def birkhoffProjectDykstra {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (maxIters : ℕ := 500) (tol : ℝ := 1e-6) : Matrix (Fin n) (Fin n) ℝ :=
  -- Dykstra's algorithm with projections onto nonneg, row sums=1, col sums=1
  sorry

/- 7. Main Theorem: Descent Magnitude -/
theorem descentMagnitudePositive {n : ℕ} (W : BirkhoffPolytope n ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    (A_star : Matrix (Fin n) (Fin n) ℝ) :
    ⟨G, birkhoffProjectDykstra (W + A_star) - W⟩ ≥ ⟨G, LMO_spectral G⟩ :=
  sorry
```

### 2.2 Coq (MathComp/Coquelicot) - `coq/BirkhoffSpectral.v`

```coq
Require Import MathComp.Analysis.Reals.
Require Import MathComp.Matrix.Matrix.
Require Import Coquelicot.Coquelicot.

(* 1. Birkhoff Polytope as a subset of 'M[R]_(n,n) *)
Definition BirkhoffPolytope (n : nat) :=
  [set A : 'M[R]_n | (∀ i, \sum_j A i j = 1) ∧ (∀ j, \sum_i A i j = 1) ∧ (∀ i j, 0 <= A i j)].

(* 2. Spectral norm via SVD (requires SVD formalization) *)
Definition msign (G : 'M[R]_n) : 'M[R]_n :=
  let (U, _, V) := svd G in U * V^T.

Definition LMO_spectral (G : 'M[R]_n) := -msign G.

(* 3. Tangent cone *)
Definition tangentCone (W : 'M[R]_n) :=
  [set A : 'M[R]_n | (∀ i, \sum_j A i j = 0) ∧ (∀ j, \sum_i A i j = 0) ∧
                      (∀ i j, W i j = 0 -> 0 <= A i j)].

(* 4. Dual ascent updates *)
Record DualState (n : nat) := {
  S1 : 'M[R]_(n,1);
  S2 : 'M[set (S1, S2, S3 : 'M[R]_(1,n) × 'M[R]_n);
  S3 : 'M[R]_n }.

(* 5. Dykstra projection *)
Fixpoint dykstra_step (A : 'M[R]_n) (P1 P2 P3 : 'M[R]_n) :=
  let Y1 := max 0 (A + P1) in
  let P1' := (A + P1) - Y1 in
  let Y2 := proj_row_sums (Y1 + P2) in
  let P2' := (Y1 + P2) - Y2 in
  let Y3 := proj_col_sums (Y2 + P3) in
  let P3' := (Y2 + P3) - Y3 in
  (Y3, P1', P2', P3').

(* 6. Main theorem *)
Theorem descent_magnitude_improves :
  ∀ (W : BirkhoffPolytope n) (G : 'M[R]_n),
  ∃ A_star : tangentCone W,
  ⟨G, birkhoff_project_dykstra (W + A_star) - W⟩ >= ⟨G, LMO_spectral G⟩.
Proof. Admitted.
```

### 2.3 Isabelle/HOL - `isabelle/BirkhoffSpectral.thy`

```isabelle
theory BirkhoffSpectral
imports "HOL-Analysis.Convex" "HOL-Library.Matrix" "HOL-Analysis.SVD"
begin

(* 1. Birkhoff Polytope *)
definition birkhoff_polytope :: "nat ⇒ ('a::ordered_semiring) matrix set" where
  "birkhoff_polytope n = {W :: 'a matrix. dim_row W = n ∧ dim_col W = n ∧
    (∀i. (∑j. W $$ (i,j)) = 1) ∧ (∀j. (∑i. W $$ (i,j)) = 1) ∧ (∀i j. 0 ≤ W $$ (i,j))}"

(* 2. Spectral norm LMO *)
definition msign :: "real matrix ⇒ real matrix" where
  "msign G = (let (U, Σ, V) = svd G in U * V^T)"

definition LMO_spectral :: "real matrix ⇒ real matrix" where
  "LMO_spectral G = -msign G"

(* 3. Tangent cone *)
definition tangent_cone :: "real matrix ⇒ real matrix set" where
  "tangent_cone W = {A. (∀i. (∑j. A $$ (i,j)) = 0) ∧ (∀j. (∑i. A $$ (i,j)) = 0) ∧
    (∀i j. W $$ (i,j) = 0 ⟶ 0 ≤ A $$ (i,j))}"

(* 4. Dual ascent state *)
record dual_state = S1 :: "real matrix" + S2 :: "real matrix" + S3 :: "real matrix"

(* 5. Dual ascent step *)
definition dual_ascent_step :: "real ⇒ real ⇒ real matrix ⇒ bool matrix ⇒ dual_state ⇒ dual_state" where
  "dual_ascent_step η σ G M state = (
    let A = -η • LMO_spectral (G + S1 * 1⇩1^T + 1⇩1 * S2^T + S3 ⊙ M);
    S1' = S1 + σ • A * 1⇩1;
    S2' = S2 + σ • A^T * 1⇩1;
    S3' = min ((S3 + σ • (A ⊙ M)) ⊙ M) 0
  )"

(* 6. Dykstra's algorithm *)
fun dykstra :: "nat ⇒ real matrix ⇒ real matrix ⇒ real matrix ⇒ real matrix ⇒ real matrix" where
  "dykstra 0 A P1 P2 P3 = A" |
  "dykstra (Suc k) A P1 P2 P3 =
    (let Y1 = max 0 (A + P1); P1' = (A + P1) - Y1;
         Y2 = proj_row_sums (Y1 + P2); P2' = (Y1 + P2) - Y2;
         Y3 = proj_col_sums (Y2 + P3); P3' = (Y2 + P3) - Y3;
     in dykstra k Y3 P1' P2' P3')"

(* 7. Main theorem *)
theorem descent_magnitude_improves:
  assumes "W ∈ birkhoff_polytope n" "G ∈ carrier_mat n n"
  shows "∃A_star ∈ tangent_cone W. ⟨G, birkhoff_project_dykstra (W + A_star) - W⟩ ≥ ⟨G, LMO_spectral G⟩"
  sorry

end
```

### 2.4 SymPy - `tools/sympy/birkhoff_spectral.py`

```python
import sympy as sp
import numpy as np
from sympy.matrices import Matrix, eye, zeros
from sympy import SVD, Min, Max, sqrt, symbols, Function

class BirkhoffSpectral:
    def __init__(self, n):
        self.n = n
        self.M = None  # mask for boundary points
    
    def msign(self, G):
        """Matrix sign function: msign(G) = U @ V.T for SVD G = U @ Σ @ V.T"""
        U, _, V = G.singular_value_decomposition()
        return U * V.T
    
    def LMO_spectral(self, G):
        """Linear minimization oracle for spectral norm"""
        return -self.msign(G)
    
    def tangent_cone_mask(self, W, tol=1e-8):
        """Mask M where M_ij = 1 if W_ij ≈ 0 (boundary)"""
        self.M = (abs(W) <= tol).astype(int)
        return self.M
    
    def dual_ascent_step(self, G, state, eta, sigma):
        """Single dual ascent step"""
        # A = -η * msign(G + S1 @ 1^T + 1 @ S2.T + S3 ⊙ M)
        M = sp.Matrix(self.M) if self.M is not None else sp.ones(self.n, self.n)
        ones_n1 = sp.ones(self.n, 1)
        ones_1n = sp.ones(1, self.n)
        
        S1, S2, S3 = state.S1, state.S2, state.S3
        
        grad = G + S1 * ones_1n + ones_n1 * S2.T + sp.Matrix.multiply_elementwise(S3, M)
        A = -eta * self.msign(grad)
        
        # S1 += σ * A @ 1
        S1_new = S1 + sigma * A * ones_n1
        # S2 += σ * A.T @ 1
        S2_new = S2 + sigma * A.T * ones_n1
        # S3 = min((S3 + σ * (A ⊙ M)) ⊙ M, 0)
        S3_new = sp.Matrix([[Min((S3[i,j] + sigma * A[i,j] * M[i,j]) * M[i,j], 0) 
                            for j in range(self.n)] for i in range(self.n)])
        
        return DualState(S1_new, S2_new, S3_new), A
    
    def dykstra_projection(self, A, max_iters=500, tol=1e-6):
        """Dykstra's algorithm for metric projection onto Birkhoff polytope"""
        n = A.rows
        P1, P2, P3 = zeros(n, n), zeros(n, n), zeros(n, n)
        X = sp.Matrix(A)
        
        def residual(X):
            rs = max([abs(sum(X[i, j] for j in range(n)) - 1) for i in range(n)])
            cs = max([abs(sum(X[i, j] for i in range(n)) - 1) for j in range(n)])
            neg = max([max(-X[i, j], 0) for i in range(n) for j in range(n)])
            return max(rs, cs, neg)
        
        for k in range(max_iters):
            # proj_nonneg
            Y1 = sp.Matrix([[max(X[i, j] + P1[i, j], 0) for j in range(n)] for i in range(n)])
            P1 = sp.Matrix([[X[i, j] + P1[i, j] - Y1[i, j] for j in range(n)] for i in range(n)])
            
            # proj_row_sums (target=1)
            row_sums = [sum(Y1[i, j] + P2[i, j] for j in range(n)) for i in range(n)]
            Y2 = sp.Matrix([[Y1[i, j] + P2[i, j] - (row_sums[i] - 1)/n for j in range(n)] for i in range(n)])
            P2 = sp.Matrix([[Y1[i, j] + P2[i, j] - Y2[i, j] for j in range(n)] for i in range(n)])
            
            # proj_col_sums (target=1)
            col_sums = [sum(Y2[i, j] + P3[i, j] for i in range(n)) for j in range(n)]
            Y3 = sp.Matrix([[Y2[i, j] + P3[i, j] - (col_sums[j] - 1)/n for j in range(n)] for i in range(n)])
            P3 = sp.Matrix([[Y2[i, j] + P3[i, j] - Y3[i, j] for j in range(n)] for i in range(n)])
            
            X = Y3
            if residual(X) < tol:
                break
        
        return X
    
    def descent_magnitude(self, W, G, A_star):
        """⟨G, retract(W + A*) - W⟩"""
        W_new = self.dykstra_projection(W + A_star)
        return sp.trace(G.T * (W_new - W))

# Dual state container
class DualState:
    def __init__(self, S1, S2, S3):
        self.S1, self.S2, self.S3 = S1, S2, S3
```

### 2.5 SageMath - `tools/sage/birkhoff_spectral.sage`

```python
from sage.all import *
import numpy as np

class BirkhoffPolytope:
    def __init__(self, n, base_ring=RR):
        self.n = n
        self.R = base_ring
    
    def msign(self, G):
        """Matrix sign via SVD: msign(G) = U * V^T"""
        U, S, V = G.SVD()
        return U * V.T
    
    def LMO_spectral(self, G):
        return -self.msign(G)
    
    def tangent_cone(self, W, tol=1e-10):
        """Return basis for tangent cone at W"""
        n = self.n
        M = matrix(n, n, lambda i,j: 1 if abs(W[i,j]) <= tol else 0)
        # Constraints: A*1=0, A.T*1=0, A_ij >= 0 where W_ij=0
        return M
    
    def dual_ascent_step(self, G, state, eta, sigma):
        """Dual ascent step with symbolic/numeric computation"""
        n = self.n
        ones_n1 = matrix(n, 1, [1]*n)
        ones_1n = matrix(1, n, [1]*n)
        M = state.M
        
        S1, S2, S3 = state.S1, state.S2, state.S3
        
        grad = G + S1 * ones_1n + ones_n1 * S2.T + S3.elementwise_product(M)
        A = -eta * self.msign(grad)
        
        S1_new = S1 + sigma * A * ones_n1
        S2_new = S2 + sigma * A.T * ones_n1
        S3_new = matrix(n, n, lambda i,j: min((S3[i,j] + sigma * A[i,j] * M[i,j]) * M[i,j], 0))
        
        return DualState(S1_new, S2_new, S3_new, M), A
    
    def dykstra_projection(self, A, max_iters=500, tol=1e-10):
        """Dykstra's algorithm for Birkhoff polytope projection"""
        n = self.n
        P1, P2, P3 = zero_matrix(n,n), zero_matrix(n,n), zero_matrix(n,n)
        X = matrix(A)
        
        def residual(X):
            rs = max(abs(sum(X[i,j] for j in range(n)) - 1) for i in range(n))
            cs = max(abs(sum(X[i,j] for i in range(n)) - 1) for j in range(n))
            neg = max(max(-X[i,j], 0) for i in range(n) for j in range(n))
            return max(rs, cs, neg)
        
        for k in range(max_iters):
            # proj_nonneg
            Y1 = matrix(n, n, lambda i,j: max(X[i,j] + P1[i,j], 0))
            P1 = X + P1 - Y1
            
            # proj_row_sums(target=1)
            row_sums = [sum(Y1[i,j] + P2[i,j] for j in range(n)) for i in range(n)]
            Y2 = matrix(n, n, lambda i,j: Y1[i,j] + P2[i,j] - (row_sums[i] - 1)/n)
            P2 = Y1 + P2 - Y2
            
            # proj_col_sums(target=1)
            col_sums = [sum(Y2[i,j] + P3[i,j] for i in range(n)) for j in range(n)]
            Y3 = matrix(n, n, lambda i,j: Y2[i,j] + P3[i,j] - (col_sums[j] - 1)/n)
            P3 = Y2 + P3 - Y3
            
            X = Y3
            if residual(X) < tol:
                break
        
        return X
    
    def descent_magnitude(self, W, G, A_star):
        W_new = self.dykstra_projection(W + A_star)
        return (G.T * (W_new - W)).trace()

class DualState:
    def __init__(self, S1, S2, S3, M):
        self.S1, self.S2, self.S3, self.M = S1, S2, S3, M
```

### 2.6 GAP - `tools/gap/birkhoff_spectral.g`

```gap
# Birkhoff Polytope Steepest Descent in GAP

# 1. Matrix sign function via SVD
Msign := function(G)
    local U, S, V;
    [U, S, V] := SingularValueDecomposition(G);
    return U * TransposedMat(V);
end;

LMO_Spectral := function(G)
    return -Msign(G);
end;

# 2. Tangent cone mask
TangentConeMask := function(W, tol)
    local n, M, i, j;
    n := Length(W);
    M := NullMat(n, n);
    for i in [1..n] do
        for j in [1..n] do
            if AbsInt(W[i][j]) <= tol then
                M[i][j] := 1;
            else
                M[i][j] := 0;
            fi;
        od;
    od;
    return M;
end;

# 3. Dual ascent state
DualState := rec(
    S1 := null,
    S2 := null,
    S3 := null,
    M := null
);

# 4. Dual ascent step
DualAscentStep := function(G, state, eta, sigma)
    local n, ones_n1, ones_1n, M, S1, S2, S3, grad, A, S1_new, S2_new, S3_new;
    n := Length(G);
    ones_n1 := List([1..n], x -> [1]);
    ones_1n := List([1..n], x -> 1);
    M := state.M;
    S1 := state.S1; S2 := state.S2; S3 := state.S3;
    
    # grad = G + S1 * ones_1n + ones_n1 * S2^T + S3 ⊙ M
    grad := G + S1 * ones_1n + ones_n1 * TransposedMat(S2);
    for i in [1..n] do
        for j in [1..n] do
            grad[i][j] := grad[i][j] + S3[i][j] * M[i][j];
        od;
    od;
    
    A := -eta * Msign(grad);
    
    S1_new := S1 + sigma * A * ones_n1;
    S2_new := S2 + sigma * TransposedMat(A) * ones_n1;
    
    S3_new := NullMat(n, n);
    for i in [1..n] do
        for j in [1..n] do
            S3_new[i][j] := Minimum([(S3[i][j] + sigma * A[i][j] * M[i][j]) * M[i][j], 0]);
        od;
    od;
    
    state.S1 := S1_new;
    state.S2 := S2_new;
    state.S3 := S3_new;
    
    return A;
end;

# 5. Dykstra's algorithm
DykstraProjection := function(A, max_iters, tol)
    local n, P1, P2, P3, X, k, Y1, Y2, Y3, row_sums, col_sums, res;
    n := Length(A);
    P1 := NullMat(n, n); P2 := NullMat(n, n); P3 := NullMat(n, n);
    X := ShallowCopy(A);
    
    res := function(X)
        local rs, cs, neg, i, j;
        rs := Maximum(List([1..n], i -> AbsInt(Sum([1..n], j -> X[i][j]) - 1)));
        cs := Maximum(List([1..n], j -> AbsInt(Sum([1..n], i -> X[i][j]) - 1)));
        neg := Maximum(List([1..n], i -> Maximum(List([1..n], j -> Maximum([0, -X[i][j]])))));
        return Maximum([rs, cs, neg]);
    end;
    
    for k := 500;
    for k in [1..max_iters] do
        # proj_nonneg
        Y1 := List([1..n], i -> List([1..n], j -> Maximum([0, X[i][j] + P1[i][j]])));
        P1 := X + P1 - Y1;
        
        # proj_row_sums
        row_sums := List([1..n], i -> Sum([1..n], j -> Y1[i][j] + P2[i][j]));
        Y2 := List([1..n], i -> List([1..n], j -> Y1[i][j] + P2[i][j] - (row_sums[i] - 1)/n));
        P2 := Y1 + P2 - Y2;
        
        # proj_col_sums
        col_sums := List([1..n], j -> Sum([1..n], i -> Y2[i][j] + P3[i][j]));
        Y3 := List([1..n], i -> List([1..n], j -> Y2[i][j] + P3[i][j] - (col_sums[j] - 1)/n));
        P3 := Y2 + P3 - Y3;
        
        X := Y3;
        if res(X) < tol then break; fi;
    od;
    
    return X;
end;

# 6. Descent magnitude
DescentMagnitude := function(W, G, A_star)
    local W_new;
    W_new := DykstraProjection(W + A_star);
    return Trace(TransposedMat(G) * (W_new - W));
end;
```

### 2.7 Macaulay2 - `tools/macaulay2/birkhoff_spectral.m2`

```macaulay2
-- Birkhoff Polytope Steepest Descent in Macaulay2

-- 1. Matrix sign via SVD
msign = method()
msign Matrix := G -> (
    U := first singularValueDecomposition G;
    V := last singularValueDecomposition G;
    U * transpose V
)

LMO_spectral = method()
LMO_spectral Matrix := G -> -msign G

-- 2. Tangent cone mask
tangentConeMask = (W, tol) -> (
    n := numgens source W;
    M := matrix apply(n, i -> apply(n, j -> if abs(W_(i,j)) <= tol then 1 else 0));
    M
)

-- 3. Dual state
DualState = new Type of MutableHashTable
DualState.S1 = MutableMatrix
DualState.S2 = MutableMatrix
DualState.S3 = MutableMatrix
DualState.M = MutableMatrix

-- 4. Dual ascent step
dualAscentStep = (G, state, eta, sigma) -> (
    n := numgens source G;
    ones_n1 := matrix apply(n, i -> {{1}});
    ones_1n := matrix apply(1, i -> apply(n, j -> 1));
    
    M := state#M;
    S1 := state#S1; S2 := state#S2; S3 := state#S3;
    
    grad := G + S1 * ones_1n + ones_n1 * transpose S2;
    for i from 0 to n-1 do for j from 0 to n-1 do
        grad_(i,j) = grad_(i,j) + S3_(i,j) * M_(i,j);
    
    A := -eta * msign grad;
    
    state#S1 = S1 + sigma * A * ones_n1;
    state#S2 = S2 + sigma * transpose A * ones_n1;
    state#S3 = matrix apply(n, i -> apply(n, j -> min((S3_(i,j) + sigma * A_(i,j) * M_(i,j)) * M_(i,j), 0)));
    
    A
)

-- 5. Dykstra's algorithm
dykstraProjection = (A, max_iters, tol) -> (
    n := numgens source A;
    P1 := mutableMatrix n n 0;
    P2 := mutableMatrix n n 0;
    P3 := mutableMatrix n n 0;
    X := mutableMatrix A;
    
    residual = () -> (
        rs := max apply(n, i -> abs(sum(0..n-1, j -> X_(i,j)) - 1));
        cs := max apply(n, j -> abs(sum(0..n-1, i -> X_(i,j)) - 1));
        neg := max apply(n, i -> max apply(n, j -> max(0, -X_(i,j))));
        max(rs, cs, neg)
    );
    
    for k from 1 to max_iters do (
        -- proj_nonneg
        Y1 := mutableMatrix n n 0;
        for i from 0 to n-1 do for j from 0 to n-1 do
            Y1_(i,j) = max(X_(i,j) + P1_(i,j), 0);
        P1 = X + P1 - Y1;
        
        -- proj_row_sums
        row_sums := apply(n, i -> sum(0..n-1, j -> Y1_(i,j) + P2_(i,j)));
        Y2 := mutableMatrix n n 0;
        for i from 0 to n-1 do for j from 0 to n-1 do
            Y2_(i,j) = Y1_(i,j) + P2_(i,j) - (row_sums#i - 1)/n;
        P2 = Y1 + P2 - Y2;
        
        -- proj_col_sums
        col_sums := apply(n, j -> sum(0..n-1, i -> Y2_(i,j) + P3_(i,j)));
        Y3 := mutableMatrix n n 0;
        for i from 0 to n-1 do for j from 0 to n-1 do
            Y3_(i,j) = Y2_(i,j) + P3_(i,j) - (col_sums#j - 1)/n;
        P3 = Y2 + P3 - Y3;
        
        X = Y3;
        if residual() < tol then break;
    );
    
    X
)

-- 6. Descent magnitude
descentMagnitude = (W, G, A_star) -> (
    W_new := dykstraProjection(W + A_star);
    trace(transpose G * (W_new - W))
)
```

### 2.8 D-Modules - `tools/dmodules/birkhoff_spectral.m2`

```macaulay2
-- D-Module Perspective on Birkhoff Spectral Descent
-- The optimization flow as a D-module on the space of matrices

restart
loadPackage "Dmodules"

-- 1. Ring of differential operators on matrix space
R = QQ[x_(1,1)..x_(n,n), dx_(1,1)..dx_(n,n), WeylAlgebra => true]

-- 2. Birkhoff constraints as D-module
birkhoffConstraints = (
    -- Row sums = 1: sum_j x_(i,j) - 1 = 0
    apply(n, i -> sum(apply(n, j -> x_(i,j))) - 1) |
    -- Col sums = 1: sum_i x_(i,j) - 1 = 0  
    apply(n, j -> sum(apply(n, i -> x_(i,j))) - 1)
)

-- 3. Spectral norm constraint as differential operator
-- ||A||_2 = sigma_max(A) -> characteristic polynomial of A^T A
-- This gives a D-module structure on the optimization flow

-- 4. Dual ascent as D-module morphism
-- The dual variables S1, S2, S3 live in the cotangent space

-- 5. Dykstra projection as solution to D-module system
-- Each projection step solves a linear system

-- 6. Main theorem: D-module version of descent magnitude
-- The holonomic rank of the optimization D-module gives convergence rate
```

---

## 3. WEAK & VAGUE PARTS IN CODEBASE

### 3.1 Critical Missing Infrastructure

| Component | Status | Issue |
|-----------|--------|-------|
| **SVD in Lean 4** | ❌ Missing | Mathlib4 has `Matrix.svd` only for `ℝ` with `IsROrC`; no generic SVD over `ℝ` with `msign` |
| **Matrix sign function** | ❌ Missing | No `msign` in any system; requires SVD + sign of singular values |
| **Dykstra's algorithm** | ❌ Missing | Only JAX implementation exists; no formal verification in any system |
| **Birkhoff polytope type** | ⚠️ Partial | `Matrix.doublyStochastic` exists in Mathlib but no tangent cone structure |
| **Spectral norm LMO** | ❌ Missing | No `LMO_spectral` in any formal system |
| **Dual ascent framework** | ❌ Missing | The generic dual ascent from "Finsler dual ascent" post not formalized |

### 3.2 Vague Mathematical Claims

| Claim | Location | Why Vague |
|-------|----------|-----------|
| "Our optimizer yields larger effective weight updates" | Section 3.1 | No formal theorem statement; "effective weight update" not defined |
| "Dykstra's algorithm converges" | Appendix A2 | No convergence proof; no rate given |
| "Dual ascent converges" | Section 2.2 | No convergence guarantee for non-smooth cone constraints |
| "Tangent cone representation is standard" | Section 2.2 | No reference to standard form in literature |
| "Metric projection vs entropic projection" | Section 2.3 | No proof that Dykstra = metric projection for Birkhoff |

### 3.3 Implementation Gaps

| File | Missing |
|------|---------|
| `lean/InfoGeometry/Optimization/` | Entire directory missing |
| `tools/sympy/birkhoff_spectral.py` | No verification harness |
| `tools/sage/birkhoff_spectral.sage` | No cross-check with JAX |
| `tools/gap/birkhoff_spectral.g` | No matrix SVD in GAP core |
| `tools/macaulay2/birkhoff_spectral.m2` | No SVD in M2 core (needs `Macaulay2/SVD` package) |
| `isabelle/BirkhoffSpectral.thy` | No SVD in HOL-Analysis |

### 3.4 Architectural Weaknesses

1. **No unified optimization framework**: The dual ascent framework from "Finsler dual ascent" post is referenced but not formalized anywhere.

2. **Missing cross-system verification**: No harness to verify that Lean/Coq/Isabelle/SymPy/Sage/GAP/M2 all compute the same dual ascent steps.

3. **No tangent cone library**: The tangent cone structure for polytopes with boundaries is not abstracted.

4. **Spectral norm LMO not generalized**: The `msign` function works only for full-rank matrices; no handling of degenerate cases.

5. **No complexity analysis**: No formal bounds on dual ascent iterations, Dykstra iterations, or SVD computation.

---

## 4. IMMEDIATE NEXT STEPS

### Priority 1: Core Infrastructure
```bash
# 1. Add SVD + msign to Lean 4 (Mathlib PR)
# 2. Implement Birkhoff polytope + tangent cone in Lean
# 3. Port dual ascent framework from "Finsler dual ascent" post

# Files to create:
lean/InfoGeometry/Optimization/BirkhoffPolytope.lean
lean/InfoGeometry/Optimization/SpectralNormLMO.lean
lean/InfoGeometry/Optimization/DualAscent.lean
lean/InfoGeometry/Optimization/DykstraProjection.lean
lean/InfoGeometry/Optimization/SteepestDescent.lean
```

### Priority 2: Cross-System Verification
```python
# tools/verify_birkhoff.py
# Runs identical test cases across all 8 systems
# Compares dual ascent steps, projections, descent magnitudes
```

### Priority 3: Formal Theorems
```lean
-- Main theorems to prove:
theorem dykstra_converges : ∀ A, ∃ W ∈ BirkhoffPolytope, W = dykstra A
theorem dual_ascent_converges : ∀ G W, ∃ A* ∈ tangentCone W, optimal
theorem descent_magnitude_improves : ⟨G, retract(W+A*) - W⟩ ≥ ⟨G, LMO G⟩
```

---

## 5. CODEBASE WEAKNESS SUMMARY

| Severity | Component | Description |
|----------|-----------|-------------|
| **CRITICAL** | SVD infrastructure | No SVD in Lean/Isabelle/Coq/GAP/M2 for `msign` |
| **CRITICAL** | Dual ascent framework | Referenced but not formalized |
| **HIGH** | Dykstra's algorithm | Only JAX; no formal verification |
| **HIGH** | Birkhoff tangent cone | No abstract polytope tangent cone library |
| **HIGH** | Cross-system verification | No automated comparison harness |
| **MEDIUM** | Spectral norm LMO | Not generalized to degenerate cases |
| **MEDIUM** | Convergence proofs | No formal rates for dual ascent/Dykstra |
| **LOW** | API consistency | Naming conventions differ across 8 systems |

---

**Bottom Line**: The article provides a complete algorithmic description but the codebase has **zero formalization** of any component. The weakest link is **SVD infrastructure** across all 8 systems, followed by the **dual ascent framework** which is the mathematical backbone but exists only as prose.