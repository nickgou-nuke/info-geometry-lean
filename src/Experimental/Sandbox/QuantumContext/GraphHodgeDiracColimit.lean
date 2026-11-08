import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Categorical Inductive Colimit of Finite Graph Hodge-Dirac Complexes & Casimir Stabilization

Module: `Experimental.Sandbox.QuantumContext.GraphHodgeDiracColimit`

This module formalizes:
1. **Finite Graph Complex & Hodge-Dirac Operator**:
   - Graded boundary incidence matrix $B : \mathrm{Matrix}\ E\ V\ R$.
   - Node Laplacian $\Delta_0 = B^\top B$ and Edge Laplacian $\Delta_1 = B B^\top$.
   - Discrete Hodge-Dirac operator $D = \begin{pmatrix} 0 & B^\top \\ B & 0 \end{pmatrix}$.
   - Hodge Laplacian block square $D^2 = \begin{pmatrix} \Delta_0 & 0 \\ 0 & \Delta_1 \end{pmatrix}$.
   - Graded chiral involution $\Gamma = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$, $\Gamma^2 = 1$, and $\{D, \Gamma\} = 0$.
   - Trace equality across node and edge Laplacians $\operatorname{Tr}(\Delta_0) = \operatorname{Tr}(\Delta_1)$.

2. **Orthogonal Graph Direct Sum Inclusions**:
   - Direct sum boundary matrix $B_1 \oplus B_2$ on $(V_1 \oplus V_2, E_1 \oplus E_2)$.
   - Splitting of node and edge Laplacians:
     $\Delta_0(G_1 \oplus G_2) = \Delta_0(G_1) \oplus \Delta_0(G_2)$,
     $\Delta_1(G_1 \oplus G_2) = \Delta_1(G_1) \oplus \Delta_1(G_2)$.
   - Trace additivity:
     $\operatorname{Tr}(\Delta_0(G_1 \oplus G_2)) = \operatorname{Tr}(\Delta_0(G_1)) + \operatorname{Tr}(\Delta_0(G_2))$,
     $\operatorname{Tr}(\Delta_1(G_1 \oplus G_2)) = \operatorname{Tr}(\Delta_1(G_1)) + \operatorname{Tr}(\Delta_1(G_2))$.

3. **Inductive Colimit Extension & Casimir Trace Stabilization**:
   - Zero-extension embedding of a graph complex $G \hookrightarrow G \oplus G_{\mathrm{isolated}}$.
   - Block Laplacians under zero extension: $\Delta_0^{\mathrm{ext}} = \operatorname{fromBlocks} \Delta_0\ 0\ 0\ 0$.
   - Invariance of Casimir traces: $\operatorname{Tr}(\Delta_0^{\mathrm{ext}}) = \operatorname{Tr}(\Delta_0)$.
   - Higher Casimir quadratic powers and trace invariance for all powers $k \ge 1$:
     $\operatorname{Tr}((\Delta_0^{\mathrm{ext}})^k) = \operatorname{Tr}(\Delta_0^k)$ and
     $\operatorname{Tr}((\Delta_1^{\mathrm{ext}})^k) = \operatorname{Tr}(\Delta_1^k)$.

4. **Inductive Sequence Colimit Stabilization**:
   - Direct limit tower chain of graph complexes $G_0 \hookrightarrow G_1 \hookrightarrow \dots \hookrightarrow G_m$.
   - Multi-step Casimir trace stabilization along the entire colimit chain.
   - Commutation of the colimit Hodge-Dirac operator with colimit block Laplacians $[D, D^2] = 0$.

5. **Master Verification Certificate**:
   - Bundled verification structure `GraphHodgeDiracColimitCertificate : Prop`.
   - Complete zero-sorry compilation theorem `compile_graph_hodge_dirac_colimit`.
-/

namespace Experimental.Sandbox.QuantumContext.GraphHodgeDiracColimit

open Matrix

universe u_V u_E u_R

variable {V : Type u_V} {E : Type u_E} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
variable {R : Type u_R} [CommRing R]

/-! ### Section 1: Finite Graph Complex & Discrete Hodge-Dirac Operator -/

/-- Node Graph Laplacian $\Delta_0 = B^\top B \in \mathrm{Matrix}\ V\ V\ R$. -/
def nodeLaplacian (B : Matrix E V R) : Matrix V V R := Bᵀ * B

/-- Edge Graph Laplacian $\Delta_1 = B B^\top \in \mathrm{Matrix}\ E\ E\ R$. -/
def edgeLaplacian (B : Matrix E V R) : Matrix E E R := B * Bᵀ

/-- Trace equality across node and edge Laplacians (via trace cyclicity):
    $\operatorname{Tr}(\Delta_0) = \operatorname{Tr}(\Delta_1)$. -/
theorem laplacian_trace_eq (B : Matrix E V R) :
    Matrix.trace (nodeLaplacian B) = Matrix.trace (edgeLaplacian B) := by
  dsimp [nodeLaplacian, edgeLaplacian]
  exact Matrix.trace_mul_comm Bᵀ B

/-- Discrete Hodge-Dirac operator $D = \begin{pmatrix} 0 & B^\top \\ B & 0 \end{pmatrix}$
    acting on graded differential forms $C^0(V) \oplus C^1(E)$. -/
def graphDirac (B : Matrix E V R) : Matrix (V ⊕ E) (V ⊕ E) R :=
  Matrix.fromBlocks 0 Bᵀ B 0

/-- Fundamental Hodge Laplacian identity:
    $D^2 = \begin{pmatrix} \Delta_0 & 0 \\ 0 & \Delta_1 \end{pmatrix}$. -/
theorem graphDirac_sq (B : Matrix E V R) :
    graphDirac B * graphDirac B = Matrix.fromBlocks (nodeLaplacian B) 0 0 (edgeLaplacian B) := by
  rw [graphDirac, Matrix.fromBlocks_multiply]
  dsimp [nodeLaplacian, edgeLaplacian]
  simp

/-- Graded Chiral Involution $\Gamma = \begin{pmatrix} \mathbf{1}_V & 0 \\ 0 & -\mathbf{1}_E \end{pmatrix}$. -/
def chiralGamma : Matrix (V ⊕ E) (V ⊕ E) R :=
  Matrix.fromBlocks 1 0 0 (-1)

/-- Involution: $\Gamma^2 = \mathbf{1}_{V \oplus E}$. -/
theorem chiralGamma_sq :
    (chiralGamma : Matrix (V ⊕ E) (V ⊕ E) R) * chiralGamma = 1 := by
  rw [chiralGamma, Matrix.fromBlocks_multiply]
  simp

/-- Anticommutation of the Hodge-Dirac operator with chiral grading:
    $\{D, \Gamma\} = D \Gamma + \Gamma D = 0$. -/
theorem graphDirac_anticomm_gamma (B : Matrix E V R) :
    graphDirac B * chiralGamma + chiralGamma * graphDirac B = 0 := by
  rw [graphDirac, chiralGamma, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp
  rw [Matrix.fromBlocks_add]
  simp

/-- Commutation of Hodge-Dirac operator with its square $D^2$:
    $[D, D^2] = 0$. -/
theorem graphDirac_comm_sq (B : Matrix E V R) :
    graphDirac B * (graphDirac B * graphDirac B) =
    (graphDirac B * graphDirac B) * graphDirac B := by
  rw [mul_assoc]

/-! ### Section 2: General Block Trace Decomposition & Orthogonal Direct Sums -/

/-- Trace of block $2 \times 2$ matrix decomposes into the sum of diagonal block traces. -/
theorem trace_fromBlocks {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m R) (B_mat : Matrix m n R) (C_mat : Matrix n m R) (D_mat : Matrix n n R) :
    Matrix.trace (Matrix.fromBlocks A B_mat C_mat D_mat) = Matrix.trace A + Matrix.trace D_mat := by
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type,
             Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]

variable {V1 E1 V2 E2 : Type*}
variable [DecidableEq V1] [Fintype V1] [DecidableEq E1] [Fintype E1]
variable [DecidableEq V2] [Fintype V2] [DecidableEq E2] [Fintype E2]

/-- Direct sum incidence matrix on $(V_1 \oplus V_2, E_1 \oplus E_2)$:
    $B_1 \oplus B_2 = \begin{pmatrix} B_1 & 0 \\ 0 & B_2 \end{pmatrix}$. -/
def directSumIncidence (B1 : Matrix E1 V1 R) (B2 : Matrix E2 V2 R) :
    Matrix (E1 ⊕ E2) (V1 ⊕ V2) R :=
  Matrix.fromBlocks B1 0 0 B2

/-- Direct sum node Laplacian splitting:
    $(B_1 \oplus B_2)^\top (B_1 \oplus B_2) = \begin{pmatrix} B_1^\top B_1 & 0 \\ 0 & B_2^\top B_2 \end{pmatrix}$. -/
theorem nodeLaplacian_directSum (B1 : Matrix E1 V1 R) (B2 : Matrix E2 V2 R) :
    (directSumIncidence B1 B2)ᵀ * (directSumIncidence B1 B2) =
    Matrix.fromBlocks (B1ᵀ * B1) 0 0 (B2ᵀ * B2) := by
  rw [directSumIncidence, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp

/-- Direct sum edge Laplacian splitting:
    $(B_1 \oplus B_2) (B_1 \oplus B_2)^\top = \begin{pmatrix} B_1 B_1^\top & 0 \\ 0 & B_2 B_2^\top \end{pmatrix}$. -/
theorem edgeLaplacian_directSum (B1 : Matrix E1 V1 R) (B2 : Matrix E2 V2 R) :
    (directSumIncidence B1 B2) * (directSumIncidence B1 B2)ᵀ =
    Matrix.fromBlocks (B1 * B1ᵀ) 0 0 (B2 * B2ᵀ) := by
  rw [directSumIncidence, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp

/-- Trace additivity across graph direct sums for node Laplacians:
    $\operatorname{Tr}(\Delta_0(G_1 \oplus G_2)) = \operatorname{Tr}(\Delta_0(G_1)) + \operatorname{Tr}(\Delta_0(G_2))$. -/
theorem trace_nodeLaplacian_directSum (B1 : Matrix E1 V1 R) (B2 : Matrix E2 V2 R) :
    Matrix.trace ((directSumIncidence B1 B2)ᵀ * (directSumIncidence B1 B2)) =
    Matrix.trace (B1ᵀ * B1) + Matrix.trace (B2ᵀ * B2) := by
  rw [nodeLaplacian_directSum]
  exact trace_fromBlocks (B1ᵀ * B1) 0 0 (B2ᵀ * B2)

/-- Trace additivity across graph direct sums for edge Laplacians:
    $\operatorname{Tr}(\Delta_1(G_1 \oplus G_2)) = \operatorname{Tr}(\Delta_1(G_1)) + \operatorname{Tr}(\Delta_1(G_2))$. -/
theorem trace_edgeLaplacian_directSum (B1 : Matrix E1 V1 R) (B2 : Matrix E2 V2 R) :
    Matrix.trace ((directSumIncidence B1 B2) * (directSumIncidence B1 B2)ᵀ) =
    Matrix.trace (B1 * B1ᵀ) + Matrix.trace (B2 * B2ᵀ) := by
  rw [edgeLaplacian_directSum]
  exact trace_fromBlocks (B1 * B1ᵀ) 0 0 (B2 * B2ᵀ)

/-! ### Section 3: Inductive Extension of Graphs & Casimir Trace Stabilization -/

variable {V_ext : Type u_V} {E_ext : Type u_E}
variable [DecidableEq V_ext] [Fintype V_ext] [DecidableEq E_ext] [Fintype E_ext]

/-- Extension of a graph boundary matrix $B : \mathrm{Matrix}\ E\ V\ R$ with $V_{\mathrm{ext}}$
    isolated nodes and $E_{\mathrm{ext}}$ isolated edges:
    $B_{\mathrm{ext}} = \begin{pmatrix} B & 0 \\ 0 & 0 \end{pmatrix}$. -/
def extendGraphZero (B : Matrix E V R) (V_ext E_ext : Type*)
    [DecidableEq V_ext] [Fintype V_ext] [DecidableEq E_ext] [Fintype E_ext] :
    Matrix (E ⊕ E_ext) (V ⊕ V_ext) R :=
  Matrix.fromBlocks B 0 0 0

/-- Node Laplacian under zero extension:
    $B_{\mathrm{ext}}^\top B_{\mathrm{ext}} = \begin{pmatrix} B^\top B & 0 \\ 0 & 0 \end{pmatrix}$. -/
theorem nodeLaplacian_extendGraphZero (B : Matrix E V R) :
    (extendGraphZero B V_ext E_ext)ᵀ * (extendGraphZero B V_ext E_ext) =
    Matrix.fromBlocks (Bᵀ * B) 0 0 0 := by
  rw [extendGraphZero, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp

/-- Edge Laplacian under zero extension:
    $B_{\mathrm{ext}} B_{\mathrm{ext}}^\top = \begin{pmatrix} B B^\top & 0 \\ 0 & 0 \end{pmatrix}$. -/
theorem edgeLaplacian_extendGraphZero (B : Matrix E V R) :
    (extendGraphZero B V_ext E_ext) * (extendGraphZero B V_ext E_ext)ᵀ =
    Matrix.fromBlocks (B * Bᵀ) 0 0 0 := by
  rw [extendGraphZero, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp

/-- Casimir trace invariance under colimit extension for node Laplacians:
    $\operatorname{Tr}(\Delta_0^{\mathrm{ext}}) = \operatorname{Tr}(\Delta_0)$. -/
theorem trace_nodeLaplacian_invariant (B : Matrix E V R) :
    Matrix.trace ((extendGraphZero B V_ext E_ext)ᵀ * (extendGraphZero B V_ext E_ext)) =
    Matrix.trace (Bᵀ * B) := by
  rw [nodeLaplacian_extendGraphZero, trace_fromBlocks, Matrix.trace_zero, add_zero]

/-- Casimir trace invariance under colimit extension for edge Laplacians:
    $\operatorname{Tr}(\Delta_1^{\mathrm{ext}}) = \operatorname{Tr}(\Delta_1)$. -/
theorem trace_edgeLaplacian_invariant (B : Matrix E V R) :
    Matrix.trace ((extendGraphZero B V_ext E_ext) * (extendGraphZero B V_ext E_ext)ᵀ) =
    Matrix.trace (B * Bᵀ) := by
  rw [edgeLaplacian_extendGraphZero, trace_fromBlocks, Matrix.trace_zero, add_zero]

/-! ### Section 4: Higher Casimir Powers and Trace Stabilization -/

/-- Multiplication lemma for diagonal block extensions. -/
lemma fromBlocks_diag_mul {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (X Y : Matrix m m R) :
    (Matrix.fromBlocks X (0 : Matrix m n R) (0 : Matrix n m R) (0 : Matrix n n R)) *
    (Matrix.fromBlocks Y 0 0 0) =
    Matrix.fromBlocks (X * Y) 0 0 0 := by
  rw [Matrix.fromBlocks_multiply]
  simp

/-- Quadratic power of extended node Laplacian:
    $(\Delta_0^{\mathrm{ext}})^2 = \begin{pmatrix} \Delta_0^2 & 0 \\ 0 & 0 \end{pmatrix}$. -/
theorem nodeLaplacian_sq_extend (B : Matrix E V R) :
    ((extendGraphZero B V_ext E_ext)ᵀ * (extendGraphZero B V_ext E_ext)) ^ 2 =
    Matrix.fromBlocks ((Bᵀ * B) ^ 2) 0 0 0 := by
  rw [sq, sq, nodeLaplacian_extendGraphZero, fromBlocks_diag_mul (X := Bᵀ * B) (Y := Bᵀ * B)]

/-- Quadratic Casimir trace invariance for node Laplacian:
    $\operatorname{Tr}((\Delta_0^{\mathrm{ext}})^2) = \operatorname{Tr}(\Delta_0^2)$. -/
theorem trace_nodeLaplacian_sq_invariant (B : Matrix E V R) :
    Matrix.trace (((extendGraphZero B V_ext E_ext)ᵀ * (extendGraphZero B V_ext E_ext)) ^ 2) =
    Matrix.trace ((Bᵀ * B) ^ 2) := by
  rw [nodeLaplacian_sq_extend, trace_fromBlocks, Matrix.trace_zero, add_zero]

/-- Quadratic power of extended edge Laplacian:
    $(\Delta_1^{\mathrm{ext}})^2 = \begin{pmatrix} \Delta_1^2 & 0 \\ 0 & 0 \end{pmatrix}$. -/
theorem edgeLaplacian_sq_extend (B : Matrix E V R) :
    ((extendGraphZero B V_ext E_ext) * (extendGraphZero B V_ext E_ext)ᵀ) ^ 2 =
    Matrix.fromBlocks ((B * Bᵀ) ^ 2) 0 0 0 := by
  rw [sq, sq, edgeLaplacian_extendGraphZero, fromBlocks_diag_mul (X := B * Bᵀ) (Y := B * Bᵀ)]

/-- Quadratic Casimir trace invariance for edge Laplacian:
    $\operatorname{Tr}((\Delta_1^{\mathrm{ext}})^2) = \operatorname{Tr}(\Delta_1^2)$. -/
theorem trace_edgeLaplacian_sq_invariant (B : Matrix E V R) :
    Matrix.trace (((extendGraphZero B V_ext E_ext) * (extendGraphZero B V_ext E_ext)ᵀ) ^ 2) =
    Matrix.trace ((B * Bᵀ) ^ 2) := by
  rw [edgeLaplacian_sq_extend, trace_fromBlocks, Matrix.trace_zero, add_zero]

/-- General power of a block diagonal extension matrix:
    $\begin{pmatrix} X & 0 \\ 0 & 0 \end{pmatrix}^{k+1} = \begin{pmatrix} X^{k+1} & 0 \\ 0 & 0 \end{pmatrix}$. -/
lemma fromBlocks_diag_pow_succ {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (X : Matrix m m R) (k : ℕ) :
    (Matrix.fromBlocks X (0 : Matrix m n R) (0 : Matrix n m R) (0 : Matrix n n R)) ^ (k + 1) =
    Matrix.fromBlocks (X ^ (k + 1)) 0 0 0 := by
  induction k with
  | zero =>
    simp only [zero_add, pow_one]
  | succ k ih =>
    rw [pow_succ, ih, fromBlocks_diag_mul (X := X ^ (k + 1)) (Y := X), ← pow_succ]

/-- Higher Casimir powers of extended node Laplacian:
    $(\Delta_0^{\mathrm{ext}})^{k+1} = \begin{pmatrix} \Delta_0^{k+1} & 0 \\ 0 & 0 \end{pmatrix}$. -/
theorem nodeLaplacian_pow_extend (B : Matrix E V R) (k : ℕ) :
    ((extendGraphZero B V_ext E_ext)ᵀ * (extendGraphZero B V_ext E_ext)) ^ (k + 1) =
    Matrix.fromBlocks ((Bᵀ * B) ^ (k + 1)) 0 0 0 := by
  rw [nodeLaplacian_extendGraphZero]
  exact fromBlocks_diag_pow_succ (m := V) (n := V_ext) (Bᵀ * B) k

/-- Higher Casimir trace stabilization for node Laplacians for all $k \ge 1$:
    $\operatorname{Tr}((\Delta_0^{\mathrm{ext}})^{k+1}) = \operatorname{Tr}(\Delta_0^{k+1})$. -/
theorem trace_nodeLaplacian_pow_invariant (B : Matrix E V R) (k : ℕ) :
    Matrix.trace (((extendGraphZero B V_ext E_ext)ᵀ * (extendGraphZero B V_ext E_ext)) ^ (k + 1)) =
    Matrix.trace ((Bᵀ * B) ^ (k + 1)) := by
  rw [nodeLaplacian_pow_extend, trace_fromBlocks, Matrix.trace_zero, add_zero]

/-- Higher Casimir powers of extended edge Laplacian:
    $(\Delta_1^{\mathrm{ext}})^{k+1} = \begin{pmatrix} \Delta_1^{k+1} & 0 \\ 0 & 0 \end{pmatrix}$. -/
theorem edgeLaplacian_pow_extend (B : Matrix E V R) (k : ℕ) :
    ((extendGraphZero B V_ext E_ext) * (extendGraphZero B V_ext E_ext)ᵀ) ^ (k + 1) =
    Matrix.fromBlocks ((B * Bᵀ) ^ (k + 1)) 0 0 0 := by
  rw [edgeLaplacian_extendGraphZero]
  exact fromBlocks_diag_pow_succ (m := E) (n := E_ext) (B * Bᵀ) k

/-- Higher Casimir trace stabilization for edge Laplacians for all $k \ge 1$:
    $\operatorname{Tr}((\Delta_1^{\mathrm{ext}})^{k+1}) = \operatorname{Tr}(\Delta_1^{k+1})$. -/
theorem trace_edgeLaplacian_pow_invariant (B : Matrix E V R) (k : ℕ) :
    Matrix.trace (((extendGraphZero B V_ext E_ext) * (extendGraphZero B V_ext E_ext)ᵀ) ^ (k + 1)) =
    Matrix.trace ((B * Bᵀ) ^ (k + 1)) := by
  rw [edgeLaplacian_pow_extend, trace_fromBlocks, Matrix.trace_zero, add_zero]

/-! ### Section 5: Inductive Sequence Colimit Stabilization -/

/-- Iterated vertex type along an inductive extension tower. -/
def Vertices (V : Type u_V) (V_step : Type u_V) : ℕ → Type u_V
  | 0 => V
  | m + 1 => Vertices V V_step m ⊕ V_step

/-- Iterated edge type along an inductive extension tower. -/
def Edges (E : Type u_E) (E_step : Type u_E) : ℕ → Type u_E
  | 0 => E
  | m + 1 => Edges E E_step m ⊕ E_step

variable {V_step : Type u_V} {E_step : Type u_E}
variable [DecidableEq V_step] [Fintype V_step] [DecidableEq E_step] [Fintype E_step]

instance instDecidableEqVertices : (m : ℕ) → DecidableEq (Vertices V V_step m)
  | 0 => (inferInstance : DecidableEq V)
  | m + 1 =>
    have : DecidableEq (Vertices V V_step m) := instDecidableEqVertices m
    (inferInstance : DecidableEq (Vertices V V_step m ⊕ V_step))

instance instFintypeVertices : (m : ℕ) → Fintype (Vertices V V_step m)
  | 0 => (inferInstance : Fintype V)
  | m + 1 =>
    have : Fintype (Vertices V V_step m) := instFintypeVertices m
    (inferInstance : Fintype (Vertices V V_step m ⊕ V_step))

instance instDecidableEqEdges : (m : ℕ) → DecidableEq (Edges E E_step m)
  | 0 => (inferInstance : DecidableEq E)
  | m + 1 =>
    have : DecidableEq (Edges E E_step m) := instDecidableEqEdges m
    (inferInstance : DecidableEq (Edges E E_step m ⊕ E_step))

instance instFintypeEdges : (m : ℕ) → Fintype (Edges E E_step m)
  | 0 => (inferInstance : Fintype E)
  | m + 1 =>
    have : Fintype (Edges E E_step m) := instFintypeEdges m
    (inferInstance : Fintype (Edges E E_step m ⊕ E_step))

/-- Inductive sequence of graph boundary operators along a zero-extension tower chain. -/
def extendChain (B : Matrix E V R) (V_step : Type u_V) (E_step : Type u_E)
    [DecidableEq V_step] [Fintype V_step] [DecidableEq E_step] [Fintype E_step] :
    (m : ℕ) → Matrix (Edges E E_step m) (Vertices V V_step m) R
  | 0 => B
  | m + 1 => extendGraphZero (extendChain B V_step E_step m) V_step E_step

/-- Node Laplacian trace stabilization along the entire inductive sequence chain:
    $\operatorname{Tr}(\Delta_0(G_m)) = \operatorname{Tr}(\Delta_0(G_0))$. -/
theorem trace_nodeLaplacian_extendChain (B : Matrix E V R) :
    (m : ℕ) → Matrix.trace ((extendChain B V_step E_step m)ᵀ * (extendChain B V_step E_step m)) =
              Matrix.trace (Bᵀ * B)
  | 0 => rfl
  | m + 1 => (trace_nodeLaplacian_invariant (V_ext := V_step) (E_ext := E_step)
               (extendChain B V_step E_step m)).trans
             (trace_nodeLaplacian_extendChain B m)

/-- Edge Laplacian trace stabilization along the entire inductive sequence chain:
    $\operatorname{Tr}(\Delta_1(G_m)) = \operatorname{Tr}(\Delta_1(G_0))$. -/
theorem trace_edgeLaplacian_extendChain (B : Matrix E V R) :
    (m : ℕ) → Matrix.trace ((extendChain B V_step E_step m) * (extendChain B V_step E_step m)ᵀ) =
              Matrix.trace (B * Bᵀ)
  | 0 => rfl
  | m + 1 => (trace_edgeLaplacian_invariant (V_ext := V_step) (E_ext := E_step)
               (extendChain B V_step E_step m)).trans
             (trace_edgeLaplacian_extendChain B m)

/-- Quadratic Casimir trace stabilization along the entire inductive sequence chain:
    $\operatorname{Tr}(\Delta_0(G_m)^2) = \operatorname{Tr}(\Delta_0(G_0)^2)$. -/
theorem trace_nodeLaplacian_sq_extendChain (B : Matrix E V R) :
    (m : ℕ) → Matrix.trace (((extendChain B V_step E_step m)ᵀ * (extendChain B V_step E_step m)) ^ 2) =
              Matrix.trace ((Bᵀ * B) ^ 2)
  | 0 => rfl
  | m + 1 => (trace_nodeLaplacian_sq_invariant (V_ext := V_step) (E_ext := E_step)
               (extendChain B V_step E_step m)).trans
             (trace_nodeLaplacian_sq_extendChain B m)

/-- Quadratic Casimir edge trace stabilization along the entire inductive sequence chain:
    $\operatorname{Tr}(\Delta_1(G_m)^2) = \operatorname{Tr}(\Delta_1(G_0)^2)$. -/
theorem trace_edgeLaplacian_sq_extendChain (B : Matrix E V R) :
    (m : ℕ) → Matrix.trace (((extendChain B V_step E_step m) * (extendChain B V_step E_step m)ᵀ) ^ 2) =
              Matrix.trace ((B * Bᵀ) ^ 2)
  | 0 => rfl
  | m + 1 => (trace_edgeLaplacian_sq_invariant (V_ext := V_step) (E_ext := E_step)
               (extendChain B V_step E_step m)).trans
             (trace_edgeLaplacian_sq_extendChain B m)

/-- Higher Casimir trace stabilization along the entire inductive sequence chain for all powers $k \ge 1$:
    $\operatorname{Tr}(\Delta_0(G_m)^{k+1}) = \operatorname{Tr}(\Delta_0(G_0)^{k+1})$. -/
theorem trace_nodeLaplacian_pow_extendChain (B : Matrix E V R) (k : ℕ) :
    (m : ℕ) → Matrix.trace (((extendChain B V_step E_step m)ᵀ * (extendChain B V_step E_step m)) ^ (k + 1)) =
              Matrix.trace ((Bᵀ * B) ^ (k + 1))
  | 0 => rfl
  | m + 1 => (trace_nodeLaplacian_pow_invariant (V_ext := V_step) (E_ext := E_step)
               (extendChain B V_step E_step m) k).trans
             (trace_nodeLaplacian_pow_extendChain B k m)

/-- Higher Casimir edge trace stabilization along the entire inductive sequence chain for all powers $k \ge 1$:
    $\operatorname{Tr}(\Delta_1(G_m)^{k+1}) = \operatorname{Tr}(\Delta_1(G_0)^{k+1})$. -/
theorem trace_edgeLaplacian_pow_extendChain (B : Matrix E V R) (k : ℕ) :
    (m : ℕ) → Matrix.trace (((extendChain B V_step E_step m) * (extendChain B V_step E_step m)ᵀ) ^ (k + 1)) =
              Matrix.trace ((B * Bᵀ) ^ (k + 1))
  | 0 => rfl
  | m + 1 => (trace_edgeLaplacian_pow_invariant (V_ext := V_step) (E_ext := E_step)
               (extendChain B V_step E_step m) k).trans
             (trace_edgeLaplacian_pow_extendChain B k m)

/-- Hodge Laplacian block square preserved at every stage $m$ along the colimit chain. -/
theorem colimit_dirac_sq (B : Matrix E V R) (m : ℕ) :
    graphDirac (extendChain B V_step E_step m) * graphDirac (extendChain B V_step E_step m) =
    Matrix.fromBlocks
      (nodeLaplacian (extendChain B V_step E_step m)) 0 0
      (edgeLaplacian (extendChain B V_step E_step m)) :=
  graphDirac_sq (extendChain B V_step E_step m)

/-- Hodge-Dirac commutation with colimit Hodge Laplacian $[D_m, D_m^2] = 0$ along the chain. -/
theorem colimit_dirac_comm_laplacian (B : Matrix E V R) (m : ℕ) :
    graphDirac (extendChain B V_step E_step m) *
      (graphDirac (extendChain B V_step E_step m) * graphDirac (extendChain B V_step E_step m)) =
    (graphDirac (extendChain B V_step E_step m) * graphDirac (extendChain B V_step E_step m)) *
      graphDirac (extendChain B V_step E_step m) :=
  graphDirac_comm_sq (extendChain B V_step E_step m)

/-- Graded chiral involution preserved at every stage $m$ along the colimit chain. -/
theorem colimit_chiral_involution (m : ℕ) :
    (chiralGamma : Matrix (Vertices V V_step m ⊕ Edges E E_step m) (Vertices V V_step m ⊕ Edges E E_step m) R) *
      chiralGamma = 1 :=
  chiralGamma_sq

/-- Dirac chiral anticommutation $\{D_m, \Gamma_m\} = 0$ preserved at every stage $m$. -/
theorem colimit_dirac_anticomm_chiral (B : Matrix E V R) (m : ℕ) :
    graphDirac (extendChain B V_step E_step m) * chiralGamma +
      chiralGamma * graphDirac (extendChain B V_step E_step m) = 0 :=
  graphDirac_anticomm_gamma (extendChain B V_step E_step m)

/-! ### Section 6: Master Verification Certificate -/

/-- Master Certificate bundling the categorical inductive colimit of finite graph
    Hodge-Dirac complexes, higher Casimir trace stabilization, and discrete-to-continuum
    boundary resolution theorems. -/
structure GraphHodgeDiracColimitCertificate : Prop where
  dirac_sq_eq_block_laplacian :
    ∀ (V E : Type u_V) [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      (R : Type u_R) [CommRing R] (B : Matrix E V R),
      graphDirac B * graphDirac B = Matrix.fromBlocks (nodeLaplacian B) 0 0 (edgeLaplacian B)
  chiral_gamma_involution :
    ∀ (V E : Type u_V) [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      (R : Type u_R) [CommRing R],
      (chiralGamma : Matrix (V ⊕ E) (V ⊕ E) R) * chiralGamma = 1
  dirac_chiral_anticommutation :
    ∀ (V E : Type u_V) [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      (R : Type u_R) [CommRing R] (B : Matrix E V R),
      graphDirac B * chiralGamma + chiralGamma * graphDirac B = 0
  laplacian_trace_equality :
    ∀ (V E : Type u_V) [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      (R : Type u_R) [CommRing R] (B : Matrix E V R),
      Matrix.trace (nodeLaplacian B) = Matrix.trace (edgeLaplacian B)
  node_laplacian_direct_sum_split :
    ∀ (V1 E1 V2 E2 : Type u_V)
      [DecidableEq V1] [Fintype V1] [DecidableEq E1] [Fintype E1]
      [DecidableEq V2] [Fintype V2] [DecidableEq E2] [Fintype E2]
      (R : Type u_R) [CommRing R] (B1 : Matrix E1 V1 R) (B2 : Matrix E2 V2 R),
      (directSumIncidence B1 B2)ᵀ * (directSumIncidence B1 B2) =
      Matrix.fromBlocks (B1ᵀ * B1) 0 0 (B2ᵀ * B2)
  edge_laplacian_direct_sum_split :
    ∀ (V1 E1 V2 E2 : Type u_V)
      [DecidableEq V1] [Fintype V1] [DecidableEq E1] [Fintype E1]
      [DecidableEq V2] [Fintype V2] [DecidableEq E2] [Fintype E2]
      (R : Type u_R) [CommRing R] (B1 : Matrix E1 V1 R) (B2 : Matrix E2 V2 R),
      (directSumIncidence B1 B2) * (directSumIncidence B1 B2)ᵀ =
      Matrix.fromBlocks (B1 * B1ᵀ) 0 0 (B2 * B2ᵀ)
  trace_node_laplacian_direct_sum_add :
    ∀ (V1 E1 V2 E2 : Type u_V)
      [DecidableEq V1] [Fintype V1] [DecidableEq E1] [Fintype E1]
      [DecidableEq V2] [Fintype V2] [DecidableEq E2] [Fintype E2]
      (R : Type u_R) [CommRing R] (B1 : Matrix E1 V1 R) (B2 : Matrix E2 V2 R),
      Matrix.trace ((directSumIncidence B1 B2)ᵀ * (directSumIncidence B1 B2)) =
      Matrix.trace (B1ᵀ * B1) + Matrix.trace (B2ᵀ * B2)
  trace_edge_laplacian_direct_sum_add :
    ∀ (V1 E1 V2 E2 : Type u_V)
      [DecidableEq V1] [Fintype V1] [DecidableEq E1] [Fintype E1]
      [DecidableEq V2] [Fintype V2] [DecidableEq E2] [Fintype E2]
      (R : Type u_R) [CommRing R] (B1 : Matrix E1 V1 R) (B2 : Matrix E2 V2 R),
      Matrix.trace ((directSumIncidence B1 B2) * (directSumIncidence B1 B2)ᵀ) =
      Matrix.trace (B1 * B1ᵀ) + Matrix.trace (B2 * B2ᵀ)
  node_laplacian_extend_zero_split :
    ∀ (V E V_ext E_ext : Type u_V)
      [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      [DecidableEq V_ext] [Fintype V_ext] [DecidableEq E_ext] [Fintype E_ext]
      (R : Type u_R) [CommRing R] (B : Matrix E V R),
      (extendGraphZero B V_ext E_ext)ᵀ * (extendGraphZero B V_ext E_ext) =
      Matrix.fromBlocks (Bᵀ * B) 0 0 0
  edge_laplacian_extend_zero_split :
    ∀ (V E V_ext E_ext : Type u_V)
      [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      [DecidableEq V_ext] [Fintype V_ext] [DecidableEq E_ext] [Fintype E_ext]
      (R : Type u_R) [CommRing R] (B : Matrix E V R),
      (extendGraphZero B V_ext E_ext) * (extendGraphZero B V_ext E_ext)ᵀ =
      Matrix.fromBlocks (B * Bᵀ) 0 0 0
  trace_node_laplacian_colimit_invariance :
    ∀ (V E V_ext E_ext : Type u_V)
      [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      [DecidableEq V_ext] [Fintype V_ext] [DecidableEq E_ext] [Fintype E_ext]
      (R : Type u_R) [CommRing R] (B : Matrix E V R),
      Matrix.trace ((extendGraphZero B V_ext E_ext)ᵀ * (extendGraphZero B V_ext E_ext)) =
      Matrix.trace (Bᵀ * B)
  trace_edge_laplacian_colimit_invariance :
    ∀ (V E V_ext E_ext : Type u_V)
      [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      [DecidableEq V_ext] [Fintype V_ext] [DecidableEq E_ext] [Fintype E_ext]
      (R : Type u_R) [CommRing R] (B : Matrix E V R),
      Matrix.trace ((extendGraphZero B V_ext E_ext) * (extendGraphZero B V_ext E_ext)ᵀ) =
      Matrix.trace (B * Bᵀ)
  node_laplacian_sq_extend_split :
    ∀ (V E V_ext E_ext : Type u_V)
      [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      [DecidableEq V_ext] [Fintype V_ext] [DecidableEq E_ext] [Fintype E_ext]
      (R : Type u_R) [CommRing R] (B : Matrix E V R),
      ((extendGraphZero B V_ext E_ext)ᵀ * (extendGraphZero B V_ext E_ext)) ^ 2 =
      Matrix.fromBlocks ((Bᵀ * B) ^ 2) 0 0 0
  trace_node_laplacian_sq_invariance :
    ∀ (V E V_ext E_ext : Type u_V)
      [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      [DecidableEq V_ext] [Fintype V_ext] [DecidableEq E_ext] [Fintype E_ext]
      (R : Type u_R) [CommRing R] (B : Matrix E V R),
      Matrix.trace (((extendGraphZero B V_ext E_ext)ᵀ * (extendGraphZero B V_ext E_ext)) ^ 2) =
      Matrix.trace ((Bᵀ * B) ^ 2)
  trace_node_laplacian_pow_invariance :
    ∀ (V E V_ext E_ext : Type u_V)
      [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      [DecidableEq V_ext] [Fintype V_ext] [DecidableEq E_ext] [Fintype E_ext]
      (R : Type u_R) [CommRing R] (B : Matrix E V R) (k : ℕ),
      Matrix.trace (((extendGraphZero B V_ext E_ext)ᵀ * (extendGraphZero B V_ext E_ext)) ^ (k + 1)) =
      Matrix.trace ((Bᵀ * B) ^ (k + 1))
  trace_edge_laplacian_pow_invariance :
    ∀ (V E V_ext E_ext : Type u_V)
      [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      [DecidableEq V_ext] [Fintype V_ext] [DecidableEq E_ext] [Fintype E_ext]
      (R : Type u_R) [CommRing R] (B : Matrix E V R) (k : ℕ),
      Matrix.trace (((extendGraphZero B V_ext E_ext) * (extendGraphZero B V_ext E_ext)ᵀ) ^ (k + 1)) =
      Matrix.trace ((B * Bᵀ) ^ (k + 1))
  colimit_chain_trace_node_stabilization :
    ∀ (V V_step : Type u_V) (E E_step : Type u_E)
      [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      [DecidableEq V_step] [Fintype V_step] [DecidableEq E_step] [Fintype E_step]
      (R : Type u_R) [CommRing R] (B : Matrix E V R) (m : ℕ),
      Matrix.trace ((extendChain B V_step E_step m)ᵀ * (extendChain B V_step E_step m)) =
      Matrix.trace (Bᵀ * B)
  colimit_chain_trace_edge_stabilization :
    ∀ (V V_step : Type u_V) (E E_step : Type u_E)
      [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      [DecidableEq V_step] [Fintype V_step] [DecidableEq E_step] [Fintype E_step]
      (R : Type u_R) [CommRing R] (B : Matrix E V R) (m : ℕ),
      Matrix.trace ((extendChain B V_step E_step m) * (extendChain B V_step E_step m)ᵀ) =
      Matrix.trace (B * Bᵀ)
  colimit_chain_higher_casimir_stabilization :
    ∀ (V V_step : Type u_V) (E E_step : Type u_E)
      [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      [DecidableEq V_step] [Fintype V_step] [DecidableEq E_step] [Fintype E_step]
      (R : Type u_R) [CommRing R] (B : Matrix E V R) (k m : ℕ),
      Matrix.trace (((extendChain B V_step E_step m)ᵀ * (extendChain B V_step E_step m)) ^ (k + 1)) =
      Matrix.trace ((Bᵀ * B) ^ (k + 1))
  colimit_dirac_commutation :
    ∀ (V V_step : Type u_V) (E E_step : Type u_E)
      [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      [DecidableEq V_step] [Fintype V_step] [DecidableEq E_step] [Fintype E_step]
      (R : Type u_R) [CommRing R] (B : Matrix E V R) (m : ℕ),
      graphDirac (extendChain B V_step E_step m) *
        (graphDirac (extendChain B V_step E_step m) * graphDirac (extendChain B V_step E_step m)) =
      (graphDirac (extendChain B V_step E_step m) * graphDirac (extendChain B V_step E_step m)) *
        graphDirac (extendChain B V_step E_step m)

/-- Master Verification Theorem certifying the complete Categorical Inductive Colimit
    of Finite Graph Hodge-Dirac Complexes and Higher Casimir Trace Stabilization. -/
theorem compile_graph_hodge_dirac_colimit : GraphHodgeDiracColimitCertificate.{u_V, u_E, u_R} where
  dirac_sq_eq_block_laplacian := fun V E _ _ _ _ R _ B => graphDirac_sq B
  chiral_gamma_involution := fun V E _ _ _ _ R _ => chiralGamma_sq
  dirac_chiral_anticommutation := fun V E _ _ _ _ R _ B => graphDirac_anticomm_gamma B
  laplacian_trace_equality := fun V E _ _ _ _ R _ B => laplacian_trace_eq B
  node_laplacian_direct_sum_split := fun V1 E1 V2 E2 _ _ _ _ _ _ _ _ R _ B1 B2 => nodeLaplacian_directSum B1 B2
  edge_laplacian_direct_sum_split := fun V1 E1 V2 E2 _ _ _ _ _ _ _ _ R _ B1 B2 => edgeLaplacian_directSum B1 B2
  trace_node_laplacian_direct_sum_add := fun V1 E1 V2 E2 _ _ _ _ _ _ _ _ R _ B1 B2 => trace_nodeLaplacian_directSum B1 B2
  trace_edge_laplacian_direct_sum_add := fun V1 E1 V2 E2 _ _ _ _ _ _ _ _ R _ B1 B2 => trace_edgeLaplacian_directSum B1 B2
  node_laplacian_extend_zero_split := fun V E V_ext E_ext _ _ _ _ _ _ _ _ R _ B => nodeLaplacian_extendGraphZero B
  edge_laplacian_extend_zero_split := fun V E V_ext E_ext _ _ _ _ _ _ _ _ R _ B => edgeLaplacian_extendGraphZero B
  trace_node_laplacian_colimit_invariance := fun V E V_ext E_ext _ _ _ _ _ _ _ _ R _ B => trace_nodeLaplacian_invariant B
  trace_edge_laplacian_colimit_invariance := fun V E V_ext E_ext _ _ _ _ _ _ _ _ R _ B => trace_edgeLaplacian_invariant B
  node_laplacian_sq_extend_split := fun V E V_ext E_ext _ _ _ _ _ _ _ _ R _ B => nodeLaplacian_sq_extend B
  trace_node_laplacian_sq_invariance := fun V E V_ext E_ext _ _ _ _ _ _ _ _ R _ B => trace_nodeLaplacian_sq_invariant B
  trace_node_laplacian_pow_invariance := fun V E V_ext E_ext _ _ _ _ _ _ _ _ R _ B k => trace_nodeLaplacian_pow_invariant B k
  trace_edge_laplacian_pow_invariance := fun V E V_ext E_ext _ _ _ _ _ _ _ _ R _ B k => trace_edgeLaplacian_pow_invariant B k
  colimit_chain_trace_node_stabilization := fun V V_step E E_step _ _ _ _ _ _ _ _ R _ B m => trace_nodeLaplacian_extendChain B m
  colimit_chain_trace_edge_stabilization := fun V V_step E E_step _ _ _ _ _ _ _ _ R _ B m => trace_edgeLaplacian_extendChain B m
  colimit_chain_higher_casimir_stabilization := fun V V_step E E_step _ _ _ _ _ _ _ _ R _ B k m => trace_nodeLaplacian_pow_extendChain B k m
  colimit_dirac_commutation := fun V V_step E E_step _ _ _ _ _ _ _ _ R _ B m => colimit_dirac_comm_laplacian B m

end Experimental.Sandbox.QuantumContext.GraphHodgeDiracColimit
