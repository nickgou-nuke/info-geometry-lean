import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# General Graph Hodge-Dirac Operator, Discrete Exterior Calculus, and Krein Chiral Split

Module: `Experimental.Sandbox.QuantumContext.GeneralGraphHodgeDiracKrein`

This module formalizes the genuine, non-scalar, discrete exterior calculus on general graphs,
the Hodge-Dirac operator on graded differential forms $\Omega^\bullet = C^0 \oplus C^1$,
the chiral grading operator $\Gamma$, the Krein $CPT$ involution $J$, the Krein-Dirac
diagonalization, and the projector sieve / Drazin core-kernel algebra.

Key Mathematical Invariants:
1. **Discrete Exterior Calculus on Graphs**:
   - Boundary/incidence matrix $B : \mathrm{Matrix}\ E\ V\ R$.
   - Discrete exterior derivative $d = B : C^0 \to C^1$.
   - Discrete codifferential $\delta = B^\top : C^1 \to C^0$.
   - Node Graph Laplacian: $\Delta_0 = B^\top B$.
   - Edge Graph Laplacian: $\Delta_1 = B B^\top$.
   - Trace equality across node and edge Laplacians: $\mathrm{Tr}(\Delta_0) = \mathrm{Tr}(\Delta_1)$.

2. **The Discrete Hodge-Dirac Operator**:
   - $D = \begin{pmatrix} 0 & B^\top \\ B & 0 \end{pmatrix} \in \mathrm{Matrix}\ (V \oplus E)\ (V \oplus E)\ R$.
   - Hodge Laplacian identity: $D^2 = \begin{pmatrix} \Delta_0 & 0 \\ 0 & \Delta_1 \end{pmatrix}$.

3. **Chiral Grading Operator (Fermion Parity)**:
   - $\Gamma = \begin{pmatrix} \mathbf{1}_V & 0 \\ 0 & -\mathbf{1}_E \end{pmatrix}$.
   - Involution: $\Gamma^2 = \mathbf{1}_{V \oplus E}$.
   - Superselection / Anticommutation: $\{D, \Gamma\} = D \Gamma + \Gamma D = 0$.

4. **Krein $CPT$ Involution and Krein-Chiral Dirac Operator**:
   - On balanced spaces ($V = E$): $J = \begin{pmatrix} 0 & -\mathbf{1}_V \\ \mathbf{1}_V & 0 \end{pmatrix}$.
   - Involutive law: $J^2 = -\mathbf{1}_{V \oplus V}$.
   - Anticommutation with $\Gamma$: $\{J, \Gamma\} = J \Gamma + \Gamma J = 0$.
   - Krein-Dirac operator: $D_{\mathrm{Krein}} = J D$.
   - Exact conversion to diagonal kinetic operator:
     $D_{\mathrm{Krein}} = \begin{pmatrix} -B & 0 \\ 0 & B^\top \end{pmatrix}$.

5. **Projector Sieve and Drazin Core-Kernel Algebra**:
   - Idempotency and mutual annihilation of null projector $1 - P$.
   - Drazin core projector $P_{\mathrm{core}} = L L^D$ idempotency: $(L L^D)^2 = L L^D$.
   - Drazin kernel projector $P_{\mathrm{ker}} = 1 - L L^D$ transient generator annihilation:
     $L (1 - L L^D) = 0$.

6. **Master Certificate**:
   - Zero sorry, zero admit, zero custom axioms.
-/

namespace InfoGeometry.QuantumContext.GeneralGraphHodgeDiracKrein

open Matrix

variable {V E : Type*} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
variable {R : Type*} [CommRing R]

/-! ### Section 1: The Discrete Exterior Derivative & Codifferential on Graphs -/

/-- Node Graph Laplacian $\Delta_0 = B^\top B \in \mathrm{Matrix}\ V\ V\ R$. -/
def nodeLaplacian (B : Matrix E V R) : Matrix V V R := Bᵀ * B

/-- Edge Graph Laplacian $\Delta_1 = B B^\top \in \mathrm{Matrix}\ E\ E\ R$. -/
def edgeLaplacian (B : Matrix E V R) : Matrix E E R := B * Bᵀ

/-- Trace equality across node and edge Laplacians (via trace cyclicity):
    $\mathrm{Tr}(\Delta_0) = \mathrm{Tr}(\Delta_1)$. -/
theorem laplacian_trace_eq (B : Matrix E V R) :
    Matrix.trace (nodeLaplacian B) = Matrix.trace (edgeLaplacian B) := by
  dsimp [nodeLaplacian, edgeLaplacian]
  exact Matrix.trace_mul_comm Bᵀ B

/-! ### Section 2: The Discrete Hodge-Dirac Operator on $\Omega^\bullet = C^0 \oplus C^1$ -/

/-- Discrete Hodge-Dirac operator $D = \begin{pmatrix} 0 & B^\top \\ B & 0 \end{pmatrix}
    acting on differential forms $C^0(V) \oplus C^1(E)$. -/
def graphDirac (B : Matrix E V R) : Matrix (V ⊕ E) (V ⊕ E) R :=
  Matrix.fromBlocks 0 Bᵀ B 0

/-- Fundamental Hodge Laplacian theorem:
    $D^2 = \begin{pmatrix} \Delta_0 & 0 \\ 0 & \Delta_1 \end{pmatrix}$. -/
theorem graphDirac_sq (B : Matrix E V R) :
    graphDirac B * graphDirac B = Matrix.fromBlocks (nodeLaplacian B) 0 0 (edgeLaplacian B) := by
  rw [graphDirac, Matrix.fromBlocks_multiply]
  dsimp [nodeLaplacian, edgeLaplacian]
  simp

/-! ### Section 3: The Chiral Grading Operator $\Gamma$ (Fermion Parity) -/

/-- Chiral grading operator $\Gamma = \begin{pmatrix} \mathbf{1}_V & 0 \\ 0 & -\mathbf{1}_E \end{pmatrix}$. -/
def graphChiralGamma : Matrix (V ⊕ E) (V ⊕ E) R :=
  Matrix.fromBlocks 1 0 0 (-1)

/-- Involution: $\Gamma^2 = \mathbf{1}$. -/
theorem graphChiralGamma_sq :
    (graphChiralGamma : Matrix (V ⊕ E) (V ⊕ E) R) * graphChiralGamma = 1 := by
  rw [graphChiralGamma, Matrix.fromBlocks_multiply]
  simp

/-- Anticommutation of the Hodge-Dirac operator with chiral grading:
    $\{D, \Gamma\} = D \Gamma + \Gamma D = 0$. -/
theorem graphDirac_anticomm_gamma (B : Matrix E V R) :
    graphDirac B * graphChiralGamma + graphChiralGamma * graphDirac B = 0 := by
  rw [graphDirac, graphChiralGamma, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp
  rw [Matrix.fromBlocks_add]
  simp

/-! ### Section 4: Krein $CPT$ Involution $J$ and Krein-Chiral Dirac Operator -/

/-- Krein $CPT$ involution $J = \begin{pmatrix} 0 & -\mathbf{1}_V \\ \mathbf{1}_V & 0 \end{pmatrix}$
    on balanced spaces ($V = E$). -/
def graphKreinJ : Matrix (V ⊕ V) (V ⊕ V) R :=
  Matrix.fromBlocks 0 (-1) 1 0

/-- Involutive law: $J^2 = -\mathbf{1}$. -/
theorem graphKreinJ_sq :
    (graphKreinJ : Matrix (V ⊕ V) (V ⊕ V) R) * graphKreinJ = -1 := by
  rw [graphKreinJ, Matrix.fromBlocks_multiply]
  simp only [mul_zero, zero_mul, add_zero, zero_add, mul_one, mul_neg, neg_mul, one_mul, neg_neg]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

/-- Anticommutation of Krein involution $J$ with chiral grading $\Gamma$:
    $\{J, \Gamma\} = J \Gamma + \Gamma J = 0$. -/
theorem graphKreinJ_anticomm_gamma :
    (graphKreinJ : Matrix (V ⊕ V) (V ⊕ V) R) * graphChiralGamma +
    (graphChiralGamma : Matrix (V ⊕ V) (V ⊕ V) R) * graphKreinJ = 0 := by
  rw [graphKreinJ, graphChiralGamma, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp
  rw [Matrix.fromBlocks_add]
  simp

/-- Krein-Dirac operator $D_{\mathrm{Krein}} = J \circ D$. -/
def graphKreinDirac (B : Matrix V V R) : Matrix (V ⊕ V) (V ⊕ V) R :=
  graphKreinJ * graphDirac B

/-- Exact conversion from off-diagonal to diagonal kinetic operator:
    $D_{\mathrm{Krein}} = \begin{pmatrix} -B & 0 \\ 0 & B^\top \end{pmatrix}$. -/
theorem graphKreinDirac_formula (B : Matrix V V R) :
    graphKreinDirac B = Matrix.fromBlocks (-B) 0 0 Bᵀ := by
  rw [graphKreinDirac, graphKreinJ, graphDirac, Matrix.fromBlocks_multiply]
  simp

/-! ### Section 5: The Projector Sieve Algebra -/

/-- Null projector $P_0 = 1 - P$ associated to a symmetric/idempotent projector $P$. -/
def nullProjector (P : Matrix V V R) : Matrix V V R := 1 - P

/-- Idempotency of the null projector: $(1 - P)^2 = 1 - P$. -/
theorem nullProjector_sq (P : Matrix V V R) (hP : P * P = P) :
    nullProjector P * nullProjector P = nullProjector P := by
  dsimp [nullProjector]
  calc
    (1 - P) * (1 - P) = (1 - P) * 1 - (1 - P) * P := mul_sub (1 - P) 1 P
    _ = (1 - P) - (1 * P - P * P) := by rw [mul_one, sub_mul]
    _ = (1 - P) - (P - P) := by rw [one_mul, hP]
    _ = (1 - P) - 0 := by rw [sub_self]
    _ = 1 - P := sub_zero (1 - P)

/-- Mutual annihilation of projector $P$ and its complement $1 - P$:
    $P (1 - P) = 0$ and $(1 - P) P = 0$. -/
theorem nullProjector_annihilate (P : Matrix V V R) (hP : P * P = P) :
    P * nullProjector P = 0 ∧ nullProjector P * P = 0 := by
  dsimp [nullProjector]
  constructor
  · calc
      P * (1 - P) = P * 1 - P * P := mul_sub P 1 P
      _ = P - P := by rw [mul_one, hP]
      _ = 0 := sub_self P
  · calc
      (1 - P) * P = 1 * P - P * P := sub_mul 1 P P
      _ = P - P := by rw [one_mul, hP]
      _ = 0 := sub_self P

/-- Drazin core projector $P_{\mathrm{core}} = L L^D$. -/
def drazinCore (L LD : Matrix V V R) : Matrix V V R := L * LD

/-- Drazin kernel projector $P_{\mathrm{ker}} = 1 - L L^D$. -/
def drazinKernel (L LD : Matrix V V R) : Matrix V V R := 1 - L * LD

/-- Idempotency of the Drazin core: $(L L^D)^2 = L L^D$. -/
theorem drazinCore_sq (L LD : Matrix V V R) (hcomm : L * LD = LD * L) (h3 : L * LD * L = L) :
    drazinCore L LD * drazinCore L LD = drazinCore L LD := by
  dsimp [drazinCore]
  calc
    (L * LD) * (L * LD) = ((L * LD) * L) * LD := (mul_assoc (L * LD) L LD).symm
    _ = L * LD := by rw [h3]

/-- The Drazin kernel strictly annihilates the transient generator $L$,
    isolating the ergodic stationary sinks: $L (1 - L L^D) = 0$. -/
theorem drazinKernel_annihilates_L (L LD : Matrix V V R) (hcomm : L * LD = LD * L) (h3 : L * LD * L = L) :
    L * drazinKernel L LD = 0 := by
  dsimp [drazinKernel]
  have h_prod : L * (L * LD) = L := by
    calc
      L * (L * LD) = L * (LD * L) := by rw [hcomm]
      _ = (L * LD) * L := (mul_assoc L LD L).symm
      _ = L := h3
  calc
    L * (1 - L * LD) = L * 1 - L * (L * LD) := mul_sub L 1 (L * LD)
    _ = L - L := by rw [mul_one, h_prod]
    _ = 0 := sub_self L

/-! ### Section 6: Master Verification Certificate -/

/-- Master Certificate bundling all foundational discrete exterior calculus,
    Hodge-Dirac, Krein-chiral splitting, and projector sieve theorems. -/
structure GeneralGraphHodgeDiracKreinCertificate : Prop where
  laplacian_trace_equality :
    ∀ (V E : Type*) [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      (R : Type*) [CommRing R] (B : Matrix E V R),
      Matrix.trace (nodeLaplacian B) = Matrix.trace (edgeLaplacian B)
  dirac_laplacian_block_squared :
    ∀ (V E : Type*) [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      (R : Type*) [CommRing R] (B : Matrix E V R),
      graphDirac B * graphDirac B = Matrix.fromBlocks (nodeLaplacian B) 0 0 (edgeLaplacian B)
  chiral_gamma_involutive :
    ∀ (V E : Type*) [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      (R : Type*) [CommRing R],
      (graphChiralGamma : Matrix (V ⊕ E) (V ⊕ E) R) * graphChiralGamma = 1
  dirac_chiral_anticommutation :
    ∀ (V E : Type*) [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      (R : Type*) [CommRing R] (B : Matrix E V R),
      graphDirac B * graphChiralGamma + graphChiralGamma * graphDirac B = 0
  krein_j_squared_neg_one :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R],
      (graphKreinJ : Matrix (V ⊕ V) (V ⊕ V) R) * graphKreinJ = -1
  krein_j_chiral_anticommutation :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R],
      (graphKreinJ : Matrix (V ⊕ V) (V ⊕ V) R) * graphChiralGamma +
      (graphChiralGamma : Matrix (V ⊕ V) (V ⊕ V) R) * graphKreinJ = 0
  krein_dirac_exact_diagonalization :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] (B : Matrix V V R),
      graphKreinDirac B = Matrix.fromBlocks (-B) 0 0 Bᵀ
  null_projector_idempotent :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R]
      (P : Matrix V V R) (hP : P * P = P),
      nullProjector P * nullProjector P = nullProjector P
  null_projector_annihilation :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R]
      (P : Matrix V V R) (hP : P * P = P),
      P * nullProjector P = 0 ∧ nullProjector P * P = 0
  drazin_core_idempotent :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R]
      (L LD : Matrix V V R) (hcomm : L * LD = LD * L) (h3 : L * LD * L = L),
      drazinCore L LD * drazinCore L LD = drazinCore L LD
  drazin_kernel_annihilation :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R]
      (L LD : Matrix V V R) (hcomm : L * LD = LD * L) (h3 : L * LD * L = L),
      L * drazinKernel L LD = 0

/-- Compilation theorem certifying the complete General Graph Hodge-Dirac Krein formalization. -/
theorem compile_general_graph_hodge_dirac_krein : GeneralGraphHodgeDiracKreinCertificate where
  laplacian_trace_equality := fun V E _ _ _ _ R _ B => laplacian_trace_eq B
  dirac_laplacian_block_squared := fun V E _ _ _ _ R _ B => graphDirac_sq B
  chiral_gamma_involutive := fun V E _ _ _ _ R _ => graphChiralGamma_sq
  dirac_chiral_anticommutation := fun V E _ _ _ _ R _ B => graphDirac_anticomm_gamma B
  krein_j_squared_neg_one := fun V _ _ R _ => graphKreinJ_sq
  krein_j_chiral_anticommutation := fun V _ _ R _ => graphKreinJ_anticomm_gamma
  krein_dirac_exact_diagonalization := fun V _ _ R _ B => graphKreinDirac_formula B
  null_projector_idempotent := fun V _ _ R _ P hP => nullProjector_sq P hP
  null_projector_annihilation := fun V _ _ R _ P hP => nullProjector_annihilate P hP
  drazin_core_idempotent := fun V _ _ R _ L LD hcomm h3 => drazinCore_sq L LD hcomm h3
  drazin_kernel_annihilation := fun V _ _ R _ L LD hcomm h3 => drazinKernel_annihilates_L L LD hcomm h3

end InfoGeometry.QuantumContext.GeneralGraphHodgeDiracKrein
