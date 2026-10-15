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
# The Discrete Krein-Andreev Graph Engine

Module: `Experimental.Sandbox.QuantumContext.DiscreteKreinAndreevGraphEngine`

This module formalizes in full native Mathlib in Lean 4:
1. **Discrete Exterior Calculus on Graphs & Hodge-Dirac Operator**:
   - Boundary incidence matrix $B : \mathrm{Matrix}\ E\ V\ R$.
   - Node Laplacian $\Delta_0 = B^\top B \in \mathrm{Matrix}\ V\ V\ R$.
   - Edge Laplacian $\Delta_1 = B B^\top \in \mathrm{Matrix}\ E\ E\ R$.
   - Trace equality across node and edge Laplacians: $\mathrm{Tr}(\Delta_0) = \mathrm{Tr}(\Delta_1)$.
   - Discrete Hodge-Dirac operator $D = \begin{pmatrix} 0 & B^\top \\ B & 0 \end{pmatrix}$.
   - Hodge-Dirac square is diagonal block Laplacian:
     $D^2 = \begin{pmatrix} \Delta_0 & 0 \\ 0 & \Delta_1 \end{pmatrix}$.

2. **Chiral Grading & Krein Fundamental Symmetry**:
   - Chiral grading involution $\Gamma = \begin{pmatrix} \mathbf{1}_V & 0 \\ 0 & -\mathbf{1}_E \end{pmatrix}$.
   - Dirac-chiral anticommutation $\{D, \Gamma\} = 0$.
   - Krein fundamental symmetry $J = \begin{pmatrix} 0 & -\mathbf{1}_V \\ \mathbf{1}_V & 0 \end{pmatrix}$ with $J^2 = -\mathbf{1}$.
   - Krein-Dirac operator $D_K = J D = \begin{pmatrix} -B & 0 \\ 0 & B^\top \end{pmatrix}$.
   - True Krein-Dirac square: $D_K^2 = \begin{pmatrix} B^2 & 0 \\ 0 & (B^\top)^2 \end{pmatrix}$.

3. **The Andreev Reflection & Bogoliubov-de Gennes (BdG) Symmetries**:
   - Nambu particle-hole / Andreev involution $\tau_1 = \begin{pmatrix} 0 & \mathbf{1} \\ \mathbf{1} & 0 \end{pmatrix}$ with $\tau_1^2 = \mathbf{1}$.
   - Discrete BdG Hamiltonian $H_{\mathrm{BdG}} = \begin{pmatrix} H_0 & \Delta \\ \Delta^\top & -H_0^\top \end{pmatrix}$.
   - Fundamental Andreev particle-hole antisymmetry:
     $\tau_1 H_{\mathrm{BdG}} \tau_1 = - H_{\mathrm{BdG}}^\top$ under skew pairing $\Delta^\top = -\Delta$.
   - Skew-pairing Andreev sign reversal:
     $\tau_1 H_{\mathrm{BdG}} \tau_1 = - H_{\mathrm{BdG}}$ when $H_0^\top = H_0$ and $\Delta^\top = -\Delta$.

4. **Genuine Matrix Moore-Penrose & Drazin Sieve Projectors (Resolving Trap T16)**:
   - Moore-Penrose matrix support projector $P_{\mathrm{supp}} = \rho \rho^\dagger$ idempotency.
   - Matrix kernel projector $P_{\mathrm{ker}} = 1 - \rho \rho^\dagger$ annihilates state density $\rho$.
   - Drazin Markov generator core projector $P_{\mathrm{core}} = L L^D$ idempotency.
   - Drazin stationary sink projector $P_\infty = 1 - L L^D$ two-sided annihilation of flow $L$.

5. **Master Verification Certificate**:
   - Bundled certificate `DiscreteKreinAndreevGraphCertificate` and proof `compile_discrete_krein_andreev_graph_engine`.
   - Zero sorry, zero admit, zero custom axioms.
-/

namespace Experimental.Sandbox.QuantumContext.DiscreteKreinAndreevGraphEngine

open Matrix

variable {V E : Type*} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
variable {R : Type*} [CommRing R]

/-! ### Section 1: The Discrete Exterior Complex & Hodge-Dirac Operator -/

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

/-- Discrete Hodge-Dirac operator $D = \begin{pmatrix} 0 & B^\top \\ B & 0 \end{pmatrix}
    acting on differential forms $C^0(V) \oplus C^1(E)$. -/
def hodgeDirac (B : Matrix E V R) : Matrix (V ⊕ E) (V ⊕ E) R :=
  Matrix.fromBlocks 0 Bᵀ B 0

/-- Fundamental Hodge-Dirac square is diagonal block Laplacian:
    $D^2 = \begin{pmatrix} \Delta_0 & 0 \\ 0 & \Delta_1 \end{pmatrix}$. -/
theorem hodgeDirac_sq (B : Matrix E V R) :
    hodgeDirac B * hodgeDirac B = Matrix.fromBlocks (nodeLaplacian B) 0 0 (edgeLaplacian B) := by
  rw [hodgeDirac, Matrix.fromBlocks_multiply]
  dsimp [nodeLaplacian, edgeLaplacian]
  simp

/-! ### Section 2: Chiral Grading & Krein Fundamental Symmetry -/

/-- Chiral grading operator $\Gamma = \begin{pmatrix} \mathbf{1}_V & 0 \\ 0 & -\mathbf{1}_E \end{pmatrix}$. -/
def chiralGamma : Matrix (V ⊕ E) (V ⊕ E) R :=
  Matrix.fromBlocks 1 0 0 (-1)

/-- Involution: $\Gamma^2 = \mathbf{1}$. -/
theorem chiralGamma_sq :
    (chiralGamma : Matrix (V ⊕ E) (V ⊕ E) R) * chiralGamma = 1 := by
  rw [chiralGamma, Matrix.fromBlocks_multiply]
  simp

/-- Anticommutation of the Hodge-Dirac operator with chiral grading:
    $\{D, \Gamma\} = D \Gamma + \Gamma D = 0$. -/
theorem dirac_anticomm_gamma (B : Matrix E V R) :
    hodgeDirac B * chiralGamma + chiralGamma * hodgeDirac B = 0 := by
  rw [hodgeDirac, chiralGamma, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp
  rw [Matrix.fromBlocks_add]
  simp

/-- Krein fundamental symmetry $J = \begin{pmatrix} 0 & -\mathbf{1}_V \\ \mathbf{1}_V & 0 \end{pmatrix}$
    on balanced carrier ($V \oplus V$). -/
def kreinJ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] : Matrix (V ⊕ V) (V ⊕ V) R :=
  Matrix.fromBlocks 0 (-1) 1 0

/-- Involutive law of Krein fundamental symmetry: $J^2 = -\mathbf{1}$. -/
theorem kreinJ_sq :
    (kreinJ V R) * (kreinJ V R) = -1 := by
  rw [kreinJ, Matrix.fromBlocks_multiply]
  simp only [mul_zero, zero_mul, add_zero, zero_add, mul_one, mul_neg, neg_mul, one_mul, neg_neg]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

/-- Anticommutation of Krein involution $J$ with chiral grading $\Gamma$:
    $\{J, \Gamma\} = J \Gamma + \Gamma J = 0$. -/
theorem kreinJ_anticomm_gamma :
    (kreinJ V R) * (chiralGamma (V := V) (E := V)) +
    (chiralGamma (V := V) (E := V)) * (kreinJ V R) = 0 := by
  rw [kreinJ, chiralGamma, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp
  rw [Matrix.fromBlocks_add]
  simp

/-- Krein-Dirac operator $D_K = J D$. -/
def kreinDirac (B : Matrix V V R) : Matrix (V ⊕ V) (V ⊕ V) R :=
  kreinJ V R * hodgeDirac B

/-- Exact conversion to diagonal kinetic operator:
    $D_K = \begin{pmatrix} -B & 0 \\ 0 & B^\top \end{pmatrix}$. -/
theorem kreinDirac_formula (B : Matrix V V R) :
    kreinDirac B = Matrix.fromBlocks (-B) 0 0 Bᵀ := by
  rw [kreinDirac, kreinJ, hodgeDirac, Matrix.fromBlocks_multiply]
  simp

/-- Exact square of Krein-Dirac operator:
    $D_K^2 = \begin{pmatrix} B^2 & 0 \\ 0 & (B^\top)^2 \end{pmatrix}$. -/
theorem kreinDirac_sq_formula (B : Matrix V V R) :
    kreinDirac B * kreinDirac B = Matrix.fromBlocks (B * B) 0 0 (Bᵀ * Bᵀ) := by
  rw [kreinDirac_formula, Matrix.fromBlocks_multiply]
  simp

/-! ### Section 3: The Andreev Reflection & Bogoliubov-de Gennes (BdG) Symmetries -/

/-- Particle-hole / Andreev involution $\tau_1 = \begin{pmatrix} 0 & \mathbf{1} \\ \mathbf{1} & 0 \end{pmatrix}$
    on Nambu doubled carrier $V \oplus V$. -/
def andreevTau1 : Matrix (V ⊕ V) (V ⊕ V) R :=
  Matrix.fromBlocks 0 1 1 0

/-- Involution: $\tau_1^2 = \mathbf{1}$. -/
theorem andreevTau1_sq :
    (andreevTau1 : Matrix (V ⊕ V) (V ⊕ V) R) * andreevTau1 = 1 := by
  rw [andreevTau1, Matrix.fromBlocks_multiply]
  simp

/-- Particle-hole block transposition action:
    $\tau_1 \begin{pmatrix} A & B \\ C & D \end{pmatrix} \tau_1 = \begin{pmatrix} D & C \\ B & A \end{pmatrix}$. -/
theorem andreev_swap (A B C D : Matrix V V R) :
    andreevTau1 * Matrix.fromBlocks A B C D * andreevTau1 = Matrix.fromBlocks D C B A := by
  rw [andreevTau1, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

/-- Discrete Bogoliubov-de Gennes (BdG) Hamiltonian with normal generator $H_0$ and pairing $\Delta$:
    $H_{\mathrm{BdG}} = \begin{pmatrix} H_0 & \Delta \\ \Delta^\top & -H_0^\top \end{pmatrix}$. -/
def bdgHamiltonian (H0 Delta : Matrix V V R) : Matrix (V ⊕ V) (V ⊕ V) R :=
  Matrix.fromBlocks H0 Delta Deltaᵀ (-H0ᵀ)

/-- Unconditional block transposition of the BdG Hamiltonian under Andreev conjugation:
    $\tau_1 H_{\mathrm{BdG}} \tau_1 = \begin{pmatrix} -H_0^\top & \Delta^\top \\ \Delta & H_0 \end{pmatrix}$. -/
theorem andreev_bdg_swap (H0 Delta : Matrix V V R) :
    andreevTau1 * bdgHamiltonian H0 Delta * andreevTau1 = Matrix.fromBlocks (-H0ᵀ) Deltaᵀ Delta H0 := by
  rw [bdgHamiltonian, andreev_swap]

/-- The Fundamental Andreev Particle-Hole Antisymmetry:
    For skew-symmetric pairing $\Delta^\top = -\Delta$,
    $\tau_1 H_{\mathrm{BdG}} \tau_1 = - H_{\mathrm{BdG}}^\top$. -/
theorem andreev_bdg_antisymmetry (H0 Delta : Matrix V V R) (hDelta : Deltaᵀ = -Delta) :
    andreevTau1 * bdgHamiltonian H0 Delta * andreevTau1 = - (bdgHamiltonian H0 Delta)ᵀ := by
  rw [andreev_bdg_swap]
  rw [bdgHamiltonian, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]
  simp only [Matrix.transpose_transpose, Matrix.transpose_neg]
  rw [hDelta]
  simp only [neg_neg]

/-- Transpose of the BdG Hamiltonian under symmetric normal generator $H_0^\top = H_0$:
    $H_{\mathrm{BdG}}^\top = H_{\mathrm{BdG}}$. -/
theorem bdgHamiltonian_transpose (H0 Delta : Matrix V V R) (hH0 : H0ᵀ = H0) :
    (bdgHamiltonian H0 Delta)ᵀ = bdgHamiltonian H0 Delta := by
  rw [bdgHamiltonian, Matrix.fromBlocks_transpose]
  simp only [Matrix.transpose_transpose, Matrix.transpose_neg, hH0]

/-- Skew-Pairing Andreev Sign Reversal (The Exact Repair of the Drunken Professor's Minus Sign):
    For symmetric normal generator $H_0^\top = H_0$ and skew-symmetric pairing $\Delta^\top = -\Delta$,
    $\tau_1 H_{\mathrm{BdG}} \tau_1 = - H_{\mathrm{BdG}}$. -/
theorem andreev_skew_pairing_reversal (H0 Delta : Matrix V V R) (hH0 : H0ᵀ = H0) (hDelta : Deltaᵀ = -Delta) :
    andreevTau1 * bdgHamiltonian H0 Delta * andreevTau1 = - bdgHamiltonian H0 Delta := by
  rw [andreev_bdg_antisymmetry H0 Delta hDelta]
  rw [bdgHamiltonian_transpose H0 Delta hH0]

/-! ### Section 4: Genuine Matrix Moore-Penrose & Drazin Sieve Projectors (Resolving Trap T16) -/

/-- Moore-Penrose matrix support projector $P_{\mathrm{supp}} = \rho \rho^\dagger$. -/
def matrixSupportProj (rho rho_pinv : Matrix V V R) : Matrix V V R :=
  rho * rho_pinv

/-- Matrix kernel projector $P_{\mathrm{ker}} = 1 - \rho \rho^\dagger$. -/
def matrixKernelProj (rho rho_pinv : Matrix V V R) : Matrix V V R :=
  1 - rho * rho_pinv

/-- Idempotency of Moore-Penrose matrix support projector:
    $(\rho \rho^\dagger)^2 = \rho \rho^\dagger$ under the 1-inversion condition $\rho \rho^\dagger \rho = \rho$. -/
theorem matrix_support_proj_idempotent (rho rho_pinv : Matrix V V R) (h : rho * rho_pinv * rho = rho) :
    matrixSupportProj rho rho_pinv * matrixSupportProj rho rho_pinv = matrixSupportProj rho rho_pinv := by
  dsimp [matrixSupportProj]
  calc
    (rho * rho_pinv) * (rho * rho_pinv) = (rho * rho_pinv * rho) * rho_pinv := by rw [← mul_assoc]
    _ = rho * rho_pinv := by rw [h]

/-- Matrix kernel projector annihilates density state:
    $(1 - \rho \rho^\dagger) \rho = 0$. -/
theorem matrix_kernel_annihilates_density (rho rho_pinv : Matrix V V R) (h : rho * rho_pinv * rho = rho) :
    (1 - matrixSupportProj rho rho_pinv) * rho = 0 := by
  dsimp [matrixSupportProj]
  calc
    (1 - rho * rho_pinv) * rho = 1 * rho - (rho * rho_pinv) * rho := by rw [sub_mul]
    _ = rho - (rho * rho_pinv * rho) := by rw [one_mul]
    _ = rho - rho := by rw [h]
    _ = 0 := sub_self rho

/-- Kernel projector idempotency: $(1 - \rho \rho^\dagger)^2 = 1 - \rho \rho^\dagger$. -/
theorem matrix_kernel_proj_idempotent (rho rho_pinv : Matrix V V R) (h : rho * rho_pinv * rho = rho) :
    matrixKernelProj rho rho_pinv * matrixKernelProj rho rho_pinv = matrixKernelProj rho rho_pinv := by
  dsimp [matrixKernelProj]
  have hsupp : (rho * rho_pinv) * (rho * rho_pinv) = rho * rho_pinv :=
    matrix_support_proj_idempotent rho rho_pinv h
  calc
    (1 - rho * rho_pinv) * (1 - rho * rho_pinv) =
      (1 - rho * rho_pinv) * 1 - (1 - rho * rho_pinv) * (rho * rho_pinv) := by rw [mul_sub]
    _ = (1 - rho * rho_pinv) - (1 * (rho * rho_pinv) - (rho * rho_pinv) * (rho * rho_pinv)) := by
      rw [mul_one, sub_mul]
    _ = (1 - rho * rho_pinv) - (rho * rho_pinv - rho * rho_pinv) := by rw [one_mul, hsupp]
    _ = (1 - rho * rho_pinv) - 0 := by rw [sub_self]
    _ = 1 - rho * rho_pinv := sub_zero _

/-- Drazin core projector $P_{\mathrm{core}} = L L^D$. -/
def drazinCoreProj (L L_D : Matrix V V R) : Matrix V V R :=
  L * L_D

/-- Drazin stationary sink projector $P_\infty = 1 - L L^D$. -/
def drazinStationarySinkProj (L L_D : Matrix V V R) : Matrix V V R :=
  1 - L * L_D

/-- Idempotency of Drazin core projector: $(L L^D)^2 = L L^D$. -/
theorem drazin_core_idempotent (L L_D : Matrix V V R) (hcomm : L * L_D = L_D * L) (h2 : L * L * L_D = L) :
    drazinCoreProj L L_D * drazinCoreProj L L_D = drazinCoreProj L L_D := by
  dsimp [drazinCoreProj]
  have hmid : (L * L_D) * L = L := by
    calc
      (L * L_D) * L = L * (L_D * L) := by rw [mul_assoc]
      _ = L * (L * L_D) := by rw [← hcomm]
      _ = L * L * L_D := by rw [← mul_assoc]
      _ = L := h2
  calc
    (L * L_D) * (L * L_D) = ((L * L_D) * L) * L_D := by rw [← mul_assoc]
    _ = L * L_D := by rw [hmid]

/-- Idempotency of Drazin stationary sink projector: $(1 - L L^D)^2 = 1 - L L^D$. -/
theorem drazin_stationary_sink_idempotent (L L_D : Matrix V V R) (hcomm : L * L_D = L_D * L) (h2 : L * L * L_D = L) :
    drazinStationarySinkProj L L_D * drazinStationarySinkProj L L_D = drazinStationarySinkProj L L_D := by
  dsimp [drazinStationarySinkProj]
  have hcore : (L * L_D) * (L * L_D) = L * L_D := drazin_core_idempotent L L_D hcomm h2
  calc
    (1 - L * L_D) * (1 - L * L_D) = (1 - L * L_D) * 1 - (1 - L * L_D) * (L * L_D) := by rw [mul_sub]
    _ = (1 - L * L_D) - (1 * (L * L_D) - (L * L_D) * (L * L_D)) := by rw [mul_one, sub_mul]
    _ = (1 - L * L_D) - (L * L_D - L * L_D) := by rw [one_mul, hcore]
    _ = (1 - L * L_D) - 0 := by rw [sub_self]
    _ = 1 - L * L_D := sub_zero _

/-- Drazin stationary sink annihilates generator flow from right:
    $L (1 - L L^D) = 0$. -/
theorem drazin_stationary_sink_annihilates_generator (L L_D : Matrix V V R) (hcomm : L * L_D = L_D * L) (h2 : L * L * L_D = L) :
    L * drazinStationarySinkProj L L_D = 0 := by
  dsimp [drazinStationarySinkProj]
  calc
    L * (1 - L * L_D) = L * 1 - L * (L * L_D) := by rw [mul_sub]
    _ = L - (L * L * L_D) := by rw [mul_one, mul_assoc]
    _ = L - L := by rw [h2]
    _ = 0 := sub_self L

/-- Drazin stationary sink annihilates generator flow from left:
    $(1 - L L^D) L = 0$. -/
theorem drazin_stationary_sink_annihilates_generator_left (L L_D : Matrix V V R) (hcomm : L * L_D = L_D * L) (h2 : L * L * L_D = L) :
    drazinStationarySinkProj L L_D * L = 0 := by
  dsimp [drazinStationarySinkProj]
  have hmid : (L * L_D) * L = L := by
    calc
      (L * L_D) * L = L * (L_D * L) := by rw [mul_assoc]
      _ = L * (L * L_D) := by rw [← hcomm]
      _ = L * L * L_D := by rw [← mul_assoc]
      _ = L := h2
  calc
    (1 - L * L_D) * L = 1 * L - (L * L_D) * L := by rw [sub_mul]
    _ = L - L := by rw [one_mul, hmid]
    _ = 0 := sub_self L

/-! ### Section 5: Master Verification Certificate -/

/-- Master Certificate bundling all foundational discrete exterior calculus,
    Hodge-Dirac, Krein-chiral involution, Andreev BdG reflection, and
    matrix Moore-Penrose / Drazin sieve theorems. -/
structure DiscreteKreinAndreevGraphCertificate : Prop where
  laplacian_trace_equality :
    ∀ (V E : Type*) [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      (R : Type*) [CommRing R] (B : Matrix E V R),
      Matrix.trace (nodeLaplacian B) = Matrix.trace (edgeLaplacian B)
  hodge_dirac_squared :
    ∀ (V E : Type*) [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      (R : Type*) [CommRing R] (B : Matrix E V R),
      hodgeDirac B * hodgeDirac B = Matrix.fromBlocks (nodeLaplacian B) 0 0 (edgeLaplacian B)
  chiral_gamma_involutive :
    ∀ (V E : Type*) [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      (R : Type*) [CommRing R],
      (chiralGamma : Matrix (V ⊕ E) (V ⊕ E) R) * chiralGamma = 1
  dirac_chiral_anticommutation :
    ∀ (V E : Type*) [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      (R : Type*) [CommRing R] (B : Matrix E V R),
      hodgeDirac B * chiralGamma + chiralGamma * hodgeDirac B = 0
  krein_j_squared_neg_one :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R],
      (kreinJ V R) * (kreinJ V R) = -1
  krein_j_chiral_anticommutation :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R],
      (kreinJ V R) * (chiralGamma (V := V) (E := V)) +
      (chiralGamma (V := V) (E := V)) * (kreinJ V R) = 0
  krein_dirac_formula :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] (B : Matrix V V R),
      kreinDirac B = Matrix.fromBlocks (-B) 0 0 Bᵀ
  krein_dirac_sq_formula :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] (B : Matrix V V R),
      kreinDirac B * kreinDirac B = Matrix.fromBlocks (B * B) 0 0 (Bᵀ * Bᵀ)
  andreev_tau1_squared :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R],
      (andreevTau1 : Matrix (V ⊕ V) (V ⊕ V) R) * andreevTau1 = 1
  andreev_swap_formula :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R]
      (A B C D : Matrix V V R),
      andreevTau1 * Matrix.fromBlocks A B C D * andreevTau1 = Matrix.fromBlocks D C B A
  andreev_bdg_antisymmetry :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R]
      (H0 Delta : Matrix V V R) (hDelta : Deltaᵀ = -Delta),
      andreevTau1 * bdgHamiltonian H0 Delta * andreevTau1 = - (bdgHamiltonian H0 Delta)ᵀ
  andreev_skew_pairing_reversal :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R]
      (H0 Delta : Matrix V V R) (hH0 : H0ᵀ = H0) (hDelta : Deltaᵀ = -Delta),
      andreevTau1 * bdgHamiltonian H0 Delta * andreevTau1 = - bdgHamiltonian H0 Delta
  matrix_support_proj_idempotent :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R]
      (rho rho_pinv : Matrix V V R) (h : rho * rho_pinv * rho = rho),
      matrixSupportProj rho rho_pinv * matrixSupportProj rho rho_pinv = matrixSupportProj rho rho_pinv
  matrix_kernel_annihilates_density :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R]
      (rho rho_pinv : Matrix V V R) (h : rho * rho_pinv * rho = rho),
      (1 - matrixSupportProj rho rho_pinv) * rho = 0
  drazin_core_idempotent :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R]
      (L L_D : Matrix V V R) (hcomm : L * L_D = L_D * L) (h2 : L * L * L_D = L),
      drazinCoreProj L L_D * drazinCoreProj L L_D = drazinCoreProj L L_D
  drazin_stationary_sink_idempotent :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R]
      (L L_D : Matrix V V R) (hcomm : L * L_D = L_D * L) (h2 : L * L * L_D = L),
      drazinStationarySinkProj L L_D * drazinStationarySinkProj L L_D = drazinStationarySinkProj L L_D
  drazin_stationary_sink_annihilates_generator :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R]
      (L L_D : Matrix V V R) (hcomm : L * L_D = L_D * L) (h2 : L * L * L_D = L),
      L * drazinStationarySinkProj L L_D = 0
  drazin_stationary_sink_annihilates_generator_left :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R]
      (L L_D : Matrix V V R) (hcomm : L * L_D = L_D * L) (h2 : L * L * L_D = L),
      drazinStationarySinkProj L L_D * L = 0

/-- Compilation theorem certifying the complete Discrete Krein-Andreev Graph Engine. -/
theorem compile_discrete_krein_andreev_graph_engine : DiscreteKreinAndreevGraphCertificate where
  laplacian_trace_equality := fun V E _ _ _ _ R _ B => laplacian_trace_eq B
  hodge_dirac_squared := fun V E _ _ _ _ R _ B => hodgeDirac_sq B
  chiral_gamma_involutive := fun V E _ _ _ _ R _ => chiralGamma_sq
  dirac_chiral_anticommutation := fun V E _ _ _ _ R _ B => dirac_anticomm_gamma B
  krein_j_squared_neg_one := fun V _ _ R _ => kreinJ_sq
  krein_j_chiral_anticommutation := fun V _ _ R _ => kreinJ_anticomm_gamma
  krein_dirac_formula := fun V _ _ R _ B => kreinDirac_formula B
  krein_dirac_sq_formula := fun V _ _ R _ B => kreinDirac_sq_formula B
  andreev_tau1_squared := fun V _ _ R _ => andreevTau1_sq
  andreev_swap_formula := fun V _ _ R _ A B C D => andreev_swap A B C D
  andreev_bdg_antisymmetry := fun V _ _ R _ H0 Delta hDelta => andreev_bdg_antisymmetry H0 Delta hDelta
  andreev_skew_pairing_reversal := fun V _ _ R _ H0 Delta hH0 hDelta => andreev_skew_pairing_reversal H0 Delta hH0 hDelta
  matrix_support_proj_idempotent := fun V _ _ R _ rho rho_pinv h => matrix_support_proj_idempotent rho rho_pinv h
  matrix_kernel_annihilates_density := fun V _ _ R _ rho rho_pinv h => matrix_kernel_annihilates_density rho rho_pinv h
  drazin_core_idempotent := fun V _ _ R _ L L_D hcomm h2 => drazin_core_idempotent L L_D hcomm h2
  drazin_stationary_sink_idempotent := fun V _ _ R _ L L_D hcomm h2 => drazin_stationary_sink_idempotent L L_D hcomm h2
  drazin_stationary_sink_annihilates_generator := fun V _ _ R _ L L_D hcomm h2 => drazin_stationary_sink_annihilates_generator L L_D hcomm h2
  drazin_stationary_sink_annihilates_generator_left := fun V _ _ R _ L L_D hcomm h2 => drazin_stationary_sink_annihilates_generator_left L L_D hcomm h2

end Experimental.Sandbox.QuantumContext.DiscreteKreinAndreevGraphEngine
