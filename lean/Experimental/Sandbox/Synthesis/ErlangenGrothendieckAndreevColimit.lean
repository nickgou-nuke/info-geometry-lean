import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

open Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Erlangen-Grothendieck-Andreev Colimit: The Categorical Authority Law
Target: `lean/Experimental/Sandbox/Synthesis/ErlangenGrothendieckAndreevColimit.lean`

Formalizes in full native Mathlib in Lean 4:
1. The Erlangen KAN & Cartan 3-Mode Supercarrier Triad:
   - Graded supertrace on total carrier `Matrix (V ⊕ E) (V ⊕ E) R`.
   - Scale, Chiral, and Volume modes.
   - Grothendieck Scale Supertrace theorem matching the Euler-Poincaré characteristic `(|V| - |E|) * σ`.
   - Discrete Hodge-Dirac injection with exact supertrace vanishing and block square.
   - Scale-Dirac homothety commutation `[scaleMode σ, hodgeDirac B] = 0`.
2. Andreev Particle-Hole Reflection & Nambu-BdG Hamiltonian:
   - Fundamental Andreev involution `τ₁` on Nambu carrier `Matrix (V ⊕ V) (V ⊕ V) R` with `τ₁² = 1`.
   - Discrete BdG Hamiltonian with normal generator `H₀` and pairing `Δ`.
   - Fundamental Andreev Particle-Hole Antisymmetry `τ₁ H_{BdG} τ₁ = - H_{BdG}ᵀ` for skew pairing `Δᵀ = -Δ`.
   - Topological Andreev Sign Reversal `τ₁ H_{BdG} τ₁ = - H_{BdG}` for symmetric `H₀ᵀ = H₀` and skew `Δᵀ = -Δ`.
3. Inductive Colimit Extension & Invariant Stabilization:
   - Trace of 2x2 block matrix decomposition into sum of diagonal traces.
   - Euler-Poincaré characteristic additivity under direct sum.
   - Zero-extension of boundary matrix `extendB`.
   - Exact colimit invariance of node and edge trace Laplacians.
   - Graded supertrace invariance of colimit Hodge-Dirac square.
   - Preservation of Andreev particle-hole antisymmetry under colimit extension `extendBdG`.
4. Grothendieck AB5 Exact Inductive Tower Chain:
   - Iterated sequence towers `Vertices` and `Edges` along `ℕ`.
   - Multi-step trace stabilization along the entire tower chain `extendChain`.
   - Colimit Hodge-Dirac algebraic cubic commutation `[D_m, D_m²] = 0`.
5. Master Verification Certificate:
   - Bundled verification structure `ErlangenGrothendieckAndreevCertificate : Prop`.
   - Complete zero-sorry compilation theorem `compile_erlangen_grothendieck_andreev_colimit`.
-/

namespace Experimental.Sandbox.Synthesis.ErlangenGrothendieckAndreevColimit

universe u_V u_E u_R

variable {V : Type u_V} {E : Type u_E} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
variable {R : Type u_R} [CommRing R]

/-! ### Section 1: The Erlangen KAN & Cartan 3-Mode Supercarrier Triad -/

/-- Graded supertrace on total supercarrier `Matrix (V ⊕ E) (V ⊕ E) R`:
    `superTrace M = Matrix.trace (Matrix.toBlocks₁₁ M) - Matrix.trace (Matrix.toBlocks₂₂ M)`. -/
def superTrace (M : Matrix (V ⊕ E) (V ⊕ E) R) : R :=
  Matrix.trace (Matrix.toBlocks₁₁ M) - Matrix.trace (Matrix.toBlocks₂₂ M)

/-- Scale Mode: uniform homothety `σ • 1` on diagonal blocks. -/
def scaleMode (σ : R) : Matrix (V ⊕ E) (V ⊕ E) R :=
  Matrix.fromBlocks (σ • (1 : Matrix V V R)) 0 0 (σ • (1 : Matrix E E R))

/-- Chiral Mode: off-diagonal odd blocks `B : Matrix V E R` and `C : Matrix E V R`. -/
def chiralMode (B : Matrix V E R) (C : Matrix E V R) : Matrix (V ⊕ E) (V ⊕ E) R :=
  Matrix.fromBlocks 0 B C 0

/-- Volume Mode: diagonal even blocks `A : Matrix V V R` and `D : Matrix E E R`. -/
def volumeMode (A : Matrix V V R) (D : Matrix E E R) : Matrix (V ⊕ E) (V ⊕ E) R :=
  Matrix.fromBlocks A 0 0 D

/-- Euler-Poincaré Characteristic of the graph complex: `χ(G) = |V| - |E|`. -/
def eulerPoincare (V E : Type*) [Fintype V] [Fintype E] (R : Type*) [CommRing R] : R :=
  (Fintype.card V : R) - (Fintype.card E : R)

/-- Grothendieck Scale Supertrace Theorem:
    The supertrace of the scale mode operator exactly computes `eulerPoincare V E R * σ`. -/
theorem superTrace_scaleMode (σ : R) :
    superTrace (scaleMode (V := V) (E := E) σ) = eulerPoincare V E R * σ := by
  dsimp [superTrace, scaleMode, eulerPoincare]
  rw [Matrix.trace_smul, Matrix.trace_smul]
  rw [Matrix.trace_one, Matrix.trace_one]
  ring

/-- Discrete Hodge-Dirac injection:
    `hodgeDirac B = Matrix.fromBlocks 0 Bᵀ B 0`. -/
def hodgeDirac (B : Matrix E V R) : Matrix (V ⊕ E) (V ⊕ E) R :=
  Matrix.fromBlocks 0 Bᵀ B 0

/-- Linear Hodge-Dirac Supertrace Vanishing:
    The supertrace of the discrete Hodge-Dirac operator vanishes identically. -/
theorem superTrace_hodgeDirac (B : Matrix E V R) :
    superTrace (hodgeDirac B) = 0 := by
  dsimp [superTrace, hodgeDirac]
  rw [Matrix.trace_zero, Matrix.trace_zero]
  ring

/-- Hodge-Laplacian Square is a Volume Mode:
    The square of the Hodge-Dirac operator decomposes into node and edge Laplacians. -/
theorem hodgeDirac_sq (B : Matrix E V R) :
    hodgeDirac B * hodgeDirac B = Matrix.fromBlocks (Bᵀ * B) 0 0 (B * Bᵀ) := by
  dsimp [hodgeDirac]
  rw [Matrix.fromBlocks_multiply]
  simp

/-- Hodge-Laplacian Supertrace Exact Cancellation via Cyclicity:
    `superTrace (D²) = Tr(Bᵀ * B) - Tr(B * Bᵀ) = 0` via Mathlib's `trace_mul_comm`. -/
theorem superTrace_hodgeDirac_sq (B : Matrix E V R) :
    superTrace (hodgeDirac B * hodgeDirac B) = 0 := by
  rw [hodgeDirac_sq]
  dsimp [superTrace]
  rw [Matrix.trace_mul_comm Bᵀ B]
  ring

/-- Scale-Dirac Commutation:
    Uniform homotheties strictly commute with the discrete Hodge-Dirac operator:
    `scaleMode σ * hodgeDirac B - hodgeDirac B * scaleMode σ = 0`. -/
theorem scaleMode_hodgeDirac_comm (σ : R) (B : Matrix E V R) :
    scaleMode σ * hodgeDirac B - hodgeDirac B * scaleMode σ = 0 := by
  dsimp [scaleMode, hodgeDirac]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

/-! ### Section 2: The Andreev Particle-Hole Reflection & Nambu-BdG Hamiltonian -/

/-- Fundamental Andreev / Particle-Hole Involution $\tau_1 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$
    on Nambu carrier `Matrix (V ⊕ V) (V ⊕ V) R`. -/
def andreevTau1 (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] :
    Matrix (V ⊕ V) (V ⊕ V) R :=
  Matrix.fromBlocks 0 1 1 0

/-- Involutive property of Andreev particle-hole symmetry: $\tau_1^2 = 1$. -/
theorem andreevTau1_sq (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] :
    (andreevTau1 V R) * (andreevTau1 V R) = 1 := by
  dsimp [andreevTau1]
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_one]

/-- Discrete Bogoliubov-de Gennes (BdG) Hamiltonian with normal generator $H_0$ and pairing $\Delta$:
    $H_{\mathrm{BdG}} = \begin{pmatrix} H_0 & \Delta \\ \Delta^\top & -H_0^\top \end{pmatrix}$. -/
def bdgHamiltonian (H0 Delta : Matrix V V R) : Matrix (V ⊕ V) (V ⊕ V) R :=
  Matrix.fromBlocks H0 Delta Deltaᵀ (-H0ᵀ)

/-- Particle-hole block transposition action under Andreev conjugation:
    $\tau_1 \begin{pmatrix} A & B \\ C & D \end{pmatrix} \tau_1 = \begin{pmatrix} D & C \\ B & A \end{pmatrix}$. -/
theorem andreev_swap (A B C D : Matrix V V R) :
    andreevTau1 V R * Matrix.fromBlocks A B C D * andreevTau1 V R = Matrix.fromBlocks D C B A := by
  dsimp [andreevTau1]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

/-- Unconditional block transposition of the BdG Hamiltonian under Andreev conjugation:
    $\tau_1 H_{\mathrm{BdG}} \tau_1 = \begin{pmatrix} -H_0^\top & \Delta^\top \\ \Delta & H_0 \end{pmatrix}$. -/
theorem andreev_bdg_swap (H0 Delta : Matrix V V R) :
    andreevTau1 V R * bdgHamiltonian H0 Delta * andreevTau1 V R =
      Matrix.fromBlocks (-H0ᵀ) Deltaᵀ Delta H0 := by
  rw [bdgHamiltonian, andreev_swap]

/-- The Fundamental Andreev Particle-Hole Antisymmetry:
    For skew-symmetric pairing $\Delta^\top = -\Delta$,
    $\tau_1 H_{\mathrm{BdG}} \tau_1 = - H_{\mathrm{BdG}}^\top$. -/
theorem andreev_bdg_antisymmetry (H0 Delta : Matrix V V R) (hDelta : Deltaᵀ = -Delta) :
    andreevTau1 V R * bdgHamiltonian H0 Delta * andreevTau1 V R = - (bdgHamiltonian H0 Delta)ᵀ := by
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

/-- Topological Andreev Skew-Pairing Sign Reversal:
    For symmetric normal generator $H_0^\top = H_0$ and skew-symmetric pairing $\Delta^\top = -\Delta$,
    $\tau_1 H_{\mathrm{BdG}} \tau_1 = - H_{\mathrm{BdG}}$. -/
theorem andreev_skew_pairing_reversal (H0 Delta : Matrix V V R) (hH0 : H0ᵀ = H0) (hDelta : Deltaᵀ = -Delta) :
    andreevTau1 V R * bdgHamiltonian H0 Delta * andreevTau1 V R = - bdgHamiltonian H0 Delta := by
  rw [andreev_bdg_antisymmetry H0 Delta hDelta]
  rw [bdgHamiltonian_transpose H0 Delta hH0]

/-! ### Section 3: Inductive Colimit Extension & Invariant Stabilization -/

/-- Trace of block $2 \times 2$ matrix decomposes into the sum of diagonal block traces. -/
theorem trace_fromBlocks {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m R) (B_mat : Matrix m n R) (C_mat : Matrix n m R) (D_mat : Matrix n n R) :
    Matrix.trace (Matrix.fromBlocks A B_mat C_mat D_mat) = Matrix.trace A + Matrix.trace D_mat := by
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type,
             Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]

variable {V_ext : Type u_V} {E_ext : Type u_E}
variable [DecidableEq V_ext] [Fintype V_ext] [DecidableEq E_ext] [Fintype E_ext]

/-- Euler-Poincaré Characteristic additivity under direct sum of graph complexes. -/
theorem eulerPoincare_directSum :
    eulerPoincare (V ⊕ V_ext) (E ⊕ E_ext) R = eulerPoincare V E R + eulerPoincare V_ext E_ext R := by
  dsimp [eulerPoincare]
  rw [Fintype.card_sum, Fintype.card_sum]
  push_cast
  ring

/-- Zero-extension of a graph boundary matrix $B : \mathrm{Matrix}\ E\ V\ R$ with $V_{\mathrm{ext}}$
    isolated nodes and $E_{\mathrm{ext}}$ isolated edges:
    $B_{\mathrm{ext}} = \begin{pmatrix} B & 0 \\ 0 & 0 \end{pmatrix}$. -/
def extendB (B : Matrix E V R) (V_ext E_ext : Type*)
    [DecidableEq V_ext] [Fintype V_ext] [DecidableEq E_ext] [Fintype E_ext] :
    Matrix (E ⊕ E_ext) (V ⊕ V_ext) R :=
  Matrix.fromBlocks B 0 0 0

/-- Node Laplacian under zero extension:
    $B_{\mathrm{ext}}^\top B_{\mathrm{ext}} = \begin{pmatrix} B^\top B & 0 \\ 0 & 0 \end{pmatrix}$. -/
theorem nodeLaplacian_extendB (B : Matrix E V R) :
    (extendB B V_ext E_ext)ᵀ * (extendB B V_ext E_ext) = Matrix.fromBlocks (Bᵀ * B) 0 0 0 := by
  dsimp [extendB]
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp

/-- Edge Laplacian under zero extension:
    $B_{\mathrm{ext}} B_{\mathrm{ext}}^\top = \begin{pmatrix} B B^\top & 0 \\ 0 & 0 \end{pmatrix}$. -/
theorem edgeLaplacian_extendB (B : Matrix E V R) :
    (extendB B V_ext E_ext) * (extendB B V_ext E_ext)ᵀ = Matrix.fromBlocks (B * Bᵀ) 0 0 0 := by
  dsimp [extendB]
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp

/-- Colimit Invariance of trace node Laplacians:
    $\operatorname{Tr}(\Delta_0^{\mathrm{ext}}) = \operatorname{Tr}(\Delta_0)$. -/
theorem trace_nodeLaplacian_extendB (B : Matrix E V R) :
    Matrix.trace ((extendB B V_ext E_ext)ᵀ * (extendB B V_ext E_ext)) = Matrix.trace (Bᵀ * B) := by
  rw [nodeLaplacian_extendB, trace_fromBlocks, Matrix.trace_zero, add_zero]

/-- Colimit Invariance of trace edge Laplacians:
    $\operatorname{Tr}(\Delta_1^{\mathrm{ext}}) = \operatorname{Tr}(\Delta_1)$. -/
theorem trace_edgeLaplacian_extendB (B : Matrix E V R) :
    Matrix.trace ((extendB B V_ext E_ext) * (extendB B V_ext E_ext)ᵀ) = Matrix.trace (B * Bᵀ) := by
  rw [edgeLaplacian_extendB, trace_fromBlocks, Matrix.trace_zero, add_zero]

/-- Supertrace invariance of the colimit Hodge-Dirac square:
    $\operatorname{STr}((D^{\mathrm{ext}})^2) = 0$. -/
theorem superTrace_hodgeDirac_sq_extendB (B : Matrix E V R) :
    superTrace (hodgeDirac (extendB B V_ext E_ext) * hodgeDirac (extendB B V_ext E_ext)) = 0 := by
  exact superTrace_hodgeDirac_sq (extendB B V_ext E_ext)

/-- Colimit extension of the Bogoliubov-de Gennes (BdG) Hamiltonian to $V \oplus V_{\mathrm{ext}}$:
    $H_{\mathrm{BdG}}^{\mathrm{ext}} = H_{\mathrm{BdG}}(H_0 \oplus 0, \Delta \oplus 0)$. -/
def extendBdG (H0 Delta : Matrix V V R) (V_ext : Type*) [DecidableEq V_ext] [Fintype V_ext] :
    Matrix ((V ⊕ V_ext) ⊕ (V ⊕ V_ext)) ((V ⊕ V_ext) ⊕ (V ⊕ V_ext)) R :=
  bdgHamiltonian (Matrix.fromBlocks H0 0 0 0) (Matrix.fromBlocks Delta 0 0 0)

/-- Andreev particle-hole reflection persists under colimit extension:
    $\tau_1 H_{\mathrm{BdG}}^{\mathrm{ext}} \tau_1 = - (H_{\mathrm{BdG}}^{\mathrm{ext}})^\top$. -/
theorem andreev_bdg_extend_antisymmetry (H0 Delta : Matrix V V R) (hDelta : Deltaᵀ = -Delta) :
    andreevTau1 (V ⊕ V_ext) R * extendBdG H0 Delta V_ext * andreevTau1 (V ⊕ V_ext) R =
      - (extendBdG H0 Delta V_ext)ᵀ := by
  apply andreev_bdg_antisymmetry
  rw [Matrix.fromBlocks_transpose, hDelta, Matrix.fromBlocks_neg]
  simp

/-! ### Section 4: Grothendieck AB5 Exact Inductive Tower Chain -/

/-- Iterated vertex carrier type along an inductive extension tower:
    $V_0 = V$, $V_{m+1} = V_m \oplus V_{\mathrm{step}}$. -/
def Vertices (V : Type u_V) (V_step : Type u_V) : ℕ → Type u_V
  | 0 => V
  | m + 1 => Vertices V V_step m ⊕ V_step

/-- Iterated edge carrier type along an inductive extension tower:
    $E_0 = E$, $E_{m+1} = E_m \oplus E_{\mathrm{step}}$. -/
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

/-- Inductive sequence of graph boundary operators along a zero-extension tower chain:
    $B_0 = B$, $B_{m+1} = \operatorname{extendB}(B_m)$. -/
def extendChain (B : Matrix E V R) (V_step : Type u_V) (E_step : Type u_E)
    [DecidableEq V_step] [Fintype V_step] [DecidableEq E_step] [Fintype E_step] :
    (m : ℕ) → Matrix (Edges E E_step m) (Vertices V V_step m) R
  | 0 => B
  | m + 1 => extendB (extendChain B V_step E_step m) V_step E_step

/-- Node Laplacian trace stabilization along the entire inductive sequence chain:
    $\operatorname{Tr}(\Delta_0(G_m)) = \operatorname{Tr}(\Delta_0(G_0))$. -/
theorem trace_nodeLaplacian_extendChain (B : Matrix E V R) :
    (m : ℕ) → Matrix.trace ((extendChain B V_step E_step m)ᵀ * (extendChain B V_step E_step m)) =
      Matrix.trace (Bᵀ * B)
  | 0 => rfl
  | m + 1 => by
    change Matrix.trace ((extendB (extendChain B V_step E_step m) V_step E_step)ᵀ *
      (extendB (extendChain B V_step E_step m) V_step E_step)) = Matrix.trace (Bᵀ * B)
    rw [trace_nodeLaplacian_extendB]
    exact trace_nodeLaplacian_extendChain B m

/-- Edge Laplacian trace stabilization along the entire inductive sequence chain:
    $\operatorname{Tr}(\Delta_1(G_m)) = \operatorname{Tr}(\Delta_1(G_0))$. -/
theorem trace_edgeLaplacian_extendChain (B : Matrix E V R) :
    (m : ℕ) → Matrix.trace ((extendChain B V_step E_step m) * (extendChain B V_step E_step m)ᵀ) =
      Matrix.trace (B * Bᵀ)
  | 0 => rfl
  | m + 1 => by
    change Matrix.trace ((extendB (extendChain B V_step E_step m) V_step E_step) *
      (extendB (extendChain B V_step E_step m) V_step E_step)ᵀ) = Matrix.trace (B * Bᵀ)
    rw [trace_edgeLaplacian_extendB]
    exact trace_edgeLaplacian_extendChain B m

/-- Master Colimit Commutation:
    The colimit Hodge-Dirac operator cubic identity $[D_m, D_m^2] = 0$ holds at every step $m$:
    $D_m (D_m D_m) = (D_m D_m) D_m$. -/
theorem colimit_hodgeDirac_comm (B : Matrix E V R) (m : ℕ) :
    hodgeDirac (extendChain B V_step E_step m) *
      (hodgeDirac (extendChain B V_step E_step m) * hodgeDirac (extendChain B V_step E_step m)) =
    (hodgeDirac (extendChain B V_step E_step m) * hodgeDirac (extendChain B V_step E_step m)) *
      hodgeDirac (extendChain B V_step E_step m) := by
  rw [mul_assoc]

/-! ### Section 5: Master Verification Certificate -/

/-- Master Verification Certificate bundling the Erlangen KAN 3-mode supercarrier triad,
    Nambu-BdG Andreev particle-hole reflection, inductive colimit extension, and Grothendieck
    AB5 invariant stabilization. -/
structure ErlangenGrothendieckAndreevCertificate : Prop where
  supertrace_scale :
    ∀ {V : Type u_V} {E : Type u_E} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      {R : Type u_R} [CommRing R] (σ : R),
      superTrace (scaleMode (V := V) (E := E) σ) = eulerPoincare V E R * σ
  supertrace_dirac :
    ∀ {V : Type u_V} {E : Type u_E} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      {R : Type u_R} [CommRing R] (B : Matrix E V R),
      superTrace (hodgeDirac B) = 0
  hodge_dirac_sq :
    ∀ {V : Type u_V} {E : Type u_E} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      {R : Type u_R} [CommRing R] (B : Matrix E V R),
      hodgeDirac B * hodgeDirac B = Matrix.fromBlocks (Bᵀ * B) 0 0 (B * Bᵀ)
  supertrace_dirac_sq :
    ∀ {V : Type u_V} {E : Type u_E} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      {R : Type u_R} [CommRing R] (B : Matrix E V R),
      superTrace (hodgeDirac B * hodgeDirac B) = 0
  scale_dirac_comm :
    ∀ {V : Type u_V} {E : Type u_E} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      {R : Type u_R} [CommRing R] (σ : R) (B : Matrix E V R),
      scaleMode σ * hodgeDirac B - hodgeDirac B * scaleMode σ = 0
  andreev_tau1_sq :
    ∀ (V : Type u_V) [DecidableEq V] [Fintype V] (R : Type u_R) [CommRing R],
      andreevTau1 V R * andreevTau1 V R = 1
  andreev_bdg_anti :
    ∀ {V : Type u_V} [DecidableEq V] [Fintype V] {R : Type u_R} [CommRing R]
      (H0 Delta : Matrix V V R), Deltaᵀ = -Delta →
      andreevTau1 V R * bdgHamiltonian H0 Delta * andreevTau1 V R = - (bdgHamiltonian H0 Delta)ᵀ
  andreev_skew_reversal :
    ∀ {V : Type u_V} [DecidableEq V] [Fintype V] {R : Type u_R} [CommRing R]
      (H0 Delta : Matrix V V R), H0ᵀ = H0 → Deltaᵀ = -Delta →
      andreevTau1 V R * bdgHamiltonian H0 Delta * andreevTau1 V R = - bdgHamiltonian H0 Delta
  euler_additivity :
    ∀ {V V_ext : Type u_V} {E E_ext : Type u_E} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      [DecidableEq V_ext] [Fintype V_ext] [DecidableEq E_ext] [Fintype E_ext] {R : Type u_R} [CommRing R],
      eulerPoincare (V ⊕ V_ext) (E ⊕ E_ext) R = eulerPoincare V E R + eulerPoincare V_ext E_ext R
  node_laplacian_extend :
    ∀ {V V_ext : Type u_V} {E E_ext : Type u_E} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      [DecidableEq V_ext] [Fintype V_ext] [DecidableEq E_ext] [Fintype E_ext] {R : Type u_R} [CommRing R]
      (B : Matrix E V R),
      (extendB B V_ext E_ext)ᵀ * (extendB B V_ext E_ext) = Matrix.fromBlocks (Bᵀ * B) 0 0 0
  edge_laplacian_extend :
    ∀ {V V_ext : Type u_V} {E E_ext : Type u_E} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      [DecidableEq V_ext] [Fintype V_ext] [DecidableEq E_ext] [Fintype E_ext] {R : Type u_R} [CommRing R]
      (B : Matrix E V R),
      (extendB B V_ext E_ext) * (extendB B V_ext E_ext)ᵀ = Matrix.fromBlocks (B * Bᵀ) 0 0 0
  trace_node_laplacian_extend :
    ∀ {V V_ext : Type u_V} {E E_ext : Type u_E} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      [DecidableEq V_ext] [Fintype V_ext] [DecidableEq E_ext] [Fintype E_ext] {R : Type u_R} [CommRing R]
      (B : Matrix E V R),
      Matrix.trace ((extendB B V_ext E_ext)ᵀ * (extendB B V_ext E_ext)) = Matrix.trace (Bᵀ * B)
  trace_edge_laplacian_extend :
    ∀ {V V_ext : Type u_V} {E E_ext : Type u_E} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      [DecidableEq V_ext] [Fintype V_ext] [DecidableEq E_ext] [Fintype E_ext] {R : Type u_R} [CommRing R]
      (B : Matrix E V R),
      Matrix.trace ((extendB B V_ext E_ext) * (extendB B V_ext E_ext)ᵀ) = Matrix.trace (B * Bᵀ)
  supertrace_hodge_sq_extend :
    ∀ {V V_ext : Type u_V} {E E_ext : Type u_E} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      [DecidableEq V_ext] [Fintype V_ext] [DecidableEq E_ext] [Fintype E_ext] {R : Type u_R} [CommRing R]
      (B : Matrix E V R),
      superTrace (hodgeDirac (extendB B V_ext E_ext) * hodgeDirac (extendB B V_ext E_ext)) = 0
  andreev_bdg_extend_anti :
    ∀ {V V_ext : Type u_V} [DecidableEq V] [Fintype V] [DecidableEq V_ext] [Fintype V_ext] {R : Type u_R} [CommRing R]
      (H0 Delta : Matrix V V R), Deltaᵀ = -Delta →
      andreevTau1 (V ⊕ V_ext) R * extendBdG H0 Delta V_ext * andreevTau1 (V ⊕ V_ext) R =
        - (extendBdG H0 Delta V_ext)ᵀ
  trace_node_laplacian_chain :
    ∀ {V V_step : Type u_V} {E E_step : Type u_E} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      [DecidableEq V_step] [Fintype V_step] [DecidableEq E_step] [Fintype E_step] {R : Type u_R} [CommRing R]
      (B : Matrix E V R) (m : ℕ),
      Matrix.trace ((extendChain B V_step E_step m)ᵀ * (extendChain B V_step E_step m)) =
        Matrix.trace (Bᵀ * B)
  trace_edge_laplacian_chain :
    ∀ {V V_step : Type u_V} {E E_step : Type u_E} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      [DecidableEq V_step] [Fintype V_step] [DecidableEq E_step] [Fintype E_step] {R : Type u_R} [CommRing R]
      (B : Matrix E V R) (m : ℕ),
      Matrix.trace ((extendChain B V_step E_step m) * (extendChain B V_step E_step m)ᵀ) =
        Matrix.trace (B * Bᵀ)
  colimit_hodge_comm :
    ∀ {V V_step : Type u_V} {E E_step : Type u_E} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
      [DecidableEq V_step] [Fintype V_step] [DecidableEq E_step] [Fintype E_step] {R : Type u_R} [CommRing R]
      (B : Matrix E V R) (m : ℕ),
      hodgeDirac (extendChain B V_step E_step m) *
        (hodgeDirac (extendChain B V_step E_step m) * hodgeDirac (extendChain B V_step E_step m)) =
      (hodgeDirac (extendChain B V_step E_step m) * hodgeDirac (extendChain B V_step E_step m)) *
        hodgeDirac (extendChain B V_step E_step m)

/-- Compilation of the master Erlangen-Grothendieck-Andreev Colimit certificate with zero sorry. -/
theorem compile_erlangen_grothendieck_andreev_colimit :
    ErlangenGrothendieckAndreevCertificate where
  supertrace_scale := fun σ => superTrace_scaleMode σ
  supertrace_dirac := fun B => superTrace_hodgeDirac B
  hodge_dirac_sq := fun B => hodgeDirac_sq B
  supertrace_dirac_sq := fun B => superTrace_hodgeDirac_sq B
  scale_dirac_comm := fun σ B => scaleMode_hodgeDirac_comm σ B
  andreev_tau1_sq := andreevTau1_sq
  andreev_bdg_anti := fun H0 Delta hDelta => andreev_bdg_antisymmetry H0 Delta hDelta
  andreev_skew_reversal := fun H0 Delta hH0 hDelta => andreev_skew_pairing_reversal H0 Delta hH0 hDelta
  euler_additivity := eulerPoincare_directSum
  node_laplacian_extend := fun B => nodeLaplacian_extendB B
  edge_laplacian_extend := fun B => edgeLaplacian_extendB B
  trace_node_laplacian_extend := fun B => trace_nodeLaplacian_extendB B
  trace_edge_laplacian_extend := fun B => trace_edgeLaplacian_extendB B
  supertrace_hodge_sq_extend := fun B => superTrace_hodgeDirac_sq_extendB B
  andreev_bdg_extend_anti := fun H0 Delta hDelta => andreev_bdg_extend_antisymmetry H0 Delta hDelta
  trace_node_laplacian_chain := fun B m => trace_nodeLaplacian_extendChain B m
  trace_edge_laplacian_chain := fun B m => trace_edgeLaplacian_extendChain B m
  colimit_hodge_comm := fun B m => colimit_hodgeDirac_comm B m

end Experimental.Sandbox.Synthesis.ErlangenGrothendieckAndreevColimit
