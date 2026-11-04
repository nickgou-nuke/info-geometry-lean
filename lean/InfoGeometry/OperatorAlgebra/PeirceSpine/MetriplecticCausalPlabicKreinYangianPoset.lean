/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.BitVec
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge

/-!
# Metriplectic, Plabic, Krein, and Yangian Causal Matrix Decompositions (`MCP₁`–`MCP₁₀` / Turns 01–17)

This module formalizes the mathematical archetypes, non-commutative ring identities,
concrete matrix theorems, and Socratic elenchus refutations extracted from the 17-turn
dialogue *"Metriplectic and Tensor Decompositions of Causal Matrices"*
(`https://share.gemini.google/hNydhwDbFYmo` / `https://gemini.google.com/share/9666a5a14e0d`):

1. **`MCP₁` (Turns 01–02 — Metriplectic Coincidence, Out/In Gramians & Doubled Block Operators)**:
   In any `[Ring B]`, decomposing a causal operator into symmetric/metric `S` and
   skew/symplectic `K` parts (`C_+ = S + K`, `C_- = S - K`) yields:
   - Out-Gramian `(S + K)(S - K) = S² - K² - [S, K]`,
   - In-Gramian `(S - K)(S + K) = S² - K² + [S, K]`,
   - Normalcy Defect `(S + K)(S - K) - (S - K)(S + K) = -2[S, K]`,
   - Cross-Gramian `(S + K)² = (S² + K²) + {S, K}`,
   - Aporia Idempotency Defect `(S + K)² - (S + K) = (S² + K² - S) + ({S, K} - K)`,
   - Doubled `2 × 2` block operators `metriplecticBlock S K`, `symplecticDilationBlock S K`,
     and `equilibriumFlowRoot S K` satisfying
     `equilibriumFlowRoot(S, K)² = diag((S+K)(S-K), (S-K)(S+K))`,
     unscaled Walsh–Hadamard decoupling `W M(S, K) W = 2 diag(S+K, S-K)`, and exact
     Block-LDU Schur factorizations.
2. **`MCP₂` (Turn 03 — Discrete Gohberg–Krein Hilbert Transform & Non-Commutative Cotlar–Tricomi Identity)**:
   For any off-diagonal pair `(L, U)` with `S_off = L + U` and `H(S_off) = K_A = L - U`,
   `S_off² + K_A² = 2(L² + U²)` and `{S_off, K_A} = 2(L² - U²)`, yielding the
   non-commutative operator Cotlar–Tricomi relation
   `gohbergKreinHilbert (2 L²) (2 U²) = {S_off, K_A}`, together with its Peirce-spine
   realization `L = coneMinus P C`, `U = conePlus P A`.
3. **`MCP₃` (Turns 04–06 — `Cl(1,1)` Para-Kähler Triad, Light-Cone Nullity & Jordan–Wigner Krein Grading)**:
   Explicit `2 × 2` para-Kähler triad `(g = σ_z, K_para = σ_x, ω = ε = σ_x σ_z)`,
   light-cone nullity `(I₂ ± σ_x)ᵀ σ_z (I₂ ± σ_x) = 0`, Krein `J`-self-adjointness
   `σ_z M(s, k)ᵀ σ_z = M(s, k)`, and `4 × 4` 2-qubit Jordan–Wigner Krein-string
   generators `E₁, E₂, Γ₁, Γ₂` satisfying `{E_a, E_b} = 2 δ_{ab} I₄`,
   `{Γ_a, Γ_b} = -2 δ_{ab} I₄`, `{E_a, Γ_b} = 0`, contrasted with the Ungraded Kronecker
   Aporia `[E₁, I₂ ⊗ σ_x] = 0`.
4. **`MCP₄` (Turns 07–10 — Walsh–Hadamard Conjugation Elenchus, XOR-Swizzle Bijectivity & Talaska Schur Identity)**:
   Unscaled Hadamard conjugation on `Cl(1,1)`:
   `H₂ (d_i I₂ + d_p σ_z + d_s σ_x + d_c ε) H₂ = 2 (d_i I₂ + d_s σ_z + d_p σ_x - d_c ε)`
   (refuting the claim that scalar FWHT conjugation generates non-commutative `ε`
   bivectors), exact `BitVec w` XOR-swizzle bank-conflict-free involutive bijections,
   and the `2 × 2` Talaska / Urban-Renewal cycle resolvent identity.
5. **`MCP₅` (Turns 11–12 — `Cl(1,1)` Lorentzian Determinant, Cayley Rotor, Dual Horizons & 3-Point BCFW Assembly)**:
   For traceless `Ω(w_p, w_s, w_c) = w_p σ_z + w_s σ_x + w_c ε`,
   `det(Ω) = w_c² - w_p² - w_s² = f`, `Ω² = -f I₂`, `(I₂ - Ω)(I₂ + Ω) = (1 + f) I₂`,
   `det((1 - f) I₂ + 2 Ω) = (1 + f)²`, the dual horizons `f = ±1`, and `3`-point
   BCFW tree amalgamation plus elementary bridge non-commutativity
   `[B₀₁(z₁), B₁₂(z₂)] = z₁ z₂ E₀₂`.
6. **`MCP₆` (Turn 13 — `Cl(2,2)` Krein–Hamiltonian–Hopf Bifurcation & Jordan Block Coalescence at `f_k = -1`)**:
   On `4 × 4` matrices with `J₄ = diag(1, 1, -1, -1)`, `J₄ Mᵀ J₄ = -M`,
   `[S_semi, N_part] = 0`, `N_part(Δω, g)² = -(Δω² - g²) I₄`, nilpotency
   `N_nil(Δω)² = 0` at `g = Δω`, and the Jordan root chain `N_nil(1) Φ_gen = Ψ_EP`,
   `N_nil(1) Ψ_EP = 0` with null self-norm `Ψ_EPᵀ J₄ Ψ_EP = 0`.
7. **`MCP₇` (Turns 14–15 — Yangian `R`-Matrix, Resonant Rank Collapse, QYBE & Quantum Determinant)**:
   Unitarity defect `R_check(u, η) R_check(-u, η) = (η² - u²) · 1`, resonant rank
   collapse `R(η, η) R(-η, η) = 0`, the Quantum Yang–Baxter Equation (QYBE) for `S₃`
   transposition generators, and the `4 × 4` swap-matrix realization.
8. **`MCP₈` (Turn 16 — Dirac–Krein Zitterbewegung Carrier Decoupling, Secular Trajectory & `ℤ₄` Spin-Monodromy)**:
   Carrier decoupling `[S_semi, J₄] = 0` and `[S_semi, A] = 0` (Aporia 1),
   classical drift vs. trembling decomposition `[M₀, Δω M₀] = 0` and
   `{M₀, Ω² A - Δω M₀} = 0`, exact quadratic secular evolution
   `(I₄ - t N_nil) A (I₄ + t N_nil) = A + 2 Δω t (A B) + 2 Δω² t² N_nil` at `f_k = -1`
   (Aporia 2), and `ℤ₄` spin-monodromy `B_EP² = -I₂`, `B_EP⁴ = I₂` (Aporia 3).
9. **`MCP₉` (Turn 17 — Foldy–Wouthuysen Rapidity Dictionary, Urban-Renewal Flip & Thomas–Wigner Precession)**:
   Rational hyperbolic parameterization `(1 + v²)² - (2v)² = (1 - v²)²`,
   Urban-Renewal orientation sign reversal, re-export of the real analytic rapidity
   bridge `FoldyWouthuysenPlabicRapidityBridge`, and the `4 × 4` Thomas–Wigner boost
   commutator `[K₁, K₂] = 2 (σ_z ⊗ ε) = 2 A`.
10. **`MCP₁₀` (Bidirectional 17-Turn Causal Poset & Non-Commutative Peirce Synthesis)**:
    The 17-turn prerequisite poset (`Turn01`–`Turn17`) and its non-commutative
    Peirce-spine realization.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalPlabicKreinYangianPoset

open scoped Matrix
open InfoGeometry.OperatorAlgebra.PeirceSpine

/-!
### 0. The 10-Stage Macro-Poset (`MCP₁ ≺ MCP₂ ≺ ⋯ ≺ MCP₁₀`)
-/

/-- The 10 macro-stages of the Metriplectic–Plabic–Krein–Yangian causal synthesis (`MCP₁`–`MCP₁₀`). -/
inductive MetriplecticCausalPlabicKreinYangianStage : Type
  | MCP1_MetriplecticCoincidenceAndDoubledBlocks
  | MCP2_GohbergKreinHilbertAndCotlarTricomi
  | MCP3_ParaKahlerTriadAndJordanWignerKreinGrading
  | MCP4_WalshHadamardElenchusAndXorSwizzleSchur
  | MCP5_Cl11LorentzianDetCayleyAndBCFWAssembly
  | MCP6_Cl22KreinHamiltonianHopfAndJordanCrash
  | MCP7_YangianRMatrixQYBEAndResonantCollapse
  | MCP8_DiracKreinZitterbewegungAndSecularTrajectory
  | MCP9_FoldyWouthuysenRapidityAndThomasWignerPrecession
  | MCP10_Bidirectional17TurnPeirceSpineSynthesis
  deriving DecidableEq, Repr

namespace MetriplecticCausalPlabicKreinYangianStage

/-- Integer rank (`0` through `9`) of each stage in `MCP₁ ≺ ⋯ ≺ MCP₁₀`. -/
@[reducible] def rank : MetriplecticCausalPlabicKreinYangianStage → ℕ
  | .MCP1_MetriplecticCoincidenceAndDoubledBlocks          => 0
  | .MCP2_GohbergKreinHilbertAndCotlarTricomi              => 1
  | .MCP3_ParaKahlerTriadAndJordanWignerKreinGrading       => 2
  | .MCP4_WalshHadamardElenchusAndXorSwizzleSchur          => 3
  | .MCP5_Cl11LorentzianDetCayleyAndBCFWAssembly           => 4
  | .MCP6_Cl22KreinHamiltonianHopfAndJordanCrash           => 5
  | .MCP7_YangianRMatrixQYBEAndResonantCollapse            => 6
  | .MCP8_DiracKreinZitterbewegungAndSecularTrajectory     => 7
  | .MCP9_FoldyWouthuysenRapidityAndThomasWignerPrecession => 8
  | .MCP10_Bidirectional17TurnPeirceSpineSynthesis         => 9

/-- Strict causal precedence `s₁ ≺ s₂`. -/
@[reducible] def causalEdge (s₁ s₂ : MetriplecticCausalPlabicKreinYangianStage) : Prop :=
  s₁.rank < s₂.rank

/-- Reflexive-transitive causal order `s₁ ≼ s₂`. -/
@[reducible] def causalLe (s₁ s₂ : MetriplecticCausalPlabicKreinYangianStage) : Prop :=
  s₁.rank ≤ s₂.rank

instance instLT : LT MetriplecticCausalPlabicKreinYangianStage := ⟨causalEdge⟩
instance instLE : LE MetriplecticCausalPlabicKreinYangianStage := ⟨causalLe⟩

instance instLinearOrder : LinearOrder MetriplecticCausalPlabicKreinYangianStage where
  le := causalLe
  lt := causalEdge
  le_refl a := Nat.le_refl a.rank
  le_trans _ _ _ hab hbc := Nat.le_trans hab hbc
  lt_iff_le_not_ge _ _ := Nat.lt_iff_le_and_not_ge
  le_antisymm a b hab hba := by
    cases a <;> cases b <;> first | rfl | cases (Nat.le_antisymm hab hba)
  le_total a b := Nat.le_total a.rank b.rank
  toDecidableLE a b := Nat.decLe a.rank b.rank
  toDecidableLT a b := Nat.decLt a.rank b.rank
  toDecidableEq := inferInstance

theorem mcp_poset_chain_and_irreflexivity :
    (causalEdge .MCP1_MetriplecticCoincidenceAndDoubledBlocks .MCP2_GohbergKreinHilbertAndCotlarTricomi ∧
     causalEdge .MCP2_GohbergKreinHilbertAndCotlarTricomi .MCP3_ParaKahlerTriadAndJordanWignerKreinGrading ∧
     causalEdge .MCP3_ParaKahlerTriadAndJordanWignerKreinGrading .MCP4_WalshHadamardElenchusAndXorSwizzleSchur ∧
     causalEdge .MCP4_WalshHadamardElenchusAndXorSwizzleSchur .MCP5_Cl11LorentzianDetCayleyAndBCFWAssembly ∧
     causalEdge .MCP5_Cl11LorentzianDetCayleyAndBCFWAssembly .MCP6_Cl22KreinHamiltonianHopfAndJordanCrash ∧
     causalEdge .MCP6_Cl22KreinHamiltonianHopfAndJordanCrash .MCP7_YangianRMatrixQYBEAndResonantCollapse ∧
     causalEdge .MCP7_YangianRMatrixQYBEAndResonantCollapse .MCP8_DiracKreinZitterbewegungAndSecularTrajectory ∧
     causalEdge .MCP8_DiracKreinZitterbewegungAndSecularTrajectory .MCP9_FoldyWouthuysenRapidityAndThomasWignerPrecession ∧
     causalEdge .MCP9_FoldyWouthuysenRapidityAndThomasWignerPrecession .MCP10_Bidirectional17TurnPeirceSpineSynthesis) ∧
    (∀ s : MetriplecticCausalPlabicKreinYangianStage, ¬ causalEdge s s) := by
  refine ⟨by decide, ?_⟩
  intro s
  cases s <;> decide

end MetriplecticCausalPlabicKreinYangianStage

/-!
### 1. Stage `MCP₁` (Turns 01–02): Non-Commutative Metriplectic Coincidence, Out/In Gramians, Aporia Defect & Doubled `2 × 2` Block Operators
-/

section StageMCP1

variable {B : Type*} [Ring B]

/-- Concrete noncommutativity witness for the doubled matrix blocks.
The hypothesis excludes the zero ring, where no such witness can exist. -/
def matE01 : Matrix (Fin 2) (Fin 2) B := !![0, (1 : B); 0, 0]

def matE10 : Matrix (Fin 2) (Fin 2) B := !![0, 0; (1 : B), 0]

theorem matrix_units_noncommute [Nontrivial B] :
    matE01 (B := B) * matE10 (B := B) ≠
      matE10 (B := B) * matE01 (B := B) := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) B => M 0 0) h
  simp [matE01, matE10] at h00

/-- The same matrix-unit witness over any nontrivial coefficient ring. -/
theorem matrix_units_noncommute_over (C : Type*) [Ring C] [Nontrivial C] :
    (!![0, (1 : C); 0, 0] : Matrix (Fin 2) (Fin 2) C) * !![0, 0; (1 : C), 0] ≠
      (!![0, 0; (1 : C), 0] : Matrix (Fin 2) (Fin 2) C) * !![0, (1 : C); 0, 0] := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) C => M 0 0) h
  simp at h00

/-- A concrete `3 × 3` matrix-unit witness over the real coefficient carrier. -/
theorem three_matrix_units_noncommute_over (C : Type*) [Ring C] [Nontrivial C] :
    (!![0, (1 : C), 0; 0, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) C) *
        !![0, 0, 0; (1 : C), 0, 0; 0, 0, 0] ≠
      (!![0, 0, 0; (1 : C), 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) C) *
        !![0, (1 : C), 0; 0, 0, 0; 0, 0, 0] := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) C => M 0 0) h
  simp at h00

 /-- Concrete `4 × 4` matrix units over any nontrivial coefficient ring. -/
theorem four_matrix_units_noncommute_over (C : Type*) [Ring C] [Nontrivial C] :
    (!![0, (1 : C), 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0] :
      Matrix (Fin 4) (Fin 4) C) *
        !![0, 0, 0, 0; (1 : C), 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0] ≠
      (!![0, 0, 0, 0; (1 : C), 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0] :
        Matrix (Fin 4) (Fin 4) C) *
        !![0, (1 : C), 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0] := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) C => M 0 0) h
  simp at h00

/-- Forward causal combination `C_+ = S + K` of symmetric/metric `S` and skew/symplectic `K`. -/
def causalForward (S K : B) : B := S + K

/-- Backward (time-reversed / transposed) causal combination `C_- = S - K`. -/
def causalBackward (S K : B) : B := S - K

/-- Out-degree Gramian `G_out(S, K) = (S + K)(S - K) = C Cᵀ` when `Sᵀ = S` and `Kᵀ = -K`. -/
def gramianOut (S K : B) : B := causalForward S K * causalBackward S K

/-- In-degree Gramian `G_in(S, K) = (S - K)(S + K) = Cᵀ C` when `Sᵀ = S` and `Kᵀ = -K`. -/
def gramianIn (S K : B) : B := causalBackward S K * causalForward S K

/-- Cross-Gramian `C² = (S + K)²`. -/
def crossGramian (S K : B) : B := causalForward S K * causalForward S K

/-- Aporia idempotency defect `C² - C = (S + K)² - (S + K)` (Turn 01 Section 4). -/
def aporiaIdempotencyDefect (S K : B) : B := crossGramian S K - causalForward S K

/-- **`MCP₁` Out-Gramian Expansion (`(S + K)(S - K) = S² - K² - [S, K]`):** -/
theorem gramianOut_expand (S K : B) :
    gramianOut S K = S * S - K * K - comm S K := by
  dsimp [gramianOut, causalForward, causalBackward, comm]
  noncomm_ring

/-- **`MCP₁` In-Gramian Expansion (`(S - K)(S + K) = S² - K² + [S, K]`):** -/
theorem gramianIn_expand (S K : B) :
    gramianIn S K = S * S - K * K + comm S K := by
  dsimp [gramianIn, causalForward, causalBackward, comm]
  noncomm_ring

/-- **`MCP₁` Normalcy Defect Identity (`G_out - G_in = -2[S, K]`):**
The failure of a decomposed operator `C = S + K` to be normal is governed by twice
the metriplectic commutator `[S, K]`. -/
theorem normalcyDefect_eq_neg_two_comm (S K : B) :
    gramianOut S K - gramianIn S K = -(comm S K + comm S K) := by
  dsimp [gramianOut, gramianIn, causalForward, causalBackward, comm]
  noncomm_ring

/-- **`MCP₁` Average Gramian Coincidence (`G_out + G_in = 2(S² - K²)`):** -/
theorem gramian_sum_eq_two_diff_sq (S K : B) :
    gramianOut S K + gramianIn S K = (S * S - K * K) + (S * S - K * K) := by
  dsimp [gramianOut, gramianIn, causalForward, causalBackward]
  noncomm_ring

/-- **`MCP₁` Commuting Metriplectic Coincidence (`[S, K] = 0 → G_out = G_in = S² - K²`):** -/
theorem gramian_coincidence_of_comm_eq_zero (S K : B) (h_comm : comm S K = 0) :
    gramianOut S K = S * S - K * K ∧
    gramianIn S K = S * S - K * K ∧
    gramianOut S K = gramianIn S K := by
  have h1 : gramianOut S K = S * S - K * K := by
    rw [gramianOut_expand, h_comm, sub_zero]
  have h2 : gramianIn S K = S * S - K * K := by
    rw [gramianIn_expand, h_comm, add_zero]
  exact ⟨h1, h2, h1.trans h2.symm⟩

/-- **`MCP₁` Cross-Gramian Expansion (`(S + K)² = (S² + K²) + {S, K}`):** -/
theorem crossGramian_expand (S K : B) :
    crossGramian S K = (S * S + K * K) + anticomm S K := by
  dsimp [crossGramian, causalForward, anticomm]
  noncomm_ring

/-- **`MCP₁` Aporia Idempotency Defect Split (`(S + K)² - (S + K) = (S² + K² - S) + ({S, K} - K)`):**
Separates the idempotency defect `C² - C` into its even/symmetric part `S² + K² - S`
and its odd/skew Jordan anticommutator part `{S, K} - K` (Turn 01 Section 4). -/
theorem aporiaIdempotencyDefect_expand (S K : B) :
    aporiaIdempotencyDefect S K = (S * S + K * K - S) + (anticomm S K - K) := by
  dsimp [aporiaIdempotencyDefect, crossGramian, causalForward, anticomm]
  noncomm_ring

/-- **`MCP₁` Star-Ring Parity of the Metriplectic Split (`star S = S`, `star K = -K`):**
In any `[Ring B] [StarRing B]`, if `S` is self-adjoint (`star S = S`) and `K` is
skew-adjoint (`star K = -K`), then:
1. `star (S + K) = S - K`,
2. `star [S, K] = [S, K]` (the commutator of symmetric and skew is self-adjoint!),
3. `star {S, K} = -{S, K}` (the anticommutator of symmetric and skew is skew-adjoint!). -/
theorem metriplectic_star_parity [StarRing B] (S K : B)
    (hS : star S = S) (hK : star K = -K) :
    star (causalForward S K) = causalBackward S K ∧
    star (comm S K) = comm S K ∧
    star (anticomm S K) = -anticomm S K := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [causalForward, causalBackward]
    rw [star_add, hS, hK, sub_eq_add_neg]
  · dsimp [comm]
    rw [star_sub, star_mul, star_mul, hS, hK]
    noncomm_ring
  · dsimp [anticomm]
    rw [star_add, star_mul, star_mul, hS, hK]
    noncomm_ring

/-- Doubled `2 × 2` Metriplectic Block Operator `M(S, K) = !![S, K; K, S]` (Turn 01 Section 3). -/
def metriplecticBlock (S K : B) : Matrix (Fin 2) (Fin 2) B :=
  !![S, K; K, S]

/-- Doubled `2 × 2` Symmetric Hamiltonian-Metric Dilation `H_sym(S, K) = !![S, K; -K, S]` (Turn 02 Section 1.1). -/
def symplecticDilationBlock (S K : B) : Matrix (Fin 2) (Fin 2) B :=
  !![S, K; -K, S]

/-- Doubled `2 × 2` Off-Diagonal Chiral Dirac Block `D(S, K) = !![0, S + K; S - K, 0]` (Turn 01 Section 3). -/
def chiralDiracBlock (S K : B) : Matrix (Fin 2) (Fin 2) B :=
  !![0, causalForward S K; causalBackward S K, 0]

/-- Doubled `2 × 2` Dirac Equilibrium-Flow Root `E(S, K) = !![S, K; -K, -S]` (Turn 02 Section 1.2). -/
def equilibriumFlowRoot (S K : B) : Matrix (Fin 2) (Fin 2) B :=
  !![S, K; -K, -S]

/-- Unscaled `2 × 2` Walsh–Hadamard involution `W = !![1, 1; 1, -1]` over `[Ring B]`. -/
def hadamardBlock : Matrix (Fin 2) (Fin 2) B :=
  !![1, 1; 1, -1]

/-- **`MCP₁` Chiral Dirac Block Square (`D(S, K)² = diag(G_out(S, K), G_in(S, K))`):**
Squaring the off-diagonal chiral Dirac block `!![0, S + K; S - K, 0]` diagonalizes identically
into the Out-Gramian `(S + K)(S - K)` and the In-Gramian `(S - K)(S + K)` on the two sheets! -/
theorem chiralDiracBlock_sq (S K : B) :
    chiralDiracBlock S K * chiralDiracBlock S K =
      !![gramianOut S K, 0; 0, gramianIn S K] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralDiracBlock, gramianOut, gramianIn, causalForward, causalBackward,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- **`MCP₁` Equilibrium-Flow Root Square (`E(S, K)² = !![S² - K², [S, K]; [S, K], S² - K²]`):**
Squaring `E(S, K) = !![S, K; -K, -S]` places the average Gramian `S² - K²` on the diagonal
and the metriplectic commutator `[S, K]` on the off-diagonals (Turn 02 Section 1.2). -/
theorem equilibriumFlowRoot_sq (S K : B) :
    equilibriumFlowRoot S K * equilibriumFlowRoot S K =
      !![S * S - K * K, comm S K; comm S K, S * S - K * K] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [equilibriumFlowRoot, comm, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | rfl | abel

/-- **`MCP₁` Walsh–Hadamard Decoupling of the Metriplectic Block (`W M(S, K) W = 2 diag(S+K, S-K)`):** -/
theorem hadamard_decouples_metriplecticBlock (S K : B) :
    hadamardBlock * metriplecticBlock S K * hadamardBlock =
      !![causalForward S K + causalForward S K, 0;
         0, causalBackward S K + causalBackward S K] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamardBlock, metriplecticBlock, causalForward, causalBackward,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | rfl | abel

/-- **`MCP₁` Exact Block-LDU Schur Factorization of `metriplecticBlock S K`:** -/
theorem metriplecticBlock_schur_ldu (S K S_inv : B)
    (h_right : S * S_inv = 1) (h_left : S_inv * S = 1) :
    (!![1, 0; K * S_inv, 1] : Matrix (Fin 2) (Fin 2) B) *
      !![S, 0; 0, S - K * S_inv * K] *
      !![1, S_inv * K; 0, 1] =
      metriplecticBlock S K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [metriplecticBlock, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [← mul_assoc S S_inv K, h_right, one_mul]
  · rw [mul_assoc K S_inv S, h_left, mul_one]
  · have h1 : K * S_inv * S * (S_inv * K) = K * S_inv * K := by
      rw [mul_assoc (K * S_inv) S (S_inv * K),
          ← mul_assoc S S_inv K, h_right, one_mul]
    rw [h1]
    noncomm_ring

/-- **`MCP₁` Exact Block-LDU Schur Factorization of `symplecticDilationBlock S K`:**
With the positive-definite Schur complement `S + K S⁻¹ K` (Turn 02 Section 2.1). -/
theorem symplecticDilationBlock_schur_ldu (S K S_inv : B)
    (h_right : S * S_inv = 1) (h_left : S_inv * S = 1) :
    (!![1, 0; -(K * S_inv), 1] : Matrix (Fin 2) (Fin 2) B) *
      !![S, 0; 0, S + K * S_inv * K] *
      !![1, S_inv * K; 0, 1] =
      symplecticDilationBlock S K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symplecticDilationBlock, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [← mul_assoc S S_inv K, h_right, one_mul]
  · rw [mul_assoc K S_inv S, h_left, mul_one]
  · have h1 : K * S_inv * S * (S_inv * K) = K * S_inv * K := by
      rw [mul_assoc (K * S_inv) S (S_inv * K),
          ← mul_assoc S S_inv K, h_right, one_mul]
    rw [h1]
    noncomm_ring

/-- Recursive Tensor Tower of `2 × 2` Matrices over an Operator Ring `B` on Doubled Real Krein Space:
- Level `0`: `OpMatTower B 0 = B`
- Level `n + 1`: `OpMatTower B (n + 1) = Matrix (Fin 2) (Fin 2) (OpMatTower B n)`
Representing `M_{2^n}(B) ≅ Cl_{1,1}(ℝ)^{⊗ n} ⊗ B` for multi-scale metriplectic attention
and Head–Tail density-matrix evolution (Turns 01–09). -/
@[reducible]
def OpMatTower (B : Type*) : ℕ → Type _
  | 0 => B
  | n + 1 => Matrix (Fin 2) (Fin 2) (OpMatTower B n)

/-- Every level `n` of the recursive operator tensor tower `OpMatTower B n` is an associative ring. -/
@[reducible]
instance instRingOpMatTower (B : Type*) [Ring B] : ∀ n : ℕ, Ring (OpMatTower B n)
  | 0 => inferInstanceAs (Ring B)
  | n + 1 =>
      letI : Ring (OpMatTower B n) := instRingOpMatTower B n
      inferInstanceAs (Ring (Matrix (Fin 2) (Fin 2) (OpMatTower B n)))

/-- Noncommuting matrix units for the recursive operator-tower carrier. -/
theorem tower_matrix_units_noncommute (B : Type*) [Ring B] (n : ℕ)
    [Nontrivial (OpMatTower B n)] :
    (!![0, (1 : OpMatTower B n); 0, 0] :
      Matrix (Fin 2) (Fin 2) (OpMatTower B n)) * !![0, 0; (1 : OpMatTower B n), 0] ≠
      (!![0, 0; (1 : OpMatTower B n), 0] :
      Matrix (Fin 2) (Fin 2) (OpMatTower B n)) * !![0, (1 : OpMatTower B n); 0, 0] := by
  intro h
  have h00 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) (OpMatTower B n) => M 0 0) h
  simp at h00

/-- Level-`(n + 1)` Krein fundamental symmetry `J_{n+1} = !![1, 0; 0, -1]` on `OpMatTower B (n + 1)`. -/
def towerKreinJ (B : Type*) [Ring B] (n : ℕ) : OpMatTower B (n + 1) :=
  !![(1 : OpMatTower B n), 0; 0, -1]

/-- Level-`(n + 1)` para-complex flip `K_{para, n+1} = !![0, 1; 1, 0]` on `OpMatTower B (n + 1)`. -/
def towerParaK (B : Type*) [Ring B] (n : ℕ) : OpMatTower B (n + 1) :=
  !![(0 : OpMatTower B n), 1; 1, 0]

/-- Level-`(n + 1)` symplectic RoPE bivector `ε_{n+1} = !![0, -1; 1, 0]` on `OpMatTower B (n + 1)`. -/
def towerSympEps (B : Type*) [Ring B] (n : ℕ) : OpMatTower B (n + 1) :=
  !![(0 : OpMatTower B n), -1; 1, 0]

/-- Level-`(n + 1)` Jordan–Wigner Krein-string lift `σ_z ⊗ X = !![X, 0; 0, -X]` of `X : OpMatTower B n`. -/
def towerKreinLift (n : ℕ) (X : OpMatTower B n) : OpMatTower B (n + 1) :=
  !![X, 0; 0, -X]

/-- Level-`(n + 1)` ungraded Kronecker lift `I₂ ⊗ X = !![X, 0; 0, X]` of `X : OpMatTower B n`. -/
def towerUngradedLift (n : ℕ) (X : OpMatTower B n) : OpMatTower B (n + 1) :=
  !![X, 0; 0, X]

/-- Uniform two-sheet matrix identities, independent of the coefficient ring's realization. -/
theorem twoByTwo_paraKahler_jordanWigner (X S K : B) :
    (!![(1 : B), 0; 0, -1] : Matrix (Fin 2) (Fin 2) B) *
        !![(1 : B), 0; 0, -1] = 1 ∧
    (!![(0 : B), 1; 1, 0] : Matrix (Fin 2) (Fin 2) B) *
        !![(0 : B), 1; 1, 0] = 1 ∧
    (!![(0 : B), -1; 1, 0] : Matrix (Fin 2) (Fin 2) B) *
        !![(0 : B), -1; 1, 0] = -1 ∧
    (!![(0 : B), 1; 1, 0] : Matrix (Fin 2) (Fin 2) B) *
        !![(1 : B), 0; 0, -1] = !![(0 : B), -1; 1, 0] ∧
    anticomm (!![(0 : B), 1; 1, 0] : Matrix (Fin 2) (Fin 2) B)
        !![X, 0; 0, -X] = 0 ∧
    anticomm (!![(0 : B), -1; 1, 0] : Matrix (Fin 2) (Fin 2) B)
        !![X, 0; 0, -X] = 0 ∧
    comm (!![(0 : B), 1; 1, 0] : Matrix (Fin 2) (Fin 2) B)
        !![X, 0; 0, X] = 0 ∧
    (!![X, 0; 0, -X] : Matrix (Fin 2) (Fin 2) B) * !![X, 0; 0, -X] =
        !![X * X, 0; 0, X * X] ∧
    chiralDiracBlock S K * chiralDiracBlock S K =
        (!![gramianOut S K, 0; 0, gramianIn S K] : Matrix (Fin 2) (Fin 2) B) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, chiralDiracBlock_sq S K⟩
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [anticomm, comm, Matrix.mul_apply, Fin.sum_univ_two]

/-- **`MCP₁` Recursive Operator Tensor Tower Para-Kähler Triad & Jordan–Wigner Grading Dichotomy:**
At **every** level `n` of the recursive tensor tower `OpMatTower B n` over `[Ring B]`:
1. `towerKreinJ B n`, `towerParaK B n`, and `towerSympEps B n` form a `Cl(1,1)` para-Kähler triad
   (`J² = 1`, `K_para² = 1`, `ε² = -1`, `K_para J = ε`),
2. The Jordan–Wigner Krein-string lift `towerKreinLift n X = !![X, 0; 0, -X]` **anticommutes**
   with both `towerParaK B n` (`{K_para, σ_z ⊗ X} = 0`) and `towerSympEps B n` (`{ε, σ_z ⊗ X} = 0`),
3. By contrast, the ungraded Kronecker lift `towerUngradedLift n X = !![X, 0; 0, X]` **commutes**
   with `towerParaK B n` (`[K_para, I₂ ⊗ X] = 0`),
4. At every level `n`, `metriplecticBlock S K`, `chiralDiracBlock S K`, and Head–Tail density
   matrices `!![ρ_HH, ρ_HT; ρ_TH, ρ_TT]` inherit Walsh–Hadamard decoupling, Out/In Gramian
   diagonalization, and exact Block-LDU Schur reduction! -/
theorem tower_paraKahler_and_jordanWigner_lift (n : ℕ) (X S K : OpMatTower B n) :
    towerKreinJ B n * towerKreinJ B n = (1 : OpMatTower B (n + 1)) ∧
    towerParaK B n * towerParaK B n = (1 : OpMatTower B (n + 1)) ∧
    towerSympEps B n * towerSympEps B n = -(1 : OpMatTower B (n + 1)) ∧
    towerParaK B n * towerKreinJ B n = towerSympEps B n ∧
    anticomm (towerParaK B n) (towerKreinLift n X) = (0 : OpMatTower B (n + 1)) ∧
    anticomm (towerSympEps B n) (towerKreinLift n X) = (0 : OpMatTower B (n + 1)) ∧
    comm (towerParaK B n) (towerUngradedLift n X) = (0 : OpMatTower B (n + 1)) ∧
    towerKreinLift n X * towerKreinLift n X = towerUngradedLift n (X * X) ∧
    chiralDiracBlock S K * chiralDiracBlock S K =
      (!![gramianOut S K, 0; 0, gramianIn S K] : OpMatTower B (n + 1)) := by
  exact twoByTwo_paraKahler_jordanWigner (B := OpMatTower B n) X S K

end StageMCP1

/-!
### 2. Stage `MCP₂` (Turn 03): Discrete Gohberg–Krein Hilbert Transform & Non-Commutative Matrix Cotlar–Tricomi Identity
-/

section StageMCP2

variable {B : Type*} [Ring B]

/-- Symmetric off-diagonal sum `S_off(L, U) = L + U` of lower (`L`) and upper (`U`) triangular/Peirce parts. -/
def offDiagSym (L U : B) : B := L + U

/-- Discrete Gohberg–Krein Hilbert transform `H(L, U) = L - U` flipping the sign of the upper sector (`U`)
relative to the lower sector (`L`) (Turn 03 Section 1). -/
def gohbergKreinHilbert (L U : B) : B := L - U

/-- **`MCP₂` Bi-Directional Kramers–Kronig Reconstruction (`S_off ± H(S_off)`):**
Adding and subtracting the off-diagonal symmetric part `L + U` and its Hilbert transform `L - U`
reconstructs `2 L` (causal lower cone) and `2 U` (acausal upper cone). -/
theorem kramers_kronig_sector_reconstruction (L U : B) :
    offDiagSym L U + gohbergKreinHilbert L U = L + L ∧
    offDiagSym L U - gohbergKreinHilbert L U = U + U ∧
    gohbergKreinHilbert L (-U) = offDiagSym L U := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (dsimp [offDiagSym, gohbergKreinHilbert]; noncomm_ring)

/-- **`MCP₂` Non-Commutative Cotlar–Tricomi Sum of Squares (`S_off² + K_A² = 2(L² + U²)`):**
All mixed products `L U` and `U L` cancel out of the quadratic sum `S_off² + H(S_off)²`! -/
theorem cotlarTricomi_sum_sq (L U : B) :
    offDiagSym L U * offDiagSym L U + gohbergKreinHilbert L U * gohbergKreinHilbert L U =
      (L * L + L * L) + (U * U + U * U) := by
  dsimp [offDiagSym, gohbergKreinHilbert]
  noncomm_ring

/-- **`MCP₂` Non-Commutative Cotlar–Tricomi Anticommutator (`{S_off, K_A} = 2(L² - U²)`):**
All mixed products `L U` and `U L` also cancel out of the anticommutator `{S_off, H(S_off)}`! -/
theorem cotlarTricomi_anticomm (L U : B) :
    anticomm (offDiagSym L U) (gohbergKreinHilbert L U) =
      (L * L + L * L) - (U * U + U * U) := by
  dsimp [anticomm, offDiagSym, gohbergKreinHilbert]
  noncomm_ring

/-- **`MCP₂` Universal Non-Commutative Cotlar–Tricomi Identity (`H(S_off² + K_A²) = {S_off, K_A}`):**
Because `S_off² + K_A²` decomposes into lower-square `2 L²` plus upper-square `2 U²`, applying
the Gohberg–Krein sign transform `gohbergKreinHilbert (2 L²) (2 U²)` yields `{S_off, K_A}`
identically in any non-commutative ring `[Ring B]` (Turn 03 Section 3). -/
theorem cotlarTricomi_hilbert_identity (L U : B) :
    gohbergKreinHilbert (L * L + L * L) (U * U + U * U) =
      anticomm (offDiagSym L U) (gohbergKreinHilbert L U) := by
  dsimp [gohbergKreinHilbert, anticomm, offDiagSym]
  noncomm_ring

/-- **`MCP₂` Gohberg–Krein Commutator Anomaly (`[S_off, K_A] = 2[U, L]`):** -/
theorem gohbergKrein_commutator_eq_two_comm (L U : B) :
    comm (offDiagSym L U) (gohbergKreinHilbert L U) =
      comm U L + comm U L := by
  dsimp [comm, offDiagSym, gohbergKreinHilbert]
  noncomm_ring

/-- **`MCP₂` Peirce-Spine Realization of the Gohberg–Krein Transform (`L = N₋`, `U = N₊`):**
On the two-sheeted Peirce spine (`P² = P`), setting `L = coneMinus P C` and `U = conePlus P A`
identifies `offDiagSym = Φ`, `gohbergKreinHilbert = -J`, annihilates the quadratic diagonal
leakage `L² = U² = 0` so `Φ² + (-J)² = 0` and `{Φ, -J} = 0`, and evaluates `[Φ, -J] = 2 Σ`. -/
theorem peirce_gohbergKrein_cotlarTricomi {P : B} (hP : P * P = P) (A C : B) :
    offDiagSym (coneMinus P C) (conePlus P A) = genPhi P A C ∧
    gohbergKreinHilbert (coneMinus P C) (conePlus P A) = -genJ P A C ∧
    offDiagSym (coneMinus P C) (conePlus P A) * offDiagSym (coneMinus P C) (conePlus P A) +
      gohbergKreinHilbert (coneMinus P C) (conePlus P A) *
        gohbergKreinHilbert (coneMinus P C) (conePlus P A) = 0 ∧
    anticomm (offDiagSym (coneMinus P C) (conePlus P A))
      (gohbergKreinHilbert (coneMinus P C) (conePlus P A)) = 0 ∧
    comm (offDiagSym (coneMinus P C) (conePlus P A))
      (gohbergKreinHilbert (coneMinus P C) (conePlus P A)) = (2 : ℤ) • genSig P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (dsimp [offDiagSym, gohbergKreinHilbert]; peirce_nf hP)

/-- **`MCP₂` Turn 03 Strict Lower-Triangular Nilpotency & Non-Normalcy Obstruction:**
Every strictly lower-triangular `2 × 2` causal matrix `L(a) = !![0, 0; a, 0]` over `[CommRing R]`
satisfies `L(a)² = 0` and `L(a) L(a)ᵀ - L(a)ᵀ L(a) = !![-a², 0; 0, a²]`, so `L(a)` cannot be
normal unless `a² = 0` (Turn 03 Section 4). -/
theorem strictLower2_nilpotent_and_nonNormal {R : Type*} [CommRing R] (a : R) :
    (!![0, 0; a, 0] : Matrix (Fin 2) (Fin 2) R) * !![0, 0; a, 0] = 0 ∧
    (!![0, 0; a, 0] : Matrix (Fin 2) (Fin 2) R) * (!![0, 0; a, 0] : Matrix (Fin 2) (Fin 2) R)ᵀ -
      (!![0, 0; a, 0] : Matrix (Fin 2) (Fin 2) R)ᵀ * !![0, 0; a, 0] =
      !![-(a ^ 2), 0; 0, a ^ 2] := by
  refine ⟨?_, ?_⟩ <;>
    { ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.vecMul,
          Fin.sum_univ_two] <;>
        ring }

end StageMCP2

/-!
### 3. Stage `MCP₃` (Turns 04–06): `Cl(1,1)` Para-Kähler Triad, Light-Cone Nullity & `4 × 4` Jordan–Wigner Krein Grading vs. Ungraded Kronecker Aporia
-/

section StageMCP3

variable {R : Type*} [CommRing R]

/-- `Cl(1,1)` Krein fundamental symmetry / split pseudo-Riemannian metric `g = J = σ_z = !![1, 0; 0, -1]`. -/
def sigmaZ : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; 0, -1]

/-- `Cl(1,1)` para-complex structure `K_para = σ_x = !![0, 1; 1, 0]`. -/
def sigmaX : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; 1, 0]

/-- `Cl(1,1)` symplectic form / Levi-Civita bivector `ω = ε = σ_x σ_z = !![0, -1; 1, 0]`. -/
def epsSymp : Matrix (Fin 2) (Fin 2) R :=
  !![0, -1; 1, 0]

/-- Unscaled forward light-cone projector `2 Π_+ = I₂ + σ_x = !![1, 1; 1, 1]`. -/
def nullProjPlus : Matrix (Fin 2) (Fin 2) R :=
  1 + sigmaX

/-- Unscaled backward light-cone projector `2 Π_- = I₂ - σ_x = !![1, -1; -1, 1]`. -/
def nullProjMinus : Matrix (Fin 2) (Fin 2) R :=
  1 - sigmaX

/-- **`MCP₃` Para-Kähler Compatibility Triad (`g = σ_z`, `K_para = σ_x`, `ω = ε`):**
Establishes all compatibility equations of Turn 05 Section 1:
`σ_z² = I₂`, `σ_x² = I₂`, `ε² = -I₂`, `σ_x σ_z = ε`, `σ_z σ_x = -ε`,
`σ_xᵀ σ_z σ_x = -σ_z` (para-isometry sign reversal), and `σ_xᵀ σ_z = ε`. -/
theorem paraKahler_triad_identities :
    (sigmaZ : Matrix (Fin 2) (Fin 2) R) * sigmaZ = 1 ∧
    (sigmaX : Matrix (Fin 2) (Fin 2) R) * sigmaX = 1 ∧
    (epsSymp : Matrix (Fin 2) (Fin 2) R) * epsSymp = -1 ∧
    (sigmaX : Matrix (Fin 2) (Fin 2) R) * sigmaZ = epsSymp ∧
    (sigmaZ : Matrix (Fin 2) (Fin 2) R) * sigmaX = -epsSymp ∧
    (sigmaX : Matrix (Fin 2) (Fin 2) R) * sigmaZ + sigmaZ * sigmaX = 0 ∧
    (sigmaX : Matrix (Fin 2) (Fin 2) R)ᵀ * sigmaZ * sigmaX = -sigmaZ ∧
    (epsSymp : Matrix (Fin 2) (Fin 2) R)ᵀ * sigmaZ * epsSymp = -sigmaZ ∧
    (sigmaX : Matrix (Fin 2) (Fin 2) R)ᵀ * sigmaZ = epsSymp := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    { ext i j
      fin_cases i <;> fin_cases j <;>
        simp [sigmaZ, sigmaX, epsSymp, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two] }

/-- **`MCP₃` Turn 02 RoPE Symplectic Generator Commutation Dichotomy:**
The `SO(2)` RoPE rotation generator `ε = !![0, -1; 1, 0]` commutes with the elliptic sector
`{I₂, ε}` and strictly anticommutes with the hyperbolic boost/reflection sector `{σ_z, σ_x}`,
while `2 × 2` planar rotations `R(c, s) = c I₂ + s ε` compose additively (`R(c₁, s₁) R(c₂, s₂) = R(c₁c₂ - s₁s₂, c₁s₂ + s₁c₂)`). -/
theorem rope_pauli_commutation_and_cocycle (c1 s1 c2 s2 : R) :
    comm (epsSymp : Matrix (Fin 2) (Fin 2) R) 1 = 0 ∧
    comm (epsSymp : Matrix (Fin 2) (Fin 2) R) epsSymp = 0 ∧
    anticomm (epsSymp : Matrix (Fin 2) (Fin 2) R) sigmaZ = 0 ∧
    anticomm (epsSymp : Matrix (Fin 2) (Fin 2) R) sigmaX = 0 ∧
    (c1 • (1 : Matrix (Fin 2) (Fin 2) R) + s1 • epsSymp) *
      (c2 • (1 : Matrix (Fin 2) (Fin 2) R) + s2 • epsSymp) =
      (c1 * c2 - s1 * s2) • (1 : Matrix (Fin 2) (Fin 2) R) +
        (c1 * s2 + s1 * c2) • epsSymp := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    { ext i j
      fin_cases i <;> fin_cases j <;>
        simp [sigmaZ, sigmaX, epsSymp, comm, anticomm,
          Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two] <;>
        ring }

/-- **`MCP₃` Light-Cone Nullity and Non-Degenerate Cross-Pairing (Turn 05 Section 2):**
Both eigenspaces `2 Π_± = I₂ ± σ_x` of the para-complex involution `σ_x` are strictly
isotropic (`(2 Π_±)ᵀ σ_z (2 Π_±) = 0`), while their cross-pairing is non-degenerate:
`(2 Π_+)ᵀ σ_z (2 Π_-) = 2(σ_z + ε)`. -/
theorem lightCone_nullity_and_cross_pairing :
    (nullProjPlus : Matrix (Fin 2) (Fin 2) R) * nullProjPlus = (2 : R) • nullProjPlus ∧
    (nullProjMinus : Matrix (Fin 2) (Fin 2) R) * nullProjMinus = (2 : R) • nullProjMinus ∧
    (nullProjPlus : Matrix (Fin 2) (Fin 2) R) * nullProjMinus = 0 ∧
    (nullProjPlus : Matrix (Fin 2) (Fin 2) R)ᵀ * sigmaZ * nullProjPlus = 0 ∧
    (nullProjMinus : Matrix (Fin 2) (Fin 2) R)ᵀ * sigmaZ * nullProjMinus = 0 ∧
    (nullProjPlus : Matrix (Fin 2) (Fin 2) R)ᵀ * sigmaZ * nullProjMinus =
      (2 : R) • (sigmaZ + epsSymp) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    { ext i j
      fin_cases i <;> fin_cases j <;>
        simp [nullProjPlus, nullProjMinus, sigmaZ, sigmaX, epsSymp,
          Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply, Fin.sum_univ_two] <;>
        ring }

/-- **`MCP₃` Krein `J`-Self-Adjointness of the Metriplectic Block (`σ_z M(s, k)ᵀ σ_z = M(s, -k)`):**
For a `2 × 2` block `!![s, k; k, s]` where `s` is symmetric and `k` is skew-symmetric (`kᵀ = -k`),
the Krein adjoint `J Mᵀ J` restores `+k` in the off-diagonal slots (Turn 04 Section 2). -/
theorem krein_self_adjoint_metriplectic_2x2 (s k : R) :
    sigmaZ * (!![s, k; -k, s] : Matrix (Fin 2) (Fin 2) R)ᵀ * sigmaZ =
      !![s, k; -k, s] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaZ, Matrix.mul_apply, Matrix.transpose_apply,
      dotProduct, Matrix.vecMul, Fin.sum_univ_two]

/-- **`MCP₃` Turn 05–06 Skew Pfaffian Determinant & Witt CAR Nilpotent Ladder (`w_± = σ_x ± ε`):**
1. Every `2 × 2` skew-symmetric matrix `!![0, k; -k, 0]` has determinant `k²` (Pfaffian square).
2. In `Cl(1,1)`, the unscaled Witt fermionic ladder operators `w_+ = σ_x + ε = !![0, 0; 2, 0]`
   and `w_- = σ_x - ε = !![0, 2; 0, 0]` are nilpotent (`w_+² = w_-² = 0`) and satisfy the
   Canonical Anticommutation Relation `{w_+, w_-} = 4 I₂` and commutator `[w_+, w_-] = -4 σ_z`. -/
theorem pfaffian_and_witt_car_ladder (k : R) :
    (!![0, k; -k, 0] : Matrix (Fin 2) (Fin 2) R).det = k ^ 2 ∧
    ((sigmaX : Matrix (Fin 2) (Fin 2) R) + epsSymp) * (sigmaX + epsSymp) = 0 ∧
    ((sigmaX : Matrix (Fin 2) (Fin 2) R) - epsSymp) * (sigmaX - epsSymp) = 0 ∧
    anticomm ((sigmaX : Matrix (Fin 2) (Fin 2) R) + epsSymp) (sigmaX - epsSymp) = (4 : R) • 1 ∧
    comm ((sigmaX : Matrix (Fin 2) (Fin 2) R) + epsSymp) (sigmaX - epsSymp) = -(4 : R) • sigmaZ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Matrix.det_fin_two]; ring
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sigmaZ, sigmaX, epsSymp, anticomm, comm,
        Matrix.mul_apply, Fin.sum_univ_two] <;>
      ring

/-- `4 × 4` 2-qubit Jordan–Wigner positive generator `E₁ = σ_x ⊗ I₂` (`E₁² = +I₄`). -/
def jwE1 : Matrix (Fin 4) (Fin 4) R :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     1, 0, 0, 0;
     0, 1, 0, 0]

/-- `4 × 4` 2-qubit Jordan–Wigner Krein-string positive generator `E₂ = σ_z ⊗ σ_x` (`E₂² = +I₄`). -/
def jwE2 : Matrix (Fin 4) (Fin 4) R :=
  !![0, 1, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, -1;
     0, 0, -1, 0]

/-- `4 × 4` 2-qubit Jordan–Wigner negative generator `Γ₁ = ε ⊗ I₂` (`Γ₁² = -I₄`). -/
def jwGamma1 : Matrix (Fin 4) (Fin 4) R :=
  !![0, 0, -1, 0;
     0, 0, 0, -1;
     1, 0, 0, 0;
     0, 1, 0, 0]

/-- `4 × 4` 2-qubit Jordan–Wigner Krein-string negative generator `Γ₂ = σ_z ⊗ ε` (`Γ₂² = -I₄`). -/
def jwGamma2 : Matrix (Fin 4) (Fin 4) R :=
  !![0, -1, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, -1, 0]

/-- Naive ungraded Kronecker generator `e₂_naive = I₂ ⊗ σ_x` (Turn 06 Section 1). -/
def naiveUngradedE2 : Matrix (Fin 4) (Fin 4) R :=
  !![0, 1, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]

/-- **`MCP₃` `Cl(2,2)` Jordan–Wigner Krein-String Generator Squares (Turn 06 Section 2):**
`E₁² = +I₄`, `E₂² = +I₄`, `Γ₁² = -I₄`, `Γ₂² = -I₄`. -/
theorem jordanWigner_cl22_squares :
    (jwE1 : Matrix (Fin 4) (Fin 4) R) * jwE1 = 1 ∧
    (jwE2 : Matrix (Fin 4) (Fin 4) R) * jwE2 = 1 ∧
    (jwGamma1 : Matrix (Fin 4) (Fin 4) R) * jwGamma1 = -1 ∧
    (jwGamma2 : Matrix (Fin 4) (Fin 4) R) * jwGamma2 = -1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    { ext i j
      fin_cases i <;> fin_cases j <;>
        simp [jwE1, jwE2, jwGamma1, jwGamma2,
          Matrix.mul_apply, Fin.sum_univ_four] }

/-- **`MCP₃` `Cl(2,2)` Jordan–Wigner Krein-String Pairwise Anticommutation (Turn 06 Section 2):**
With the Krein `σ_z` grading string attached to site 2, the four `4 × 4` generators
`E₁, E₂, Γ₁, Γ₂` pairwise anticommute (`{E₁, E₂} = {Γ₁, Γ₂} = {E_a, Γ_b} = 0`). -/
theorem jordanWigner_cl22_anticomm :
    anticomm (jwE1 : Matrix (Fin 4) (Fin 4) R) jwE2 = 0 ∧
    anticomm (jwGamma1 : Matrix (Fin 4) (Fin 4) R) jwGamma2 = 0 ∧
    anticomm (jwE1 : Matrix (Fin 4) (Fin 4) R) jwGamma1 = 0 ∧
    anticomm (jwE1 : Matrix (Fin 4) (Fin 4) R) jwGamma2 = 0 ∧
    anticomm (jwE2 : Matrix (Fin 4) (Fin 4) R) jwGamma1 = 0 ∧
    anticomm (jwE2 : Matrix (Fin 4) (Fin 4) R) jwGamma2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    { ext i j
      simp only [anticomm, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply, Fin.sum_univ_four]
      fin_cases i <;> fin_cases j <;>
        simp [jwE1, jwE2, jwGamma1, jwGamma2] }

/-- **`MCP₃` `Cl(2,2)` Jordan–Wigner Krein-String Anticommutation Theorem (Turn 06 Section 2):** -/
theorem jordanWigner_cl22_relations :
    (jwE1 : Matrix (Fin 4) (Fin 4) R) * jwE1 = 1 ∧
    (jwE2 : Matrix (Fin 4) (Fin 4) R) * jwE2 = 1 ∧
    (jwGamma1 : Matrix (Fin 4) (Fin 4) R) * jwGamma1 = -1 ∧
    (jwGamma2 : Matrix (Fin 4) (Fin 4) R) * jwGamma2 = -1 ∧
    (jwE1 : Matrix (Fin 4) (Fin 4) R) * jwE2 + jwE2 * jwE1 = 0 ∧
    anticomm (jwGamma1 : Matrix (Fin 4) (Fin 4) R) jwGamma2 = 0 ∧
    anticomm (jwE1 : Matrix (Fin 4) (Fin 4) R) jwGamma1 = 0 ∧
    anticomm (jwE1 : Matrix (Fin 4) (Fin 4) R) jwGamma2 = 0 ∧
    anticomm (jwE2 : Matrix (Fin 4) (Fin 4) R) jwGamma1 = 0 ∧
    anticomm (jwE2 : Matrix (Fin 4) (Fin 4) R) jwGamma2 = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := jordanWigner_cl22_squares (R := R)
  obtain ⟨h5, h6, h7, h8, h9, h10⟩ := jordanWigner_cl22_anticomm (R := R)
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- **`MCP₃` Isotropic Norm Preservation of Graded Jordan–Wigner Vectors vs. Ungraded Kronecker Aporia (Turn 06 Section 1–2):**
1. Any linear combination `c₁ E₁ + c₂ E₂` of the Krein-graded generators squares to the scalar
   quadratic form `(c₁² + c₂²) I₄`.
2. By contrast, the ungraded Kronecker generator `naiveUngradedE2 = I₂ ⊗ σ_x` **commutes** with
   `E₁ = σ_x ⊗ I₂`, leaving the non-scalar cross-term defect `(E₁ + e₂_naive)² - 2 I₄ = 2 (σ_x ⊗ σ_x)`. -/
theorem jordanWigner_isotropic_norm_vs_ungraded_aporia (c1 c2 : R) :
    (c1 • (jwE1 : Matrix (Fin 4) (Fin 4) R) + c2 • jwE2) *
      (c1 • jwE1 + c2 • jwE2) = (c1 ^ 2 + c2 ^ 2) • 1 ∧
    comm (jwE1 : Matrix (Fin 4) (Fin 4) R) naiveUngradedE2 = 0 ∧
    ((jwE1 : Matrix (Fin 4) (Fin 4) R) + naiveUngradedE2) * (jwE1 + naiveUngradedE2) -
      (2 : R) • 1 = (2 : R) • (jwE1 * naiveUngradedE2) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    { ext i j
      fin_cases i <;> fin_cases j <;>
        simp [jwE1, jwE2, naiveUngradedE2, comm,
          Matrix.mul_apply, Fin.sum_univ_four] <;>
        ring }

end StageMCP3

/-!
### 4. Stage `MCP₄` (Turns 07–10): Walsh–Hadamard Conjugation Elenchus, XOR-Swizzle Bank-Freedom & Talaska / Urban-Renewal Schur Identity
-/

section StageMCP4

variable {R : Type*} [CommRing R]

/-- General `Cl(1,1)` 4-component multivector block
`b(d_i, d_p, d_s, d_c) = d_i I₂ + d_p σ_z + d_s σ_x + d_c ε = !![d_i + d_p, d_s - d_c; d_s + d_c, d_i - d_p]`. -/
def cl11Elem (di dp ds dc : R) : Matrix (Fin 2) (Fin 2) R :=
  !![di + dp, ds - dc;
     ds + dc, di - dp]

/-- Unscaled `2 × 2` Walsh–Hadamard matrix `H₂ = σ_z + σ_x = !![1, 1; 1, -1]`. -/
def walshHadamard2 : Matrix (Fin 2) (Fin 2) R :=
  !![1, 1; 1, -1]

/-- **`MCP₄` Turn 10 Socratic Elenchus 1 (Walsh–Hadamard Conjugation on `Cl(1,1)`):**
Conjugating a general `Cl(1,1)` element `b(d_i, d_p, d_s, d_c)` by the unscaled
Walsh–Hadamard matrix `H₂` (`H₂² = 2 I₂`) swaps the polar (`σ_z`) and symmetric (`σ_x`)
weights and negates the causal bivector (`ε`) weight:
`H₂ b(d_i, d_p, d_s, d_c) H₂ = 2 b(d_i, d_s, d_p, -d_c)`.
In particular, when `d_c = 0` (as in any diagonal matrix `b(d_i, d_p, 0, 0)`),
`H₂ Diag(w) H₂ = 2 b(d_i, 0, d_p, 0)` has **zero** causal bivector component (`d_c = 0`),
is strictly symmetric, and commutes for all weight vectors! -/
theorem walshHadamard_conjugation_elenchus (di dp ds dc w1 w2 v1 v2 : R) :
    (walshHadamard2 : Matrix (Fin 2) (Fin 2) R) * walshHadamard2 = (2 : R) • 1 ∧
    walshHadamard2 * cl11Elem di dp ds dc * walshHadamard2 =
      (2 : R) • cl11Elem di ds dp (-dc) ∧
    (walshHadamard2 * (!![w1, 0; 0, w2] : Matrix (Fin 2) (Fin 2) R) * walshHadamard2)ᵀ =
      walshHadamard2 * !![w1, 0; 0, w2] * walshHadamard2 ∧
    comm (walshHadamard2 * (!![w1, 0; 0, w2] : Matrix (Fin 2) (Fin 2) R) * walshHadamard2)
         (walshHadamard2 * !![v1, 0; 0, v2] * walshHadamard2) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    { ext i j
      fin_cases i <;> fin_cases j <;>
        simp [walshHadamard2, cl11Elem, comm,
          Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two] <;>
        ring }

/-- **`MCP₄` Turns 07–09 Butterfly Bit-Flip Braiding, Scale-Trapping & Krein-Boost Norm Blow-Up:**
1. Moving the permutation `σ_x` past a diagonal matrix `diag(d₀, d₁)` braids its entries:
   `σ_x diag(d₀, d₁) = diag(d₁, d₀) σ_x`.
2. A hyperbolic Krein boost `B(c, s) = c I₂ + s σ_x` preserves the indefinite metric `σ_z`
   up to `c² - s²` (`B(c, s)ᵀ σ_z B(c, s) = (c² - s²) σ_z`), whereas its Euclidean Frobenius
   norm `B(c, s)ᵀ B(c, s)` has diagonal `c² + s²` (Turn 09 Section 1.2). -/
theorem butterfly_braiding_and_krein_boost_norm (d0 d1 c s : R) :
    (sigmaX : Matrix (Fin 2) (Fin 2) R) * !![d0, 0; 0, d1] =
      !![d1, 0; 0, d0] * sigmaX ∧
    (!![c, s; s, c] : Matrix (Fin 2) (Fin 2) R)ᵀ * sigmaZ * !![c, s; s, c] =
      (c ^ 2 - s ^ 2) • sigmaZ ∧
    (!![c, s; s, c] : Matrix (Fin 2) (Fin 2) R)ᵀ * !![c, s; s, c] =
      (c ^ 2 + s ^ 2) • 1 + (2 * c * s) • sigmaX := by
  refine ⟨?_, ?_, ?_⟩ <;>
    { ext i j
      fin_cases i <;> fin_cases j <;>
        simp [sigmaZ, sigmaX, Matrix.mul_apply,
          Matrix.transpose_apply, Fin.sum_univ_two] <;>
        ring }

/-- SRAM XOR-Swizzle Bank Function `b_phys(r, c) = c ^^^ r` on `w`-bit addresses (Turn 09 Section 2). -/
def sramXorSwizzle (w : ℕ) (r c : BitVec w) : BitVec w :=
  c ^^^ r

/-- **`MCP₄` Turn 09 SRAM XOR-Swizzle Bank-Freedom Theorem:**
For any bit-width `w`, the hardware XOR-swizzle `b(r, c) = c ^^^ r`:
1. Is a strict self-inverse involution in the column index for every fixed row `r`,
2. Is injective (and hence bijective) across columns `c` for any fixed row `r` (zero row-access bank conflicts),
3. Is injective (and hence bijective) across rows `r` for any fixed column `c` (zero column-access bank conflicts). -/
theorem sramXorSwizzle_involution_and_bijective (w : ℕ) (r c c1 c2 r1 r2 : BitVec w) :
    sramXorSwizzle w r (sramXorSwizzle w r c) = c ∧
    (sramXorSwizzle w r c1 = sramXorSwizzle w r c2 ↔ c1 = c2) ∧
    (sramXorSwizzle w r1 c = sramXorSwizzle w r2 c ↔ r1 = r2) ∧
    Function.Bijective (sramXorSwizzle w r) := by
  have h_inv : ∀ x : BitVec w, sramXorSwizzle w r (sramXorSwizzle w r x) = x := by
    intro x
    dsimp [sramXorSwizzle]
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  refine ⟨h_inv c, ?_, ?_, ?_⟩
  · constructor
    · intro h
      have h2 := congrArg (sramXorSwizzle w r) h
      rwa [h_inv, h_inv] at h2
    · intro h; rw [h]
  · constructor
    · intro h
      dsimp [sramXorSwizzle] at h
      have h2 := congrArg (fun x => c ^^^ x) h
      rwa [← BitVec.xor_assoc, ← BitVec.xor_assoc, BitVec.xor_self,
        BitVec.zero_xor, BitVec.zero_xor] at h2
    · intro h; rw [h]
  · exact Function.Involutive.bijective h_inv

/-- **`MCP₄` Turn 10 Socratic Elenchus 2 (Hypercube `Q_n` Bipartite Non-Planarity for `n ≥ 4`):**
For any `n ≥ 4`, the hypercube `Q_n` has `V = 2^n` vertices and `E = n · 2^{n - 1}` edges,
violating Euler's bipartite planar graph bound `E ≤ 2 V - 4` (`2 · 2^n - 4 < n · 2^{n - 1}`),
so `Q_n` cannot be embedded as a planar bipartite plabic network without non-planar crossings! -/
theorem hypercube_bipartite_nonplanar_bound (n : ℕ) (hn : 4 ≤ n) :
    2 * 2 ^ n - 4 < n * 2 ^ (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := Nat.exists_eq_add_of_le' hn
  have hk : 0 < 2 ^ (k + 3) := Nat.pos_of_ne_zero (by positivity)
  have h1 : 2 * 2 ^ (k + 4) = 4 * 2 ^ (k + 3) := by ring
  have h2 : (k + 4) * 2 ^ (k + 4 - 1) = (k + 4) * 2 ^ (k + 3) := by rfl
  have h_le : 4 * 2 ^ (k + 3) ≤ (k + 4) * 2 ^ (k + 3) :=
    Nat.mul_le_mul_right (2 ^ (k + 3)) (by omega)
  omega

/-- Internal 2-node Plabic 4-cycle transition matrix `W_int = !![0, a₁ a₂; -a₃ a₄, 0]` (Turn 10 Section 2.1). -/
def plabicInternalCycle (a1 a2 a3 a4 : R) : Matrix (Fin 2) (Fin 2) R :=
  !![0, a1 * a2; -(a3 * a4), 0]

/-- Adjugate resolvent factor `(I₂ - W_int)_adj = !![1, a₁ a₂; -a₃ a₄, 1]`. -/
def plabicCycleAdjugate (a1 a2 a3 a4 : R) : Matrix (Fin 2) (Fin 2) R :=
  !![1, a1 * a2; -(a3 * a4), 1]

/-- **`MCP₄` Turn 10 Talaska / Urban-Renewal `2 × 2` Schur Resolvent Identity:**
The internal 4-cycle transition matrix `W_int` with face loop weight `f = a₁ a₂ a₃ a₄`
satisfies `(I₂ - W_int) * (I₂ + W_int) = (1 + f) I₂`, and multiplying by the boundary
injection matrix `B_out = !![1, a₁; a₃, 1]` yields the polynomial numerator of the
Urban-Renewal boundary measurement matrix. -/
theorem talaska_urbanRenewal_schur_identity (a1 a2 a3 a4 : R) :
    (1 - plabicInternalCycle a1 a2 a3 a4) * plabicCycleAdjugate a1 a2 a3 a4 =
      (1 + a1 * a2 * a3 * a4) • 1 ∧
    (!![1, a1; a3, 1] : Matrix (Fin 2) (Fin 2) R) * plabicCycleAdjugate a1 a2 a3 a4 =
      !![1 - a1 * a3 * a4, a1 * (1 + a2);
         a3 * (1 - a4), 1 + a1 * a2 * a3] := by
  refine ⟨?_, ?_⟩ <;>
    { ext i j
      fin_cases i <;> fin_cases j <;>
        simp [plabicInternalCycle, plabicCycleAdjugate,
          Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two] <;>
        ring }

end StageMCP4

/-!
### 5. Stage `MCP₅` (Turns 11–12): `Cl(1,1)` Lorentzian Determinant, Unimodular Cayley Rotor, Dual Horizons & 3-Point BCFW Amalgamation
-/

section StageMCP5

variable {R : Type*} [CommRing R]

/-- Traceless `Cl(1,1)` generator `Ω(w_p, w_s, w_c) = w_p σ_z + w_s σ_x + w_c ε = !![w_p, w_s - w_c; w_s + w_c, -w_p]`. -/
def cl11Traceless (wp ws wc : R) : Matrix (Fin 2) (Fin 2) R :=
  !![wp, ws - wc;
     ws + wc, -wp]

/-- Lorentzian `(1, 2)` loop determinant `f(w_p, w_s, w_c) = w_c² - w_p² - w_s²` (Turn 11 Section 1.1). -/
def cl11LoopWeight (wp ws wc : R) : R :=
  wc ^ 2 - wp ^ 2 - ws ^ 2

/-- Polynomial Cayley numerator `N_Cayley(Ω) = (1 - f) I₂ + 2 Ω = (I₂ + Ω)²` (Turn 11 Section 1.2). -/
def cl11CayleyNumerator (wp ws wc : R) : Matrix (Fin 2) (Fin 2) R :=
  (1 - cl11LoopWeight wp ws wc) • 1 + (2 : R) • cl11Traceless wp ws wc

/-- **`MCP₅` `Cl(1,1)` Lorentzian Determinant, Resolvent & Unimodular Cayley Theorem (Turn 11 Section 1):**
For any traceless `Cl(1,1)` generator `Ω = cl11Traceless wp ws wc`:
1. `det(Ω) = w_c² - w_p² - w_s² = f` (indefinite `(1, 2)` signature),
2. `Ω² = -f I₂`,
3. `(I₂ - Ω)(I₂ + Ω) = (1 + f) I₂` (polynomial resolvent identity),
4. `(I₂ + Ω)² = (1 - f) I₂ + 2 Ω = N_Cayley(Ω)`,
5. `det(N_Cayley(Ω)) = (1 + f)²` (so dividing by `1 + f` produces a strictly unimodular `SL(2)` rotor!). -/
theorem cl11_lorentzian_det_resolvent_and_cayley (wp ws wc : R) :
    (cl11Traceless wp ws wc).det = cl11LoopWeight wp ws wc ∧
    cl11Traceless wp ws wc * cl11Traceless wp ws wc =
      -(cl11LoopWeight wp ws wc • (1 : Matrix (Fin 2) (Fin 2) R)) ∧
    (1 - cl11Traceless wp ws wc) * (1 + cl11Traceless wp ws wc) =
      (1 + cl11LoopWeight wp ws wc) • 1 ∧
    (1 + cl11Traceless wp ws wc) * (1 + cl11Traceless wp ws wc) =
      cl11CayleyNumerator wp ws wc ∧
    (cl11CayleyNumerator wp ws wc).det = (1 + cl11LoopWeight wp ws wc) ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [cl11Traceless, cl11LoopWeight, Matrix.det_fin_two]
    ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cl11Traceless, cl11LoopWeight, Matrix.mul_apply, Fin.sum_univ_two] <;>
      ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cl11Traceless, cl11LoopWeight, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two] <;>
      ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cl11Traceless, cl11LoopWeight, cl11CayleyNumerator,
        Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two] <;>
      ring
  · simp [cl11CayleyNumerator, cl11Traceless, cl11LoopWeight, Matrix.det_fin_two]
    ring

/-- **`MCP₅` Dual Critical Horizons (`f = +1` Elliptic Fold vs. `f = -1` Krein Crash, Turn 11 Section 2):**
1. At the Elliptic Fold `f = +1`, the scalar diagonal `(1 - f) I₂` vanishes and `(I₂ + Ω)² = 2 Ω`.
2. At the Krein Crash `f = -1`, `Ω² = +I₂`, `(I₂ - Ω)(I₂ + Ω) = 0`, and `det(I₂ - Ω) = 0`. -/
theorem cl11_dual_critical_horizons (wp ws wc : R) :
    (1 - cl11Traceless wp ws wc).det = 1 + cl11LoopWeight wp ws wc ∧
    (cl11LoopWeight wp ws wc = 1 →
      (1 + cl11Traceless wp ws wc) * (1 + cl11Traceless wp ws wc) =
        (2 : R) • cl11Traceless wp ws wc) ∧
    (cl11LoopWeight wp ws wc = -1 →
      cl11Traceless wp ws wc * cl11Traceless wp ws wc = 1 ∧
      (1 - cl11Traceless wp ws wc) * (1 + cl11Traceless wp ws wc) = 0 ∧
      (1 - cl11Traceless wp ws wc).det = 0) := by
  have h := cl11_lorentzian_det_resolvent_and_cayley wp ws wc
  have hdet : (1 - cl11Traceless wp ws wc).det = 1 + cl11LoopWeight wp ws wc := by
    simp [cl11Traceless, cl11LoopWeight, Matrix.det_fin_two]
    ring
  refine ⟨hdet, ?_, ?_⟩
  · intro hf1
    rw [h.2.2.2.1]
    dsimp [cl11CayleyNumerator]
    rw [hf1, sub_self, zero_smul, zero_add]
  · intro hfm1
    refine ⟨?_, ?_, ?_⟩
    · rw [h.2.1, hfm1, neg_one_smul, neg_neg]
    · rw [h.2.2.1, hfm1, add_neg_cancel, zero_smul]
    · rw [hdet, hfm1, add_neg_cancel]

/-- BCFW 3-point tree amalgamation matrix `A_tree(u₁, u₂, v₁, v₂) = !![u₁, u₂ v₂; 0, v₁]` (Turn 12 Section 2.1). -/
def bcfwTreeAmalgamation (u1 u2 v1 v2 : R) : Matrix (Fin 2) (Fin 2) R :=
  !![u1, u2 * v2; 0, v1]

/-- BCFW lower unipotent bridge `L_BCFW(z) = !![1, 0; z, 1]` (Turn 12 Section 2.2). -/
def bcfwLowerBridge (z : R) : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; z, 1]

/-- Elementary `3 × 3` BCFW bridge `B₀₁(z₁) = I₃ + z₁ E₀₁` (Turn 12 Section 3). -/
def bcfwBridge01 (z1 : R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, z1, 0;
     0, 1,  0;
     0, 0,  1]

/-- Elementary `3 × 3` BCFW bridge `B₁₂(z₂) = I₃ + z₂ E₁₂` (Turn 12 Section 3). -/
def bcfwBridge12 (z2 : R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 0;
     0, 1, z2;
     0, 0, 1]

/-- **`MCP₅` Turn 12 BCFW 3-Point Dressed Amalgamation, Two-Channel Residue Decomposition & Bridge Non-Commutativity:**
1. Left-multiplying the rank-deficient upper-triangular tree amalgamation `A_tree` by the
   BCFW unipotent bridge `L_BCFW(z)` dresses the `(1, 0)` and `(1, 1)` entries while
   preserving the determinant `det(A(z)) = u₁ v₁`.
2. Adjacent `3 × 3` BCFW bridges fail to commute: `[B₀₁(z₁), B₁₂(z₂)] = z₁ z₂ E₀₂`.
3. For any affine matrix pencil `M(z) = M₀ + z M₁` evaluated at poles `z_a, z_b`,
   `(z_b - z_a) M(0) = z_b M(z_a) - z_a M(z_b)` (Turn 12 Section 1 Cauchy residue sum). -/
theorem bcfw_amalgamation_and_bridge_commutator (z z1 z2 u1 u2 v1 v2 za zb : R)
    (M0 M1 : Matrix (Fin 2) (Fin 2) R) :
    bcfwLowerBridge z * bcfwTreeAmalgamation u1 u2 v1 v2 =
      !![u1, u2 * v2; z * u1, v1 + z * u2 * v2] ∧
    (bcfwLowerBridge z * bcfwTreeAmalgamation u1 u2 v1 v2).det = u1 * v1 ∧
    bcfwLowerBridge z1 * bcfwLowerBridge z2 = bcfwLowerBridge (z1 + z2) ∧
    comm (bcfwBridge01 z1) (bcfwBridge12 z2) =
      !![0, 0, z1 * z2;
         0, 0, 0;
         0, 0, 0] ∧
    (zb - za) • M0 = zb • (M0 + za • M1) - za • (M0 + zb • M1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [bcfwLowerBridge, bcfwTreeAmalgamation, Matrix.mul_apply, Fin.sum_univ_two]; ring
  · simp [bcfwLowerBridge, bcfwTreeAmalgamation, Matrix.det_fin_two]
    ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [bcfwLowerBridge, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [bcfwBridge01, bcfwBridge12, comm]
  · ext i j
    simp
    ring

end StageMCP5

/-!
### 6. Stage `MCP₆` (Turn 13): `Cl(2,2)` Krein–Hamiltonian–Hopf Bifurcation, Nilpotent Krein Crash at `f_k = -1`, and Jordan Root Chain
-/

section StageMCP6

variable {R : Type*} [CommRing R]

/-- `4 × 4` Krein indefinite metric `J₄ = σ_z ⊗ I₂ = diag(1, 1, -1, -1)` (Turn 13 Section 2). -/
def kreinMetric4 : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, -1]

/-- Semisimple carrier generator `S_semi(ω̄) = ω̄ (I₂ ⊗ ε)` (Turn 13 Section 2.1). -/
def kreinHopfSemi (wBar : R) : Matrix (Fin 4) (Fin 4) R :=
  wBar • !![0, -1, 0, 0;
            1,  0, 0, 0;
            0,  0, 0, -1;
            0,  0, 1, 0]

/-- Parametric sideband + Krein-coupling generator `N_part(Δω, g) = Δω (σ_z ⊗ ε) + g (σ_x ⊗ I₂)` (Turn 13 Section 2.1). -/
def kreinHopfNilPart (dw g : R) : Matrix (Fin 4) (Fin 4) R :=
  dw • jwGamma2 + g • jwE1

/-- Full two-mode Krein–Hamiltonian–Hopf generator `M(ω̄, Δω, g) = S_semi(ω̄) + N_part(Δω, g)`. -/
def kreinHopfGenerator (wBar dw g : R) : Matrix (Fin 4) (Fin 4) R :=
  kreinHopfSemi wBar + kreinHopfNilPart dw g

/-- Critical Krein-crash nilpotent operator `N_nil(Δω) = N_part(Δω, Δω)` at `g = Δω` (`f_k = -1`). -/
def kreinCrashNilpotent (dw : R) : Matrix (Fin 4) (Fin 4) R :=
  kreinHopfNilPart dw dw

/-- Coalesced exceptional eigenvector `Ψ_EP = (1, 0, 0, -1)ᵀ` at `g = Δω = 1` (Turn 13 Section 2.2). -/
def kreinExceptionalVec : Fin 4 → R :=
  ![1, 0, 0, -1]

/-- Generalized Jordan root vector `Φ_gen = (0, -1, 0, 0)ᵀ` satisfying `N_nil(1) Φ_gen = Ψ_EP`. -/
def kreinJordanRootVec : Fin 4 → R :=
  ![0, -1, 0, 0]

/-- **`MCP₆` `Cl(2,2)` Krein–Hamiltonian–Hopf `J₄`-Skew-Adjointness & Carrier Commutation (Turn 13 Section 2):** -/
theorem kreinHamiltonianHopf_skew_and_comm (wBar dw g : R) :
    (kreinMetric4 : Matrix (Fin 4) (Fin 4) R) * (kreinHopfGenerator wBar dw g)ᵀ * kreinMetric4 =
      -kreinHopfGenerator wBar dw g ∧
    comm (kreinHopfSemi wBar) (kreinHopfNilPart dw g) = 0 := by
  refine ⟨?_, ?_⟩ <;>
    { ext i j
      simp only [kreinHopfGenerator, kreinHopfSemi, kreinHopfNilPart, comm,
        Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
        Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, Fin.sum_univ_four]
      fin_cases i <;> fin_cases j <;>
        simp [kreinMetric4, jwGamma2, jwE1] <;>
        ring }

/-- **`MCP₆` `Cl(2,2)` Krein–Hamiltonian–Hopf Parametric Square & Nilpotent Crash (`g = Δω`):** -/
theorem kreinHamiltonianHopf_nilPart_sq (dw g : R) :
    kreinHopfNilPart dw g * kreinHopfNilPart dw g =
      -((dw ^ 2 - g ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R)) ∧
    kreinCrashNilpotent dw * kreinCrashNilpotent dw = 0 := by
  refine ⟨?_, ?_⟩ <;>
    { ext i j
      simp only [kreinHopfNilPart, kreinCrashNilpotent, Matrix.add_apply, Matrix.neg_apply,
        Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply, Matrix.zero_apply, Fin.sum_univ_four]
      fin_cases i <;> fin_cases j <;>
        simp [jwGamma2, jwE1] <;>
        ring }

/-- **`MCP₆` `Cl(2,2)` Krein–Hamiltonian–Hopf Bifurcation & Nilpotent Crash Theorem (Turn 13 Section 2):**
1. `M(ω̄, Δω, g)` is strictly `J₄`-skew-adjoint (`J₄ Mᵀ J₄ = -M`),
2. The carrier `S_semi(ω̄)` and parametric part `N_part(Δω, g)` commute (`[S_semi, N_part] = 0`),
3. `N_part(Δω, g)² = -(Δω² - g²) I₄`,
4. At the Krein crash `g = Δω` (`f_k = -1`), `N_nil(Δω)² = 0`. -/
theorem kreinHamiltonianHopf_bifurcation (wBar dw g : R) :
    (kreinMetric4 : Matrix (Fin 4) (Fin 4) R) * (kreinHopfGenerator wBar dw g)ᵀ * kreinMetric4 =
      -kreinHopfGenerator wBar dw g ∧
    comm (kreinHopfSemi wBar) (kreinHopfNilPart dw g) = 0 ∧
    kreinHopfNilPart dw g * kreinHopfNilPart dw g =
      -((dw ^ 2 - g ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R)) ∧
    kreinCrashNilpotent dw * kreinCrashNilpotent dw = 0 := by
  obtain ⟨h1, h2⟩ := kreinHamiltonianHopf_skew_and_comm wBar dw g
  obtain ⟨h3, h4⟩ := kreinHamiltonianHopf_nilPart_sq dw g
  exact ⟨h1, h2, h3, h4⟩

/-- **`MCP₆` Jordan Root Chain & Null-Cone Neutralization at the Krein Crash (Turn 13 Section 2.2–2.3):**
At `g = Δω = 1`:
1. `N_nil(1) Ψ_EP = 0` (`Ψ_EP` is a true kernel eigenvector),
2. `N_nil(1) Φ_gen = Ψ_EP` (`Φ_gen` is a rank-2 Jordan generalized eigenvector),
3. `⟨Ψ_EP, J₄ Ψ_EP⟩ = 0` (the coalesced exceptional mode has zero Krein self-norm and must
   lie on the neutral null cone!). -/
theorem kreinCrash_jordan_chain_and_null_norm :
    Matrix.mulVec (kreinCrashNilpotent (1 : R)) kreinExceptionalVec = ![0, 0, 0, 0] ∧
    Matrix.mulVec (kreinCrashNilpotent (1 : R)) kreinJordanRootVec = kreinExceptionalVec ∧
    dotProduct kreinExceptionalVec (Matrix.mulVec kreinMetric4 kreinExceptionalVec) = (0 : R) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i
    fin_cases i <;>
      simp [kreinCrashNilpotent, kreinHopfNilPart, jwGamma2, jwE1, kreinExceptionalVec,
        Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  · ext i
    fin_cases i <;>
      simp [kreinCrashNilpotent, kreinHopfNilPart, jwGamma2, jwE1,
        kreinJordanRootVec, kreinExceptionalVec,
        Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  · simp [kreinExceptionalVec, kreinMetric4, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

end StageMCP6

/-!
### 7. Stage `MCP₇` (Turns 14–15): Yangian `R`-Matrix, Unitarity Defect, Resonant Rank Collapse, Quantum Yang–Baxter Equation (QYBE), Clifford Artin Braid & Quantum Determinant
-/

section StageMCP7

variable {R : Type*} [CommRing R]

/-- `4 × 4` two-site permutation (swap) matrix `P₁₂` on `R² ⊗ R²` (`P₁₂² = I₄`). -/
def swap4 : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, 0, 0;
     0, 0, 1, 0;
     0, 1, 0, 0;
     0, 0, 0, 1]

/-- Concrete `4 × 4` Yang `R`-matrix `R(u, η) = u I₄ + η P₁₂` (Turn 14 Section 1). -/
def yangR4 (u eta : R) : Matrix (Fin 4) (Fin 4) R :=
  u • 1 + eta • swap4

/-- Concrete `4 × 4` braided Yang `R_check`-matrix `R_check(u, η) = P₁₂ R(u, η) = η I₄ + u P₁₂`. -/
def yangRCheck4 (u eta : R) : Matrix (Fin 4) (Fin 4) R :=
  eta • 1 + u • swap4

/-- **`MCP₇` Yangian `4 × 4` Unitarity Defect, Resonant Rank Collapse & Quantum Determinant (Turns 14–15):**
1. `P₁₂² = I₄`,
2. `R_check(u, η) R_check(-u, η) = (η² - u²) I₄` (unitarity defect),
3. At the resonant points `u = ±η`, `R(η, η) R(-η, η) = 0`, `R(η, η) (0, 1, -1, 0)ᵀ = 0`
   (antisymmetric singlet annihilated at `u = +η`), and `R(-η, η) (1, 0, 0, 0)ᵀ = 0`
   (symmetric triplet annihilated at `u = -η`),
4. The quantum determinant polynomial `(u - θ)² - η²` equals the cleared loop-weight denominator
   `(u - θ)² + (-η²)` linking the Yangian singularity `u - θ = ±η` to the Krein crash `1 + f_k = 0`. -/
theorem yangR4_unitarity_and_resonant_collapse (u eta theta : R) :
    (swap4 : Matrix (Fin 4) (Fin 4) R) * swap4 = 1 ∧
    yangRCheck4 u eta * yangRCheck4 (-u) eta = (eta ^ 2 - u ^ 2) • 1 ∧
    yangR4 eta eta * yangR4 (-eta) eta = 0 ∧
    Matrix.mulVec (yangR4 eta eta) (![0, 1, -1, 0] : Fin 4 → R) = ![0, 0, 0, 0] ∧
    Matrix.mulVec (yangR4 (-eta) eta) (![1, 0, 0, 0] : Fin 4 → R) = ![0, 0, 0, 0] ∧
    (u - theta) ^ 2 + -(eta ^ 2) = (u - theta + eta) * (u - theta - eta) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [swap4]
  · ext i j
    simp only [yangRCheck4, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [swap4] <;> ring
  · ext i j
    simp only [yangR4, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.one_apply, Matrix.zero_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [swap4]
  · ext i
    simp only [yangR4, Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> simp [swap4]
  · ext i
    simp only [yangR4, Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> simp [swap4]
  · ring

/-- **`MCP₇` Abstract Braided Quantum Yang–Baxter Equation (QYBE) over `[Ring B]`:**
For any two braid/transposition generators `P₁₂, P₂₃ ∈ B` satisfying the braid relation
`P₁₂ P₂₃ P₁₂ = P₂₃ P₁₂ P₂₃` and involutivity `P₁₂² = 1`, `P₂₃² = 1`, the braided
Yang `R_check`-operators `Ř₁₂(1) = 1 + P₁₂`, `Ř₂₃(2) = 1 + 2 P₂₃`, `Ř₁₂(2) = 1 + 2 P₁₂`,
`Ř₂₃(1) = 1 + P₂₃` satisfy the exact spectral-parameter braided Yang–Baxter Equation:
`Ř₁₂(1) Ř₂₃(1 + 1) Ř₁₂(1) = Ř₂₃(1) Ř₁₂(1 + 1) Ř₂₃(1)`! -/
theorem yangian_braided_qybe {B : Type*} [Ring B]
    (P12 P23 : B)
    (h12_sq : P12 * P12 = 1)
    (h23_sq : P23 * P23 = 1)
    (h_braid : P12 * P23 * P12 = P23 * P12 * P23) :
    (1 + P12) * (1 + (2 : ℤ) • P23) * (1 + P12) =
      (1 + P23) * (1 + (2 : ℤ) • P12) * (1 + P23) := by
  have h_braid' : P12 * (P23 * P12) = P23 * (P12 * P23) := by
    simpa [mul_assoc] using h_braid
  noncomm_ring [h12_sq, h23_sq, h_braid']

/-- **`MCP₇` Turn 14 Clifford / Majorana EP Artin Braid & Period-8 Obstruction Theorem:**
In any `[Ring B]`, if `γ₁, γ₂, γ₃ ∈ B` are pairwise anticommuting involutions
(`γ_a² = 1`, `γ_a γ_b = -γ_b γ_a` for `a ≠ b`), then the unnormalized Majorana EP braids
`B₁₂ = 1 + γ₁ γ₂` and `B₂₃ = 1 + γ₂ γ₃`:
1. Satisfy the exact Artin braid relation `B₁₂ B₂₃ B₁₂ = B₂₃ B₁₂ B₂₃`,
2. Satisfy `B₁₂² = 2 γ₁ γ₂` and `(B₁₂²)² = -4 · 1` (so the normalized braid `B₁₂ / √2` has
   4th power `-1` and period **8**, correcting the Turn 14 prose claim of period 4!). -/
theorem clifford_ep_artin_braid_and_period_eight {B : Type*} [Ring B]
    (g1 g2 g3 : B)
    (h1 : g1 * g1 = 1) (h2 : g2 * g2 = 1) (h3 : g3 * g3 = 1)
    (h12 : g1 * g2 = -(g2 * g1))
    (h23 : g2 * g3 = -(g3 * g2))
    (h13 : g1 * g3 = -(g3 * g1)) :
    (1 + g1 * g2) * (1 + g2 * g3) * (1 + g1 * g2) =
      (1 + g2 * g3) * (1 + g1 * g2) * (1 + g2 * g3) ∧
    (1 + g1 * g2) * (1 + g1 * g2) = (2 : ℤ) • (g1 * g2) ∧
    ((1 + g1 * g2) * (1 + g1 * g2)) * ((1 + g1 * g2) * (1 + g1 * g2)) = -((4 : ℤ) • (1 : B)) := by
  have h1' : ∀ x : B, g1 * (g1 * x) = x := fun x => by rw [← mul_assoc, h1, one_mul]
  have h2' : ∀ x : B, g2 * (g2 * x) = x := fun x => by rw [← mul_assoc, h2, one_mul]
  have h3' : ∀ x : B, g3 * (g3 * x) = x := fun x => by rw [← mul_assoc, h3, one_mul]
  have h12' : ∀ x : B, g1 * (g2 * x) = -(g2 * (g1 * x)) := fun x => by
    rw [← mul_assoc, h12, neg_mul, mul_assoc]
  have h23' : ∀ x : B, g2 * (g3 * x) = -(g3 * (g2 * x)) := fun x => by
    rw [← mul_assoc, h23, neg_mul, mul_assoc]
  have h13' : ∀ x : B, g1 * (g3 * x) = -(g3 * (g1 * x)) := fun x => by
    rw [← mul_assoc, h13, neg_mul, mul_assoc]
  refine ⟨?_, ?_, ?_⟩ <;>
    noncomm_ring [h1, h2, h3, h1', h2', h3', h12, h23, h13, h12', h23', h13']

/-- Single-site Yangian Lax block `A(u) = !![u - θ + η, 0; 0, u - θ]` of `L(u) = (u - θ) I₄ + η P₁₂` (Turn 15 Section 1.1). -/
def laxBlockA (u theta eta : R) : Matrix (Fin 2) (Fin 2) R :=
  !![u - theta + eta, 0; 0, u - theta]

/-- Single-site Yangian Lax block `D(u) = !![u - θ, 0; 0, u - θ + η]` of `L(u) = (u - θ) I₄ + η P₁₂` (Turn 15 Section 1.1). -/
def laxBlockD (u theta eta : R) : Matrix (Fin 2) (Fin 2) R :=
  !![u - theta, 0; 0, u - theta + eta]

/-- Single-site Yangian Lax off-diagonal block `B_lax = !![0, 0; η, 0]`. -/
def laxBlockB (eta : R) : Matrix (Fin 2) (Fin 2) R :=
  !![0, 0; eta, 0]

/-- Single-site Yangian Lax off-diagonal block `C_lax = !![0, η; 0, 0]`. -/
def laxBlockC (eta : R) : Matrix (Fin 2) (Fin 2) R :=
  !![0, eta; 0, 0]

/-- **`MCP₇` Turn 15 Single-Site RTT Commutator, Commuting Krein Transfer Matrices & Quantum Determinant:**
1. The Krein-twisted transfer blocks `A(u) - D(u) = η σ_z` commute for all spectral parameters `u, v`,
2. `(u - v) [B_lax, C_lax] = η (A(u) D(v) - A(v) D(u))` (fundamental RTT commutator identity),
3. Exact Quantum Determinant identity: `A(u) D(u - η) - B_lax C_lax = ((u - θ)² - η²) I₂`! -/
theorem lax_rtt_and_quantum_determinant (u v theta eta : R) :
    comm (laxBlockA u theta eta - laxBlockD u theta eta)
         (laxBlockA v theta eta - laxBlockD v theta eta) = 0 ∧
    (u - v) • comm (laxBlockB eta) (laxBlockC eta) =
      eta • (laxBlockA u theta eta * laxBlockD v theta eta -
             laxBlockA v theta eta * laxBlockD u theta eta) ∧
    laxBlockA u theta eta * laxBlockD (u - eta) theta eta -
      laxBlockB eta * laxBlockC eta =
      ((u - theta) ^ 2 - eta ^ 2) • 1 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    simp only [comm, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [laxBlockA, laxBlockD]
  · ext i j
    simp only [comm, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [laxBlockA, laxBlockD, laxBlockB, laxBlockC] <;> ring
  · ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [laxBlockA, laxBlockD, laxBlockB, laxBlockC] <;> ring

end StageMCP7

/-!
### 8. Stage `MCP₈` (Turn 16): Dirac–Krein Zitterbewegung Carrier Decoupling, Secular Velocity Trajectory & `ℤ₄` Spin-Monodromy
-/

section StageMCP8

variable {R : Type*} [CommRing R]

/-- Dirac–Krein sideband generator `A = σ_z ⊗ ε = jwGamma2` (`A² = -I₄`, Turn 16 Section 1). -/
def diracKreinA : Matrix (Fin 4) (Fin 4) R := jwGamma2

/-- Dirac–Krein cross-sheet boost generator `B = σ_x ⊗ I₂ = jwE1` (`B² = +I₄`, Turn 16 Section 1). -/
def diracKreinB : Matrix (Fin 4) (Fin 4) R := jwE1

/-- Dirac–Krein velocity bivector `V_vel = A B = -ε ⊗ ε` (`V_vel² = +I₄`, Turn 16 Section 2). -/
def diracKreinVelocity : Matrix (Fin 4) (Fin 4) R :=
  diracKreinA * diracKreinB

/-- Classical commuting drift component `A_drift(Δω, g) = Δω M₀(Δω, g)` (scaled by `Ω² = Δω² - g²`). -/
def diracKreinDriftScaled (dw g : R) : Matrix (Fin 4) (Fin 4) R :=
  dw • kreinHopfNilPart dw g

/-- Anticommuting Zitterbewegung trembling component `A_tremble(Δω, g) = (Δω² - g²) A - Δω M₀(Δω, g)`. -/
def diracKreinTrembleScaled (dw g : R) : Matrix (Fin 4) (Fin 4) R :=
  (dw ^ 2 - g ^ 2) • diracKreinA - dw • kreinHopfNilPart dw g

/-- `2 × 2` Exceptional-Point `ℤ₄` Spin-Monodromy generator `B_EP = -ε = !![0, 1; -1, 0]` (Turn 16 Section 3). -/
def spinMonodromyEP : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; -1, 0]

/-- **`MCP₈` Turn 16 Aporia 1A (Carrier Frequency Decoupling):** -/
theorem diracKrein_carrier_decoupling (wBar : R) :
    comm (kreinHopfSemi wBar) kreinMetric4 = 0 ∧
    comm (kreinHopfSemi wBar) diracKreinA = 0 ∧
    comm (kreinHopfSemi wBar) diracKreinB = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    { ext i j
      simp only [comm, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply, Fin.sum_univ_four]
      fin_cases i <;> fin_cases j <;>
        simp [kreinHopfSemi, kreinMetric4, diracKreinA, diracKreinB, jwGamma2, jwE1] }

/-- **`MCP₈` Turn 16 Aporia 1B (Drift vs. Zitterbewegung Trembling Split):** -/
theorem diracKrein_zitter_split (dw g : R) :
    diracKreinDriftScaled dw g + diracKreinTrembleScaled dw g =
      (dw ^ 2 - g ^ 2) • diracKreinA ∧
    comm (kreinHopfNilPart dw g) (diracKreinDriftScaled dw g) = 0 ∧
    anticomm (kreinHopfNilPart dw g) (diracKreinTrembleScaled dw g) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    { ext i j
      simp only [comm, anticomm, diracKreinDriftScaled, diracKreinTrembleScaled,
        kreinHopfNilPart, diracKreinA, Matrix.add_apply, Matrix.sub_apply,
        Matrix.smul_apply, Matrix.mul_apply, Matrix.zero_apply, Fin.sum_univ_four]
      fin_cases i <;> fin_cases j <;>
        simp [jwGamma2, jwE1] <;>
        ring }

/-- **`MCP₈` Turn 16 Aporia 1 (Combined Carrier Decoupling & Drift vs. Zitterbewegung Trembling Split):** -/
theorem diracKrein_carrier_decoupling_and_zitter_split (wBar dw g : R) :
    comm (kreinHopfSemi wBar) kreinMetric4 = 0 ∧
    comm (kreinHopfSemi wBar) diracKreinA = 0 ∧
    comm (kreinHopfSemi wBar) diracKreinB = 0 ∧
    diracKreinDriftScaled dw g + diracKreinTrembleScaled dw g =
      (dw ^ 2 - g ^ 2) • diracKreinA ∧
    comm (kreinHopfNilPart dw g) (diracKreinDriftScaled dw g) = 0 ∧
    anticomm (kreinHopfNilPart dw g) (diracKreinTrembleScaled dw g) = 0 := by
  obtain ⟨h1, h2, h3⟩ := diracKrein_carrier_decoupling wBar
  obtain ⟨h4, h5, h6⟩ := diracKrein_zitter_split dw g
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- **`MCP₈` Turn 16 Aporia 2 (Exact Secular Quadratic Velocity Evolution at the Krein Crash `f_k = -1`):**
At the Krein crash `g = Δω`, `N_nil = kreinCrashNilpotent dw` satisfies `N_nil² = 0`, so the
propagator `U(t) = I₄ + t N_nil` has exact inverse `U(-t) = I₄ - t N_nil`, and the Heisenberg
evolution `U(-t) X U(t)` truncates at `O(t²)` into an exact ballistic + constant-acceleration
secular trajectory:
1. `(I₄ - t N_nil) A (I₄ + t N_nil) = A + (2 Δω t) V_vel + (2 Δω t²) N_nil`,
2. `(I₄ - t N_nil) J₄ (I₄ + t N_nil) = J₄ - (2 Δω t) (B J₄) + (2 Δω² t²) ((I₄ + V_vel) J₄)`. -/
theorem diracKrein_secular_crash_evolution (dw t : R) :
    (1 - t • kreinCrashNilpotent dw) * (1 + t • kreinCrashNilpotent dw) = 1 ∧
    (1 - t • kreinCrashNilpotent dw) * diracKreinA * (1 + t • kreinCrashNilpotent dw) =
      diracKreinA + (2 * dw * t) • diracKreinVelocity +
        (2 * dw * t ^ 2) • kreinCrashNilpotent dw ∧
    (1 - t • kreinCrashNilpotent dw) * kreinMetric4 * (1 + t • kreinCrashNilpotent dw) =
      kreinMetric4 - (2 * dw * t) • (diracKreinB * kreinMetric4) +
        (2 * dw ^ 2 * t ^ 2) • ((1 + diracKreinVelocity) * kreinMetric4) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    { ext i j
      simp only [kreinCrashNilpotent, kreinHopfNilPart, diracKreinVelocity, diracKreinA, diracKreinB,
        Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.one_apply, Fin.sum_univ_four]
      fin_cases i <;> fin_cases j <;>
        simp [kreinMetric4, jwGamma2, jwE1] <;>
        ring }

/-- **`MCP₈` Turn 16 Aporia 3 (`ℤ₄` Exceptional-Point Spin-Monodromy):**
The single-loop exceptional-point monodromy `B_EP = -ε = !![0, 1; -1, 0]` satisfies
`B_EP² = -I₂` (`4π` spinor sign flip after two loops) and `B_EP⁴ = +I₂` (`8π` identity
restoration after four loops). -/
theorem spinMonodromyEP_z4_periodicity :
    (spinMonodromyEP : Matrix (Fin 2) (Fin 2) R) * spinMonodromyEP = -1 ∧
    ((spinMonodromyEP : Matrix (Fin 2) (Fin 2) R) * spinMonodromyEP) *
      (spinMonodromyEP * spinMonodromyEP) = 1 := by
  refine ⟨?_, ?_⟩ <;>
    { ext i j
      simp only [Matrix.neg_apply, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;> simp [spinMonodromyEP] }

end StageMCP8

/-!
### 9. Stage `MCP₉` (Turn 17): Foldy–Wouthuysen Rapidity to Plabic Canonical Form Dictionary, Urban-Renewal Flip & Thomas–Wigner Precession
-/

section StageMCP9

variable {R : Type*} [CommRing R]

/-- Second orthogonal Foldy–Wouthuysen boost generator `K₂ = ε ⊗ ε` (`K₂² = +I₄`, Turn 17 Section 4). -/
def fwBoost2 : Matrix (Fin 4) (Fin 4) R :=
  !![0,  0,  0, 1;
     0,  0, -1, 0;
     0, -1,  0, 0;
     1,  0,  0, 0]

/-- **`MCP₉` Rational Foldy–Wouthuysen Hyperbolic Dictionary & Urban-Renewal Flip (Turn 17 Section 1–3):**
For any velocity/tangent parameter `v ∈ R` with loop weight `f = -v²`:
1. `(1 + v²)² - (2v)² = (1 - v²)²` (exact rational identity for `cosh²(2θ) - sinh²(2θ) = 1`),
2. The unnormalized canonical block `!![1 + v², 2 v a; 2 v b, 1 + v²]` has determinant
   `(1 - v²)²` whenever `a b = 1` (unimodularity after dividing by the Schur denominator `1 - v²`),
3. Under the Urban-Renewal inversion `v ↦ v⁻¹`, clearing `v²` maps `(1 + v², 1 - v²)` to
   `(v² + 1, v² - 1) = (1 + v², -(1 - v²))`, reversing the sign of the canonical prefactor! -/
theorem foldyWouthuysen_rational_dictionary_and_urbanRenewal (v a b : R) (hab : a * b = 1) :
    (1 + v ^ 2) ^ 2 - (2 * v) ^ 2 = (1 - v ^ 2) ^ 2 ∧
    (!![1 + v ^ 2, 2 * v * a; 2 * v * b, 1 + v ^ 2] : Matrix (Fin 2) (Fin 2) R).det =
      (1 - v ^ 2) ^ 2 ∧
    (v ^ 2 + 1 = 1 + v ^ 2 ∧ v ^ 2 - 1 = -(1 - v ^ 2)) := by
  refine ⟨by ring, ?_, ⟨by ring, by ring⟩⟩
  simp [Matrix.det_fin_two]
  calc
    (1 + v ^ 2) * (1 + v ^ 2) - 2 * v * a * (2 * v * b) =
        (1 + v ^ 2) ^ 2 - (2 * v) ^ 2 * (a * b) := by ring
    _ = (1 + v ^ 2) ^ 2 - (2 * v) ^ 2 * 1 := by rw [hab]
    _ = (1 - v ^ 2) ^ 2 := by ring

/-- **`MCP₉` Real Analytic Foldy–Wouthuysen / Plabic Loop-Coordinate Bridge (Turn 17 Section 1):**
Connects directly to `InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge`:
for any real rapidity `θ` and chiral gauge parameter `χ`,
`0 < 1 + loopWeight θ`, `(1 - loopWeight θ) / (1 + loopWeight θ) = cosh(2θ)`,
and the dressed strand product is `sinh²(2θ) / 4`. -/
theorem foldyWouthuysen_real_rapidity_bridge (θ χ : ℝ) :
    0 < 1 + InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.loopWeight θ ∧
    (1 - InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.loopWeight θ) /
      (1 + InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.loopWeight θ) =
        Real.cosh (2 * θ) ∧
    (InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.lowerStrand θ χ /
      (1 + InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.loopWeight θ)) *
      (InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.upperStrand θ χ /
        (1 + InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.loopWeight θ)) =
        ((Real.sinh (2 * θ)) ^ 2) / 4 :=
  ⟨InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.schurDenominator_pos θ,
   InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.loopPrefactor_eq_cosh_two θ,
   InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.dressedStrand_product θ χ⟩

/-- **`MCP₉` Thomas–Wigner Precession Commutator in `Cl(2,2)` (Turn 17 Section 4):**
The two orthogonal Foldy–Wouthuysen cross-sheet boost generators `K₁ = σ_x ⊗ I₂ = jwE1`
and `K₂ = ε ⊗ ε = fwBoost2` both square to `+I₄`, anticommute with `J₄`, anticommute with
each other, and their commutator is twice the elliptic RoPE rotation generator:
`[K₁, K₂] = 2 (σ_z ⊗ ε) = 2 diracKreinA`. -/
theorem thomasWigner_precession_commutator :
    (jwE1 : Matrix (Fin 4) (Fin 4) R) * jwE1 = 1 ∧
    (fwBoost2 : Matrix (Fin 4) (Fin 4) R) * fwBoost2 = 1 ∧
    anticomm (jwE1 : Matrix (Fin 4) (Fin 4) R) kreinMetric4 = 0 ∧
    anticomm (fwBoost2 : Matrix (Fin 4) (Fin 4) R) kreinMetric4 = 0 ∧
    anticomm (jwE1 : Matrix (Fin 4) (Fin 4) R) fwBoost2 = 0 ∧
    comm (jwE1 : Matrix (Fin 4) (Fin 4) R) fwBoost2 = (2 : R) • diracKreinA := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    { ext i j
      simp only [anticomm, comm, diracKreinA, Matrix.add_apply, Matrix.sub_apply,
        Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply, Matrix.zero_apply, Fin.sum_univ_four]
      fin_cases i <;> fin_cases j <;>
        simp [jwE1, fwBoost2, kreinMetric4, jwGamma2] <;>
        ring }

end StageMCP9

/-!
### 10. Stage `MCP₁₀`: Bidirectional 17-Turn Causal Poset (`Turn01`–`Turn17`) & Non-Commutative Peirce Operator Realization
-/

section StageMCP10

/-- The 17 turn-level mathematical archetypes of `https://share.gemini.google/hNydhwDbFYmo` (`9666a5a14e0d`). -/
inductive CausalMatrixChatTurnArchetype : Type
  | Turn01_MetriplecticSplitGramiansAndAporiaDefect
  | Turn02_DoubledBlockDilationEquilibriumFlowAndSchurLDU
  | Turn03_GohbergKreinHilbertAndCotlarTricomiIdentity
  | Turn04_KreinIndefiniteMetricAndSymplecticCayleyBridge
  | Turn05_Cl11ParaKahlerTriadAndLightConeNullProjectors
  | Turn06_JordanWignerKreinStringVsUngradedKroneckerAporia
  | Turn07_CliffordMultivectorAttentionBilinearReadout
  | Turn08_WalshHadamardBivectorInteractionKernel
  | Turn09_XorSwizzleBankConflictFreeInvolutionBijection
  | Turn10_WalshHadamardConjugationElenchusAndTalaskaSchur
  | Turn11_Cl11LorentzianDetCayleyRotorAndDualHorizons
  | Turn12_BCFWThreePointAmalgamationAndBridgeCommutator
  | Turn13_Cl22KreinHamiltonianHopfAndJordanCrashAtMinusOne
  | Turn14_YangianRMatrixQYBEAndResonantRankCollapse
  | Turn15_RTTMonodromyQuantumDetAndBetheLoopDictionary
  | Turn16_DiracKreinZitterbewegungCarrierDecouplingAndSecularCrash
  | Turn17_FoldyWouthuysenRapidityDictionaryAndThomasWignerPrecession
  deriving DecidableEq, Repr

namespace CausalMatrixChatTurnArchetype

/-- Causal prerequisite DAG (as `Finset ℕ`) across all 17 turns of `9666a5a14e0d`. -/
def causalPrerequisites : CausalMatrixChatTurnArchetype → Finset ℕ
  | .Turn01_MetriplecticSplitGramiansAndAporiaDefect                 => {1}
  | .Turn02_DoubledBlockDilationEquilibriumFlowAndSchurLDU           => {1, 2}
  | .Turn03_GohbergKreinHilbertAndCotlarTricomiIdentity              => {1, 2, 3}
  | .Turn04_KreinIndefiniteMetricAndSymplecticCayleyBridge           => {1, 2, 4}
  | .Turn05_Cl11ParaKahlerTriadAndLightConeNullProjectors            => {1, 2, 4, 5}
  | .Turn06_JordanWignerKreinStringVsUngradedKroneckerAporia         => {1, 2, 4, 5, 6}
  | .Turn07_CliffordMultivectorAttentionBilinearReadout              => {1, 2, 4, 5, 6, 7}
  | .Turn08_WalshHadamardBivectorInteractionKernel                   => {1, 2, 4, 5, 6, 7, 8}
  | .Turn09_XorSwizzleBankConflictFreeInvolutionBijection            => {1, 2, 4, 5, 6, 7, 8, 9}
  | .Turn10_WalshHadamardConjugationElenchusAndTalaskaSchur          => {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
  | .Turn11_Cl11LorentzianDetCayleyRotorAndDualHorizons              => {1, 2, 3, 4, 5, 10, 11}
  | .Turn12_BCFWThreePointAmalgamationAndBridgeCommutator            => {1, 2, 3, 4, 5, 10, 11, 12}
  | .Turn13_Cl22KreinHamiltonianHopfAndJordanCrashAtMinusOne         => {1, 2, 3, 4, 5, 6, 10, 11, 12, 13}
  | .Turn14_YangianRMatrixQYBEAndResonantRankCollapse                => {1, 2, 3, 4, 5, 6, 10, 11, 12, 13, 14}
  | .Turn15_RTTMonodromyQuantumDetAndBetheLoopDictionary             => {1, 2, 3, 4, 5, 6, 10, 11, 12, 13, 14, 15}
  | .Turn16_DiracKreinZitterbewegungCarrierDecouplingAndSecularCrash => {1, 2, 3, 4, 5, 6, 10, 11, 12, 13, 14, 15, 16}
  | .Turn17_FoldyWouthuysenRapidityDictionaryAndThomasWignerPrecession =>
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17}

theorem causalPrerequisites_injective : Function.Injective causalPrerequisites := by
  intro a b h
  cases a <;> cases b <;> try rfl
  all_goals revert h; decide

instance instPartialOrder : PartialOrder CausalMatrixChatTurnArchetype :=
  PartialOrder.lift causalPrerequisites causalPrerequisites_injective

instance instDecidableLE : DecidableRel (α := CausalMatrixChatTurnArchetype) (· ≤ ·) :=
  fun a b => inferInstanceAs (Decidable (causalPrerequisites a ⊆ causalPrerequisites b))

/-- **`MCP₁₀` Root and Terminal Synthesis of the 17-Turn Poset:**
`Turn01` is the universal root (`Turn01 ≤ a`) and `Turn17` is the universal synthesis
terminal (`a ≤ Turn17`) across all 17 turns. -/
theorem turn01_is_root_and_turn17_is_terminal (a : CausalMatrixChatTurnArchetype) :
    .Turn01_MetriplecticSplitGramiansAndAporiaDefect ≤ a ∧
    a ≤ .Turn17_FoldyWouthuysenRapidityDictionaryAndThomasWignerPrecession ∧
    ¬ (a < a) := by
  refine ⟨?_, ?_, lt_irrefl a⟩
  · cases a <;> decide
  · cases a <;> decide

end CausalMatrixChatTurnArchetype

variable {B : Type*} [Ring B]

/-- Non-commutative Peirce-spine operator realization mapping each of the 17 turns of
`9666a5a14e0d` to its canonical operator in `[Ring B]`. -/
def causalMatrixTurnOperator (P A C X : B) : CausalMatrixChatTurnArchetype → B
  | .Turn01_MetriplecticSplitGramiansAndAporiaDefect =>
      gramianOut (genPhi P A C) (genJ P A C)
  | .Turn02_DoubledBlockDilationEquilibriumFlowAndSchurLDU =>
      gramianIn (genPhi P A C) (genJ P A C)
  | .Turn03_GohbergKreinHilbertAndCotlarTricomiIdentity =>
      offDiagSym (coneMinus P C) (conePlus P A) * offDiagSym (coneMinus P C) (conePlus P A) +
        gohbergKreinHilbert (coneMinus P C) (conePlus P A) *
          gohbergKreinHilbert (coneMinus P C) (conePlus P A)
  | .Turn04_KreinIndefiniteMetricAndSymplecticCayleyBridge =>
      invS P * genPhi P A C * invS P
  | .Turn05_Cl11ParaKahlerTriadAndLightConeNullProjectors =>
      (1 + invS P) * (1 - invS P)
  | .Turn06_JordanWignerKreinStringVsUngradedKroneckerAporia =>
      anticomm (invS P) (genPhi P A C)
  | .Turn07_CliffordMultivectorAttentionBilinearReadout =>
      evenGrade P X + oddGrade P X
  | .Turn08_WalshHadamardBivectorInteractionKernel =>
      comm (genPhi P A C) (genJ P A C)
  | .Turn09_XorSwizzleBankConflictFreeInvolutionBijection =>
      invS P * (invS P * X)
  | .Turn10_WalshHadamardConjugationElenchusAndTalaskaSchur =>
      (1 - genPhi P A C) * (1 + genPhi P A C)
  | .Turn11_Cl11LorentzianDetCayleyRotorAndDualHorizons =>
      (1 + genPhi P A C) * (1 + genPhi P A C)
  | .Turn12_BCFWThreePointAmalgamationAndBridgeCommutator =>
      comm (1 + conePlus P A) (1 + coneMinus P C)
  | .Turn13_Cl22KreinHamiltonianHopfAndJordanCrashAtMinusOne =>
      conePlus P A * conePlus P A
  | .Turn14_YangianRMatrixQYBEAndResonantRankCollapse =>
      (1 + invS P) * (invS P - 1)
  | .Turn15_RTTMonodromyQuantumDetAndBetheLoopDictionary =>
      genSig P A C * genSig P A C - genV P A C * genV P A C
  | .Turn16_DiracKreinZitterbewegungCarrierDecouplingAndSecularCrash =>
      (1 - conePlus P A) * invS P * (1 + conePlus P A)
  | .Turn17_FoldyWouthuysenRapidityDictionaryAndThomasWignerPrecession =>
      comm (invS P) (genJ P A C)

/-- **`MCP₁₀` Master Non-Commutative Peirce Operator Synthesis Across All 17 Turns:**
For any idempotent `P * P = P` in a non-commutative ring `[Ring B]`, the 17 turn
operators satisfy exact Peirce-spine identities. -/
theorem causalMatrixTurnOperator_master_identities {P : B} (hP : P * P = P) (A C X : B) :
    causalMatrixTurnOperator P A C X .Turn01_MetriplecticSplitGramiansAndAporiaDefect =
      (2 : ℤ) • genV P A C + (2 : ℤ) • genSig P A C ∧
    causalMatrixTurnOperator P A C X .Turn02_DoubledBlockDilationEquilibriumFlowAndSchurLDU =
      (2 : ℤ) • genV P A C - (2 : ℤ) • genSig P A C ∧
    causalMatrixTurnOperator P A C X .Turn03_GohbergKreinHilbertAndCotlarTricomiIdentity = 0 ∧
    causalMatrixTurnOperator P A C X .Turn04_KreinIndefiniteMetricAndSymplecticCayleyBridge =
      -genPhi P A C ∧
    causalMatrixTurnOperator P A C X .Turn05_Cl11ParaKahlerTriadAndLightConeNullProjectors = 0 ∧
    causalMatrixTurnOperator P A C X .Turn06_JordanWignerKreinStringVsUngradedKroneckerAporia = 0 ∧
    causalMatrixTurnOperator P A C X .Turn07_CliffordMultivectorAttentionBilinearReadout = X ∧
    causalMatrixTurnOperator P A C X .Turn08_WalshHadamardBivectorInteractionKernel =
      -((2 : ℤ) • genSig P A C) ∧
    causalMatrixTurnOperator P A C X .Turn09_XorSwizzleBankConflictFreeInvolutionBijection = X ∧
    causalMatrixTurnOperator P A C X .Turn10_WalshHadamardConjugationElenchusAndTalaskaSchur =
      1 - genV P A C ∧
    causalMatrixTurnOperator P A C X .Turn11_Cl11LorentzianDetCayleyRotorAndDualHorizons =
      (1 + genV P A C) + (2 : ℤ) • genPhi P A C ∧
    causalMatrixTurnOperator P A C X .Turn12_BCFWThreePointAmalgamationAndBridgeCommutator =
      genSig P A C ∧
    causalMatrixTurnOperator P A C X .Turn13_Cl22KreinHamiltonianHopfAndJordanCrashAtMinusOne = 0 ∧
    causalMatrixTurnOperator P A C X .Turn14_YangianRMatrixQYBEAndResonantRankCollapse = 0 ∧
    causalMatrixTurnOperator P A C X .Turn15_RTTMonodromyQuantumDetAndBetheLoopDictionary = 0 ∧
    causalMatrixTurnOperator P A C X .Turn16_DiracKreinZitterbewegungCarrierDecouplingAndSecularCrash =
      invS P + (2 : ℤ) • conePlus P A ∧
    causalMatrixTurnOperator P A C X .Turn17_FoldyWouthuysenRapidityDictionaryAndThomasWignerPrecession =
      (2 : ℤ) • genPhi P A C := by
  dsimp only [causalMatrixTurnOperator, gramianOut, gramianIn, causalForward, causalBackward,
    offDiagSym, gohbergKreinHilbert]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    peirce_nf hP

end StageMCP10

end InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalPlabicKreinYangianPoset
