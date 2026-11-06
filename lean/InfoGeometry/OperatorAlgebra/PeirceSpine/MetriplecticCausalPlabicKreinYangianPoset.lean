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
import InfoGeometry.Core.IdempotentGraphGrassmannian
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.PeirceSpine.StarGrading
import InfoGeometry.OperatorAlgebra.PeirceSpine.RingHomTransport
import InfoGeometry.OperatorAlgebra.PeirceSpine.Unipotent
import InfoGeometry.OperatorAlgebra.PeirceSpine.TransferDefect
import InfoGeometry.OperatorAlgebra.PeirceSpine.GradingPerturbation
import InfoGeometry.OperatorAlgebra.PeirceSpine.Bergman
import InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralEulerFactors
import InfoGeometry.OperatorAlgebra.PeirceSpine.BlockTriangularIntervention
import InfoGeometry.OperatorAlgebra.PeirceSpine.PhaseConjugateSteinberg
import InfoGeometry.OperatorAlgebra.PeirceSpine.ZitterbewegungVelocity
import InfoGeometry.OperatorAlgebra.PeirceSpine.PlabicVertexContraction
import InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixColimitTransport
import InfoGeometry.OperatorAlgebra.PeirceSpine.GradingTransfer
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoStateSandwich
import InfoGeometry.OperatorAlgebra.PeirceSpine.PlabicKleinActionBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.ConeSheetBraiding
import InfoGeometry.OperatorAlgebra.PeirceSpine.TransferMoments
import InfoGeometry.OperatorAlgebra.PeirceSpine.PrimalDual
import InfoGeometry.OperatorAlgebra.PeirceSpine.SandwichBrackets
import InfoGeometry.OperatorAlgebra.PeirceSpine.CurvatureDoubleCommutator
import InfoGeometry.OperatorAlgebra.PeirceSpine.KantorCornerAnomaly
import InfoGeometry.OperatorAlgebra.PeirceSpine.KreinXiStarDefect
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.TowerMatrix
import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Clifford.Cl11TensorTowerIteration
import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Clifford.Cl11TensorTowerSupergraded
import InfoGeometry.Clifford.Cl11StarAlgebraColimit
import InfoGeometry.Clifford.Cl11StarAlgebraFiltration
import InfoGeometry.Clifford.Cl11JordanWignerCARBridge
import InfoGeometry.Clifford.Cl11GradingSl2
import InfoGeometry.Clifford.Cl11MarkovJonesEngine
import InfoGeometry.Clifford.Cl11TensorStageFactorization
import InfoGeometry.Clifford.Cl11TensorTowerNormalizedTrace
import InfoGeometry.Algebra.LightConePair
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
open InfoGeometry.Core.IdempotentGraphGrassmannian

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

/-! **`MCP₁` Aporia Defect Star-Adjoint Split under Metriplectic Parity.**
Under star parity (`star S = S`, `star K = -K`) the aporia idempotency defect
splits into a self-adjoint "real" part and a skew-adjoint "imaginary" part,
mirroring the S/K metriplectic split itself:
`star (aporiaIdempotencyDefect S K) = (S² + K² − S) − ({S, K} − K)`.  The
self-adjoint half `S² + K² − S` is fixed by the involution while the skew
half `{S, K} − K` changes sign — so the defect is neither self-adjoint nor
skew-adjoint unless one half vanishes. -/

theorem star_aporiaIdempotencyDefect_split [StarRing B] (S K : B)
    (hS : star S = S) (hK : star K = -K) :
    star (aporiaIdempotencyDefect S K) =
      (S * S + K * K - S) - (anticomm S K - K) := by
  have h₁ : star (aporiaIdempotencyDefect S K)
      = star ((S * S + K * K - S) + (anticomm S K - K)) := by
    rw [aporiaIdempotencyDefect_expand]
  rw [h₁]
  have h₂ : star (S * S + K * K - S) = S * S + K * K - S := by
    rw [star_sub, star_add, star_mul, star_mul, hS, hK]
    noncomm_ring
  have h₃ : star (anticomm S K - K) = -(anticomm S K - K) := by
    dsimp [anticomm]
    rw [star_sub, star_add, star_mul, star_mul, hS, hK]
    noncomm_ring
  rw [star_add, h₂, h₃]
  noncomm_ring

/-! **`MCP₁` Aporia–Idempotency Bridge.**
The aporia idempotency defect `aporiaIdempotencyDefect S K = (S + K)² − (S + K)` is
exactly `IdempotentGraphGrassmannian.idempotencyDefect (causalForward S K)`. This
connects Turn 01's metriplectic aporia directly to the idempotency defect of the
causal sum in `InfoGeometry.Core.IdempotentGraphGrassmannian`. -/

theorem aporiaIdempotencyDefect_eq_idempotencyDefect (S K : B) :
    aporiaIdempotencyDefect S K = idempotencyDefect (causalForward S K) := by
  calc
    aporiaIdempotencyDefect S K
      = crossGramian S K - causalForward S K := by rw [aporiaIdempotencyDefect]
    _ = (causalForward S K) * (causalForward S K) - causalForward S K := by
      rw [crossGramian]
      <;> simp [causalForward]
      <;> abel
    _ = idempotencyDefect (causalForward S K) := by
      simp [idempotencyDefect]

/-! **`MCP₁` Star-Ring Parity of the Metriplectic Split (`star S = S`, `star K = -K`):**
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

/-! **`MCP₁` Metriplectic–DIGRAC Split:**
Under star parity (`star S = S`, `star K = -K`) the DIGRAC symmetric/skew
decomposition of the causal sum `S + K` recovers the S/K metriplectic split:
`digracSym (S + K) = 2 • S` (self-adjoint part) and
`digracImb (S + K) = 2 • K` (skew-adjoint part). This closes the loop between
Turn 01's metriplectic parity and `StarGrading`'s symmetric/skew components. -/
theorem metriplectic_digrac_split [StarRing B] (S K : B)
    (hS : star S = S) (hK : star K = -K) :
    digracSym (causalForward S K) = (2 : ℤ) • S ∧
    digracImb (causalForward S K) = (2 : ℤ) • K := by
  constructor
  · dsimp [digracSym, causalForward]
    rw [star_add, hS, hK]
    simp only [two_smul]
    abel
  · dsimp [digracImb, causalForward]
    rw [star_add, hS, hK]
    simp only [two_smul]
    abel

/-! **`MCP₁` Krein involution: star-adjoint Gramians and Hadamard involution.**
When `S` is self-adjoint (`star S = S`) and `K` is skew-adjoint (`star K = -K`),
both Gramians `G_out = (S+K)(S-K)` and `G_in = (S-K)(S+K)` are self-adjoint:
they are the two orderings of the same Krein norm. The Walsh–Hadamard block is
self-adjoint and squares to `2 • 1`, i.e. a scaled unitary (involution up to
the factor `2`). -/

theorem star_gramianOut_self_adjoint [StarRing B] (S K : B)
    (hS : star S = S) (hK : star K = -K) :
    star (gramianOut S K) = gramianOut S K := by
  dsimp [gramianOut, causalForward, causalBackward]
  rw [star_mul, star_sub, star_add, hS, hK]
  noncomm_ring

theorem star_gramianIn_self_adjoint [StarRing B] (S K : B)
    (hS : star S = S) (hK : star K = -K) :
    star (gramianIn S K) = gramianIn S K := by
  dsimp [gramianIn, causalForward, causalBackward]
  rw [star_mul, star_add, star_sub, hS, hK]
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

theorem hadamardBlock_transpose_self :
    (hadamardBlock : Matrix (Fin 2) (Fin 2) B)ᵀ = hadamardBlock := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamardBlock, Matrix.transpose_apply]

theorem hadamardBlock_square_two :
    (hadamardBlock : Matrix (Fin 2) (Fin 2) B) * hadamardBlock =
      (2 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) B) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamardBlock, Matrix.mul_apply, Fin.sum_univ_two, zsmul_eq_mul] <;>
    norm_num

/-! **`MCP₁` Krein J-signature block and J-self-adjoint Gramian diagonal.**
The Krein signature matrix `J = diag(1, -1)` is a self-adjoint involution (`J² = 1`,
`Jᵀ = J`). Under star parity (`star S = S`, `star K = -K`) both Gramians are
self-adjoint (`star G_out = G_out`, `star G_in = G_in`), so the Gramian diagonal
`diag(G_out, G_in)` is J-self-adjoint: `star (J * diag(G_out, G_in)) = J * diag(G_out,
G_in)`. This is the operator-algebra statement of the Krein indefinite inner product:
`J` supplies the signature `(+,−)` and the two Gramians are the self-adjoint Gram
operators on the two sheets. -/

def kreinJ : Matrix (Fin 2) (Fin 2) B :=
  !![(1 : B), 0; 0, -1]

theorem kreinJ_square_one : (kreinJ : Matrix (Fin 2) (Fin 2) B) * kreinJ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kreinJ, Matrix.mul_apply, Matrix.one_apply, Fin.val_zero, Fin.val_one]
    <;> norm_num

theorem kreinJ_transpose_self : (kreinJ : Matrix (Fin 2) (Fin 2) B)ᵀ = kreinJ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kreinJ, Matrix.transpose_apply, Fin.val_zero, Fin.val_one]
    <;> rfl

def kreinGramianDiagonal (S K : B) : Matrix (Fin 2) (Fin 2) B :=
  !![gramianOut S K, 0; 0, gramianIn S K]

theorem star_kreinGramianDiagonal_krein_self_adjoint [StarRing B] (S K : B)
    (hS : star S = S) (hK : star K = -K) :
    star ((kreinJ : Matrix (Fin 2) (Fin 2) B) * kreinGramianDiagonal S K) =
      (kreinJ : Matrix (Fin 2) (Fin 2) B) * kreinGramianDiagonal S K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kreinJ, kreinGramianDiagonal, gramianOut, gramianIn, causalForward,
      causalBackward, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two,
      Fin.val_zero, Fin.val_one, star_add, star_sub, star_neg, star_one, star_zero,
      hS, hK, sub_eq_add_neg]
    <;>
    (try norm_num) <;>
    (try abel) <;>
    (try ring_nf) <;>
    (try simp_all [Matrix.star_apply]) <;>
    (try norm_num)

theorem star_chiralDiracBlock_self_adjoint [StarRing B] (S K : B)
    (hS : star S = S) (hK : star K = -K) :
    Matrix.transpose ((chiralDiracBlock S K : Matrix (Fin 2) (Fin 2) B).map star) =
      chiralDiracBlock S K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralDiracBlock, causalForward, causalBackward, Matrix.transpose_apply,
      Matrix.map_apply, Fin.val_zero, Fin.val_one, star_add, star_sub, star_neg,
      star_one, star_zero, hS, hK, sub_eq_add_neg]
    <;> abel

theorem star_symplecticDilationBlock_self_adjoint [StarRing B] (S K : B)
    (hS : star S = S) (hK : star K = -K) :
    Matrix.transpose ((symplecticDilationBlock S K : Matrix (Fin 2) (Fin 2) B).map star) =
      symplecticDilationBlock S K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symplecticDilationBlock, Matrix.transpose_apply, Matrix.map_apply,
      star_neg, star_zero, hS, hK]

theorem star_equilibriumFlowRoot_self_adjoint [StarRing B] (S K : B)
    (hS : star S = S) (hK : star K = -K) :
    Matrix.transpose ((equilibriumFlowRoot S K : Matrix (Fin 2) (Fin 2) B).map star) =
      equilibriumFlowRoot S K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [equilibriumFlowRoot, Matrix.transpose_apply, Matrix.map_apply,
      star_neg, star_zero, hS, hK]

theorem star_metriplecticBlock_flips_K [StarRing B] (S K : B)
    (hS : star S = S) (hK : star K = -K) :
    Matrix.transpose ((metriplecticBlock S K : Matrix (Fin 2) (Fin 2) B).map star) =
      metriplecticBlock S (-K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [metriplecticBlock, Matrix.transpose_apply, Matrix.map_apply,
      star_neg, hS, hK]

/-! **`MCP₁` Chiral Dirac Block Square (`D(S, K)² = diag(G_out(S, K), G_in(S, K))`):**
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

/-- One-step ungraded Kronecker embedding `X ↦ !![X, 0; 0, X]` as a unital `RingHom`. -/
def twoByTwoUngradedRingHom (B : Type*) [Ring B] : B →+* Matrix (Fin 2) (Fin 2) B where
  toFun X := !![X, 0; 0, X]
  map_one' := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_mul' X Y := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  map_zero' := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_add' X Y := by
    ext i j; fin_cases i <;> fin_cases j <;> simp

/-- Level-`n` ungraded Kronecker lift `OpMatTower B n →+* OpMatTower B (n + 1)` as a unital `RingHom`. -/
def towerUngradedRingHom (B : Type*) [Ring B] (n : ℕ) :
    OpMatTower B n →+* OpMatTower B (n + 1) :=
  twoByTwoUngradedRingHom (OpMatTower B n)

/-- Uniform two-sheet Jordan–Wigner Krein-lift anticommutator and `RingHom` intertwining laws. -/
theorem twoByTwo_kreinLift_anticomm_and_ringHom (X Y : B) :
    anticomm (!![(0 : B), 1; 1, 0] : Matrix (Fin 2) (Fin 2) B)
      !![(0 : B), -1; 1, 0] = 0 ∧
    anticomm (!![X, 0; 0, -X] : Matrix (Fin 2) (Fin 2) B) !![Y, 0; 0, -Y] =
      twoByTwoUngradedRingHom B (anticomm X Y) ∧
    comm (!![X, 0; 0, -X] : Matrix (Fin 2) (Fin 2) B) !![Y, 0; 0, -Y] =
      twoByTwoUngradedRingHom B (comm X Y) ∧
    twoByTwoUngradedRingHom B (comm X Y) =
      comm (twoByTwoUngradedRingHom B X) (twoByTwoUngradedRingHom B Y) ∧
    twoByTwoUngradedRingHom B (anticomm X Y) =
      anticomm (twoByTwoUngradedRingHom B X) (twoByTwoUngradedRingHom B Y) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    { ext i j
      fin_cases i <;> fin_cases j <;>
        simp [twoByTwoUngradedRingHom, anticomm, comm] }

/-- Inductive `n`-site Jordan–Wigner positive Clifford generator `E_k^{(n)} ∈ OpMatTower B n` (`(E_k^{(n)})² = +1`). -/
def towerJWPos (B : Type*) [Ring B] : (n : ℕ) → Fin n → OpMatTower B n
  | 0, k => k.elim0
  | n + 1, k =>
      Fin.cases (towerParaK B n) (fun i => towerKreinLift n (towerJWPos B n i)) k

/-- Inductive `n`-site Jordan–Wigner negative Clifford generator `Γ_k^{(n)} ∈ OpMatTower B n` (`(Γ_k^{(n)})² = -1`). -/
def towerJWNeg (B : Type*) [Ring B] : (n : ℕ) → Fin n → OpMatTower B n
  | 0, k => k.elim0
  | n + 1, k =>
      Fin.cases (towerSympEps B n) (fun i => towerKreinLift n (towerJWNeg B n i)) k

/-- Every positive Jordan–Wigner generator `E_k^{(n)}` in `OpMatTower B n` squares to `+1`. -/
theorem towerJWPos_sq (B : Type*) [Ring B] :
    ∀ (n : ℕ) (k : Fin n), towerJWPos B n k * towerJWPos B n k = (1 : OpMatTower B n)
  | 0, k => k.elim0
  | n + 1, k => by
      induction' k using Fin.cases with i
      · simpa [towerJWPos] using
          (tower_paraKahler_and_jordanWigner_lift (B := B) n 0 0 0).2.1
      · change towerKreinLift n (towerJWPos B n i) * towerKreinLift n (towerJWPos B n i) = 1
        rw [(tower_paraKahler_and_jordanWigner_lift (B := B) n (towerJWPos B n i) 0 0).2.2.2.2.2.2.2.1]
        rw [towerJWPos_sq B n i]
        exact (twoByTwoUngradedRingHom (OpMatTower B n)).map_one

/-- Every negative Jordan–Wigner generator `Γ_k^{(n)}` in `OpMatTower B n` squares to `-1`. -/
theorem towerJWNeg_sq (B : Type*) [Ring B] :
    ∀ (n : ℕ) (k : Fin n), towerJWNeg B n k * towerJWNeg B n k = -(1 : OpMatTower B n)
  | 0, k => k.elim0
  | n + 1, k => by
      induction' k using Fin.cases with i
      · simpa [towerJWNeg] using
          (tower_paraKahler_and_jordanWigner_lift (B := B) n 0 0 0).2.2.1
      · change towerKreinLift n (towerJWNeg B n i) * towerKreinLift n (towerJWNeg B n i) = -1
        rw [(tower_paraKahler_and_jordanWigner_lift (B := B) n (towerJWNeg B n i) 0 0).2.2.2.2.2.2.2.1]
        rw [towerJWNeg_sq B n i]
        change (twoByTwoUngradedRingHom (OpMatTower B n)) (-1) = -1
        rw [RingHom.map_neg, RingHom.map_one]

/-- Distinct positive Jordan–Wigner generators `E_j^{(n)}, E_k^{(n)}` (`j ≠ k`) anticommute at every tower depth `n`. -/
theorem towerJWPos_anticomm (B : Type*) [Ring B] :
    ∀ (n : ℕ) (j k : Fin n), j ≠ k →
      anticomm (towerJWPos B n j) (towerJWPos B n k) = (0 : OpMatTower B n)
  | 0, j, _, _ => j.elim0
  | n + 1, j, k, hjk => by
      induction' j using Fin.cases with j' <;> induction' k using Fin.cases with k'
      · exact (hjk rfl).elim
      · simpa [towerJWPos] using
          (tower_paraKahler_and_jordanWigner_lift (B := B) n (towerJWPos B n k') 0 0).2.2.2.2.1
      · have h_symm :
            anticomm (towerKreinLift n (towerJWPos B n j')) (towerParaK B n) =
              anticomm (towerParaK B n) (towerKreinLift n (towerJWPos B n j')) := by
          dsimp [anticomm]; abel
        simpa [towerJWPos, h_symm] using
          (tower_paraKahler_and_jordanWigner_lift (B := B) n (towerJWPos B n j') 0 0).2.2.2.2.1
      · have hne : j' ≠ k' := fun h => hjk (congrArg Fin.succ h)
        change anticomm (towerKreinLift n (towerJWPos B n j'))
          (towerKreinLift n (towerJWPos B n k')) = 0
        rw [show anticomm (towerKreinLift n (towerJWPos B n j'))
              (towerKreinLift n (towerJWPos B n k')) =
              twoByTwoUngradedRingHom (OpMatTower B n)
                (anticomm (towerJWPos B n j') (towerJWPos B n k')) by
          simpa [towerKreinLift] using
            (twoByTwo_kreinLift_anticomm_and_ringHom (B := OpMatTower B n)
              (towerJWPos B n j') (towerJWPos B n k')).2.1]
        rw [towerJWPos_anticomm B n j' k' hne, RingHom.map_zero]

/-- Distinct negative Jordan–Wigner generators `Γ_j^{(n)}, Γ_k^{(n)}` (`j ≠ k`) anticommute at every tower depth `n`. -/
theorem towerJWNeg_anticomm (B : Type*) [Ring B] :
    ∀ (n : ℕ) (j k : Fin n), j ≠ k →
      anticomm (towerJWNeg B n j) (towerJWNeg B n k) = (0 : OpMatTower B n)
  | 0, j, _, _ => j.elim0
  | n + 1, j, k, hjk => by
      induction' j using Fin.cases with j' <;> induction' k using Fin.cases with k'
      · exact (hjk rfl).elim
      · simpa [towerJWNeg] using
          (tower_paraKahler_and_jordanWigner_lift (B := B) n (towerJWNeg B n k') 0 0).2.2.2.2.2.1
      · have h_symm :
            anticomm (towerKreinLift n (towerJWNeg B n j')) (towerSympEps B n) =
              anticomm (towerSympEps B n) (towerKreinLift n (towerJWNeg B n j')) := by
          dsimp [anticomm]; abel
        simpa [towerJWNeg, h_symm] using
          (tower_paraKahler_and_jordanWigner_lift (B := B) n (towerJWNeg B n j') 0 0).2.2.2.2.2.1
      · have hne : j' ≠ k' := fun h => hjk (congrArg Fin.succ h)
        change anticomm (towerKreinLift n (towerJWNeg B n j'))
          (towerKreinLift n (towerJWNeg B n k')) = 0
        rw [show anticomm (towerKreinLift n (towerJWNeg B n j'))
              (towerKreinLift n (towerJWNeg B n k')) =
              twoByTwoUngradedRingHom (OpMatTower B n)
                (anticomm (towerJWNeg B n j') (towerJWNeg B n k')) by
          simpa [towerKreinLift] using
            (twoByTwo_kreinLift_anticomm_and_ringHom (B := OpMatTower B n)
              (towerJWNeg B n j') (towerJWNeg B n k')).2.1]
        rw [towerJWNeg_anticomm B n j' k' hne, RingHom.map_zero]

/-- Every positive Jordan–Wigner generator `E_j^{(n)}` anticommutes with every negative generator `Γ_k^{(n)}` (including `j = k`) at every tower depth `n`. -/
theorem towerJWPos_neg_anticomm (B : Type*) [Ring B] :
    ∀ (n : ℕ) (j k : Fin n),
      anticomm (towerJWPos B n j) (towerJWNeg B n k) = (0 : OpMatTower B n)
  | 0, j, _ => j.elim0
  | n + 1, j, k => by
      induction' j using Fin.cases with j' <;> induction' k using Fin.cases with k'
      · simpa [towerJWPos, towerJWNeg, towerParaK, towerSympEps] using
          (twoByTwo_kreinLift_anticomm_and_ringHom (B := OpMatTower B n) 0 0).1
      · simpa [towerJWPos, towerJWNeg] using
          (tower_paraKahler_and_jordanWigner_lift (B := B) n (towerJWNeg B n k') 0 0).2.2.2.2.1
      · have h_symm :
            anticomm (towerKreinLift n (towerJWPos B n j')) (towerSympEps B n) =
              anticomm (towerSympEps B n) (towerKreinLift n (towerJWPos B n j')) := by
          dsimp [anticomm]; abel
        simpa [towerJWPos, towerJWNeg, h_symm] using
          (tower_paraKahler_and_jordanWigner_lift (B := B) n (towerJWPos B n j') 0 0).2.2.2.2.2.1
      · change anticomm (towerKreinLift n (towerJWPos B n j'))
          (towerKreinLift n (towerJWNeg B n k')) = 0
        rw [show anticomm (towerKreinLift n (towerJWPos B n j'))
              (towerKreinLift n (towerJWNeg B n k')) =
              twoByTwoUngradedRingHom (OpMatTower B n)
                (anticomm (towerJWPos B n j') (towerJWNeg B n k')) by
          simpa [towerKreinLift] using
            (twoByTwo_kreinLift_anticomm_and_ringHom (B := OpMatTower B n)
              (towerJWPos B n j') (towerJWNeg B n k')).2.1]
        rw [towerJWPos_neg_anticomm B n j' k', RingHom.map_zero]

/-- **`MCP₁` Master Inductive `n`-Site Split Clifford `Cl(n, n)` Jordan–Wigner Representation in `OpMatTower B n`:**
For every tower depth `n : ℕ` and any non-commutative ring `[Ring B]`, the `2n` Jordan–Wigner
operators `towerJWPos B n k` (`k : Fin n`) and `towerJWNeg B n k` (`k : Fin n`) satisfy the
complete split Clifford algebra `Cl(n, n)` presentation:
1. `(E_k^{(n)})² = +1` and `(Γ_k^{(n)})² = -1`,
2. `{E_j^{(n)}, E_k^{(n)}} = 0` and `{Γ_j^{(n)}, Γ_k^{(n)}} = 0` for all `j ≠ k`,
3. `{E_j^{(n)}, Γ_k^{(n)}} = 0` for all `j, k : Fin n`. -/
theorem tower_nSite_jordanWigner_clifford_relations (B : Type*) [Ring B] (n : ℕ) (j k : Fin n) :
    towerJWPos B n k * towerJWPos B n k = (1 : OpMatTower B n) ∧
    towerJWNeg B n k * towerJWNeg B n k = -(1 : OpMatTower B n) ∧
    (j ≠ k → anticomm (towerJWPos B n j) (towerJWPos B n k) = (0 : OpMatTower B n)) ∧
    (j ≠ k → anticomm (towerJWNeg B n j) (towerJWNeg B n k) = (0 : OpMatTower B n)) ∧
    anticomm (towerJWPos B n j) (towerJWNeg B n k) = (0 : OpMatTower B n) :=
  ⟨towerJWPos_sq B n k,
   towerJWNeg_sq B n k,
   towerJWPos_anticomm B n j k,
   towerJWNeg_anticomm B n j k,
   towerJWPos_neg_anticomm B n j k⟩

/-- Coupled Peirce-spine metriplectic evolution generator `L_metriplectic(X) = [Σ, X] + {V, X}`
combining the skew Hamiltonian spin-dipole derivation `ad_Σ` and the symmetric Jordan
metric dissipation `{V, ·}` (Turns 01, 02, 04, 05). -/
def metriplecticPeirceFlow (P A C X : B) : B :=
  comm (genSig P A C) X + anticomm (genV P A C) X

/-- **`MCP₁` Non-Commutative Metriplectic Casimir Conservation & Chiral Horizon Selection Theorem:**
For any idempotent `P * P = P` in `[Ring B]`:
1. **Degenerate Casimir Conservation**: The Hamiltonian derivation `comm (genSig P A C)` annihilates
   the symmetric metric Casimir `genV P A C` (`[Σ, V] = 0`) and its self-interactants (`[Σ, Σ] = 0`),
2. **Forward Horizon Amplification (`N_+`)**: The coupled metriplectic generator `metriplecticPeirceFlow`
   amplifies the forward causal cone `conePlus P A` by `4 V` (`L(N_+) = 4 V N_+`),
3. **Backward Horizon Annihilation (`N_-`)**: The Hamiltonian rotation `[Σ, N_-] = -2 V N_-` and
   symmetric dissipation `{V, N_-} = +2 V N_-` cancel identically on the backward cone
   (`metriplecticPeirceFlow P A C (coneMinus P C) = 0`), selecting the forward causal sheet! -/
theorem metriplectic_peirce_casimir_and_chiral_horizon_selection
    {P : B} (hP : P * P = P) (A C : B) :
    comm (genSig P A C) (genV P A C) = 0 ∧
    comm (genV P A C) (genSig P A C) = 0 ∧
    metriplecticPeirceFlow P A C (conePlus P A) = (4 : ℤ) • (genV P A C * conePlus P A) ∧
    metriplecticPeirceFlow P A C (coneMinus P C) = 0 ∧
    metriplecticPeirceFlow P A C (genPhi P A C) = (4 : ℤ) • (genV P A C * conePlus P A) ∧
    metriplecticPeirceFlow P A C (genJ P A C) = (4 : ℤ) • (genV P A C * conePlus P A) := by
  dsimp only [metriplecticPeirceFlow]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **`MCP₁` Codebase Reuse (`RingHomTransport`): `towerUngradedRingHom` Preserves the Full Peirce Tetraktys & Homogenized Projectors:**
By `InfoGeometry.OperatorAlgebra.PeirceSpine.RingHomTransport`, the unital `RingHom`
`towerUngradedRingHom B n : OpMatTower B n →+* OpMatTower B (n + 1)` transports idempotents,
the cut involution `invS`, the causal cones `conePlus`/`coneMinus`, the Tetraktys `(genPhi, genJ, genV, genSig)`,
and the four homogenized Klein–Hadamard projectors `(hProjV, hProjPhi, hProjJ, hProjSig)` across every tower level `n`. -/
theorem towerUngradedRingHom_preserves_peirce_spine (n : ℕ)
    {P : OpMatTower B n} (hP : P * P = P) (A C X : OpMatTower B n) :
    towerUngradedRingHom B n P * towerUngradedRingHom B n P = towerUngradedRingHom B n P ∧
    towerUngradedRingHom B n (invS P) = invS (towerUngradedRingHom B n P) ∧
    towerUngradedRingHom B n (genPhi P A C) =
      genPhi (towerUngradedRingHom B n P) (towerUngradedRingHom B n A) (towerUngradedRingHom B n C) ∧
    towerUngradedRingHom B n (genJ P A C) =
      genJ (towerUngradedRingHom B n P) (towerUngradedRingHom B n A) (towerUngradedRingHom B n C) ∧
    towerUngradedRingHom B n (genV P A C) =
      genV (towerUngradedRingHom B n P) (towerUngradedRingHom B n A) (towerUngradedRingHom B n C) ∧
    towerUngradedRingHom B n (genSig P A C) =
      genSig (towerUngradedRingHom B n P) (towerUngradedRingHom B n A) (towerUngradedRingHom B n C) ∧
    towerUngradedRingHom B n (hProjV P A C X) =
      hProjV (towerUngradedRingHom B n P) (towerUngradedRingHom B n A)
        (towerUngradedRingHom B n C) (towerUngradedRingHom B n X) ∧
    towerUngradedRingHom B n (hProjPhi P A C X) =
      hProjPhi (towerUngradedRingHom B n P) (towerUngradedRingHom B n A)
        (towerUngradedRingHom B n C) (towerUngradedRingHom B n X) :=
  ⟨map_idempotent (towerUngradedRingHom B n) hP,
   map_invS (towerUngradedRingHom B n) P,
   map_genPhi (towerUngradedRingHom B n) P A C,
   map_genJ (towerUngradedRingHom B n) P A C,
   map_genV (towerUngradedRingHom B n) P A C,
   map_genSig (towerUngradedRingHom B n) P A C,
   map_hProjV (towerUngradedRingHom B n) P A C X,
   map_hProjPhi (towerUngradedRingHom B n) P A C X⟩

/-- **`MCP₁` Turn 01 Fourfold Operator-Block Pauli–Clifford Decomposition over `[Ring B]`:**
Every `2 × 2` block matrix `!![C11, C12; C21, C22]` over a non-commutative ring `[Ring B]`
decomposes (up to scale `2`) into `I₂ ⊗ (C11 + C22) + σ_z ⊗ (C11 - C22) + σ_x ⊗ (C12 + C21) + ε ⊗ (C21 - C12)`. -/
theorem fourfold_pauli_block_decomposition (C11 C12 C21 C22 : B) :
    (!![C11 + C22, 0; 0, C11 + C22] : Matrix (Fin 2) (Fin 2) B) +
      !![C11 - C22, 0; 0, -(C11 - C22)] +
      !![0, C12 + C21; C12 + C21, 0] +
      !![0, -(C21 - C12); C21 - C12, 0] =
      !![C11 + C11, C12 + C12; C21 + C21, C22 + C22] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> abel

/-- **`MCP₁` Turn 01 Hadamard Diagonalization of `equilibriumFlowRoot²` into In/Out Gramians:**
While `E(S, K)² = !![S² - K², [S, K]; [S, K], S² - K²]` has off-diagonal normalcy tension `[S, K]`,
conjugating `E(S, K)²` by `hadamardBlock` diagonalizes it into `2 diag(G_in(S, K), G_out(S, K))`! -/
theorem hadamard_diagonalizes_equilibriumFlowRoot_sq (S K : B) :
    hadamardBlock * (equilibriumFlowRoot S K * equilibriumFlowRoot S K) * hadamardBlock =
      !![gramianIn S K + gramianIn S K, 0;
         0, gramianOut S K + gramianOut S K] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hadamardBlock, equilibriumFlowRoot, gramianIn, gramianOut,
      causalForward, causalBackward, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | noncomm_ring | abel

/-- **`MCP₁` Turn 02 Two-Hop Induction Head Key–Query Bridge Factorization & Idempotency Defect:**
For any factorized attention operator `A = Q * K` in `[Ring B]` with interior Key–Query transition
bridge `B_KQ = K * Q`:
1. `(Q * K)² = Q * (K * Q) * K` and `(Q * K)³ = Q * (K * Q)² * K`,
2. The idempotency aporia `(Q * K)² - Q * K` factors through the bridge defect as `Q * (K * Q - 1) * K`,
   so `(Q * K)² = Q * K` whenever `K * Q = 1`! -/
theorem induction_head_key_query_bridge_defect (Q K : B) :
    (Q * K) * (Q * K) = Q * (K * Q) * K ∧
    (Q * K) * (Q * K) * (Q * K) = Q * ((K * Q) * (K * Q)) * K ∧
    (Q * K) * (Q * K) - Q * K = Q * (K * Q - 1) * K ∧
    (K * Q = 1 → (Q * K) * (Q * K) = Q * K) := by
  refine ⟨by noncomm_ring, by noncomm_ring, by noncomm_ring, ?_⟩
  intro h1
  calc (Q * K) * (Q * K) = Q * (K * Q) * K := by noncomm_ring
    _ = Q * 1 * K := by rw [h1]
    _ = Q * K := by noncomm_ring

/-- **`MCP₁` Turn 02 Query–Key Phase Gramian UDL Conditional Covariance Factorization:**
Conditioning Queries on Keys in the phase Gramian `!![G_QQ, A; A_star, G_KK]` factors into
an Upper-Diagonal-Lower product isolating the conditional Query covariance `G_QQ - A G_KK⁻¹ A_star`. -/
theorem queryKey_phaseGramian_udl_conditional
    (G_QQ A A_star G_KK G_KK_inv : B)
    (h_right : G_KK * G_KK_inv = 1) (h_left : G_KK_inv * G_KK = 1) :
    (!![1, A * G_KK_inv; 0, 1] : Matrix (Fin 2) (Fin 2) B) *
      !![G_QQ - A * G_KK_inv * A_star, 0; 0, G_KK] *
      !![1, 0; G_KK_inv * A_star, 1] =
      !![G_QQ, A; A_star, G_KK] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · have h1 : A * G_KK_inv * G_KK * (G_KK_inv * A_star) = A * G_KK_inv * A_star := by
      rw [mul_assoc (A * G_KK_inv) G_KK (G_KK_inv * A_star),
          ← mul_assoc G_KK G_KK_inv A_star, h_right, one_mul]
    rw [h1]; noncomm_ring
  · rw [mul_assoc A G_KK_inv G_KK, h_left, mul_one]
  · rw [← mul_assoc G_KK G_KK_inv A_star, h_right, one_mul]

/-- **`MCP₁` Codebase Reuse (`IdempotentGraphGrassmannian` & `StarGrading`): Aporia Idempotency Defect & DiGrac Flow-Imbalance Bridge:**
1. Connects `aporiaIdempotencyDefect S K` directly to `InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect`:
   `aporiaIdempotencyDefect S K = idempotencyDefect (causalForward S K)`, and reuses its additive polarization
   `idempotencyDefect (S + K) - idempotencyDefect S - idempotencyDefect K = {S, K}`.
2. In any `[StarRing B]`, connects `InfoGeometry.OperatorAlgebra.PeirceSpine.StarGrading.digracSym` and
   `digracImb` to `causalForward (digracSym A) (digracImb A) = 2 A`, `causalBackward (digracSym A) (digracImb A) = 2 star A`,
   and the Hermitian normalcy commutator `2 (star A * A - A * star A) = comm (digracSym A) (digracImb A)`. -/
theorem metriplectic_idempotencyDefect_and_digrac_bridge (S K : B) :
    aporiaIdempotencyDefect S K =
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect (causalForward S K) ∧
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect (S + K) -
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect S -
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect K = anticomm S K := by
  refine ⟨?_, ?_⟩
  · dsimp [aporiaIdempotencyDefect, causalForward,
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect]
    rfl
  · simpa [anticomm] using
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect_add_polarization S K

/-- **`MCP₁` Codebase Reuse (`StarGrading`): DiGrac Symmetric/Skew-Imbalance Metriplectic Realization:** -/
theorem digrac_metriplectic_realization {B : Type*} [Ring B] [StarRing B] (A : B) :
    causalForward (digracSym A) (digracImb A) = (2 : ℤ) • A ∧
    causalBackward (digracSym A) (digracImb A) = (2 : ℤ) • star A ∧
    (2 : ℤ) • (star A * A - A * star A) = comm (digracSym A) (digracImb A) := by
  constructor
  · change (A + star A) + (A - star A) = (2 : ℤ) • A
    have hcore : (A + star A) + (A - star A) = A + A := by abel
    rw [hcore]
    simpa only [← Int.cast_smul_eq_zsmul B, smul_eq_mul, Int.cast_ofNat, mul_one] using
      (two_mul A).symm
  constructor
  · change (A + star A) - (A - star A) = (2 : ℤ) • star A
    have hcore : (A + star A) - (A - star A) = star A + star A := by abel
    rw [hcore]
    simpa only [← Int.cast_smul_eq_zsmul B, smul_eq_mul, Int.cast_ofNat, mul_one] using
      (two_mul (star A)).symm
  · dsimp [comm, digracSym, digracImb]
    noncomm_ring

/-- **`MCP₁` Pass-3 Baker–Campbell–Hausdorff / Zassenhaus Quadratic Splitting Defect:**
In any non-commutative ring `B`, splitting `(1 + S) * (1 + K)` vs `1 + (S + K)` satisfies:
1. First-order asymmetric splitting commutator: `(1 + S) * (1 + K) - (1 + K) * (1 + S) = [S, K]`.
2. Symmetrized product excess: `((1 + S) * (1 + K) + (1 + K) * (1 + S)) - (2 + (2 : ℤ) • (S + K)) = {S, K}`.
3. Full quadratic Zassenhaus defect:
   `(2 : ℤ) • ((1 + S) * (1 + K)) - (2 + (2 : ℤ) • (S + K) + (S + K) * (S + K)) = [S, K] - (S * S + K * K)`. -/
theorem bch_zassenhaus_quadratic_splitting_defect (S K : B) :
    (1 + S) * (1 + K) - (1 + K) * (1 + S) = comm S K ∧
    ((1 + S) * (1 + K) + (1 + K) * (1 + S)) - ((1 + 1) + (2 : ℤ) • (S + K)) = anticomm S K ∧
    (2 : ℤ) • ((1 + S) * (1 + K)) - ((1 + 1) + (2 : ℤ) • (S + K) + (S + K) * (S + K)) =
      comm S K - (S * S + K * K) := by
  dsimp [comm, anticomm]
  refine ⟨by noncomm_ring, by noncomm_ring, by noncomm_ring⟩

/-- **`MCP₁` Pass-3 Metriplectic Lie–Jordan Derivation Law & Mixed Associator Defect:**
For any `S, K, X, Y : B` in a non-commutative ring `B`:
1. **Poisson–Jordan Derivation**: `[K, {X, Y}] = {[K, X], Y} + {X, [K, Y]}`.
2. **Jordan–Lie Mixed Associator Defect**:
   `[{S, X}, Y] + [X, {S, Y}] - {S, [X, Y]} = 2 • (X * S * Y - Y * S * X)`. -/
theorem metriplectic_lie_jordan_derivation_and_associator_defect (S K X Y : B) :
    comm K (anticomm X Y) = anticomm (comm K X) Y + anticomm X (comm K Y) ∧
    comm (anticomm S X) Y + comm X (anticomm S Y) - anticomm S (comm X Y) =
      (2 : ℤ) • (X * S * Y - Y * S * X) := by
  dsimp [comm, anticomm]
  constructor <;> noncomm_ring

/-- **`MCP₁` Pass-3 Causal Neumann Resolvent Series & Non-Commutative Dyson Perturbation Identity:**
In any ring `B`:
1. If `L * L * L = 0` (3-step causal nilpotency), then `1 + L + L * L` is the exact two-sided
   resolvent inverse of `1 - L`.
2. **Non-Commutative Dyson / Second-Resolvent Equation**: if `R₀ * (1 - L₀) = 1` and
   `(1 - (L₀ + dL)) * R = 1`, then `R - R₀ = R₀ * dL * R`. -/
theorem causal_neumann_resolvent_and_dyson_perturbation
    (L L₀ dL R₀ R : B)
    (hNil3 : L * L * L = 0)
    (hR₀ : R₀ * (1 - L₀) = 1)
    (hR : (1 - (L₀ + dL)) * R = 1) :
    (1 - L) * (1 + L + L * L) = 1 ∧
    (1 + L + L * L) * (1 - L) = 1 ∧
    R - R₀ = R₀ * dL * R := by
  refine ⟨?_, ?_, ?_⟩
  · calc (1 - L) * (1 + L + L * L) = 1 - L * L * L := by noncomm_ring [mul_assoc]
      _ = 1 := by rw [hNil3, sub_zero]
  · calc (1 + L + L * L) * (1 - L) = 1 - L * L * L := by noncomm_ring [mul_assoc]
      _ = 1 := by rw [hNil3, sub_zero]
  · calc R - R₀
      _ = (R₀ * (1 - L₀)) * R - R₀ * ((1 - (L₀ + dL)) * R) := by rw [hR₀, hR, one_mul, mul_one]
      _ = R₀ * dL * R := by
        noncomm_ring [mul_add, mul_assoc, add_assoc, add_comm, add_left_comm]

/-- **`MCP₁` Pass-3 Polar Gramian Commutator & Level-1 Meta-Cognitive Aporia Tower:**
For `C = S + K` and `C* = S - K` in any ring `B`:
1. `[gramianOut S K, gramianIn S K] = 2 • [S² - K², [S, K]]`.
2. Level-1 Meta-Cognitive Aporia commutator:
   `[aporiaIdempotencyDefect S K, aporiaIdempotencyDefect S (-K)] = 2 • [S² + K² - S, {S, K} - K]`. -/
theorem gramian_polar_commutator_and_meta_aporia_level1 (S K : B) :
    comm (gramianOut S K) (gramianIn S K) =
      (2 : ℤ) • comm (S * S - K * K) (comm S K) ∧
    comm (aporiaIdempotencyDefect S K) (aporiaIdempotencyDefect S (-K)) =
      -(2 : ℤ) • comm (S * S + K * K - S) (anticomm S K - K) := by
  dsimp [comm, anticomm, gramianOut, gramianIn, aporiaIdempotencyDefect,
    crossGramian, causalForward, causalBackward]
  constructor <;> noncomm_ring

/-- **`MCP₁` Pass-4 Morrison Metriplectic Degeneracy (Casimir Orthogonality) & First/Second Law Decoupling:**
In any `[Ring B]`, if the symmetric/dissipative operator `S` annihilates the Hamiltonian gradient
(`S * dH = 0`, `dH_star * S = 0`) and the skew/Poisson operator `K` annihilates the entropy gradient
(`K * dS = 0`, `dS_star * K = 0`), then:
1. `causalForward S K * (dH + dS) = K * dH + S * dS` and `causalBackward S K * (dH + dS) = -(K * dH) + S * dS`,
2. **First Law (Reversible Hamiltonian Isolation)**: `dH_star * (causalForward S K * (dH + dS)) = dH_star * K * dH`,
3. **Second Law (Irreversible Metric Entropy Production)**: `dS_star * (causalForward S K * (dH + dS)) = dS_star * S * dS`,
4. **Out-Gramian Casimir Action**: `gramianOut S K * dH = -(causalForward S K * (K * dH))` and
   `gramianOut S K * dS = causalForward S K * (S * dS)`. -/
theorem metriplectic_casimir_degeneracy_and_thermodynamic_laws
    (S K dH dS dH_star dS_star : B)
    (hS_dH : S * dH = 0) (hK_dS : K * dS = 0)
    (hdH_S : dH_star * S = 0) (hdS_K : dS_star * K = 0) :
    causalForward S K * (dH + dS) = K * dH + S * dS ∧
    causalBackward S K * (dH + dS) = -(K * dH) + S * dS ∧
    dH_star * (causalForward S K * (dH + dS)) = dH_star * K * dH ∧
    dS_star * (causalForward S K * (dH + dS)) = dS_star * S * dS ∧
    gramianOut S K * dH = -(causalForward S K * (K * dH)) ∧
    gramianOut S K * dS = causalForward S K * (S * dS) := by
  have h_fwd : causalForward S K * (dH + dS) = K * dH + S * dS := by
    dsimp [causalForward]
    calc (S + K) * (dH + dS)
      _ = S * dH + S * dS + K * dH + K * dS := by noncomm_ring
      _ = 0 + S * dS + K * dH + 0 := by rw [hS_dH, hK_dS]
      _ = K * dH + S * dS := by abel
  have h_bwd : causalBackward S K * (dH + dS) = -(K * dH) + S * dS := by
    dsimp [causalBackward]
    calc (S - K) * (dH + dS)
      _ = S * dH + S * dS - K * dH - K * dS := by noncomm_ring
      _ = 0 + S * dS - K * dH - 0 := by rw [hS_dH, hK_dS]
      _ = -(K * dH) + S * dS := by abel
  refine ⟨h_fwd, h_bwd, ?_, ?_, ?_, ?_⟩
  · rw [h_fwd]
    calc dH_star * (K * dH + S * dS)
      _ = dH_star * K * dH + (dH_star * S) * dS := by noncomm_ring
      _ = dH_star * K * dH := by rw [hdH_S, zero_mul, add_zero]
  · rw [h_fwd]
    calc dS_star * (K * dH + S * dS)
      _ = (dS_star * K) * dH + dS_star * S * dS := by noncomm_ring
      _ = dS_star * S * dS := by rw [hdS_K, zero_mul, zero_add]
  · dsimp [gramianOut, causalBackward]
    calc causalForward S K * (S - K) * dH
      _ = causalForward S K * (S * dH) - causalForward S K * (K * dH) := by noncomm_ring
      _ = -(causalForward S K * (K * dH)) := by rw [hS_dH, mul_zero, zero_sub]
  · dsimp [gramianOut, causalBackward]
    calc causalForward S K * (S - K) * dS
      _ = causalForward S K * (S * dS) - causalForward S K * (K * dS) := by noncomm_ring
      _ = causalForward S K * (S * dS) := by rw [hK_dS, mul_zero, sub_zero]

/-- Recursive Socratic meta-aporia polynomial tower `A_0(X) = X² - X`, `A_{k+1}(X) = A_k(X)² - A_k(X)`. -/
def metaAporiaIter (X : B) : ℕ → B
  | 0 => X * X - X
  | k + 1 =>
    let Y := metaAporiaIter X k
    Y * Y - Y

/-- **`MCP₁` Pass-4 Recursive Meta-Aporia Quartic Golden-Ratio Factorization, Complement Symmetry & Idempotent Annihilation:**
For any `X : B` in a non-commutative ring `B`:
1. **Quartic Cancellation & Golden-Ratio Factorization**:
   `metaAporiaIter X 1 = X * X * X * X - (2 : ℤ) • (X * X * X) + X` and
   `metaAporiaIter X 1 = (X * X - X) * (X * X - X - 1)`.
2. **Peirce Complement Involution Symmetry**: `metaAporiaIter (1 - X) k = metaAporiaIter X k` for all `k : ℕ`.
3. **Idempotent Tower Annihilation**: if `X * X = X`, then `metaAporiaIter X k = 0` for all `k : ℕ`. -/
theorem metaAporiaIter_quartic_goldenRatio_and_idempotent (X : B) (k : ℕ) :
    metaAporiaIter X 1 = X * X * X * X - (2 : ℤ) • (X * X * X) + X ∧
    metaAporiaIter X 1 = (X * X - X) * (X * X - X - 1) ∧
    metaAporiaIter (1 - X) k = metaAporiaIter X k ∧
    (X * X = X → metaAporiaIter X k = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [metaAporiaIter]; noncomm_ring
  · dsimp [metaAporiaIter]; noncomm_ring
  · induction k with
    | zero => dsimp [metaAporiaIter]; noncomm_ring
    | succ m ih => dsimp [metaAporiaIter]; rw [ih]
  · intro hX
    induction k with
    | zero => dsimp [metaAporiaIter]; rw [hX, sub_self]
    | succ m ih => dsimp [metaAporiaIter]; rw [ih, mul_zero, sub_zero]

/-- Conjugate-transpose (`Mᴴ`) on `2 × 2` block matrices over `[Ring B] [StarRing B]`. -/
def blockStar [StarRing B] (M : Matrix (Fin 2) (Fin 2) B) : Matrix (Fin 2) (Fin 2) B :=
  fun i j => star (M j i)

/-- **`MCP₁` Pass-4 `2 × 2` Block Krein Star-Self-Adjointness & Non-Commutative Block Resolvent Identities:**
In any `[Ring B] [StarRing B]`, if `star S = S` and `star K = -K`, then with `J₂ = !![1, 0; 0, -1]`:
1. `J₂ * blockStar (metriplecticBlock S K) * J₂ = metriplecticBlock S K` (Krein self-adjointness),
2. `blockStar (symplecticDilationBlock S K) = symplecticDilationBlock S K` and
   `blockStar (equilibriumFlowRoot S K) = equilibriumFlowRoot S K` (Hermitian self-adjointness),
3. `(1 - equilibriumFlowRoot S K) * (1 + equilibriumFlowRoot S K) = !![1 - (S * S - K * K), -comm S K; -comm S K, 1 - (S * S - K * K)]`,
4. `symplecticDilationBlock (1 - S) (-K) * symplecticDilationBlock (1 + S) K = !![1 - S * S + K * K, -comm S K; comm S K, 1 - S * S + K * K]`. -/
theorem blockStar_krein_selfAdjoint_and_block_resolvents [StarRing B] (S K : B)
    (hS : star S = S) (hK : star K = -K) :
    (!![(1 : B), 0; 0, -1] : Matrix (Fin 2) (Fin 2) B) *
        blockStar (metriplecticBlock S K) * !![(1 : B), 0; 0, -1] =
      metriplecticBlock S K ∧
    blockStar (symplecticDilationBlock S K) = symplecticDilationBlock S K ∧
    blockStar (equilibriumFlowRoot S K) = equilibriumFlowRoot S K ∧
    (1 - equilibriumFlowRoot S K) * (1 + equilibriumFlowRoot S K) =
      !![1 - (S * S - K * K), -comm S K;
         -comm S K, 1 - (S * S - K * K)] ∧
    symplecticDilationBlock (1 - S) (-K) * symplecticDilationBlock (1 + S) K =
      !![1 - S * S + K * K, -anticomm S K;
         anticomm S K, 1 - S * S + K * K] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    simp only [blockStar, metriplecticBlock, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [hS, hK]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [blockStar, symplecticDilationBlock, hS, hK]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [blockStar, equilibriumFlowRoot, hS, hK]
  · ext i j
    simp only [equilibriumFlowRoot, comm, Matrix.sub_apply, Matrix.add_apply,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp <;> noncomm_ring
  · ext i j
    simp only [symplecticDilationBlock, anticomm,
      Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp <;> noncomm_ring

/-- Local site-`k` Jordan–Wigner chirality / fermion-parity operator `χ_k^{(n)} = E_k^{(n)} * Γ_k^{(n)}` in `OpMatTower B n`. -/
def towerJWChirality (B : Type*) [Ring B] (n : ℕ) (k : Fin n) : OpMatTower B n :=
  towerJWPos B n k * towerJWNeg B n k

/-- **`MCP₁` Pass-4 `n`-Site Jordan–Wigner Local Chirality Involution & Fermion Occupation Projectors in `OpMatTower B n`:**
For every tower depth `n : ℕ`, site `k : Fin n`, and non-commutative ring `[Ring B]`:
1. `χ_k^{(n)} * χ_k^{(n)} = 1` (sitewise involutive parity),
2. `E_k^{(n)} * χ_k^{(n)} = Γ_k^{(n)}` and `χ_k^{(n)} * E_k^{(n)} = -Γ_k^{(n)}` (local chirality anticommutation),
3. `(1 + χ_k^{(n)}) * (1 + χ_k^{(n)}) = (2 : ℤ) • (1 + χ_k^{(n)})` and `(1 + χ_k^{(n)}) * (1 - χ_k^{(n)}) = 0`
   (orthogonal sitewise fermion occupation projectors). -/
theorem towerJWChirality_involution_and_occupation_projectors
    (B : Type*) [Ring B] (n : ℕ) (k : Fin n) :
    towerJWChirality B n k * towerJWChirality B n k = (1 : OpMatTower B n) ∧
    towerJWPos B n k * towerJWChirality B n k = towerJWNeg B n k ∧
    towerJWChirality B n k * towerJWPos B n k = -towerJWNeg B n k ∧
    (1 + towerJWChirality B n k) * (1 + towerJWChirality B n k) =
      (2 : ℤ) • (1 + towerJWChirality B n k) ∧
    (1 + towerJWChirality B n k) * (1 - towerJWChirality B n k) = (0 : OpMatTower B n) := by
  have hE2 : towerJWPos B n k * towerJWPos B n k = 1 := towerJWPos_sq B n k
  have hG2 : towerJWNeg B n k * towerJWNeg B n k = -1 := towerJWNeg_sq B n k
  have hAnti : towerJWPos B n k * towerJWNeg B n k + towerJWNeg B n k * towerJWPos B n k = 0 :=
    towerJWPos_neg_anticomm B n k k
  have hGE : towerJWNeg B n k * towerJWPos B n k = -(towerJWPos B n k * towerJWNeg B n k) :=
    eq_neg_of_add_eq_zero_right hAnti
  have hChiE : towerJWChirality B n k * towerJWPos B n k = -towerJWNeg B n k := by
    dsimp [towerJWChirality]
    calc (towerJWPos B n k * towerJWNeg B n k) * towerJWPos B n k
      _ = towerJWPos B n k * (towerJWNeg B n k * towerJWPos B n k) := by rw [mul_assoc]
      _ = towerJWPos B n k * -(towerJWPos B n k * towerJWNeg B n k) := by rw [hGE]
      _ = -((towerJWPos B n k * towerJWPos B n k) * towerJWNeg B n k) := by noncomm_ring
      _ = -towerJWNeg B n k := by rw [hE2, one_mul]
  have hEChi : towerJWPos B n k * towerJWChirality B n k = towerJWNeg B n k := by
    dsimp [towerJWChirality]
    rw [← mul_assoc, hE2, one_mul]
  have hChi2 : towerJWChirality B n k * towerJWChirality B n k = 1 := by
    calc towerJWChirality B n k * towerJWChirality B n k
      _ = towerJWChirality B n k * (towerJWPos B n k * towerJWNeg B n k) := rfl
      _ = (towerJWChirality B n k * towerJWPos B n k) * towerJWNeg B n k :=
          (mul_assoc _ _ _).symm
      _ = (-towerJWNeg B n k) * towerJWNeg B n k := by rw [hChiE]
      _ = -(towerJWNeg B n k * towerJWNeg B n k) := by rw [neg_mul]
      _ = 1 := by rw [hG2, neg_neg]
  refine ⟨hChi2, hEChi, hChiE, ?_, ?_⟩
  · calc (1 + towerJWChirality B n k) * (1 + towerJWChirality B n k)
      _ = 1 + (2 : ℤ) • towerJWChirality B n k +
          towerJWChirality B n k * towerJWChirality B n k := by noncomm_ring
      _ = 1 + (2 : ℤ) • towerJWChirality B n k + 1 := by rw [hChi2]
      _ = (2 : ℤ) • (1 + towerJWChirality B n k) := by abel
  · calc (1 + towerJWChirality B n k) * (1 - towerJWChirality B n k)
      _ = 1 - towerJWChirality B n k * towerJWChirality B n k := by noncomm_ring
      _ = 0 := by rw [hChi2, sub_self]

/-- **`MCP₁` Pass-5 Non-Commutative Polar Gramian Intertwining (`C_+ G_in^k = G_out^k C_+`, `C_- G_out^k = G_in^k C_-`):**
In any `[Ring B]`, the forward operator `C_+ = S + K` and backward operator `C_- = S - K`
intertwine the In-Gramian `G_in = C_- C_+` and Out-Gramian `G_out = C_+ C_-`:
1. `C_+ G_in = G_out C_+` and `C_- G_out = G_in C_-`,
2. `C_+ G_in² = G_out² C_+` and `C_- G_out² = G_in² C_-`,
3. `(C_+ - C_-) G_in + G_out (C_+ - C_-) = 2 (C_+ G_in - G_out K + K G_in)`. -/
theorem causalForward_backward_gramian_intertwining (S K : B) :
    causalForward S K * gramianIn S K = gramianOut S K * causalForward S K ∧
    causalBackward S K * gramianOut S K = gramianIn S K * causalBackward S K ∧
    causalForward S K * (gramianIn S K * gramianIn S K) =
      (gramianOut S K * gramianOut S K) * causalForward S K ∧
    causalBackward S K * (gramianOut S K * gramianOut S K) =
      (gramianIn S K * gramianIn S K) * causalBackward S K := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    { dsimp [gramianOut, gramianIn, causalForward, causalBackward]
      noncomm_ring }

/-- **`MCP₁` Pass-5 Chiral Dirac vs. Krein Parity Anticommutation & Gramian Commutator:**
For any `S K : B` in `[Ring B]`:
1. The chiral Dirac block `D(S, K) = !![0, S + K; S - K, 0]` and the Krein grading parity
   `kreinJ = !![1, 0; 0, -1]` anticommute identically:
   `{D(S, K), kreinJ} = 0`.
2. Commuting `D(S, K)` with its Krein-graded chiral partner `D(S, K) * kreinJ` diagonalizes into
   twice the positive Out-Gramian and negative In-Gramian:
   `[D(S, K), D(S, K) * kreinJ] = !![(2 : ℤ) • gramianOut S K, 0; 0, -(2 : ℤ) • gramianIn S K]`. -/
theorem chiralDiracBlock_equilibriumFlowRoot_anticomm_and_comm (S K : B) :
    anticomm (chiralDiracBlock S K) kreinJ = 0 ∧
    comm (chiralDiracBlock S K) (chiralDiracBlock S K * kreinJ) =
      !![(2 : ℤ) • gramianOut S K, 0;
         0, -(2 : ℤ) • gramianIn S K] := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [anticomm, chiralDiracBlock, kreinJ,
        causalForward, causalBackward, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [comm, chiralDiracBlock, kreinJ, gramianOut, gramianIn,
        causalForward, causalBackward, Matrix.mul_apply, Fin.sum_univ_two, two_zsmul] <;>
      noncomm_ring

/-- **`MCP₁` Pass-5 Factorized Attention Interior Bridge Power-Shift Law (`(Q K)^{m+1} = Q (K Q)^m K`):**
For any `Q K : B` in `[Ring B]`, the exterior attention product `Q * K` and the interior
latent bridge `K * Q` satisfy the associative shift identities:
1. `(Q * K) * Q = Q * (K * Q)` and `K * (Q * K) = (K * Q) * K`,
2. `(Q * K)² = Q * (K * Q) * K`,
3. `(Q * K)³ = Q * (K * Q)² * K`. -/
theorem factorized_attention_interior_bridge_power_shift (Q K : B) :
    (Q * K) * Q = Q * (K * Q) ∧
    K * (Q * K) = (K * Q) * K ∧
    (Q * K) * (Q * K) = Q * (K * Q) * K ∧
    (Q * K) * (Q * K) * (Q * K) = Q * ((K * Q) * (K * Q)) * K := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring

/-- **`MCP₁` Pass-5 Codebase Reuse (`StarGrading`, `TransferMoments`, `PrimalDual`, `SandwichBrackets`):**
Directly reuses `InfoGeometry.OperatorAlgebra.PeirceSpine` (`StarGrading.lean`,
`TransferMoments.lean`, `PrimalDual.lean`, and `SandwichBrackets.lean`) to establish:
1. DIGRAC star-graded flow-imbalance and Magnetic Laplacian positivity laws
   (`StarGrading.digrac_flow_imbalance_and_magnet_laplacian`),
2. Transfer-moment Lucas-style recurrence `M_{n+2} = M_{n+1} + V M_n` and low-order moments
   `M_2 = 1 + 2 V`, `M_3 = 1 + 3 V` (`TransferMoments`),
3. Primal-dual chord potential sum and difference identities (`PrimalDual`),
4. Corner double-commutator identity and charge-spin commutator vanishing
   (`SandwichBrackets`). -/
theorem digrac_transferMoments_primalDual_and_sandwich_reuse
    {B : Type*} [Ring B] [StarRing B] {P : B} (hP : P * P = P) (hPstar : star P = P)
    (A C X : B) (n : ℕ) :
    (digracSym (conePlus P A) = genPhi P A (star A) ∧
     digracImb (conePlus P A) = genJ P A (star A) ∧
     digracImb (conePlus P A) * digracImb (conePlus P A) = -genV P A (star A) ∧
     magnetAdj P A * magnetAdj P A = genV P A (star A)) ∧
    (transferMoment P A C (n + 2) =
       transferMoment P A C (n + 1) + genV P A C * transferMoment P A C n ∧
     transferMoment P A C 2 = 1 + (2 : ℤ) • genV P A C ∧
     transferMoment P A C 3 = 1 + (3 : ℤ) • genV P A C) ∧
    ((P - conjPlus P A P) * (conjMinus P C P - P) = qgtPlus P A C ∧
     (conjMinus P C P - P) * (P - conjPlus P A P) = qgtMinus P A C ∧
     qgtPlus P A C + qgtMinus P A C = genV P A C ∧
     qgtPlus P A C - qgtMinus P A C = genSig P A C) ∧
    (comm (conePlus P A) (comm (coneMinus P C) X) -
       comm (coneMinus P C) (comm (conePlus P A) X) = comm (genSig P A C) X ∧
     charge P (comm (genSig P A C)) X = 0) := by
  have hDig := digrac_flow_imbalance_and_magnet_laplacian hPstar hP (conePlus P A) A 0
  exact ⟨⟨hDig.2.2.2.1, hDig.2.2.2.2.1, hDig.2.2.2.2.2.1, hDig.2.2.2.2.2.2.2.2.2⟩,
         ⟨transferMoment_recurrence hP A C n,
          transferMoment_two hP A C,
          transferMoment_three hP A C⟩,
         archetype_A42_primal_dual_chord_potentials hP A C,
         ⟨corner_commutator_pair hP A C X,
          charge_spin_comm hP A C X⟩⟩

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

/-- Strictly lower-triangular (causal retarded, `j < i`) matrix projector on `Matrix (Fin n) (Fin n) R`. -/
def matStrictLower {n : ℕ} {R : Type*} [Ring R] (X : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => if j < i then X i j else 0

/-- Diagonal (`i = j`) matrix projector on `Matrix (Fin n) (Fin n) R`. -/
def matDiagPart {n : ℕ} {R : Type*} [Ring R] (X : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => if i = j then X i j else 0

/-- Strictly upper-triangular (acausal advanced, `i < j`) matrix projector on `Matrix (Fin n) (Fin n) R`. -/
def matStrictUpper {n : ℕ} {R : Type*} [Ring R] (X : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => if i < j then X i j else 0

/-- Entrywise Discrete Gohberg–Krein Hilbert Transform `H(X)_{i,j} = sgn(i - j) X_{i,j}` on `Matrix (Fin n) (Fin n) R`. -/
def matDiscreteHilbert {n : ℕ} {R : Type*} [Ring R] (X : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R :=
  matStrictLower X - matStrictUpper X

/-- **`MCP₂` Turn 03 Matrix Trichotomy, Transpose Anticommutation & Split-Complex Involution `H² = Id - P₀`:**
For any `n × n` matrix `X : Matrix (Fin n) (Fin n) R`:
1. `X = P_-(X) + P_0(X) + P_+(X)` (exact trichotomy),
2. `(H(X))ᵀ = -H(Xᵀ)` (anti-commutation with transposition),
3. `H(H(X)) = X - P_0(X)` (split-complex involution on off-diagonal space, annihilating the diagonal),
4. For any causally masked matrix (`P_+(A) = 0`), `H(A + Aᵀ) = A - Aᵀ`! -/
theorem matDiscreteHilbert_trichotomy_and_involution {n : ℕ} {R : Type*} [Ring R]
    (X A : Matrix (Fin n) (Fin n) R) (hA_causal : matStrictUpper A = 0) :
    matStrictLower X + matDiagPart X + matStrictUpper X = X ∧
    (matDiscreteHilbert X)ᵀ = -matDiscreteHilbert Xᵀ ∧
    matDiscreteHilbert (matDiscreteHilbert X) = X - matDiagPart X ∧
    matDiscreteHilbert (A + Aᵀ) = A - Aᵀ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    dsimp [matStrictLower, matDiagPart, matStrictUpper]
    rcases lt_trichotomy j i with hji | rfl | hij
    · have hne : i ≠ j := ne_of_gt hji
      have hij : ¬(i < j) := not_lt_of_gt hji
      simp [hji, hne, hij]
    · simp
    · have hne : i ≠ j := ne_of_lt hij
      have hji : ¬(j < i) := not_lt_of_gt hij
      simp [hij, hne, hji]
  · ext i j
    dsimp [matDiscreteHilbert, matStrictLower, matStrictUpper, Matrix.transpose_apply]
    rcases lt_trichotomy j i with hji | rfl | hij
    · have hij : ¬(i < j) := not_lt_of_gt hji
      simp [hji, hij]
    · simp
    · have hji : ¬(j < i) := not_lt_of_gt hij
      simp [hij, hji]
  · ext i j
    dsimp [matDiscreteHilbert, matStrictLower, matStrictUpper, matDiagPart]
    rcases lt_trichotomy j i with hji | rfl | hij
    · have hij : ¬(i < j) := not_lt_of_gt hji
      have hne : i ≠ j := ne_of_gt hji
      simp [hji, hij, hne]
    · simp
    · have hji : ¬(j < i) := not_lt_of_gt hij
      have hne : i ≠ j := ne_of_lt hij
      simp [hij, hji, hne]
  · ext i j
    have hA_ij : i < j → A i j = 0 := by
      intro hij
      have h0 := congrFun (congrFun hA_causal i) j
      simpa [matStrictUpper, hij] using h0
    have hA_ji : j < i → A j i = 0 := by
      intro hji
      have h0 := congrFun (congrFun hA_causal j) i
      simpa [matStrictUpper, hji] using h0
    dsimp [matDiscreteHilbert, matStrictLower, matStrictUpper, Matrix.transpose_apply]
    rcases lt_trichotomy j i with hji | rfl | hij
    · have hij : ¬(i < j) := not_lt_of_gt hji
      simp [hji, hij, hA_ji hji]
    · simp
    · have hji : ¬(j < i) := not_lt_of_gt hij
      simp [hij, hji, hA_ij hij]

/-- **`MCP₂` Turn 03 Causal Mask Diagonal-Shift vs. Off-Diagonal Normalcy Commutator Decomposition:**
For `A = D + L` and `A* = D + U`, the normalcy commutator `[A, A*]` splits into the diagonal-shift
commutator `-[D, L - U]` plus the off-diagonal commutator `[L, U]`. -/
theorem causal_diagonal_shift_normalcy_commutator (D L U : B) :
    comm (D + L) (D + U) = -comm D (L - U) + comm L U := by
  dsimp [comm]; noncomm_ring

/-- **`MCP₂` Pass-3 Rota–Baxter Weight `-1` Identity & Gohberg–Krein Factorization Leakage:**
On `Matrix (Fin 3) (Fin 3) R`, the strict causal projection `P₋ = matStrictLower` and strict
acausal projection `P₊ = matStrictUpper` are subalgebra-closed (`P₋(P₋(X) P₋(Y)) = P₋(X) P₋(Y)`),
satisfy the Rota–Baxter weight `-1` identity
`P₋(P₋(X) Y + X P₋(Y) - P₋(X) P₋(Y)) = P₋(X) P₋(Y)`, and decompose the Gohberg–Krein
factorization excess `(1 + P₋(X))(1 + P₊(Y)) - 1` across the three trichotomy sectors. -/
theorem rota_baxter_weight_neg_one_and_gohberg_krein_leakage
    {R : Type*} [CommRing R] (X Y : Matrix (Fin 3) (Fin 3) R) :
    matStrictLower (matStrictLower X * matStrictLower Y) =
      matStrictLower X * matStrictLower Y ∧
    matStrictLower (matStrictLower X * Y + X * matStrictLower Y -
      X * Y) =
      matStrictLower X * matStrictLower Y ∧
    matDiagPart ((1 + matStrictLower X) * (1 + matStrictUpper Y) - 1) =
      matDiagPart (matStrictLower X * matStrictUpper Y) ∧
    matStrictLower ((1 + matStrictLower X) * (1 + matStrictUpper Y) - 1) =
      matStrictLower X + matStrictLower (matStrictLower X * matStrictUpper Y) ∧
    matStrictUpper ((1 + matStrictLower X) * (1 + matStrictUpper Y) - 1) =
      matStrictUpper Y + matStrictUpper (matStrictLower X * matStrictUpper Y) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp only [matStrictLower, matDiagPart, matStrictUpper,
        Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
        Fin.sum_univ_three] <;> simp <;> ring)

/-- `3 × 3` causal forward-shift (subdiagonal lag) matrix `S₃`. -/
def causalShift3 (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![0, 0, 0;
     1, 0, 0;
     0, 1, 0]

/-- `3 × 3` causal Toeplitz matrix `T(a₀, a₁, a₂) = a₀ I₃ + a₁ S₃ + a₂ S₃²`. -/
def causalToeplitz3 {R : Type*} [CommRing R] (a₀ a₁ a₂ : R) : Matrix (Fin 3) (Fin 3) R :=
  !![a₀, 0,  0;
     a₁, a₀, 0;
     a₂, a₁, a₀]

/-- **`MCP₂` Pass-3 Causal Toeplitz Commutant Algebra & Shift Boundary Displacement Defect:**
1. `causalShift3 R * causalShift3 R * causalShift3 R = 0` (3-step causal nilpotency),
2. Any two causal Toeplitz matrices `causalToeplitz3 a₀ a₁ a₂` and `causalToeplitz3 b₀ b₁ b₂`
   commute (`[T(a), T(b)] = 0`),
3. The shift normal defect `[S₃, S₃ᵀ]` equals the boundary source-minus-sink diagonal matrix
   `diag(-1, 0, 1)`. -/
theorem causalToeplitz3_commute_and_shift_boundary_defect
    {R : Type*} [CommRing R] (a₀ a₁ a₂ b₀ b₁ b₂ : R) :
    causalShift3 R * causalShift3 R * causalShift3 R = 0 ∧
    causalToeplitz3 a₀ a₁ a₂ * causalToeplitz3 b₀ b₁ b₂ =
      causalToeplitz3 b₀ b₁ b₂ * causalToeplitz3 a₀ a₁ a₂ ∧
    causalShift3 R * (causalShift3 R)ᵀ - (causalShift3 R)ᵀ * causalShift3 R =
      !![(-1 : R), 0, 0;
         0,        0, 0;
         0,        0, 1] := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [causalShift3, Matrix.mul_apply, Fin.sum_univ_three]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [causalToeplitz3, Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  · ext i j
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;>
      norm_num [causalShift3, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]

/-- **`MCP₂` Pass-3 Codebase Reuse (`BlockTriangularIntervention`): Block-Lower Subalgebra Closure & Ranked 3-Layer DAG Resolvent:**
Directly reuses `InfoGeometry.OperatorAlgebra.PeirceSpine` (`BlockTriangularIntervention.lean`) to establish:
1. Lower-block triangular subalgebra closure (`blockLower_upper_right`, `blockLower_mul`),
2. Bilateral idempotent compression idempotency and `11`-block preservation (`idempotentCompression_idempotent`, `idempotentCompression_peirce11`),
3. Ranked 3-layer DAG path square, 3-step nilpotency, and finite Green resolvent inverse (`ranked_dag_three_layer_resolvent`). -/
theorem blockLower_and_ranked_dag_resolvent_reuse
    {P Q P₁ P₂ : B} (hP : P * P = P) (hQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0)
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0)
    (F₁ L₁ D₁ F₂ L₂ D₂ T A C : B) :
    P * blockLower P F₁ L₁ D₁ * (1 - P) = 0 ∧
    blockLower P F₁ L₁ D₁ * blockLower P F₂ L₂ D₂ =
      blockLower P (F₁ * P * F₂) (L₁ * P * F₂ + D₁ * (1 - P) * L₂) (D₁ * (1 - P) * D₂) ∧
    idempotentCompression Q (idempotentCompression Q T) = idempotentCompression Q T ∧
    peirce11 P (idempotentCompression Q T) = peirce11 P T ∧
    dagEdge2 P₁ P₂ A C * dagEdge2 P₁ P₂ A C = P₁ * A * P₂ * C * (1 - P₁ - P₂) ∧
    dagEdge2 P₁ P₂ A C * dagEdge2 P₁ P₂ A C * dagEdge2 P₁ P₂ A C = 0 ∧
    (1 - dagEdge2 P₁ P₂ A C) * dagGreen2 P₁ P₂ A C = 1 ∧
    dagGreen2 P₁ P₂ A C * (1 - dagEdge2 P₁ P₂ A C) = 1 := by
  rcases ranked_dag_three_layer_resolvent h1 h2 h12 h21 A C with ⟨hG1, hG2, hG3, hG4⟩
  exact ⟨blockLower_upper_right hP F₁ L₁ D₁,
    blockLower_mul hP F₁ L₁ D₁ F₂ L₂ D₂,
    idempotentCompression_idempotent hQ T,
    idempotentCompression_peirce11 hPQ hQP T,
    hG1, hG2, hG3, hG4⟩

/-- **`MCP₂` Pass-4 Exact `3 × 3` Triangular Neumann Resolvent & Wiener–Hopf Factorization Inverse:**
For any `3 × 3` matrices `X, Y : Matrix (Fin 3) (Fin 3) R` over `[CommRing R]`, let
`L = matStrictLower X` and `U = matStrictUpper Y`:
1. `L * L * L = 0` and `U * U * U = 0` (universal 3-step nilpotency),
2. `(1 - L) * (1 + L + L * L) = 1` and `(1 + U + U * U) * (1 - U) = 1`,
3. **Wiener–Hopf / Gohberg–Krein Cross-Resolvent Identity**:
   `((1 - L) * (1 - U)) * ((1 + U + U * U) * (1 + L + L * L)) = 1`. -/
theorem matStrictLower3_neumann_inverse_and_wienerHopf
    {R : Type*} [CommRing R] (X Y : Matrix (Fin 3) (Fin 3) R) :
    matStrictLower X * matStrictLower X * matStrictLower X = 0 ∧
    matStrictUpper Y * matStrictUpper Y * matStrictUpper Y = 0 ∧
    (1 - matStrictLower X) * (1 + matStrictLower X + matStrictLower X * matStrictLower X) = 1 ∧
    (1 + matStrictUpper Y + matStrictUpper Y * matStrictUpper Y) * (1 - matStrictUpper Y) = 1 ∧
    ((1 - matStrictLower X) * (1 - matStrictUpper Y)) *
      ((1 + matStrictUpper Y + matStrictUpper Y * matStrictUpper Y) *
       (1 + matStrictLower X + matStrictLower X * matStrictLower X)) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp only [matStrictLower, matStrictUpper,
        Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
        Matrix.zero_apply, Fin.sum_univ_three] <;> simp <;> ring)

/-- **`MCP₂` Pass-4 Diagonal Position-Encoding vs. Causal Toeplitz Commutator & Uniform Clock Derivation:**
For `D = !![d₀, 0, 0; 0, d₁, 0; 0, 0, d₂]` and `T = causalToeplitz3 a₀ a₁ a₂`:
1. `[D, T]` is strictly lower-triangular and independent of `a₀`:
   `comm D (causalToeplitz3 a₀ a₁ a₂) = !![0, 0, 0; (d₁ - d₀) * a₁, 0, 0; (d₂ - d₀) * a₂, (d₂ - d₁) * a₁, 0]`.
2. Under uniform clock steps `(d₀, d₀ + δ, d₀ + 2 δ)`, `[D, T]` acts as the exact lag-number derivation:
   `comm !![d₀, 0, 0; 0, d₀ + δ, 0; 0, 0, d₀ + 2 * δ] (causalToeplitz3 a₀ a₁ a₂) = δ • causalToeplitz3 0 a₁ (2 * a₂)`. -/
theorem diag_causalToeplitz3_commutator_and_clock_derivation
    {R : Type*} [CommRing R] (d₀ d₁ d₂ δ a₀ a₁ a₂ : R) :
    comm (!![d₀, 0, 0; 0, d₁, 0; 0, 0, d₂] : Matrix (Fin 3) (Fin 3) R)
         (causalToeplitz3 a₀ a₁ a₂) =
      !![0,               0, 0;
         (d₁ - d₀) * a₁, 0, 0;
         (d₂ - d₀) * a₂, (d₂ - d₁) * a₁, 0] ∧
    comm (!![d₀, 0, 0; 0, d₀ + δ, 0; 0, 0, d₀ + 2 * δ] : Matrix (Fin 3) (Fin 3) R)
         (causalToeplitz3 a₀ a₁ a₂) =
      δ • causalToeplitz3 0 a₁ (2 * a₂) := by
  refine ⟨?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [comm, causalToeplitz3] <;> ring)

/-- **`MCP₂` Pass-4 Entrywise `3 × 3` Matrix Cotlar–Tricomi Second Form & Riesz Holomorphic Projectors:**
For any strictly off-diagonal `3 × 3` matrix `S_off : Matrix (Fin 3) (Fin 3) R` (`matDiagPart S_off = 0`,
modeled as `S_off = matStrictLower X + matStrictUpper X`):
1. **Riesz Causal/Acausal Reconstruction**:
   `S_off + matDiscreteHilbert S_off = (2 : R) • matStrictLower X` and
   `S_off - matDiscreteHilbert S_off = (2 : R) • matStrictUpper X`.
2. **Entrywise Matrix Cotlar–Tricomi First Form**:
   `matDiscreteHilbert (S_off * S_off + matDiscreteHilbert S_off * matDiscreteHilbert S_off) =
    anticomm S_off (matDiscreteHilbert S_off)`.
3. **Entrywise Matrix Cotlar–Tricomi Second Form (Turn 03 Eq. 344)**:
   `(matDiscreteHilbert S_off) * (matDiscreteHilbert S_off) =
    -(S_off * S_off) + matDiscreteHilbert (anticomm S_off (matDiscreteHilbert S_off))`. -/
theorem matDiscreteHilbert3_riesz_and_cotlarTricomi_second_form
    {R : Type*} [CommRing R] (X : Matrix (Fin 3) (Fin 3) R) :
    let S_off := matStrictLower X + matStrictUpper X
    S_off + matDiscreteHilbert S_off = (2 : R) • matStrictLower X ∧
    S_off - matDiscreteHilbert S_off = (2 : R) • matStrictUpper X ∧
    matDiscreteHilbert (S_off * S_off + matDiscreteHilbert S_off * matDiscreteHilbert S_off) =
      anticomm S_off (matDiscreteHilbert S_off) ∧
    matDiscreteHilbert S_off * matDiscreteHilbert S_off =
      -(S_off * S_off) + matDiscreteHilbert (anticomm S_off (matDiscreteHilbert S_off)) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp only [matDiscreteHilbert, matStrictLower, matStrictUpper, anticomm,
        Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
        Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_three] <;>
      simp <;> ring)

/-- Doubled positive (causal) Riesz holomorphic operator `2 Π_+(X) = X + H[X]` on `M_n(R)`. -/
def matRieszPosDoubled {n : ℕ} {R : Type*} [Ring R]
    (X : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  X + matDiscreteHilbert X

/-- Doubled negative (acausal) Riesz anti-holomorphic operator `2 Π_-(X) = X - H[X]` on `M_n(R)`. -/
def matRieszNegDoubled {n : ℕ} {R : Type*} [Ring R]
    (X : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  X - matDiscreteHilbert X

/-- **`MCP₂` Pass-5 Entrywise Riesz Holomorphic Projector Algebra (`Π_+ + Π_- = I`, `4 Π_+ Π_- = P_diag`, `4 Π_±² = 4 Π_± - P_diag`):**
For any `n × n` matrix `X` on `Fin n`:
1. `2 Π_+(X) + 2 Π_-(X) = 2 X` and `2 Π_+(X) - 2 Π_-(X) = 2 H[X]`,
2. `2 Π_+(2 Π_-(X)) = matDiagPart X` and `2 Π_-(2 Π_+(X)) = matDiagPart X` (orthogonal off-diagonal annihilation),
3. `2 Π_+(2 Π_+(X)) = 2 (2 Π_+(X)) - matDiagPart X` and `2 Π_-(2 Π_-(X)) = 2 (2 Π_-(X)) - matDiagPart X`. -/
theorem matRieszDoubled_projector_orthogonality_and_idempotency
    {n : ℕ} {R : Type*} [CommRing R] (X : Matrix (Fin n) (Fin n) R) :
    matRieszPosDoubled X + matRieszNegDoubled X = (2 : R) • X ∧
    matRieszPosDoubled X - matRieszNegDoubled X = (2 : R) • matDiscreteHilbert X ∧
    matRieszPosDoubled (matRieszNegDoubled X) = matDiagPart X ∧
    matRieszNegDoubled (matRieszPosDoubled X) = matDiagPart X ∧
    matRieszPosDoubled (matRieszPosDoubled X) = (2 : R) • matRieszPosDoubled X - matDiagPart X ∧
    matRieszNegDoubled (matRieszNegDoubled X) = (2 : R) • matRieszNegDoubled X - matDiagPart X := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    { ext i j
      simp only [matRieszPosDoubled, matRieszNegDoubled, matDiscreteHilbert,
        matStrictLower, matStrictUpper, matDiagPart,
        Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      rcases lt_trichotomy j i with hji | rfl | hij
      · have hnot : ¬ i < j := not_lt_of_gt hji
        have hne : i ≠ j := ne_of_gt hji
        simp [hji, hnot, hne]; try ring
      · simp; try ring
      · have hnot : ¬ j < i := not_lt_of_gt hij
        have hne : i ≠ j := ne_of_lt hij
        simp [hij, hnot, hne]; try ring }

/-- **`MCP₂` Pass-5 Multi-Hop Kramers–Kronig Hierarchy Lock & 4-Hop Vanishing on `M_4(R)`:**
Because strictly lower and strictly upper triangular matrices form nilpotent subalgebras (`L^k`
is strictly lower, `U^k` is strictly upper), the discrete Hilbert transform `matDiscreteHilbert`
locks the even (`L^k + U^k`) and odd (`L^k - U^k`) multi-hop propagators at every hop `k ≥ 1`:
1. **2-Hop Kramers–Kronig Lock**:
   `H[L² + U²] = L² - U²` and `H[L² - U²] = L² + U²`,
2. **3-Hop Kramers–Kronig Lock**:
   `H[L³ + U³] = L³ - U³` and `H[L³ - U³] = L³ + U³`,
3. **4-Hop Nilpotent Horizon on `Fin 4`**:
   `L⁴ = 0` and `U⁴ = 0`. -/
theorem multiHop_kramersKronig_hierarchy_lock_fin4
    {R : Type*} [CommRing R] (X : Matrix (Fin 4) (Fin 4) R) :
    let L := matStrictLower X
    let U := matStrictUpper X
    matDiscreteHilbert (L * L + U * U) = L * L - U * U ∧
    matDiscreteHilbert (L * L - U * U) = L * L + U * U ∧
    matDiscreteHilbert (L * L * L + U * U * U) = L * L * L - U * U * U ∧
    matDiscreteHilbert (L * L * L - U * U * U) = L * L * L + U * U * U ∧
    L * L * L * L = 0 ∧
    U * U * U * U = 0 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp only [matDiscreteHilbert, matStrictLower, matStrictUpper,
        Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.zero_apply,
        Fin.sum_univ_four] <;>
      simp <;> ring)

/-- **`MCP₂` Pass-5 Schwinger–Keldysh Retarded/Advanced Contour Rotation (Turn 03 Section 3):**
Rotating the Keldysh contour block `metriplecticBlock (G_R + G_A) (G_R - G_A)` by the unscaled
Walsh–Hadamard matrix `hadamardBlock` decouples the Retarded propagator `G_R` and Advanced
propagator `G_A` into orthogonal diagonal blocks:
`W * M(G_R + G_A, G_R - G_A) * W = !![4 G_R, 0; 0, 4 G_A]`. -/
theorem schwingerKeldysh_retarded_advanced_contour_decoupling (G_R G_A : B) :
    causalForward (G_R + G_A) (G_R - G_A) = (2 : ℤ) • G_R ∧
    causalBackward (G_R + G_A) (G_R - G_A) = (2 : ℤ) • G_A ∧
    hadamardBlock * metriplecticBlock (G_R + G_A) (G_R - G_A) * hadamardBlock =
      !![(4 : ℤ) • G_R, 0;
         0, (4 : ℤ) • G_A] := by
  refine ⟨by dsimp [causalForward]; noncomm_ring,
          by dsimp [causalBackward]; noncomm_ring, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamardBlock, metriplecticBlock, Matrix.mul_apply, Fin.sum_univ_two] <;>
    noncomm_ring

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

/-- Concrete `2 × 2` Witt CAR creation/annihilation `LightConePair` reusing `InfoGeometry.Algebra.LightConePair`. -/
def wittLightConePair (R : Type*) [CommRing R] :
    InfoGeometry.Algebra.LightConePair (Matrix (Fin 2) (Fin 2) R) where
  ePlus := !![(0 : R), 1; 0, 0]
  eMinus := !![(0 : R), 0; 1, 0]
  ePlus_sq := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  eMinus_sq := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  anticomm := by
    ext i j; fin_cases i <;> fin_cases j <;> simp

/-- **`MCP₃` Codebase Reuse (`InfoGeometry.Algebra.LightConePair`): Witt CAR Lightcone Projectors:**
Reuses `LightConePair.lightcone_compensation_packet` on `wittLightConePair R` to establish
idempotency, mutual orthogonality, and completeness (`pPlus + pMinus = 1`) of the Head/Tail Witt projectors. -/
theorem wittLightCone_compensation :
    (wittLightConePair R).pPlus * (wittLightConePair R).pPlus = (wittLightConePair R).pPlus ∧
    (wittLightConePair R).pMinus * (wittLightConePair R).pMinus = (wittLightConePair R).pMinus ∧
    (wittLightConePair R).pPlus * (wittLightConePair R).pMinus = 0 ∧
    (wittLightConePair R).pMinus * (wittLightConePair R).pPlus = 0 ∧
    (wittLightConePair R).pPlus + (wittLightConePair R).pMinus = 1 :=
  (wittLightConePair R).lightcone_compensation_packet

/-- **`MCP₃` Turn 02 RoPE Conjugation on `Cl(1,1)` (Elliptic Invariance vs. Double-Angle Hyperbolic Rotation):**
Conjugating `d_i I₂ + d_p σ_z + d_s σ_x + d_c ε` by the RoPE rotor `R(c, s) = c I₂ + s ε`
preserves `(d_i, d_c)` up to `c² + s²` while rotating `(d_p, d_s)` by the double angle
`(c² - s², 2 c s)`, proving that `{σ_z, σ_x}` break RoPE shift-invariance! -/
theorem rope_conjugation_elliptic_invariance_and_double_angle (c s di dp ds dc : R) :
    (c • (1 : Matrix (Fin 2) (Fin 2) R) + s • epsSymp)ᵀ *
      (di • (1 : Matrix (Fin 2) (Fin 2) R) + dp • sigmaZ + ds • sigmaX + dc • epsSymp) *
      (c • (1 : Matrix (Fin 2) (Fin 2) R) + s • epsSymp) =
      ((c ^ 2 + s ^ 2) * di) • 1 +
      ((c ^ 2 - s ^ 2) * dp + 2 * c * s * ds) • sigmaZ +
      (-(2 * c * s * dp) + (c ^ 2 - s ^ 2) * ds) • sigmaX +
      ((c ^ 2 + s ^ 2) * dc) • epsSymp := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigmaZ, sigmaX, epsSymp,
      Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two] <;>
    ring

/-- **`MCP₃` Turn 04 Symplectic Group Preservation `Mᵀ ε M = det(M) ε` & Universal Cayley–Krein Identity:**
1. Every `2 × 2` matrix `M` over `[CommRing R]` satisfies `Mᵀ ε M = det(M) • ε`.
2. In any `[Ring B] [StarRing B]`, if `J` is self-adjoint (`star J = J`) and `Ω` is `J`-skew-adjoint
   (`star Ω * J = -(J * Ω)`), then `(1 - Ω)* J (1 - Ω) = J (1 - Ω²) = (1 + Ω)* J (1 + Ω)`. -/
theorem symplectic_det_and_cayley_krein_isometry (M : Matrix (Fin 2) (Fin 2) R)
    {B : Type*} [Ring B] [StarRing B] (J Omega : B)
    (hOmega : star Omega * J = -(J * Omega)) :
    Mᵀ * epsSymp * M = M.det • (epsSymp : Matrix (Fin 2) (Fin 2) R) ∧
    star (1 - Omega) * J * (1 - Omega) = J * (1 - Omega * Omega) ∧
    star (1 + Omega) * J * (1 + Omega) = J * (1 - Omega * Omega) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [epsSymp, Matrix.det_fin_two, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two] <;>
      ring
  · calc star (1 - Omega) * J * (1 - Omega)
      _ = (J - star Omega * J) * (1 - Omega) := by rw [star_sub, star_one]; noncomm_ring
      _ = (J - -(J * Omega)) * (1 - Omega) := by rw [hOmega]
      _ = J * (1 - Omega * Omega) := by noncomm_ring
  · calc star (1 + Omega) * J * (1 + Omega)
      _ = (J + star Omega * J) * (1 + Omega) := by rw [star_add, star_one]; noncomm_ring
      _ = (J + -(J * Omega)) * (1 + Omega) := by rw [hOmega]
      _ = J * (1 - Omega * Omega) := by noncomm_ring

/-- **`MCP₃` Turn 05 `4 × 4` Skew-Symmetric Pfaffian Determinant Identity (`det(K₄) = Pf(K₄)²`):** -/
theorem skew4_det_eq_pfaffian_sq (k01 k02 k03 k12 k13 k23 : R) :
    (!![0, k01, k02, k03;
        -k01, 0, k12, k13;
        -k02, -k12, 0, k23;
        -k03, -k13, -k23, 0] : Matrix (Fin 4) (Fin 4) R).det =
      (k01 * k23 - k02 * k13 + k03 * k12) ^ 2 := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply]
  simp [Fin.succAbove]
  ring

/-- **`MCP₃` Turn 05 Socratic Aporia (Quaternionic Idempotency Obstruction in `Cl(0,2) ≅ ℍ`):**
In the quaternion division ring `Cl(0,2)(ℝ) ≅ ℍ`, `q² = q` yields `x₀² - (x₁² + x₂² + x₃²) = x₀`
and `2 x₀ x_r = x_r` (`r = 1, 2, 3`), which over `ℝ` forces `x₁ = x₂ = x₃ = 0` and `(x₀ = 0 ∨ x₀ = 1)`. -/
theorem cl02_quaternionic_idempotency_obstruction (x0 x1 x2 x3 : ℝ)
    (h_re : x0 ^ 2 - (x1 ^ 2 + x2 ^ 2 + x3 ^ 2) = x0)
    (h_i : 2 * x0 * x1 = x1) (h_j : 2 * x0 * x2 = x2) (h_k : 2 * x0 * x3 = x3) :
    x1 = 0 ∧ x2 = 0 ∧ x3 = 0 ∧ (x0 = 0 ∨ x0 = 1) := by
  have h_sum_zero : (2 * x0 - 1) ^ 2 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2) = 0 := by
    have h1 : (2 * x0 - 1) * x1 = 0 := by linarith [h_i]
    have h2 : (2 * x0 - 1) * x2 = 0 := by linarith [h_j]
    have h3 : (2 * x0 - 1) * x3 = 0 := by linarith [h_k]
    calc (2 * x0 - 1) ^ 2 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2)
      _ = ((2 * x0 - 1) * x1) ^ 2 + ((2 * x0 - 1) * x2) ^ 2 + ((2 * x0 - 1) * x3) ^ 2 := by ring
      _ = 0 := by rw [h1, h2, h3]; ring
  have h_vec_zero : x1 ^ 2 + x2 ^ 2 + x3 ^ 2 = 0 := by
    rcases mul_eq_zero.mp h_sum_zero with h_half | h_v
    · exfalso
      have hx0 : 2 * x0 - 1 = 0 := by
        have hx0_sq : (2 * x0 - 1) * (2 * x0 - 1) = 0 := by
          simpa [pow_two] using h_half
        rcases mul_eq_zero.mp hx0_sq with h | h <;> linarith
      nlinarith [h_re, hx0, sq_nonneg x1, sq_nonneg x2, sq_nonneg x3]
    · exact h_v
  have hx1 : x1 = 0 := by nlinarith [h_vec_zero, sq_nonneg x1, sq_nonneg x2, sq_nonneg x3]
  have hx2 : x2 = 0 := by nlinarith [h_vec_zero, sq_nonneg x1, sq_nonneg x2, sq_nonneg x3]
  have hx3 : x3 = 0 := by nlinarith [h_vec_zero, sq_nonneg x1, sq_nonneg x2, sq_nonneg x3]
  have hx0_fac : x0 * (x0 - 1) = 0 := by linarith [h_re, h_vec_zero]
  refine ⟨hx1, hx2, hx3, ?_⟩
  rcases mul_eq_zero.mp hx0_fac with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linarith [h1])

/-- **`MCP₃` Turn 06 `Cl(1,1)` `ℤ₂` Parity Grading Involution & Witt Round-Trip Tail Transfer:**
1. Conjugation by `σ_z` splits `!![d_i + d_p, d_s - d_c; d_s + d_c, d_i - d_p]` into its even
   Class-BDI subalgebra `span{I₂, σ_z}` and its odd space `span{σ_x, ε}`.
2. The Witt projectors `2 P_± = I₂ ± σ_z` and ladder operators `2 σ_∓ = σ_x ± ε` satisfy
   the dyadic round-trip transfers `(σ_x + ε)(I₂ + σ_z)(σ_x - ε) = 4(I₂ - σ_z)` and
   `(σ_x - ε)(I₂ - σ_z)(σ_x + ε) = 4(I₂ + σ_z)`. -/
theorem cl11_z2_parity_and_witt_tail_transfer (di dp ds dc : R) :
    (!![di + dp, ds - dc; ds + dc, di - dp] : Matrix (Fin 2) (Fin 2) R) +
      sigmaZ * !![di + dp, ds - dc; ds + dc, di - dp] * sigmaZ =
      (2 : R) • !![di + dp, 0; 0, di - dp] ∧
    (!![di + dp, ds - dc; ds + dc, di - dp] : Matrix (Fin 2) (Fin 2) R) -
      sigmaZ * !![di + dp, ds - dc; ds + dc, di - dp] * sigmaZ =
      (2 : R) • !![0, ds - dc; ds + dc, 0] ∧
    ((sigmaX : Matrix (Fin 2) (Fin 2) R) + epsSymp) * (1 + sigmaZ) * (sigmaX - epsSymp) =
      (4 : R) • (1 - sigmaZ) ∧
    ((sigmaX : Matrix (Fin 2) (Fin 2) R) - epsSymp) * (1 - sigmaZ) * (sigmaX + epsSymp) =
      (4 : R) • (1 + sigmaZ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    { ext i j; fin_cases i <;> fin_cases j <;>
        simp [sigmaZ, sigmaX, epsSymp, Matrix.mul_apply, Matrix.vecMul,
          dotProduct, Fin.sum_univ_two] <;>
        ring }

/-- **`MCP₃` Pass-3 Pauli–Krein `𝔰𝔩(2, R) ≅ 𝔰𝔲(1,1)` Lie Algebra, Lorentzian Casimir & Hodge Duality:**
For `K₀ = epsSymp`, `K₁ = sigmaZ`, `K₂ = sigmaX` in `M₂(R)`:
1. **Lie Bracket Closure**: `[K₀, K₁] = 2 K₂`, `[K₀, K₂] = -2 K₁`, `[K₁, K₂] = -2 K₀`.
2. **Universal Lorentzian Casimir Square**: `(x₀ • K₀ + x₁ • K₁ + x₂ • K₂)² = (-x₀² + x₁² + x₂²) • I₂`.
3. **Para-Kähler Hodge Pseudoscalar Duality**: `σ_z * (a • σ_x + b • ε) = (-b) • σ_x + (-a) • ε`. -/
theorem sl2_pauli_krein_lie_casimir_and_hodge_duality (x₀ x₁ x₂ a b : R) :
    (comm (epsSymp : Matrix (Fin 2) (Fin 2) R) sigmaZ = (2 : R) • sigmaX ∧
     comm (epsSymp : Matrix (Fin 2) (Fin 2) R) sigmaX = -(2 : R) • sigmaZ ∧
     comm (sigmaZ : Matrix (Fin 2) (Fin 2) R) sigmaX = -(2 : R) • epsSymp) ∧
    (x₀ • (epsSymp : Matrix (Fin 2) (Fin 2) R) + x₁ • sigmaZ + x₂ • sigmaX) *
      (x₀ • epsSymp + x₁ • sigmaZ + x₂ • sigmaX) =
      (-x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2) • (1 : Matrix (Fin 2) (Fin 2) R) ∧
    (sigmaZ : Matrix (Fin 2) (Fin 2) R) * (a • sigmaX + b • epsSymp) =
      (-b) • sigmaX + (-a) • epsSymp := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    { ext i j
      fin_cases i <;> fin_cases j <;>
        simp [comm, epsSymp, sigmaZ, sigmaX, Matrix.mul_apply, Fin.sum_univ_two] <;>
        ring }

/-- **`MCP₃` Pass-3 Universal Krein-Hamiltonian Lie Bracket Closure & Jordan Anticommutator Self-Adjointness:**
In any `[Ring B] [StarRing B]`, if `H₁, H₂ : B` are `J`-skew-adjoint with respect to `J : B`
(`J * star H₁ + H₁ * J = 0` and `J * star H₂ + H₂ * J = 0`), then:
1. Their Lie commutator `[H₁, H₂]` is `J`-skew-adjoint (`J * star [H₁, H₂] + [H₁, H₂] * J = 0`),
2. Their Jordan anticommutator `{H₁, H₂}` is `J`-self-adjoint (`J * star {H₁, H₂} - {H₁, H₂} * J = 0`). -/
theorem krein_hamiltonian_lie_closure_and_jordan_self_adjoint
    {B : Type*} [Ring B] [StarRing B] (J H₁ H₂ : B)
    (hH₁ : J * star H₁ + H₁ * J = 0)
    (hH₂ : J * star H₂ + H₂ * J = 0) :
    J * star (comm H₁ H₂) + comm H₁ H₂ * J = 0 ∧
    J * star (anticomm H₁ H₂) - anticomm H₁ H₂ * J = 0 := by
  have h1 : J * star H₁ = -H₁ * J := by
    calc J * star H₁ = (J * star H₁ + H₁ * J) - H₁ * J := by noncomm_ring
      _ = -H₁ * J := by rw [hH₁, zero_sub, neg_mul]
  have h2 : J * star H₂ = -H₂ * J := by
    calc J * star H₂ = (J * star H₂ + H₂ * J) - H₂ * J := by noncomm_ring
      _ = -H₂ * J := by rw [hH₂, zero_sub, neg_mul]
  constructor
  · dsimp [comm]
    calc J * star (H₁ * H₂ - H₂ * H₁) + (H₁ * H₂ - H₂ * H₁) * J
      _ = (J * star H₂) * star H₁ - (J * star H₁) * star H₂ + (H₁ * H₂ - H₂ * H₁) * J := by
        simp [star_sub, star_mul]; noncomm_ring
      _ = (-H₂ * J) * star H₁ - (-H₁ * J) * star H₂ + (H₁ * H₂ - H₂ * H₁) * J := by
        rw [h1, h2]
      _ = -H₂ * (J * star H₁) + H₁ * (J * star H₂) + (H₁ * H₂ - H₂ * H₁) * J := by
        noncomm_ring
      _ = -H₂ * (-H₁ * J) + H₁ * (-H₂ * J) + (H₁ * H₂ - H₂ * H₁) * J := by
        rw [h1, h2]
      _ = 0 := by noncomm_ring
  · dsimp [anticomm]
    calc J * star (H₁ * H₂ + H₂ * H₁) - (H₁ * H₂ + H₂ * H₁) * J
      _ = (J * star H₂) * star H₁ + (J * star H₁) * star H₂ - (H₁ * H₂ + H₂ * H₁) * J := by
        simp [star_add, star_mul]; noncomm_ring
      _ = (-H₂ * J) * star H₁ + (-H₁ * J) * star H₂ - (H₁ * H₂ + H₂ * H₁) * J := by
        rw [h1, h2]
      _ = -H₂ * (J * star H₁) - H₁ * (J * star H₂) - (H₁ * H₂ + H₂ * H₁) * J := by
        noncomm_ring
      _ = -H₂ * (-H₁ * J) - H₁ * (-H₂ * J) - (H₁ * H₂ + H₂ * H₁) * J := by
        rw [h1, h2]
      _ = 0 := by noncomm_ring

/-- **`MCP₃` Pass-3 Codebase Reuse (`Bergman` & `ChiralEulerFactors`): Bergman Operator, Jordan Triple & Chiral Euler Factors:**
Directly reuses `InfoGeometry.OperatorAlgebra.PeirceSpine` (`Bergman.lean` and `ChiralEulerFactors.lean`)
to establish:
1. `bergmanOp P A C 1 = 1 - genV P A C` and `bergmanOp P A C (conePlus P A) = (1 - V)² N₊` (`archetype_A23_bergman_operator`),
2. `jordanTriple (genPhi P A C) (genPhi P A C) (genPhi P A C) = 2 • (V * Φ)` (`archetype_A25_jordan_triple_and_grade_inversion`),
3. `(1 - qgtPlus P A C) * (1 - qgtMinus P A C) = zetaFactor P A C` (`chiralEuler_factorizations`),
4. `(1 - Φ)(1 - J)(1 + J)(1 + Φ) = 1 - V²` (`supercharge_four_factor_product`). -/
theorem bergman_symplectic_and_chiral_euler_reuse
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B) :
    bergmanOp P A C 1 = 1 - genV P A C ∧
    bergmanOp P A C (conePlus P A) =
      (1 - genV P A C) * (1 - genV P A C) * conePlus P A ∧
    jordanTriple (genPhi P A C) (genPhi P A C) (genPhi P A C) =
      (2 : ℤ) • (genV P A C * genPhi P A C) ∧
    (1 - qgtPlus P A C) * (1 - qgtMinus P A C) = zetaFactor P A C ∧
    (1 - genPhi P A C) * (1 - genJ P A C) *
      (1 + genJ P A C) * (1 + genPhi P A C) =
      1 - genV P A C * genV P A C := by
  rcases archetype_A23_bergman_operator hP A C with ⟨hB1, hB2, _⟩
  rcases archetype_A25_jordan_triple_and_grade_inversion hP A C with ⟨_, _, hJ3, _⟩
  rcases chiralEuler_factorizations hP A C with ⟨hE1, _⟩
  exact ⟨hB1, hB2, hJ3, hE1, supercharge_four_factor_product hP A C⟩

/-- **`MCP₃` Pass-3 Codebase Reuse: Full Clifford `Cl(1,1)` $\to$ Matrix `M₂(ℝ)` $\to$ Tensor-Tower (`MatStage n`) $\to$ Iterated Kronecker Tower $\to$ Direct-Limit Colimit Spine:**
Directly reuses `InfoGeometry.Clifford.Cl11Matrix`, `InfoGeometry.Clifford.TowerMatrix`,
`InfoGeometry.Clifford.Cl11TensorTower`, `InfoGeometry.Clifford.Cl11TensorTowerIteration`,
`InfoGeometry.Clifford.Cl11TensorTowerLimit`, `InfoGeometry.Clifford.Cl11TensorTowerSupergraded`,
and `InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixColimitTransport` to establish:
1. **Clifford `Cl(1,1)` to `2 × 2` Real Pauli Matrix Algebra Isomorphism (`Cl11Matrix`)**:
   `cl11EquivMat (ι(1,0)) = Eplus = σ_z` (`Eplus² = 1`),
   `cl11EquivMat (ι(0,1)) = Eminus = ε` (`Eminus² = -1`), and `{Eplus, Eminus} = 0`.
2. **Stage-`n` Binary Kronecker Tensor-Tower Metric & Cartan Involution (`TowerMatrix`)**:
   `Jn J1 n * Jn J1 n = 1` and `cartan J1 n (cartan J1 n X) = X` for every `X : MatStage n`.
3. **Recursive Jordan–Wigner Tensor-String Embedding & Normalized Invariants (`Cl11TensorTower`)**:
   `matStageEmbed n (jwCreation n k) = jwCreation (n + 1) k.castSucc`,
   `matStageEmbed n (jwAnnihilation n k) = jwAnnihilation (n + 1) k.castSucc`,
   `normalizedTrace (n + 1) (matStageEmbed n X) = normalizedTrace n X`, and
   `normalizedLogAbsDet (n + 1) (matStageEmbed n X) = normalizedLogAbsDet n X`.
4. **Iterated `k`-Step Kronecker Tower Stabilization (`Cl11TensorTowerIteration`)**:
   `normalizedTrace (n + k) (iteratedStageEmbed n k X) = normalizedTrace n X` and
   `Matrix.det (iteratedStageEmbed n k X) = (Matrix.det X) ^ (2 ^ k)`.
5. **Supergraded Bracket Transport to the Algebraic Direct-Limit Colimit (`Cl11TensorTowerSupergraded`)**:
   `stageEmbed n (stageSuperBracket px py X Y) = stageSuperBracket px py (stageEmbed n X) (stageEmbed n Y)`
   and `ofStage n (stageSuperBracket px py X Y) = superBracket px py (ofStage n X) (ofStage n Y)`.
6. **Peirce Homogenized Channels & Perturbed Grading in the Matrix Tensor-Tower Colimit (`MatrixColimitTransport`)**:
   `matrix_limit_grading_phi_sq`, `matrix_limit_hProjV_bond`, and `matrix_limit_hProjPhi_bond`. -/
theorem clifford_to_matrix_to_tensorTower_and_colimit_spine
    (n k : ℕ) (idx : Fin n)
    {P_stage : InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage n}
    (hP_stage : P_stage * P_stage = P_stage)
    (X Y A_stage C_stage : InfoGeometry.Clifford.Cl11TensorTower.MatStage n)
    (A_lim C_lim : InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit)
    (px py : Bool) :
    InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat
        (CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (1, 0)) =
      InfoGeometry.Clifford.Cl11Matrix.Eplus ∧
    InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat
        (CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (0, 1)) =
      InfoGeometry.Clifford.Cl11Matrix.Eminus ∧
    InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat
        (CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (1, 0)) *
      InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat
        (CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (0, 1)) +
    InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat
        (CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (0, 1)) *
      InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat
        (CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (1, 0)) = 0 ∧
    InfoGeometry.Clifford.TowerMatrix.Jn InfoGeometry.Clifford.Cl11Matrix.J1 n *
      InfoGeometry.Clifford.TowerMatrix.Jn InfoGeometry.Clifford.Cl11Matrix.J1 n = 1 ∧
    InfoGeometry.Clifford.TowerMatrix.cartan InfoGeometry.Clifford.Cl11Matrix.J1 n
      (InfoGeometry.Clifford.TowerMatrix.cartan InfoGeometry.Clifford.Cl11Matrix.J1 n X) = X ∧
    InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed n
        (InfoGeometry.Clifford.Cl11TensorTower.jwCreation n idx) =
      InfoGeometry.Clifford.Cl11TensorTower.jwCreation (n + 1) idx.castSucc ∧
    InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed n
        (InfoGeometry.Clifford.Cl11TensorTower.jwAnnihilation n idx) =
      InfoGeometry.Clifford.Cl11TensorTower.jwAnnihilation (n + 1) idx.castSucc ∧
    InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace (n + k)
        (InfoGeometry.Clifford.Cl11TensorTowerIteration.iteratedStageEmbed n k X) =
      InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace n X ∧
    Matrix.det (InfoGeometry.Clifford.Cl11TensorTowerIteration.iteratedStageEmbed n k X) =
      Matrix.det X ^ (2 ^ k) ∧
    InfoGeometry.Clifford.Cl11TensorTowerSupergraded.ofStage n
        (InfoGeometry.Clifford.Cl11TensorTowerSupergraded.stageSuperBracket px py X Y) =
      InfoGeometry.Algebra.SupergradedBracket.superBracket px py
        (InfoGeometry.Clifford.Cl11TensorTowerSupergraded.ofStage n X)
        (InfoGeometry.Clifford.Cl11TensorTowerSupergraded.ofStage n Y) ∧
    (invS (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n P_stage) +
      genPhi (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n P_stage) A_lim C_lim) *
      (invS (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n P_stage) +
        genPhi (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n P_stage) A_lim C_lim) =
      zetaPlusFactor (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n P_stage) A_lim C_lim ∧
    InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage (n + 1)
      (hProjV (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n P_stage)
        (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n A_stage)
        (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n C_stage)
        (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n X)) =
      InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n (hProjV P_stage A_stage C_stage X) ∧
    InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage (n + 1)
      (hProjPhi (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n P_stage)
        (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n A_stage)
        (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n C_stage)
        (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n X)) =
      InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n (hProjPhi P_stage A_stage C_stage X) := by
  have hJn_sq := InfoGeometry.Clifford.TowerMatrix.Jn_sq
    InfoGeometry.Clifford.Cl11Matrix.J1 InfoGeometry.Clifford.Cl11Matrix.J1_sq n
  have hJn_t := InfoGeometry.Clifford.TowerMatrix.Jn_transpose
    InfoGeometry.Clifford.Cl11Matrix.J1 InfoGeometry.Clifford.Cl11Matrix.J1_transpose n
  exact ⟨InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat_iota_pos,
         InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat_iota_neg,
         InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat_iota_pos_neg_anticomm,
         hJn_sq,
         InfoGeometry.Clifford.TowerMatrix.cartan_involutive
           InfoGeometry.Clifford.Cl11Matrix.J1 n hJn_sq hJn_t X,
         InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed_jwCreation idx,
         InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed_jwAnnihilation idx,
         InfoGeometry.Clifford.Cl11TensorTowerIteration.iteratedStageEmbed_normalizedTrace n k X,
         InfoGeometry.Clifford.Cl11TensorTowerIteration.iteratedStageEmbed_det n k X,
         InfoGeometry.Clifford.Cl11TensorTowerSupergraded.ofStage_superBracket px py X Y,
         matrix_limit_grading_phi_sq n hP_stage A_lim C_lim,
         matrix_limit_hProjV_bond n P_stage A_stage C_stage X,
         matrix_limit_hProjPhi_bond n P_stage A_stage C_stage X⟩

/-- **`MCP₃` Pass-4 Symplectic Lie Algebra Trace Law `Xᵀ ε + ε X = tr(X) ε` & Hyperbolic vs. Elliptic Cayley Dichotomy:**
1. For every `X : Matrix (Fin 2) (Fin 2) R`, `Xᵀ * epsSymp + epsSymp * X = Matrix.trace X • epsSymp`.
2. The hyperbolic boost Cayley numerator `N_hyp(t) = (1 + t • sigmaX)² = (1 + t²) • 1 + (2 t) • sigmaX`
   satisfies `N_hyp(t)ᵀ * sigmaZ * N_hyp(t) = (1 - t²)² • sigmaZ` (singular at `t = ±1`).
3. The elliptic RoPE Cayley numerator `N_ell(t) = (1 + t • epsSymp)² = (1 - t²) • 1 + (2 t) • epsSymp`
   satisfies `N_ell(t)ᵀ * N_ell(t) = (1 + t²)² • 1` (nonsingular for all `t : ℝ`). -/
theorem sp2_trace_law_and_hyperbolic_vs_elliptic_cayley
    (X : Matrix (Fin 2) (Fin 2) R) (t : R) :
    Xᵀ * (epsSymp : Matrix (Fin 2) (Fin 2) R) + epsSymp * X =
      Matrix.trace X • (epsSymp : Matrix (Fin 2) (Fin 2) R) ∧
    ((1 + t • (sigmaX : Matrix (Fin 2) (Fin 2) R)) * (1 + t • sigmaX))ᵀ * sigmaZ *
      ((1 + t • sigmaX) * (1 + t • sigmaX)) =
      ((1 - t ^ 2) ^ 2) • (sigmaZ : Matrix (Fin 2) (Fin 2) R) ∧
    ((1 + t • (epsSymp : Matrix (Fin 2) (Fin 2) R)) * (1 + t • epsSymp))ᵀ *
      ((1 + t • epsSymp) * (1 + t • epsSymp)) =
      ((1 + t ^ 2) ^ 2) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    { ext i j
      simp only [epsSymp, sigmaX, sigmaZ, Matrix.trace, Matrix.diag,
        Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;> simp <;> ring }

/-- **`MCP₃` Pass-4 Codebase Reuse (`Cl11StarAlgebraColimit`, `Cl11StarAlgebraFiltration`, `Cl11JordanWignerCARBridge`, `Cl11GradingSl2`, `GradingTransfer`):**
Directly reuses the repository's `Cl(1,1)` Star-Algebra Colimit, Strict Subalgebra Filtration,
Same-Site Jordan–Wigner CAR, Parabolic `sl(2)` Grading Triple, and Peirce `GradingTransfer` owners:
1. Faithful star-algebra embedding `Function.Injective (ofStageStarAlgHom n)` (`Cl11StarAlgebraColimit`),
2. Strict `StarSubalgebra ℝ Limit` filtration `stageImage n < stageImage (n + 1)`, exact stage
   dimension `Module.finrank ℝ (stageImage n) = 4 ^ n`, and infinite-dimensionality `¬ Module.Finite ℝ Limit`
   (`Cl11StarAlgebraFiltration`),
3. Full `n`-site Jordan–Wigner CAR `jwAnnihilation n i * jwCreation n j + jwCreation n j * jwAnnihilation n i = if i = j then 1 else 0`
   (`Cl11JordanWignerCARBridge`),
4. Parabolic `sl(2)` triple `⁅clH, clE⁆ = (2 : ℝ) • clE ∧ ⁅clH, clF⁆ = (-2 : ℝ) • clF ∧ ⁅clE, clF⁆ = clH`
   in `CliffordAlgebra q11` (`Cl11GradingSl2`),
5. Peirce transfer discriminant squares `((2 : ℤ) • peirceTransfer P A C - 1)² = 1 + 4 • genV P A C` and
   `((2 : ℤ) • peirceTransferJ P A C - 1)² = 1 - 4 • genV P A C` (`GradingTransfer`). -/
theorem cl11_starColimit_filtration_car_and_sl2_reuse
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B)
    (n : ℕ) (i j : Fin n) :
    Function.Injective (InfoGeometry.Clifford.Cl11StarAlgebraColimit.ofStageStarAlgHom n) ∧
    InfoGeometry.Clifford.Cl11StarAlgebraFiltration.stageImage n <
      InfoGeometry.Clifford.Cl11StarAlgebraFiltration.stageImage (n + 1) ∧
    Module.finrank ℝ (InfoGeometry.Clifford.Cl11StarAlgebraFiltration.stageImage n) = 4 ^ n ∧
    ¬ Module.Finite ℝ InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit ∧
    InfoGeometry.Clifford.Cl11TensorTower.jwAnnihilation n i *
        InfoGeometry.Clifford.Cl11TensorTower.jwCreation n j +
      InfoGeometry.Clifford.Cl11TensorTower.jwCreation n j *
        InfoGeometry.Clifford.Cl11TensorTower.jwAnnihilation n i =
      (if i = j then 1 else 0) ∧
    (⁅InfoGeometry.Clifford.Cl11GradingSl2.clH, InfoGeometry.Clifford.Cl11GradingSl2.clE⁆ =
       (2 : ℝ) • InfoGeometry.Clifford.Cl11GradingSl2.clE ∧
     ⁅InfoGeometry.Clifford.Cl11GradingSl2.clH, InfoGeometry.Clifford.Cl11GradingSl2.clF⁆ =
       (-2 : ℝ) • InfoGeometry.Clifford.Cl11GradingSl2.clF ∧
     ⁅InfoGeometry.Clifford.Cl11GradingSl2.clE, InfoGeometry.Clifford.Cl11GradingSl2.clF⁆ =
       InfoGeometry.Clifford.Cl11GradingSl2.clH) ∧
    ((2 : ℤ) • peirceTransfer P A C - 1) * ((2 : ℤ) • peirceTransfer P A C - 1) =
      1 + (4 : ℤ) • genV P A C ∧
    ((2 : ℤ) • peirceTransferJ P A C - 1) * ((2 : ℤ) • peirceTransferJ P A C - 1) =
      1 - (4 : ℤ) • genV P A C :=
  ⟨InfoGeometry.Clifford.Cl11StarAlgebraColimit.ofStageStarAlgHom_injective n,
   InfoGeometry.Clifford.Cl11StarAlgebraFiltration.stageImage_lt_succ n,
   InfoGeometry.Clifford.Cl11StarAlgebraFiltration.stageImage_finrank n,
   InfoGeometry.Clifford.Cl11StarAlgebraFiltration.not_moduleFinite,
   InfoGeometry.Clifford.Cl11JordanWignerCARBridge.jwAnnihilation_creation_anticommutator n i j,
   InfoGeometry.Clifford.Cl11GradingSl2.cl11ParabolicSL2Triple,
   transfer_discriminant_square hP A C,
   transfer_j_discriminant_square hP A C⟩

/-- **`MCP₃` Pass-5 Walsh–Hadamard Rotation between Diagonal Krein Metric `σ_z` and Light-Cone Metric `σ_x` (Turn 04 Section 1.1):**
Conjugating the `Cl(1,1)` para-Kähler triad `(sigmaZ, sigmaX, epsSymp)` by the unscaled
Walsh–Hadamard matrix `hadamardBlock = !![1, 1; 1, -1]` exchanges the diagonal Krein metric
`σ_z` and the off-diagonal light-cone hyperbolic metric `σ_x`, while reversing the symplectic
orientation `ε`:
1. `Wᵀ σ_z W = 2 σ_x` and `Wᵀ σ_x W = 2 σ_z`,
2. `Wᵀ ε W = -2 ε`,
3. `(W v)ᵀ σ_z (W v) = 4 v₀ v₁ = 2 (vᵀ σ_x v)`. -/
theorem walshHadamard2_krein_lightCone_metric_rotation (v0 v1 : R) :
    (hadamardBlock : Matrix (Fin 2) (Fin 2) R)ᵀ * sigmaZ * hadamardBlock =
      (2 : R) • sigmaX ∧
    (hadamardBlock : Matrix (Fin 2) (Fin 2) R)ᵀ * sigmaX * hadamardBlock =
      (2 : R) • sigmaZ ∧
    (hadamardBlock : Matrix (Fin 2) (Fin 2) R)ᵀ * epsSymp * hadamardBlock =
      -(2 : R) • epsSymp ∧
    dotProduct (Matrix.mulVec (hadamardBlock : Matrix (Fin 2) (Fin 2) R) ![v0, v1])
      (Matrix.mulVec sigmaZ
        (Matrix.mulVec (hadamardBlock : Matrix (Fin 2) (Fin 2) R) ![v0, v1])) =
      4 * v0 * v1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hadamardBlock, sigmaZ, sigmaX, Matrix.mul_apply, Matrix.transpose_apply,
        Fin.sum_univ_two] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hadamardBlock, sigmaZ, sigmaX, Matrix.mul_apply, Matrix.transpose_apply,
        Fin.sum_univ_two] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hadamardBlock, epsSymp, Matrix.mul_apply, Matrix.transpose_apply,
        Fin.sum_univ_two] <;> ring
  · simp [hadamardBlock, sigmaZ, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

/-- General non-commutative ring lemma: for pairwise anticommuting elements `x, y, z` in `[Ring A]`,
the commutator of the quadratic bivectors `x * y` and `y * z` is `2 • (x * y² * z)`. -/
theorem clifford_bivector_comm_of_anticomm {A : Type*} [Ring A] {x y z : A}
    (hxy : anticomm x y = 0) (hyz : anticomm y z = 0) (hxz : anticomm x z = 0) :
    comm (x * y) (y * z) = (2 : ℤ) • (x * (y * y) * z) := by
  have hyx : y * x = -(x * y) := eq_neg_of_add_eq_zero_right hxy
  have hzy : z * y = -(y * z) := eq_neg_of_add_eq_zero_right hyz
  have hzx : z * x = -(x * z) := eq_neg_of_add_eq_zero_right hxz
  have hrev : (y * z) * (x * y) = -(x * (y * y) * z) := by
    calc (y * z) * (x * y)
      _ = y * (z * x) * y := by noncomm_ring
      _ = y * -(x * z) * y := by rw [hzx]
      _ = -(y * x) * (z * y) := by noncomm_ring
      _ = -(-(x * y)) * -(y * z) := by rw [hyx, hzy]
      _ = -(x * (y * y) * z) := by noncomm_ring
  dsimp [comm]
  rw [hrev]
  noncomm_ring

/-- **`MCP₃` Pass-5 `n`-Site Quadratic Bivector `so(n, n)` Lie Subalgebra Closure in `OpMatTower B n` (Turn 05 Section 4):**
For any tower depth `n : ℕ` and non-commutative ring `[Ring B]`, the quadratic products of
distinct Jordan–Wigner generators close under the Lie commutator into the split orthogonal
Lie algebra `so(n, n)`:
1. `[E_i^{(n)} E_j^{(n)}, E_j^{(n)} E_k^{(n)}] = 2 E_i^{(n)} E_k^{(n)}` for pairwise distinct `i, j, k`,
2. `[Γ_i^{(n)} Γ_j^{(n)}, Γ_j^{(n)} Γ_k^{(n)}] = -2 Γ_i^{(n)} Γ_k^{(n)}` for pairwise distinct `i, j, k`,
3. `[E_i^{(n)} Γ_j^{(n)}, Γ_j^{(n)} E_k^{(n)}] = -2 E_i^{(n)} E_k^{(n)}` for `i ≠ k` and arbitrary `j`. -/
theorem towerJW_quadratic_bivector_sonn_lie_closure
    (B : Type*) [Ring B] (n : ℕ) {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    comm (towerJWPos B n i * towerJWPos B n j)
         (towerJWPos B n j * towerJWPos B n k) =
      (2 : ℤ) • (towerJWPos B n i * towerJWPos B n k) ∧
    comm (towerJWNeg B n i * towerJWNeg B n j)
         (towerJWNeg B n j * towerJWNeg B n k) =
      -(2 : ℤ) • (towerJWNeg B n i * towerJWNeg B n k) ∧
    comm (towerJWPos B n i * towerJWNeg B n j)
         (towerJWNeg B n j * towerJWPos B n k) =
      -(2 : ℤ) • (towerJWPos B n i * towerJWPos B n k) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [clifford_bivector_comm_of_anticomm
          (towerJWPos_anticomm B n i j hij)
          (towerJWPos_anticomm B n j k hjk)
          (towerJWPos_anticomm B n i k hik),
        towerJWPos_sq B n j, mul_one]
  · rw [clifford_bivector_comm_of_anticomm
          (towerJWNeg_anticomm B n i j hij)
          (towerJWNeg_anticomm B n j k hjk)
          (towerJWNeg_anticomm B n i k hik),
        towerJWNeg_sq B n j]
    noncomm_ring
  · have h_gj_ek : anticomm (towerJWNeg B n j) (towerJWPos B n k) = 0 := by
      have h := towerJWPos_neg_anticomm B n k j
      dsimp [anticomm] at h ⊢
      abel_nf at h ⊢
      exact h
    rw [clifford_bivector_comm_of_anticomm
          (towerJWPos_neg_anticomm B n i j)
          h_gj_ek
          (towerJWPos_anticomm B n i k hik),
        towerJWNeg_sq B n j]
    noncomm_ring

/-- **`MCP₃` Pass-5 Codebase Reuse (`Cl11MarkovJonesEngine` & `Cl11TensorTowerNormalizedTrace`):**
Directly reuses `InfoGeometry.Clifford.Cl11MarkovJonesEngine` and
`InfoGeometry.Clifford.Cl11TensorTowerNormalizedTrace` to establish:
1. One-step and multi-step stability of `cl11MarkovTraceNet` along `cl11InductiveAlgebraNet`
   (`cl11_normalizedTrace_one_step`, `cl11_normalizedTrace_stable_embedMap`),
2. Raw determinant squaring `det(A ⊗ I₂) = (det A)²` and normalized log-abs-det stability
   (`cl11_rawDet_one_step_square`, `cl11_normalizedLogAbsDet_one_step`),
3. Preservation of real self-adjoint projections under `matStageEmbed` and trace doubling
   `Tr(A ⊗ I₂) = 2 Tr(A)` (`matStageEmbed_preserves_real_projection`, `trace_matStageEmbed_readout`). -/
theorem cl11_markovJones_and_normalizedTrace_reuse
    (m n : ℕ) (hmn : m ≤ n)
    (A : InfoGeometry.Clifford.Cl11TensorTower.MatStage m)
    (P : InfoGeometry.Clifford.Cl11TensorTower.MatStage m)
    (hP : IsIdempotentElem P ∧ star P = P) :
    InfoGeometry.Clifford.Cl11MarkovJonesEngine.cl11MarkovTraceNet.trace (m + 1)
      (InfoGeometry.Clifford.Cl11MarkovJonesEngine.cl11InductiveAlgebraNet.embed m A) =
      InfoGeometry.Clifford.Cl11MarkovJonesEngine.cl11MarkovTraceNet.trace m A ∧
    InfoGeometry.Clifford.Cl11MarkovJonesEngine.cl11MarkovTraceNet.trace n
      (InfoGeometry.Clifford.Cl11MarkovJonesEngine.cl11InductiveAlgebraNet.embedMap m n hmn A) =
      InfoGeometry.Clifford.Cl11MarkovJonesEngine.cl11MarkovTraceNet.trace m A ∧
    Matrix.det (InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed m A) =
      Matrix.det A ^ (2 : ℕ) ∧
    InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet (m + 1)
      (InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed m A) =
      InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet m A ∧
    (IsIdempotentElem (InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed m P) ∧
     star (InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed m P) =
       InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed m P) ∧
    Matrix.trace (InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed m A) =
      2 * Matrix.trace A :=
  ⟨InfoGeometry.Clifford.Cl11MarkovJonesEngine.cl11_normalizedTrace_one_step m A,
   InfoGeometry.Clifford.Cl11MarkovJonesEngine.cl11_normalizedTrace_stable_embedMap m n hmn A,
   InfoGeometry.Clifford.Cl11MarkovJonesEngine.cl11_rawDet_one_step_square m A,
   InfoGeometry.Clifford.Cl11MarkovJonesEngine.cl11_normalizedLogAbsDet_one_step m A,
   InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed_preserves_real_projection m P hP,
   InfoGeometry.Clifford.Cl11TensorTower.trace_matStageEmbed_readout m A⟩

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

/-- **`MCP₄` Turn 07 `Cl(1,1)` Multivector Attention Bilinear Readout & Quadratic Norm:**
For any `Cl(1,1)` multivector `M = cl11Elem di dp ds dc = d_i I₂ + d_p σ_z + d_s σ_x + d_c ε`:
1. `trace(M) = 2 d_i` (scalar attention channel readout),
2. `trace(σ_z M) = 2 d_p` (polar/Krein channel readout),
3. `trace(σ_x M) = 2 d_s` (symmetric dissipative channel readout),
4. `trace(ε M) = -2 d_c` (symplectic/causal bivector channel readout),
5. `det(M) = d_i² - d_p² - d_s² + d_c²` (split-quaternion / `Cl(1,1)` norm). -/
theorem clifford_attention_multivector_bilinear_readout (di dp ds dc : R) :
    Matrix.trace (cl11Elem di dp ds dc) = (2 : R) * di ∧
    Matrix.trace (sigmaZ * cl11Elem di dp ds dc) = (2 : R) * dp ∧
    Matrix.trace (sigmaX * cl11Elem di dp ds dc) = (2 : R) * ds ∧
    Matrix.trace (epsSymp * cl11Elem di dp ds dc) = -(2 : R) * dc ∧
    (cl11Elem di dp ds dc).det = di ^ 2 - dp ^ 2 - ds ^ 2 + dc ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [cl11Elem, Matrix.trace, Matrix.diag, Fin.sum_univ_two]; ring
  · simp [cl11Elem, sigmaZ, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]; ring
  · simp [cl11Elem, sigmaX, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]; ring
  · simp [cl11Elem, epsSymp, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]; ring
  · simp [cl11Elem, Matrix.det_fin_two]; ring

/-- Operator-valued Walsh–Hadamard antisymmetric difference block `E_pm(X) = !![X, -X; -X, X]`
and chiral bivector block `B_wh(X) = !![X, -X; X, -X]` over `[Ring B]` (Turn 08 Sections 2–3). -/
def walshHadamardDiffBlock {B : Type*} [Ring B] (X : B) : Matrix (Fin 2) (Fin 2) B :=
  !![X, -X; -X, X]

/-- Operator-valued Walsh–Hadamard chiral bivector block `B_wh(X) = !![X, -X; X, -X]` (`(I₂ + σ_x)(I₂ - σ_z)/2` seed). -/
def walshHadamardBivectorBlock {B : Type*} [Ring B] (X : B) : Matrix (Fin 2) (Fin 2) B :=
  !![X, -X; X, -X]

/-- **`MCP₄` Turn 08 Walsh–Hadamard Bivector Nilpotency, Commutator & Idempotency Defect over `[Ring B]`:**
For any non-commutative operators `X, Y ∈ B`:
1. The chiral Walsh–Hadamard bivector block `B_wh(X) = !![X, -X; X, -X]` annihilates `B_wh(Y)`
   identically (`B_wh(X) * B_wh(Y) = 0`),
2. The symmetric Walsh–Hadamard difference block `E_pm(X) = !![X, -X; -X, X]` satisfies
   `E_pm(X) * E_pm(Y) = E_pm(2 X Y)`,
3. Its commutator is `comm (E_pm X) (E_pm Y) = E_pm(2 [X, Y])`,
4. Its scaled idempotency defect is `E_pm(X)² - 2 E_pm(X) = E_pm(2(X² - X))`! -/
theorem walshHadamard_bivector_commutator_and_idempotency_defect
    {B : Type*} [Ring B] (X Y : B) :
    walshHadamardBivectorBlock X * walshHadamardBivectorBlock Y = 0 ∧
    walshHadamardDiffBlock X * walshHadamardDiffBlock Y =
      walshHadamardDiffBlock (X * Y + X * Y) ∧
    comm (walshHadamardDiffBlock X) (walshHadamardDiffBlock Y) =
      walshHadamardDiffBlock (comm X Y + comm X Y) ∧
    walshHadamardDiffBlock X * walshHadamardDiffBlock X -
      (walshHadamardDiffBlock X + walshHadamardDiffBlock X) =
      walshHadamardDiffBlock ((X * X - X) + (X * X - X)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    { ext i j
      fin_cases i <;> fin_cases j <;>
        simp [walshHadamardBivectorBlock, walshHadamardDiffBlock, comm,
          Matrix.mul_apply, Fin.sum_univ_two] <;>
        noncomm_ring }

/-- **`MCP₄` Turn 10 Socratic Elenchus 3 (Hadamard Causal Mask Destroys Zero-Row-Sum Spectral Structure):**
For any `2 × 2` zero-row-sum spectral matrix `S = !![a, -a; -b, b]` (whose row sums are `a + (-a) = 0`
and `-b + b = 0`), entrywise (Hadamard) multiplication by the lower-triangular causal mask
`M_causal = !![1, 0; 1, 1]` yields `S_masked = !![a, 0; -b, b]`, whose top row sum is `a + 0 = a`,
violating the zero-row-sum invariant whenever `a ≠ 0`! -/
theorem elenchus_hadamard_mask_destroys_causal_zero (a b : R) :
    ((!![a, -a; -b, b] : Matrix (Fin 2) (Fin 2) R) 0 0 +
     (!![a, -a; -b, b] : Matrix (Fin 2) (Fin 2) R) 0 1 = 0) ∧
    ((!![a * 1, (-a) * 0; (-b) * 1, b * 1] : Matrix (Fin 2) (Fin 2) R) 0 0 +
     (!![a * 1, (-a) * 0; (-b) * 1, b * 1] : Matrix (Fin 2) (Fin 2) R) 0 1 = a) := by
  refine ⟨?_, ?_⟩ <;> simp

/-- **`MCP₄` Turns 05 & 07 Universal `Cl(1,1) ≅ M₂(R)` Basis Expansion Identity:**
Every `2 × 2` matrix `M : Matrix (Fin 2) (Fin 2) R` is reconstructed (up to scale `2`) from its
four `Cl(1,1)` trace inner products:
`2 M = tr(M) I₂ + tr(σ_z M) σ_z + tr(σ_x M) σ_x - tr(ε M) ε`. -/
theorem cl11_universal_matrix_basis_expansion (M : Matrix (Fin 2) (Fin 2) R) :
    (2 : R) • M =
      Matrix.trace M • (1 : Matrix (Fin 2) (Fin 2) R) +
      Matrix.trace (sigmaZ * M) • sigmaZ +
      Matrix.trace (sigmaX * M) • sigmaX -
      Matrix.trace (epsSymp * M) • epsSymp := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigmaZ, sigmaX, epsSymp, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

/-- **`MCP₄` Turn 07–08 Scale-Trapping Subalgebra Closure & FWHT XOR-Convolution Diagonalization:**
1. **Scale-Trapping (Aporia 1)**: `(D₀ + σ_x D₁)² = (D₀² + D₁ τ(D₁)) + σ_x (τ(D₀) D₁ + D₁ D₀)`.
2. **FWHT XOR Diagonalization**: `H₂ (c₀ I₂ + c₁ σ_x) H₂ = 2 diag(c₀ + c₁, c₀ - c₁)`. -/
theorem scale_trapping_and_fwht_xor_diagonalization (a0 b0 a1 b1 c0 c1 : R) :
    ((!![a0, 0; 0, b0] : Matrix (Fin 2) (Fin 2) R) + sigmaX * !![a1, 0; 0, b1]) *
      (!![a0, 0; 0, b0] + sigmaX * !![a1, 0; 0, b1]) =
      (!![a0, 0; 0, b0] * !![a0, 0; 0, b0] + !![a1, 0; 0, b1] * !![b1, 0; 0, a1]) +
      sigmaX * (!![b0, 0; 0, a0] * !![a1, 0; 0, b1] + !![a1, 0; 0, b1] * !![a0, 0; 0, b0]) ∧
    walshHadamard2 * (c0 • (1 : Matrix (Fin 2) (Fin 2) R) + c1 • sigmaX) * walshHadamard2 =
      (2 : R) • !![c0 + c1, 0; 0, c0 - c1] := by
  refine ⟨?_, ?_⟩ <;>
    { ext i j; fin_cases i <;> fin_cases j <;>
        simp [walshHadamard2, sigmaX, Matrix.mul_apply, Matrix.vecMul,
          dotProduct, Fin.sum_univ_two] <;>
        ring }

/-- **`MCP₄` Turn 07–08 Aporia 2 (Monarch Coarse-Block Rank-1 Bottleneck vs. Square Rank Escape):**
Every coarse block `!![u₀ v₀, u₀ v₁; u₁ v₀, u₁ v₁]` of a single Monarch pass has `det = 0`,
whereas the two-path sum in `M_N²` has determinant `(u₀ u₁' - u₁ u₀')(v₀ v₁' - v₁ v₀')`. -/
theorem monarch_coarse_block_rank1_vs_square_escape (u0 u1 v0 v1 u0' u1' v0' v1' : R) :
    (!![u0 * v0, u0 * v1; u1 * v0, u1 * v1] : Matrix (Fin 2) (Fin 2) R).det = 0 ∧
    (!![u0 * v0 + u0' * v0', u0 * v1 + u0' * v1';
        u1 * v0 + u1' * v0', u1 * v1 + u1' * v1'] : Matrix (Fin 2) (Fin 2) R).det =
      (u0 * u1' - u1 * u0') * (v0 * v1' - v1 * v0') := by
  refine ⟨?_, ?_⟩ <;>
    (simp [Matrix.det_fin_two]; ring)

/-- **`MCP₄` Turn 10 Socratic Elenchus 1A (Position-Independent Kronecker Commutativity Collapse):**
When `CliffordHadamardAttention` uses sequence-constant weights `(n_bits, d, 1)`, the stage-1
operator `B₁ = b₁ ⊗ I₂` and stage-2 operator `B₂ = I₂ ⊗ b₂` commute identically (`[B₁, B₂] = 0`)
for ALL `2 × 2` matrices `b₁, b₂`, collapsing the multi-stage cascade to `b₁ ⊗ b₂`! -/
theorem elenchus_position_independent_kronecker_commute
    (a11 a12 a21 a22 b11 b12 b21 b22 : R) :
    comm (!![a11, 0, a12, 0;
             0, a11, 0, a12;
             a21, 0, a22, 0;
             0, a21, 0, a22] : Matrix (Fin 4) (Fin 4) R)
         (!![b11, b12, 0, 0;
             b21, b22, 0, 0;
             0, 0, b11, b12;
             0, 0, b21, b22] : Matrix (Fin 4) (Fin 4) R) = 0 := by
  ext i j
  simp only [comm, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- **`MCP₄` Turn 10 Non-Commutative Talaska Boundary Formula ≡ Block-LDU Schur Complement:**
In any `[Ring B]`, if `R_inv` is the two-sided resolvent inverse of `1 - W_int`
(`(1 - W_int) * R_inv = 1` and `R_inv * (1 - W_int) = 1`), then the Block-LDU factorization of the
Plabic system `!![1 - W_int, -B_in; B_out, D_direct]` has lower-right Schur complement equal
identically to Talaska's boundary measurement operator `D_direct + B_out * R_inv * B_in`! -/
theorem talaska_boundary_eq_block_ldu_schur {B : Type*} [Ring B]
    (W_int R_inv B_in B_out D_direct : B)
    (h_right : (1 - W_int) * R_inv = 1) (h_left : R_inv * (1 - W_int) = 1) :
    (!![1, 0; B_out * R_inv, 1] : Matrix (Fin 2) (Fin 2) B) *
      !![1 - W_int, 0; 0, D_direct + B_out * R_inv * B_in] *
      !![1, -(R_inv * B_in); 0, 1] =
      !![1 - W_int, -B_in; B_out, D_direct] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [← mul_assoc (1 - W_int) R_inv B_in, h_right, one_mul]
  · rw [mul_assoc B_out R_inv (1 - W_int), h_left, mul_one]
  · have h1 : B_out * R_inv * (1 - W_int) * (R_inv * B_in) = B_out * R_inv * B_in := by
      rw [mul_assoc (B_out * R_inv) (1 - W_int) (R_inv * B_in),
          ← mul_assoc (1 - W_int) R_inv B_in, h_right, one_mul]
    rw [h1]; noncomm_ring

/-- `4 × 4` 2-qubit Walsh–Hadamard matrix `H₄ = H₂ ⊗ H₂`. -/
def walshHadamard4 : Matrix (Fin 4) (Fin 4) R :=
  !![1,  1,  1,  1;
     1, -1,  1, -1;
     1,  1, -1, -1;
     1, -1, -1,  1]

/-- `4 × 4` dyadic XOR-convolution matrix `xorConv4 c₀₀ c₀₁ c₁₀ c₁₁` whose `(i, j)` entry is `c_{i ⊕ j}`. -/
def xorConv4 (c₀₀ c₀₁ c₁₀ c₁₁ : R) : Matrix (Fin 4) (Fin 4) R :=
  !![c₀₀, c₀₁, c₁₀, c₁₁;
     c₀₁, c₀₀, c₁₁, c₁₀;
     c₁₀, c₁₁, c₀₀, c₀₁;
     c₁₁, c₁₀, c₀₁, c₀₀]

/-- **`MCP₄` Pass-3 2-Qubit Butterfly Factorization & Full `4 × 4` FWHT XOR-Convolution Diagonalization:**
1. **Cooley–Tukey / Monarch Butterfly Factorization**: `H₄ = (H₂ ⊗ I₂) * (I₂ ⊗ H₂)` and `H₄² = 4 I₄`.
2. **Simultaneous 4-Channel XOR-Convolution Diagonalization**:
   `H₄ * xorConv4 c₀₀ c₀₁ c₁₀ c₁₁ * H₄ = 4 • diag(c₀₀+c₀₁+c₁₀+c₁₁, c₀₀-c₀₁+c₁₀-c₁₁, c₀₀+c₀₁-c₁₀-c₁₁, c₀₀-c₀₁-c₁₀+c₁₁)`. -/
theorem walshHadamard4_butterfly_and_xorConv4_diagonalization (c₀₀ c₀₁ c₁₀ c₁₁ : R) :
    (walshHadamard4 : Matrix (Fin 4) (Fin 4) R) =
      !![(1 : R), 0,  1,  0;
         0,       1,  0,  1;
         1,       0, -1,  0;
         0,       1,  0, -1] *
      !![(1 : R),  1, 0,  0;
         1,       -1, 0,  0;
         0,        0, 1,  1;
         0,        0, 1, -1] ∧
    (walshHadamard4 : Matrix (Fin 4) (Fin 4) R) * walshHadamard4 =
      (4 : R) • (1 : Matrix (Fin 4) (Fin 4) R) ∧
    (walshHadamard4 : Matrix (Fin 4) (Fin 4) R) * xorConv4 c₀₀ c₀₁ c₁₀ c₁₁ * walshHadamard4 =
      !![(4 : R) * (c₀₀ + c₀₁ + c₁₀ + c₁₁), 0, 0, 0;
         0, (4 : R) * (c₀₀ - c₀₁ + c₁₀ - c₁₁), 0, 0;
         0, 0, (4 : R) * (c₀₀ + c₀₁ - c₁₀ - c₁₁), 0;
         0, 0, 0, (4 : R) * (c₀₀ - c₀₁ - c₁₀ + c₁₁)] := by
  refine ⟨?_, ?_, ?_⟩ <;>
    { ext i j
      fin_cases i <;> fin_cases j <;>
        simp [walshHadamard4, xorConv4, Matrix.mul_apply, Fin.sum_univ_four] <;>
        ring }

/-- Recursive `n`-qubit Walsh–Hadamard operator `H_{2^n}` in `OpMatTower B n` over `[Ring B]`. -/
def towerWalshHadamard (B : Type*) [Ring B] : (n : ℕ) → OpMatTower B n
  | 0 => 1
  | n + 1 =>
    let H := towerWalshHadamard B n
    !![H,  H;
       H, -H]

/-- Uniform `2 × 2` operator Walsh–Hadamard block square over any `[Ring B]`. -/
theorem twoByTwo_walshHadamard_sq {B : Type*} [Ring B] (H : B) (k : ℕ)
    (hH : H * H = k • (1 : B)) :
    (!![H, H; H, -H] : Matrix (Fin 2) (Fin 2) B) * !![H, H; H, -H] =
      (2 * k) • (1 : Matrix (Fin 2) (Fin 2) B) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, two_mul, add_smul, hH]

/-- **`MCP₄` Pass-3 Recursive `n`-Qubit Walsh–Hadamard Scaling Involution in `OpMatTower B n`:**
For every `n : ℕ` and any non-commutative ring `B`,
`towerWalshHadamard B n * towerWalshHadamard B n = (2 ^ n : ℕ) • 1`. -/
theorem towerWalshHadamard_mul_self (B : Type*) [Ring B] (n : ℕ) :
    towerWalshHadamard B n * towerWalshHadamard B n =
      (2 ^ n : ℕ) • (1 : OpMatTower B n) := by
  induction n with
  | zero =>
    change (1 : B) * 1 = (1 : ℕ) • (1 : B)
    simp
  | succ n ih =>
    have hstep := twoByTwo_walshHadamard_sq (B := OpMatTower B n) (towerWalshHadamard B n) (2 ^ n) ih
    have hpow : 2 * 2 ^ n = 2 ^ (n + 1) := by ring
    rw [hpow] at hstep
    exact hstep

/-- **`MCP₄` Pass-3 Universal Non-Commutative Pushthrough & Woodbury Matrix Identity:**
In any non-commutative ring `B`:
1. **Pushthrough Identity**: `U * (1 + V * U) = (1 + U * V) * U`.
2. **Non-Commutative Woodbury Identity**: if `A * A_inv = 1`, `C * C_inv = 1`, and
   `(C_inv + V * A_inv * U) * W = 1`, then
   `(A + U * C * V) * (A_inv - A_inv * U * W * V * A_inv) = 1`. -/
theorem noncomm_pushthrough_and_woodbury_identity
    {B : Type*} [Ring B] (A A_inv C C_inv U V W : B)
    (hA : A * A_inv = 1) (hC : C * C_inv = 1)
    (hW : (C_inv + V * A_inv * U) * W = 1) :
    U * (1 + V * U) = (1 + U * V) * U ∧
    (A + U * C * V) * (A_inv - A_inv * U * W * V * A_inv) = 1 := by
  refine ⟨by noncomm_ring, ?_⟩
  calc (A + U * C * V) * (A_inv - A_inv * U * W * V * A_inv)
    _ = A * A_inv - (A * A_inv) * U * W * V * A_inv +
        U * C * (V * A_inv) - U * C * (V * A_inv * U) * W * V * A_inv := by noncomm_ring
    _ = 1 - U * W * V * A_inv +
        U * C * (V * A_inv) - U * C * (V * A_inv * U) * W * V * A_inv := by
        rw [hA, one_mul]
    _ = 1 - U * (C * C_inv) * W * V * A_inv +
        U * C * (V * A_inv) - U * C * (V * A_inv * U) * W * V * A_inv := by
        rw [hC, mul_one]
    _ = 1 + U * C * V * A_inv - U * C * ((C_inv + V * A_inv * U) * W) * V * A_inv := by
        noncomm_ring
    _ = 1 + U * C * V * A_inv - U * C * 1 * V * A_inv := by rw [hW]
    _ = 1 := by noncomm_ring

/-- **`MCP₄` Pass-4 Recursive Butterfly Conjugation of Block-Diagonal vs. Block-XOR Operators in `OpMatTower B (n + 1)`:**
For any non-commutative ring `[Ring B]`, tower depth `n : ℕ`, and `D₀, D₁, C₀, C₁ : OpMatTower B n`,
let `H = towerWalshHadamard B n` and `H_next = towerWalshHadamard B (n + 1)`:
1. **Block-Diagonal to Block-XOR Duality**:
   `H_next * !![D₀, 0; 0, D₁] * H_next = !![H * (D₀ + D₁) * H, H * (D₀ - D₁) * H; H * (D₀ - D₁) * H, H * (D₀ + D₁) * H]`.
2. **Recursive Block-XOR Diagonalization**:
   `H_next * !![C₀, C₁; C₁, C₀] * H_next = !![(2 : ℤ) • (H * (C₀ + C₁) * H), 0; 0, (2 : ℤ) • (H * (C₀ - C₁) * H)]`. -/
theorem towerWalshHadamard_conjugation_diag_and_xor
    (B : Type*) [Ring B] (n : ℕ) (D₀ D₁ C₀ C₁ : OpMatTower B n) :
    let H := towerWalshHadamard B n
    towerWalshHadamard B (n + 1) * (!![D₀, 0; 0, D₁] : OpMatTower B (n + 1)) *
      towerWalshHadamard B (n + 1) =
      (!![H * (D₀ + D₁) * H, H * (D₀ - D₁) * H;
          H * (D₀ - D₁) * H, H * (D₀ + D₁) * H] : OpMatTower B (n + 1)) ∧
    towerWalshHadamard B (n + 1) * (!![C₀, C₁; C₁, C₀] : OpMatTower B (n + 1)) *
      towerWalshHadamard B (n + 1) =
      (!![(2 : ℤ) • (H * (C₀ + C₁) * H), 0;
          0, (2 : ℤ) • (H * (C₀ - C₁) * H)] : OpMatTower B (n + 1)) := by
  dsimp [towerWalshHadamard]
  constructor <;>
    { ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        noncomm_ring }

/-- `4 × 4` Monarch bit-reversal / stride permutation matrix `P_stride` swapping indices `1 ↔ 2`. -/
def monarchStridePerm4 : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, 0, 0;
     0, 0, 1, 0;
     0, 1, 0, 0;
     0, 0, 0, 1]

/-- **`MCP₄` Pass-4 Monarch Stride Permutation Involution & Kronecker Tensor-Factor Swap Theorem:**
1. `monarchStridePerm4 * monarchStridePerm4 = 1` and `monarchStridePerm4ᵀ = monarchStridePerm4`.
2. Conjugating the fine-grained block-diagonal matrix `I₂ ⊗ B` by `monarchStridePerm4` swaps the
   tensor factors to `B ⊗ I₂`.
3. For general position-dependent block-diagonal `diag(L₀, L₁)` and `diag(R₀, R₁)`, the Monarch
   product `(P_stride * diag(L₀, L₁) * P_stride) * diag(R₀, R₁)` populates all four `2 × 2` blocks! -/
theorem monarchStridePerm4_kronecker_swap_and_full_mixing
    (b00 b01 b10 b11 l0 l1 r1 : R) :
    (monarchStridePerm4 : Matrix (Fin 4) (Fin 4) R) * monarchStridePerm4 = 1 ∧
    (monarchStridePerm4 : Matrix (Fin 4) (Fin 4) R)ᵀ = monarchStridePerm4 ∧
    (monarchStridePerm4 : Matrix (Fin 4) (Fin 4) R) *
      !![b00, b01, 0,   0;
         b10, b11, 0,   0;
         0,   0,   b00, b01;
         0,   0,   b10, b11] * monarchStridePerm4 =
      !![b00, 0,   b01, 0;
         0,   b00, 0,   b01;
         b10, 0,   b11, 0;
         0,   b10, 0,   b11] ∧
    ((monarchStridePerm4 : Matrix (Fin 4) (Fin 4) R) *
      !![1,  0,  0,  0;
         l0, 1,  0,  0;
         0,  0,  1,  0;
         0,  0,  l1, 1] * monarchStridePerm4) *
      !![1, 0, 0, 0;
         0, 1, 0, 0;
         0, 0, 1, r1;
         0, 0, 0, 1] =
      !![1,  0,  0,  0;
         0,  1,  0,  0;
         l0, 0,  1,  r1;
         0,  l1, 0,  1] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    { ext i j
      simp only [monarchStridePerm4, Matrix.mul_apply, Fin.sum_univ_four]
      fin_cases i <;> fin_cases j <;> simp }

/-- **`MCP₄` Pass-4 Talaska Plabic Factored Determinant Law & Twisted vs. Untwisted Loop Pole Dichotomy:**
1. The determinant of the Talaska 4-cycle boundary numerator
   `B_out * plabicCycleAdjugate a1 a2 a3 a4` factors identically as
   `(1 - a1 * a3) * (1 + a1 * a2 * a3 * a4)`.
2. Right-multiplying by `1 - plabicInternalCycle a1 a2 a3 a4` clears the cycle resolvent:
   `(B_out * plabicCycleAdjugate a1 a2 a3 a4) * (1 - plabicInternalCycle a1 a2 a3 a4) = (1 + a1 * a2 * a3 * a4) • B_out`.
3. **Twisted vs. Untwisted Loop Denominator**: At `a1 = a2 = a3 = a4 = 1`, the Postnikov–Talaska
   twisted denominator `det(1 - plabicInternalCycle 1 1 1 1) = 2` is nonsingular, whereas the
   untwisted cycle `!![0, 1; 1, 0]` has `det(1 - !![0, 1; 1, 0]) = 0` (singular pole!). -/
theorem talaska_plabic_factored_det_and_untwisted_pole (a1 a2 a3 a4 : R) :
    ((!![1, a1; a3, 1] : Matrix (Fin 2) (Fin 2) R) *
      plabicCycleAdjugate a1 a2 a3 a4).det =
      (1 - a1 * a3) * (1 + a1 * a2 * a3 * a4) ∧
    ((!![1, a1; a3, 1] : Matrix (Fin 2) (Fin 2) R) *
      plabicCycleAdjugate a1 a2 a3 a4) *
      (1 - plabicInternalCycle a1 a2 a3 a4) =
      (1 + a1 * a2 * a3 * a4) • (!![1, a1; a3, 1] : Matrix (Fin 2) (Fin 2) R) ∧
    (1 - plabicInternalCycle (1 : R) 1 1 1).det = 2 ∧
    (1 - (!![0, (1 : R); 1, 0] : Matrix (Fin 2) (Fin 2) R)).det = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [plabicCycleAdjugate, Matrix.det_fin_two]
    ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [plabicCycleAdjugate, plabicInternalCycle,
        Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two] <;>
      ring
  · simp [plabicInternalCycle, Matrix.det_fin_two]; ring
  · simp [Matrix.det_fin_two]

/-- `4 × 4` cyclic shift permutation matrix `S_cycle,4 = !![0,0,0,1; 1,0,0,0; 0,1,0,0; 0,0,1,0]` (`j ↦ (j + 1) mod 4`). -/
def cyclicShiftMat4 : Matrix (Fin 4) (Fin 4) R :=
  !![0, 0, 0, 1;
     1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0]

/-- `4 × 4` LSB-controlled MSB flip (`CNOT_{0 → 1}`) carry-propagation matrix `!![1,0,0,0; 0,0,0,1; 0,0,1,0; 0,1,0,0]`. -/
def butterflyCarryCNOT4 : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0;
     0, 1, 0, 0]

/-- `4 × 4` unconditioned LSB flip (`I₂ ⊗ σ_x`) butterfly stage `!![0,1,0,0; 1,0,0,0; 0,0,0,1; 0,0,1,0]`. -/
def butterflyLSBFlip4 : Matrix (Fin 4) (Fin 4) R :=
  !![0, 1, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]

/-- **`MCP₄` Pass-5 Cyclic Shift vs. Carry-Free Butterfly CNOT Factorization (Turn 08 Section 2.1):**
Unlike carry-free XOR-swizzle permutations (`I₂ ⊗ σ_x` and `σ_x ⊗ I₂`), which commute and factor
independently by bit-plane, the `4 × 4` cyclic shift `cyclicShiftMat4` (`j ↦ j + 1 mod 4`) requires
an inter-bit carry gate `butterflyCarryCNOT4` (`CNOT_{0 → 1}`) that does not commute with the LSB flip:
1. `butterflyLSBFlip4 * butterflyCarryCNOT4 = cyclicShiftMat4` and
   `butterflyCarryCNOT4 * butterflyLSBFlip4 = cyclicShiftMat4ᵀ`,
2. `butterflyCarryCNOT4² = 1` and `butterflyLSBFlip4² = 1` (each factor is involutive),
3. `[butterflyLSBFlip4, butterflyCarryCNOT4] = cyclicShiftMat4 - cyclicShiftMat4ᵀ` (non-commuting carry defect),
4. `cyclicShiftMat4² = !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0]` (`σ_x ⊗ I₂` MSB flip) and `cyclicShiftMat4⁴ = 1`. -/
theorem cyclicShiftMat4_butterfly_carry_factorization :
    (butterflyLSBFlip4 : Matrix (Fin 4) (Fin 4) R) * butterflyCarryCNOT4 = cyclicShiftMat4 ∧
    (butterflyCarryCNOT4 : Matrix (Fin 4) (Fin 4) R) * butterflyCarryCNOT4 = 1 ∧
    (butterflyLSBFlip4 : Matrix (Fin 4) (Fin 4) R) * butterflyLSBFlip4 = 1 ∧
    comm (butterflyLSBFlip4 : Matrix (Fin 4) (Fin 4) R) butterflyCarryCNOT4 =
      cyclicShiftMat4 - (cyclicShiftMat4 : Matrix (Fin 4) (Fin 4) R)ᵀ ∧
    (cyclicShiftMat4 : Matrix (Fin 4) (Fin 4) R) * cyclicShiftMat4 =
      !![0, 0, 1, 0;
         0, 0, 0, 1;
         1, 0, 0, 0;
         0, 1, 0, 0] ∧
    ((cyclicShiftMat4 : Matrix (Fin 4) (Fin 4) R) * cyclicShiftMat4) *
      (cyclicShiftMat4 * cyclicShiftMat4) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    { ext i j
      simp only [comm, cyclicShiftMat4, butterflyCarryCNOT4, butterflyLSBFlip4,
        Matrix.mul_apply, Matrix.sub_apply, Matrix.transpose_apply, Matrix.one_apply,
        Fin.sum_univ_four]
      fin_cases i <;> fin_cases j <;> simp }

/-- Off-diagonal square plabic transfer numerator `N_sq = !![0, a₁; a₃, 0] * plabicCycleAdjugate a₁ a₂ a₃ a₄`
(Turn 10 Section 2.2 Eqs. 1426–1435). -/
def plabicSquareTransferNum (a1 a2 a3 a4 : R) : Matrix (Fin 2) (Fin 2) R :=
  !![0, a1; a3, 0] * plabicCycleAdjugate a1 a2 a3 a4

/-- **`MCP₄` Pass-5 Square Plabic Disjoint-Path Loop Cancellation & Determinant Factorization (Turn 10 Section 2.2):**
1. The square plabic transfer numerator `plabicSquareTransferNum a1 a2 a3 a4` equals
   `!![-(a1 * a3 * a4), a1; a3, a1 * a2 * a3]`.
2. Right-multiplying by `1 - plabicInternalCycle a1 a2 a3 a4` recovers the loop-scaled boundary
   source-to-sink matrix `(1 + a1 * a2 * a3 * a4) • !![0, a1; a3, 0]`.
3. In its determinant `(-(a1 * a3 * a4)) * (a1 * a2 * a3) - a1 * a3 = -a1 * a3 * (1 + a1 * a2 * a3 * a4)`,
   the internal 4-cycle polynomial `(1 + a1 * a2 * a3 * a4)` factors out identically, leaving the
   loop-independent disjoint-path determinant `-a1 * a3` (Turn 10 Eq. 1435)! -/
theorem plabicSquareTransferNum_loop_cancellation_and_factorization (a1 a2 a3 a4 : R) :
    plabicSquareTransferNum a1 a2 a3 a4 =
      !![-(a1 * a3 * a4), a1;
         a3, a1 * a2 * a3] ∧
    plabicSquareTransferNum a1 a2 a3 a4 * (1 - plabicInternalCycle a1 a2 a3 a4) =
      (1 + a1 * a2 * a3 * a4) • (!![0, a1; a3, 0] : Matrix (Fin 2) (Fin 2) R) ∧
    (plabicSquareTransferNum a1 a2 a3 a4).det =
      -(a1 * a3) * (1 + a1 * a2 * a3 * a4) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [plabicSquareTransferNum, plabicCycleAdjugate, Matrix.mul_apply, Fin.sum_univ_two] <;>
      ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [plabicSquareTransferNum, plabicCycleAdjugate, plabicInternalCycle,
        Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two] <;>
      ring
  · simp [plabicSquareTransferNum, plabicCycleAdjugate, Matrix.det_fin_two]
    ring

/-- **`MCP₄` Pass-5 Codebase Reuse (`Cl11TensorStageFactorization` & `KantorCornerAnomaly`):**
Directly reuses `InfoGeometry.Clifford.Cl11TensorStageFactorization` and
`InfoGeometry.OperatorAlgebra.PeirceSpine.KantorCornerAnomaly` to establish:
1. Finite-stage tensor factorization naturality under `stageEmbed`:
   `stageTensorFactorization n (m + 1) (stageEmbed (n + m) (stageTensorFactorization n m).symm z) = (id ⊗ stageEmbed m) z`
   and colimit bond compatibility `factorizedStageToLimit_stageEmbed` (`Cl11TensorStageFactorization`),
2. Associative Peirce homotope Jacobi identity `upper_homotope_jacobi`, corner nilpotency
   `upper_kantor_anomaly_corner`, and right/left reference corner commutator pairings
   `upper_anomaly_reference_pairing` and `upper_anomaly_left_reference_pairing` (`KantorCornerAnomaly`). -/
theorem cl11_stageTensorFactorization_and_kantorCorner_reuse
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C Z W : B)
    (n m : ℕ)
    (z : TensorProduct ℝ
      (InfoGeometry.Clifford.Cl11TensorTower.MatStage n)
      (InfoGeometry.Clifford.Cl11TensorTower.MatStage m)) :
    (InfoGeometry.Clifford.Cl11TensorStageFactorization.stageTensorFactorization n (m + 1)
       (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed (n + m)
         ((InfoGeometry.Clifford.Cl11TensorStageFactorization.stageTensorFactorization n m).symm z)) =
       TensorProduct.map
         (LinearMap.id :
           InfoGeometry.Clifford.Cl11TensorTower.MatStage n →ₗ[ℝ]
             InfoGeometry.Clifford.Cl11TensorTower.MatStage n)
         (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed m).toLinearMap z ∧
     InfoGeometry.Clifford.Cl11TensorStageFactorization.factorizedStageToLimit n (m + 1)
       (TensorProduct.map
         (LinearMap.id :
           InfoGeometry.Clifford.Cl11TensorTower.MatStage n →ₗ[ℝ]
             InfoGeometry.Clifford.Cl11TensorTower.MatStage n)
         (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed m).toLinearMap z) =
       InfoGeometry.Clifford.Cl11TensorStageFactorization.factorizedStageToLimit n m z) ∧
    (upperHomotopeBracket P C A (upperHomotopeBracket P C Z W) +
       upperHomotopeBracket P C Z (upperHomotopeBracket P C W A) +
       upperHomotopeBracket P C W (upperHomotopeBracket P C A Z) = 0 ∧
     opKantorAnomaly (conePlus P A) (conePlus P Z) (coneMinus P C) * coneMinus P C =
       comm (qgtPlus P A C) (qgtPlus P Z C) ∧
     coneMinus P C * upperHomotopeBracket P C A Z =
       comm (qgtMinus P A C) (qgtMinus P Z C)) :=
  ⟨⟨InfoGeometry.Clifford.Cl11TensorStageFactorization.stageTensorFactorization_stageEmbed_map n m z,
    InfoGeometry.Clifford.Cl11TensorStageFactorization.factorizedStageToLimit_stageEmbed n m z⟩,
   ⟨upper_homotope_jacobi hP C A Z W,
    upper_anomaly_reference_pairing hP A C Z,
    upper_anomaly_left_reference_pairing P A C Z⟩⟩

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

/-- **`MCP₅` Codebase Reuse (`TransferDefect`, `GradingPerturbation` & `Unipotent`): Peirce Plabic Resolvent, Perturbed Grading Square & Steinberg Braid Bridge:**
In any `[Ring B]` with idempotent `P * P = P`:
1. The ordered Peirce factors `(1 ± conePlus * coneMinus)(1 ± coneMinus * conePlus)` reduce to `1 ± V`
   (`TransferDefect.qgt_primal_dual_euler_zeta_factorization`),
2. `(S + Φ)² = 1 + V` and `(S + J)² = 1 - V` (`GradingPerturbation.grading_add_phi_sq` & `grading_add_j_sq`),
3. `steinbergBraid P A C * steinbergBraidInv P A C = 1` (`Unipotent.steinbergBraid_mul_inv`),
4. `steinbergBraid P A C - steinbergBraidDual P A C = (1 - genV P A C) * genPhi P A C`
   (`Unipotent.steinbergBraid_dual_expansion_and_difference`). -/
theorem peirce_plabic_resolvent_and_steinberg_braid_bridge {B : Type*} [Ring B]
    {P : B} (hP : P * P = P) (A C : B) :
    (1 - conePlus P A * coneMinus P C) * (1 - coneMinus P C * conePlus P A) =
      1 - genV P A C ∧
    (invS P + genPhi P A C) * (invS P + genPhi P A C) = 1 + genV P A C ∧
    (invS P + genJ P A C) * (invS P + genJ P A C) = 1 - genV P A C ∧
    steinbergBraid P A C * steinbergBraidInv P A C = 1 ∧
    steinbergBraid P A C - steinbergBraidDual P A C = (1 - genV P A C) * genPhi P A C :=
  ⟨(qgt_primal_dual_euler_zeta_factorization hP A C).2.2.1,
   grading_add_phi_sq hP A C,
   grading_add_j_sq hP A C,
   (steinbergBraid_mul_inv hP A C).1,
   (steinbergBraid_dual_expansion_and_difference hP A C).2.1⟩

/-- **`MCP₅` Turn 11 Exact Krein `σ_z`-Isometry & Symplectic `ε`-Preservation of `cl11CayleyNumerator`:**
At `w_p = 0, w_c = 0`, the hyperbolic boost Cayley numerator `N_Cayley(0, w_s, 0)` is a scaled `σ_z`-Krein
isometry (`N σ_z Nᵀ = (1 + f)² σ_z`), and for ALL `(w_p, w_s, w_c)` `cl11CayleyNumerator` is a scaled
symplectic isometry (`Nᵀ ε N = (1 + f)² ε`)! -/
theorem cl11_cayley_krein_and_symplectic_unitarity (wp ws wc : R) :
    cl11CayleyNumerator 0 ws 0 * sigmaZ * (cl11CayleyNumerator 0 ws 0)ᵀ =
      ((1 + cl11LoopWeight 0 ws 0) ^ 2) • sigmaZ ∧
    (cl11CayleyNumerator wp ws wc)ᵀ * epsSymp * cl11CayleyNumerator wp ws wc =
      ((1 + cl11LoopWeight wp ws wc) ^ 2) • epsSymp := by
  refine ⟨?_, ?_⟩ <;>
    { ext i j; fin_cases i <;> fin_cases j <;>
        simp [cl11CayleyNumerator, cl11Traceless, cl11LoopWeight,
          sigmaZ, epsSymp, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two] <;>
        ring }

/-- **`MCP₅` Turn 11–12 Canonical Plabic Loop Jacobian & `Gr(2,4)` Plücker Relation:**
1. The cleared numerator of the canonical loop-coordinate derivative `d/df ((1 - f)/(1 + f))`
   is `-2 (1 + f)` (`-(1 + f) - (1 - f) = -2`), and `(1 - f)² + 4 f = (1 + f)²`,
2. For any `2 × 2` boundary matrix `M = !![m₀₀, m₀₁; m₁₀, m₁₁]`, the six `2 × 2` Plücker coordinates
   of `[I₂ | M]` in `Gr(2, 4)` (`Δ₁₂ = 1`, `Δ₁₃ = m₁₀`, `Δ₁₄ = m₁₁`, `Δ₂₃ = -m₀₀`, `Δ₂₄ = -m₀₁`,
   `Δ₃₄ = m₀₀ m₁₁ - m₀₁ m₁₀ = det(M)`) satisfy the quadratic Grassmann–Plücker relation
   `Δ₁₂ Δ₃₄ - Δ₁₃ Δ₂₄ + Δ₁₄ Δ₂₃ = 0` identically! -/
theorem cl11_canonical_jacobian_and_gr24_plucker (f m00 m01 m10 m11 : R) :
    (-(1 + f) - (1 - f) = -(2 : R) ∧ (1 - f) ^ 2 + 4 * f = (1 + f) ^ 2) ∧
    (1 : R) * (m00 * m11 - m01 * m10) - m10 * (-m01) + m11 * (-m00) = 0 := by
  refine ⟨⟨by ring, by ring⟩, by ring⟩

/-- **`MCP₅` Turn 12 Three-Channel BCFW Spurious Pole Cancellation Identity:**
For any three simple poles `z_a, z_b, z_c ∈ R` and shift `z ∈ R`, the cleared numerator of the
sum of the three cyclic residue fractions vanishes at leading order in `z`:
`(z - z_a)(z_b - z_c) + (z - z_b)(z_c - z_a) + (z - z_c)(z_a - z_b) = 0`,
and `z_b z_c (z_b - z_c) + z_c z_a (z_c - z_a) + z_a z_b (z_a - z_b) = -(z_a - z_b)(z_b - z_c)(z_c - z_a)`. -/
theorem bcfw_three_channel_spurious_pole_cancellation (z za zb zc : R) :
    (z - za) * (zb - zc) + (z - zb) * (zc - za) + (z - zc) * (za - zb) = 0 ∧
    zb * zc * (zb - zc) + zc * za * (zc - za) + za * zb * (za - zb) =
      -(za - zb) * (zb - zc) * (zc - za) := by
  refine ⟨by ring, by ring⟩

/-- Upper unipotent `2 × 2` Chevalley bridge `x_+(a) = !![1, a; 0, 1]` over `[Ring B]`. -/
def plabicUnipotentUpper {B : Type*} [Ring B] (a : B) : Matrix (Fin 2) (Fin 2) B :=
  !![1, a; 0, 1]

/-- Lower unipotent `2 × 2` Chevalley bridge `x_-(b) = !![1, 0; b, 1]` over `[Ring B]`. -/
def plabicUnipotentLower {B : Type*} [Ring B] (b : B) : Matrix (Fin 2) (Fin 2) B :=
  !![1, 0; b, 1]

/-- **`MCP₅` Pass-3 Lusztig–Steinberg 3-Step Unipotent Braid Relation & 3-Point BCFW Pachner Move:**
1. **Non-Commutative Unipotent Addition Law**: Over any `[Ring B]`,
   `x_+(a₁) x_+(a₂) = x_+(a₁ + a₂)` and `x_-(b₁) x_-(b₂) = x_-(b₁ + b₂)`.
2. **Non-Commutative Weyl Reflection Braid Identity**:
   `x_+(1) x_-(-1) x_+(1) = x_-(-1) x_+(1) x_-(-1) = !![0, 1; -1, 0]`.
3. **3-Point BCFW Chevalley–Steinberg 2-2 Pachner Move in `M₃(R)`**:
   `bcfwBridge01 z1 * bcfwBridge12 z2 * bcfwBridge01 z3 = bcfwBridge12 z2 * bcfwBridge01 (z1 + z3) * !![1, 0, z1 * z2; 0, 1, 0; 0, 0, 1]`. -/
theorem lusztig_steinberg_unipotent_braid_and_bcfw3_pachner
    {B : Type*} [Ring B] (a1 a2 b1 b2 : B) (z1 z2 z3 : R) :
    plabicUnipotentUpper a1 * plabicUnipotentUpper a2 = plabicUnipotentUpper (a2 + a1) ∧
    plabicUnipotentLower b1 * plabicUnipotentLower b2 = plabicUnipotentLower (b1 + b2) ∧
    plabicUnipotentUpper (1 : B) * plabicUnipotentLower (-1 : B) * plabicUnipotentUpper (1 : B) =
      plabicUnipotentLower (-1 : B) * plabicUnipotentUpper (1 : B) * plabicUnipotentLower (-1 : B) ∧
    plabicUnipotentUpper (1 : B) * plabicUnipotentLower (-1 : B) * plabicUnipotentUpper (1 : B) =
      !![(0 : B), 1; -1, 0] ∧
    bcfwBridge01 z1 * bcfwBridge12 z2 * bcfwBridge01 z3 =
      bcfwBridge12 z2 * bcfwBridge01 (z1 + z3) *
        !![(1 : R), 0, z1 * z2;
           0,       1, 0;
           0,       0, 1] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [plabicUnipotentUpper, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [plabicUnipotentLower, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [plabicUnipotentUpper, plabicUnipotentLower, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [plabicUnipotentUpper, plabicUnipotentLower, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;>
      simp [bcfwBridge01, bcfwBridge12]
    ring

/-- General `2 × 2` Plücker minor `Δ_{ij}(C) = C_{0,i} C_{1,j} - C_{0,j} C_{1,i}` of any `2 × 4` matrix `C`. -/
def pluckerMinor24 (C : Matrix (Fin 2) (Fin 4) R) (i j : Fin 4) : R :=
  C 0 i * C 1 j - C 0 j * C 1 i

/-- Postnikov's 4-parameter top-cell positroid boundary measurement matrix in `Gr(2,4)`:
`C_top(w₁, w₂, w₃, w₄) = !![1, w₁, 0, -w₄; 0, w₂, 1, w₃]`. -/
def plabicPositroidTop24 (w1 w2 w3 w4 : R) : Matrix (Fin 2) (Fin 4) R :=
  !![1, w1, 0, -w4;
     0, w2, 1, w3]

/-- **`MCP₅` Pass-3 All 6 Plücker Minors of `Gr_+(2,4)`, Universal 3-Term Plücker Syzygy & Total Positivity:**
1. **Universal 3-Term Grassmann–Plücker Syzygy**: For any `C ∈ M_{2×4}(R)`,
   `Δ₀₁(C) Δ₂₃(C) - Δ₀₂(C) Δ₁₃(C) + Δ₀₃(C) Δ₁₂(C) = 0`.
2. **All 6 Plücker Coordinates of `plabicPositroidTop24 w1 w2 w3 w4`**:
   `Δ₀₁ = w₂`, `Δ₀₂ = 1`, `Δ₀₃ = w₃`, `Δ₁₂ = w₁`, `Δ₁₃ = w₁ w₃ + w₂ w₄`, `Δ₂₃ = w₄`.
3. **Strict Total Positivity on `Gr_+(2,4)`**: Over `ℝ`, if `w₁, w₂, w₃, w₄ > 0`, all 6 ordered
   Plücker minors are strictly positive! -/
theorem plabic_positroid_gr24_all_six_plucker_and_total_positivity
    (C : Matrix (Fin 2) (Fin 4) R) (w1 w2 w3 w4 : R)
    (tw1 tw2 tw3 tw4 : ℝ) (hw1 : 0 < tw1) (hw2 : 0 < tw2) (hw3 : 0 < tw3) (hw4 : 0 < tw4) :
    pluckerMinor24 C 0 1 * pluckerMinor24 C 2 3 -
      pluckerMinor24 C 0 2 * pluckerMinor24 C 1 3 +
      pluckerMinor24 C 0 3 * pluckerMinor24 C 1 2 = 0 ∧
    pluckerMinor24 (plabicPositroidTop24 w1 w2 w3 w4) 0 1 = w2 ∧
    pluckerMinor24 (plabicPositroidTop24 w1 w2 w3 w4) 0 2 = 1 ∧
    pluckerMinor24 (plabicPositroidTop24 w1 w2 w3 w4) 0 3 = w3 ∧
    pluckerMinor24 (plabicPositroidTop24 w1 w2 w3 w4) 1 2 = w1 ∧
    pluckerMinor24 (plabicPositroidTop24 w1 w2 w3 w4) 1 3 = w1 * w3 + w2 * w4 ∧
    pluckerMinor24 (plabicPositroidTop24 w1 w2 w3 w4) 2 3 = w4 ∧
    (0 < pluckerMinor24 (plabicPositroidTop24 tw1 tw2 tw3 tw4) 0 1 ∧
     0 < pluckerMinor24 (plabicPositroidTop24 tw1 tw2 tw3 tw4) 0 2 ∧
     0 < pluckerMinor24 (plabicPositroidTop24 tw1 tw2 tw3 tw4) 0 3 ∧
     0 < pluckerMinor24 (plabicPositroidTop24 tw1 tw2 tw3 tw4) 1 2 ∧
     0 < pluckerMinor24 (plabicPositroidTop24 tw1 tw2 tw3 tw4) 1 3 ∧
     0 < pluckerMinor24 (plabicPositroidTop24 tw1 tw2 tw3 tw4) 2 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [pluckerMinor24]; ring
  · simp [pluckerMinor24, plabicPositroidTop24]
  · simp [pluckerMinor24, plabicPositroidTop24]
  · simp [pluckerMinor24, plabicPositroidTop24]
  · simp [pluckerMinor24, plabicPositroidTop24]
  · simp [pluckerMinor24, plabicPositroidTop24]; ring
  · simp [pluckerMinor24, plabicPositroidTop24]
  · have h01 : pluckerMinor24 (plabicPositroidTop24 tw1 tw2 tw3 tw4) 0 1 = tw2 := by
      simp [pluckerMinor24, plabicPositroidTop24]
    have h02 : pluckerMinor24 (plabicPositroidTop24 tw1 tw2 tw3 tw4) 0 2 = 1 := by
      simp [pluckerMinor24, plabicPositroidTop24]
    have h03 : pluckerMinor24 (plabicPositroidTop24 tw1 tw2 tw3 tw4) 0 3 = tw3 := by
      simp [pluckerMinor24, plabicPositroidTop24]
    have h12 : pluckerMinor24 (plabicPositroidTop24 tw1 tw2 tw3 tw4) 1 2 = tw1 := by
      simp [pluckerMinor24, plabicPositroidTop24]
    have h13 : pluckerMinor24 (plabicPositroidTop24 tw1 tw2 tw3 tw4) 1 3 = tw1 * tw3 + tw2 * tw4 := by
      simp [pluckerMinor24, plabicPositroidTop24]; ring
    have h23 : pluckerMinor24 (plabicPositroidTop24 tw1 tw2 tw3 tw4) 2 3 = tw4 := by
      simp [pluckerMinor24, plabicPositroidTop24]
    rw [h01, h02, h03, h12, h13, h23]
    exact ⟨hw2, zero_lt_one, hw3, hw1, add_pos (mul_pos hw1 hw3) (mul_pos hw2 hw4), hw4⟩

/-- Gauge-fixed `2 × 4` boundary measurement matrix `[I₂ | A]` associated to `A ∈ M₂(R)`. -/
def plabicGaugeFixed24 (A : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 4) R :=
  !![1, 0, A 0 0, A 0 1;
     0, 1, A 1 0, A 1 1]

/-- **`MCP₅` Pass-3 Plabic Amalgamation & Cauchy–Binet Plücker Minor Multiplicativity:**
Amalgamating two `2 × 2` Plabic transfer operators `A₁, A₂` into `[I₂ | A₁ A₂]` fixes `Δ₀₁ = 1`,
multiplies the terminal Plücker minor `Δ₂₃([I₂ | A₁ A₂]) = Δ₂₃([I₂ | A₁]) * Δ₂₃([I₂ | A₂])`,
and left-amalgamation by `bcfwLowerBridge z` preserves `Δ₂₃` while shearing `Δ₀₂, Δ₀₃`. -/
theorem plabic_amalgamation_cauchy_binet_plucker_multiplicativity
    (A1 A2 : Matrix (Fin 2) (Fin 2) R) (z : R) :
    pluckerMinor24 (plabicGaugeFixed24 (A1 * A2)) 0 1 = 1 ∧
    pluckerMinor24 (plabicGaugeFixed24 (A1 * A2)) 2 3 =
      pluckerMinor24 (plabicGaugeFixed24 A1) 2 3 *
        pluckerMinor24 (plabicGaugeFixed24 A2) 2 3 ∧
    pluckerMinor24 (plabicGaugeFixed24 (bcfwLowerBridge z * A1)) 2 3 =
      pluckerMinor24 (plabicGaugeFixed24 A1) 2 3 ∧
    pluckerMinor24 (plabicGaugeFixed24 (bcfwLowerBridge z * A1)) 0 2 =
      pluckerMinor24 (plabicGaugeFixed24 A1) 0 2 + z * A1 0 0 ∧
    pluckerMinor24 (plabicGaugeFixed24 (bcfwLowerBridge z * A1)) 0 3 =
      pluckerMinor24 (plabicGaugeFixed24 A1) 0 3 + z * A1 0 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    { simp [pluckerMinor24, plabicGaugeFixed24, bcfwLowerBridge, Matrix.mul_apply, Fin.sum_univ_two]
      try ring }

/-- **`MCP₅` Pass-3 Codebase Reuse (`PhaseConjugateSteinberg` & `PlabicVertexContraction`):**
Directly reuses `InfoGeometry.OperatorAlgebra.PeirceSpine` (`PhaseConjugateSteinberg.lean` and
`PlabicVertexContraction.lean`) to establish:
1. Parity conjugation maps the Steinberg braid to its inverse (`parityConj_steinbergBraid`),
2. Double Steinberg-parity round-trip identity (`parityConj_steinberg_round_trip`),
3. Non-commutative middle-vertex Plabic contraction `(1 - q)(e + q + r)(1 - r) = e - q r`
   (`PlabicVertexContraction.middle_vertex_contraction`). -/
theorem phaseConjugate_steinberg_and_middle_vertex_contraction_reuse
    {B : Type*} [Ring B] {P e q r : B} (hP : P * P = P)
    (hqe : q * e = q) (her : e * r = r) (hq : q * q = 0) (hr : r * r = 0)
    (A C X : B) :
    parityConj P (steinbergBraid P A C) = steinbergBraidInv P A C ∧
    parityConj P
      (steinbergBraid P A C *
        parityConj P (steinbergBraid P A C * X * steinbergBraidInv P A C) *
        steinbergBraidInv P A C) = X ∧
    (1 - q) * (e + q + r) * (1 - r) = e - q * r :=
  ⟨parityConj_steinbergBraid hP A C,
   parityConj_steinberg_round_trip hP A C X,
   PlabicVertexContraction.middle_vertex_contraction hqe her hq hr⟩

/-- **`MCP₅` Pass-4 Lusztig–Postnikov Urban Renewal Cluster Mutation & 4-Point BCFW `s`/`t`-Channel Split:**
1. **Polynomial-Cleared Lusztig–Postnikov 2-2 Urban Renewal Identity**:
   For `D = x + z + x * y * z`,
   `diag(D, 1) * x_-(y z) * x_+(1) * x_-(x y) * diag(1, D) = D • (x_+(x) * x_-(y) * x_+(z))`.
2. **Lower-Left Entry Factorization**: `y * z + x * y + x * y ^ 2 * z = y * (x + z + x * y * z)`.
3. **4-Point BCFW `s`-Channel (`w₄ = 0`) vs. `t`-Channel (`w₁ = 0`) Plücker Decomposition**:
   `Δ₁₃(C_top(w₁, w₂, w₃, w₄)) = Δ₁₃(C_top(w₁, w₂, w₃, 0)) + Δ₁₃(C_top(0, w₂, w₃, w₄))`,
   where the `s`-channel boundary has `Δ₂₃ = 0, Δ₁₃ = w₁ w₃` and the `t`-channel boundary has
   `Δ₁₂ = 0, Δ₁₃ = w₂ w₄`. -/
theorem postnikov_urbanRenewal_mutation_and_bcfw_st_channels (x y z w1 w2 w3 w4 : R) :
    let D := x + z + x * y * z
    !![D, 0; 0, (1 : R)] *
        (plabicUnipotentLower (y * z) * plabicUnipotentUpper (1 : R) * plabicUnipotentLower (x * y)) *
        !![(1 : R), 0; 0, D] =
      D • (plabicUnipotentUpper x * plabicUnipotentLower y * plabicUnipotentUpper z) ∧
    y * z + x * y + x * y ^ 2 * z = y * D ∧
    pluckerMinor24 (plabicPositroidTop24 w1 w2 w3 w4) 1 3 =
      pluckerMinor24 (plabicPositroidTop24 w1 w2 w3 0) 1 3 +
        pluckerMinor24 (plabicPositroidTop24 0 w2 w3 w4) 1 3 ∧
    pluckerMinor24 (plabicPositroidTop24 w1 w2 w3 0) 2 3 = 0 ∧
    pluckerMinor24 (plabicPositroidTop24 0 w2 w3 w4) 1 2 = 0 := by
  intro D
  refine ⟨?_, by ring, ?_, ?_, ?_⟩
  · ext i j
    simp only [D, plabicUnipotentUpper, plabicUnipotentLower,
      Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp <;> ring
  · simp [pluckerMinor24, plabicPositroidTop24]
  · simp [pluckerMinor24, plabicPositroidTop24]
  · simp [pluckerMinor24, plabicPositroidTop24]

/-- `4 × 4` twisted cyclic shift matrix `S_cyc` on `Gr(2,4)` with `(-1)^{k-1} = -1` wrap-around sign. -/
def gr24TwistedCyclicShift : Matrix (Fin 4) (Fin 4) R :=
  !![0,  1, 0, 0;
     0,  0, 1, 0;
     0,  0, 0, 1;
     -1, 0, 0, 0]

/-- Column-action formula for right-multiplication by `gr24TwistedCyclicShift` on `M_{2×4}(R)`. -/
lemma mul_gr24TwistedCyclicShift_apply (C : Matrix (Fin 2) (Fin 4) R) (i : Fin 2) :
    (C * (gr24TwistedCyclicShift : Matrix (Fin 4) (Fin 4) R)) i 0 = -C i 3 ∧
    (C * (gr24TwistedCyclicShift : Matrix (Fin 4) (Fin 4) R)) i 1 = C i 0 ∧
    (C * (gr24TwistedCyclicShift : Matrix (Fin 4) (Fin 4) R)) i 2 = C i 1 ∧
    (C * (gr24TwistedCyclicShift : Matrix (Fin 4) (Fin 4) R)) i 3 = C i 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    { rw [Matrix.mul_apply, Fin.sum_univ_four]
      simp [gr24TwistedCyclicShift] }

/-- Congruence helper for `pluckerMinor24` on an arbitrary `2 × 4` matrix `M`. -/
lemma pluckerMinor24_congr {M : Matrix (Fin 2) (Fin 4) R} {i j : Fin 4} {a b c d : R}
    (ha : M 0 i = a) (hb : M 1 j = b) (hc : M 0 j = c) (hd : M 1 i = d) :
    pluckerMinor24 M i j = a * b - c * d := by
  dsimp [pluckerMinor24]
  rw [ha, hb, hc, hd]

/-- **`MCP₅` Pass-4 `Gr_+(2,4)` Twisted Cyclic Shift Plücker Rotation & `S_cyc⁴ = -I₄` Spinor Periodicity:**
For any `2 × 4` boundary measurement matrix `C ∈ M_{2×4}(R)`:
1. Right-multiplying by `gr24TwistedCyclicShift` rotates all 6 ordered Plücker minors positively:
   `Δ₀₁(C S_cyc) = Δ₀₃(C)`, `Δ₀₂(C S_cyc) = Δ₁₃(C)`, `Δ₀₃(C S_cyc) = Δ₂₃(C)`,
   `Δ₁₂(C S_cyc) = Δ₀₁(C)`, `Δ₁₃(C S_cyc) = Δ₀₂(C)`, and `Δ₂₃(C S_cyc) = Δ₁₂(C)`.
2. `S_cyc⁴ = -I₄` (spinor sign flip after 4 column shifts, preserving all Plücker minors `Δ_{ij}(-C) = Δ_{ij}(C)`). -/
theorem gr24_twisted_cyclic_shift_plucker_rotation (C : Matrix (Fin 2) (Fin 4) R) :
    pluckerMinor24 (C * gr24TwistedCyclicShift) 0 1 = pluckerMinor24 C 0 3 ∧
    pluckerMinor24 (C * gr24TwistedCyclicShift) 0 2 = pluckerMinor24 C 1 3 ∧
    pluckerMinor24 (C * gr24TwistedCyclicShift) 0 3 = pluckerMinor24 C 2 3 ∧
    pluckerMinor24 (C * gr24TwistedCyclicShift) 1 2 = pluckerMinor24 C 0 1 ∧
    pluckerMinor24 (C * gr24TwistedCyclicShift) 1 3 = pluckerMinor24 C 0 2 ∧
    pluckerMinor24 (C * gr24TwistedCyclicShift) 2 3 = pluckerMinor24 C 1 2 ∧
    (gr24TwistedCyclicShift : Matrix (Fin 4) (Fin 4) R) * gr24TwistedCyclicShift *
      (gr24TwistedCyclicShift * gr24TwistedCyclicShift) = -1 := by
  have h0 := mul_gr24TwistedCyclicShift_apply C (0 : Fin 2)
  have h1 := mul_gr24TwistedCyclicShift_apply C (1 : Fin 2)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (pluckerMinor24_congr h0.1 h1.2.1 h0.2.1 h1.1).trans (by dsimp [pluckerMinor24]; ring)
  · exact (pluckerMinor24_congr h0.1 h1.2.2.1 h0.2.2.1 h1.1).trans (by dsimp [pluckerMinor24]; ring)
  · exact (pluckerMinor24_congr h0.1 h1.2.2.2 h0.2.2.2 h1.1).trans (by dsimp [pluckerMinor24]; ring)
  · exact (pluckerMinor24_congr h0.2.1 h1.2.2.1 h0.2.2.1 h1.2.1).trans rfl
  · exact (pluckerMinor24_congr h0.2.1 h1.2.2.2 h0.2.2.2 h1.2.1).trans rfl
  · exact (pluckerMinor24_congr h0.2.2.1 h1.2.2.2 h0.2.2.2 h1.2.2.1).trans rfl
  · ext i j
    simp only [Matrix.neg_apply, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [gr24TwistedCyclicShift]

/-- **`MCP₅` Pass-4 Codebase Reuse (`TwoStateSandwich`, `PlabicKleinActionBridge`, `ConeSheetBraiding`):**
Directly reuses `InfoGeometry.OperatorAlgebra.PeirceSpine` (`TwoStateSandwich.lean`,
`PlabicKleinActionBridge.lean`, and `ConeSheetBraiding.lean`) to establish:
1. Two-factor Bruhat chart conjugation transitions `chartBruhatConj P A C (P + coneMinus P C) = P - conePlus P A`
   and corner complement product `(1 - qgtPlus P A C) * (1 - qgtMinus P A C) = 1 - genV P A C` (`TwoStateSandwich`),
2. Parity automorphism transport of the plabic boundary idempotent and twistor null-space solution
   `parityConjRingEquiv hP (plabicBoundaryOp P A C) = plabicBoundaryOp P (-A) (-C)` (`PlabicKleinActionBridge`),
3. Defect-iterate braiding and commutativity of the cycle-defect sum with both light-cone nilpotents
   `comm (conePlus P A) (idempotencyDefect^[n] (qgtPlus P A C) + idempotencyDefect^[n] (qgtMinus P A C)) = 0`
   (`ConeSheetBraiding`). -/
theorem twoStateSandwich_plabicKlein_and_coneSheetBraiding_reuse
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C Z : B) (n : ℕ) :
    (chartBruhatConj P A C (P + coneMinus P C) = P - conePlus P A ∧
     chartBruhatConjInv P A C (P - conePlus P A) = P + coneMinus P C) ∧
    (1 - qgtPlus P A C) * (1 - qgtMinus P A C) = 1 - genV P A C ∧
    (parityConjRingEquiv hP (plabicBoundaryOp P A C) = plabicBoundaryOp P (-A) (-C) ∧
     parityConjRingEquiv hP (plabicTwistorSol P A C Z) =
       plabicTwistorSol P (-A) (-C) (parityConjRingEquiv hP Z)) ∧
    (comm (conePlus P A)
       (InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[n]
          (InfoGeometry.OperatorAlgebra.PeirceSpine.qgtPlus P A C) +
        InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[n]
          (InfoGeometry.OperatorAlgebra.PeirceSpine.qgtMinus P A C)) = 0 ∧
     comm (coneMinus P C)
       (InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[n]
          (InfoGeometry.OperatorAlgebra.PeirceSpine.qgtPlus P A C) +
        InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[n]
          (InfoGeometry.OperatorAlgebra.PeirceSpine.qgtMinus P A C)) = 0) :=
  ⟨chart_bruhat_conjugation_transition hP A C,
   chart_corner_complement_product hP A C,
   parity_transports_plabic_boundary_and_nullspace hP A C Z,
   qgt_defect_iterate_sum_commutes_with_cones hP A C n⟩

/-- **`MCP₅` Pass-5 Non-Commutative Peirce Cayley Rotor, Zorn Grade Inversion & Bergman–Hua Reflection Laws (Turn 11 Section 1):**
In any non-commutative ring `[Ring B]` with idempotent `P * P = P`:
1. The odd Peirce generator `genPhi P A C` (`Φ² = V`) and symplectic generator `genJ P A C` (`J² = -V`)
   satisfy the unscaled Cayley norm factorizations:
   `(1 + Φ)(1 - Φ) = zetaFactor P A C = 1 - V` and `(1 + J)(1 - J) = zetaPlusFactor P A C = 1 + V`,
2. Grade inversion `zornConj P X = S X S` maps the forward Cayley factor `1 + Φ` to its backward inverse
   factor `1 - Φ` (`zornConj P (1 + Φ) = 1 - Φ` and `zornConj P (1 + J) = 1 - J`),
3. The squared Cayley rotor decomposes into its even boost scalar `1 + V` and odd generator `2 Φ`:
   `(1 + Φ)² + (1 - Φ)² = 2 • (1 + V)` and `(1 + Φ)² - (1 - Φ)² = 4 • Φ`,
4. Reuses `Bergman.translated_reflection_and_bergman_hua_laws` to express the product and commutator of
   the translated corner reflections `invS (P - N_+)` and `invS (P + N_-)`. -/
theorem peirce_cayley_rotor_and_bergman_hua_bridge
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B) :
    (1 + genPhi P A C) * (1 - genPhi P A C) = zetaFactor P A C ∧
    (1 + genJ P A C) * (1 - genJ P A C) = zetaPlusFactor P A C ∧
    zornConj P (1 + genPhi P A C) = 1 - genPhi P A C ∧
    zornConj P (1 + genJ P A C) = 1 - genJ P A C ∧
    (1 + genPhi P A C) * (1 + genPhi P A C) + (1 - genPhi P A C) * (1 - genPhi P A C) =
      (2 : ℤ) • (1 + genV P A C) ∧
    (1 + genPhi P A C) * (1 + genPhi P A C) - (1 - genPhi P A C) * (1 - genPhi P A C) =
      (4 : ℤ) • genPhi P A C ∧
    invS (P - conePlus P A) * invS (P + coneMinus P C) =
      1 + (2 : ℤ) • genJ P A C - (2 : ℤ) • genV P A C - (2 : ℤ) • genSig P A C ∧
    comm (invS (P - conePlus P A)) (invS (P + coneMinus P C)) =
      (4 : ℤ) • (genJ P A C - genSig P A C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_,
          (translated_reflection_and_bergman_hua_laws hP A C).2.2.2.2.2.2.2.1,
          (translated_reflection_and_bergman_hua_laws hP A C).2.2.2.2.2.2.2.2.2⟩
  · simp only [zetaFactor]; peirce_nf hP
  · simp only [zetaPlusFactor]; peirce_nf hP
  · simp only [zornConj]; peirce_nf hP
  · simp only [zornConj]; peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP

/-- Parametric `3 × 3` elementary upper-triangular Plabic bridge `x_{01}(x) = I₃ + x E_{01}` (Turn 12 Section 2). -/
def plabicBridge01Param (x : R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, x, 0;
     0, 1, 0;
     0, 0, 1]

/-- Parametric `3 × 3` elementary upper-triangular Plabic bridge `x_{12}(y) = I₃ + y E_{12}` (Turn 12 Section 2). -/
def plabicBridge12Param (y : R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 0;
     0, 1, y;
     0, 0, 1]

/-- **`MCP₅` Pass-5 Parametric `3 × 3` Plabic Bridge Additivity, Heisenberg Commutator & Acyclic DAG Resolvent (Turn 12 Section 2):**
1. Elementary bridges along the same adjacent pair are additive:
   `x_{01}(x₁) * x_{01}(x₂) = x_{01}(x₁ + x₂)` and `x_{12}(y₁) * x_{12}(y₂) = x_{12}(y₁ + y₂)`.
2. Ordered amalgamation generates the 2-step corner path weight `x * y`, while the reverse order does not:
   `x_{01}(x) * x_{12}(y) = !![1, x, x * y; 0, 1, y; 0, 0, 1]` and
   `comm (x_{01}(x)) (x_{12}(y)) = !![0, 0, x * y; 0, 0, 0; 0, 0, 0]`.
3. For any 3-vertex acyclic directed path adjacency matrix `W_dag = !![0, x, z; 0, 0, y; 0, 0, 0]`,
   its exact Talaska boundary resolvent `(I₃ - W_dag)⁻¹ = I₃ + W_dag + W_dag²` equals
   `!![1, x, z + x * y; 0, 1, y; 0, 0, 1]` (summing the direct edge `z` and 2-hop path `x * y`). -/
theorem plabicBridge3_parametric_heisenberg_and_dag_resolvent (x1 x2 x y z : R) :
    plabicBridge01Param x1 * plabicBridge01Param x2 = plabicBridge01Param (x1 + x2) ∧
    plabicBridge12Param x1 * plabicBridge12Param x2 = plabicBridge12Param (x1 + x2) ∧
    plabicBridge01Param x * plabicBridge12Param y =
      !![1, x, x * y;
         0, 1, y;
         0, 0, 1] ∧
    comm (plabicBridge01Param x) (plabicBridge12Param y) =
      !![0, 0, x * y;
         0, 0, 0;
         0, 0, 0] ∧
    (1 - (!![0, x, z; 0, 0, y; 0, 0, 0] : Matrix (Fin 3) (Fin 3) R)) *
      !![1, x, z + x * y;
         0, 1, y;
         0, 0, 1] = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    { ext i j
      simp only [comm, plabicBridge01Param, plabicBridge12Param,
        Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_three]
      fin_cases i <;> fin_cases j <;> simp <;> ring }

/-- Gauge-fixed canonical `2 × 4` positroid matrix `C(a, b, c, d) = [I₂ | A] = !![1, 0, a, b; 0, 1, c, d]`
in `Gr(2,4)` (Turn 12 Section 1). -/
def plabicPositroidCanon24 (a b c d : R) : Matrix (Fin 2) (Fin 4) R :=
  !![1, 0, a, b;
     0, 1, c, d]

/-- Orthogonal Gale-dual `2 × 4` subspace matrix `C^⊥(a, b, c, d) = [-Aᵀ | I₂] = !![-a, -c, 1, 0; -b, -d, 0, 1]`
to `plabicPositroidCanon24 a b c d = !![1, 0, a, b; 0, 1, c, d]` in `Gr(2,4)` (Turn 12 Section 1). -/
def plabicPositroidDual24 (a b c d : R) : Matrix (Fin 2) (Fin 4) R :=
  !![-a, -c, 1, 0;
     -b, -d, 0, 1]

/-- **`MCP₅` Pass-5 `Gr(2,4)` Orthogonal Gale-Dual Subspace & 6-Minor Hodge–Plücker Duality (Turn 12 Section 1):**
For any `a b c d : R`, the Gale-dual matrix `C^⊥ = plabicPositroidDual24 a b c d` is strictly
orthogonal to `C = plabicPositroidCanon24 a b c d` (`C * (C^⊥)ᵀ = 0`) and satisfies the
complete 6-minor Grassmannian Hodge–Plücker duality:
`Δ₂₃(C^⊥) = Δ₀₁(C) = 1`, `Δ₀₁(C^⊥) = Δ₂₃(C) = a d - b c`,
`Δ₁₃(C^⊥) = -Δ₀₂(C) = -c`, `Δ₁₂(C^⊥) = Δ₀₃(C) = d`,
`Δ₀₃(C^⊥) = Δ₁₂(C) = -a`, and `Δ₀₂(C^⊥) = -Δ₁₃(C) = b`. -/
theorem gr24_gale_dual_orthogonality_and_plucker_duality (a b c d : R) :
    plabicPositroidCanon24 a b c d * (plabicPositroidDual24 a b c d)ᵀ = 0 ∧
    pluckerMinor24 (plabicPositroidDual24 a b c d) 2 3 =
      pluckerMinor24 (plabicPositroidCanon24 a b c d) 0 1 ∧
    pluckerMinor24 (plabicPositroidDual24 a b c d) 0 1 =
      pluckerMinor24 (plabicPositroidCanon24 a b c d) 2 3 ∧
    pluckerMinor24 (plabicPositroidDual24 a b c d) 1 3 =
      -pluckerMinor24 (plabicPositroidCanon24 a b c d) 0 2 ∧
    pluckerMinor24 (plabicPositroidDual24 a b c d) 1 2 =
      pluckerMinor24 (plabicPositroidCanon24 a b c d) 0 3 ∧
    pluckerMinor24 (plabicPositroidDual24 a b c d) 0 3 =
      pluckerMinor24 (plabicPositroidCanon24 a b c d) 1 2 ∧
    pluckerMinor24 (plabicPositroidDual24 a b c d) 0 2 =
      -pluckerMinor24 (plabicPositroidCanon24 a b c d) 1 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    simp only [plabicPositroidCanon24, plabicPositroidDual24,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp <;> ring_nf
  all_goals
    dsimp [pluckerMinor24, plabicPositroidDual24, plabicPositroidCanon24]
    try ring

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

/-- Second coalesced exceptional eigenvector `Ψ_EP^{(2)} = (0, 1, 1, 0)ᵀ` at `g = Δω = 1` (Turn 13 Section 2.2). -/
def kreinExceptionalVec2 : Fin 4 → R :=
  ![0, 1, 1, 0]

/-- Second generalized Jordan root vector `Φ_gen^{(2)} = (1, 0, 0, 0)ᵀ` satisfying `N_nil(1) Φ_gen^{(2)} = Ψ_EP^{(2)}`. -/
def kreinJordanRootVec2 : Fin 4 → R :=
  ![1, 0, 0, 0]

/-- **`MCP₆` Turn 13 Second Jordan Root Chain & Non-Degenerate Off-Diagonal Krein Pairing (Gelfand–Lidskii Theorem):**
At the critical Krein crash `g = Δω = 1`, `N_nil(1)` has a complete 2-dimensional isotropic
kernel spanned by `Ψ_EP^{(1)} = (1, 0, 0, -1)ᵀ` and `Ψ_EP^{(2)} = (0, 1, 1, 0)ᵀ` with
generalized root vectors `Φ_gen^{(1)} = (0, -1, 0, 0)ᵀ` and `Φ_gen^{(2)} = (1, 0, 0, 0)ᵀ` satisfying:
1. `N_nil(1) Ψ_EP^{(2)} = 0` and `N_nil(1) Φ_gen^{(2)} = Ψ_EP^{(2)}`,
2. Both exceptional eigenvectors are Krein-null and mutually Krein-orthogonal:
   `⟨Ψ_EP^{(2)}, J₄ Ψ_EP^{(2)}⟩ = 0` and `⟨Ψ_EP^{(1)}, J₄ Ψ_EP^{(2)}⟩ = 0`,
3. Their cross-pairings with the Jordan root vectors are non-degenerate:
   `⟨Ψ_EP^{(1)}, J₄ Φ_gen^{(2)}⟩ = 1` and `⟨Ψ_EP^{(2)}, J₄ Φ_gen^{(1)}⟩ = -1`! -/
theorem kreinGelfandLidskii_and_second_jordan_chain :
    Matrix.mulVec (kreinCrashNilpotent (1 : R)) kreinExceptionalVec2 = ![0, 0, 0, 0] ∧
    Matrix.mulVec (kreinCrashNilpotent (1 : R)) kreinJordanRootVec2 = kreinExceptionalVec2 ∧
    dotProduct kreinExceptionalVec2 (Matrix.mulVec kreinMetric4 kreinExceptionalVec2) = (0 : R) ∧
    dotProduct kreinExceptionalVec (Matrix.mulVec kreinMetric4 kreinExceptionalVec2) = (0 : R) ∧
    dotProduct kreinExceptionalVec (Matrix.mulVec kreinMetric4 kreinJordanRootVec2) = (1 : R) ∧
    dotProduct kreinExceptionalVec2 (Matrix.mulVec kreinMetric4 kreinJordanRootVec) = -(1 : R) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i; fin_cases i <;>
      simp [kreinCrashNilpotent, kreinHopfNilPart, jwGamma2, jwE1, kreinExceptionalVec2,
        Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  · ext i; fin_cases i <;>
      simp [kreinCrashNilpotent, kreinHopfNilPart, jwGamma2, jwE1,
        kreinJordanRootVec2, kreinExceptionalVec2,
        Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  · simp [kreinExceptionalVec2, kreinMetric4, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  · simp [kreinExceptionalVec, kreinExceptionalVec2, kreinMetric4, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  · simp [kreinExceptionalVec, kreinJordanRootVec2, kreinMetric4, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  · simp [kreinExceptionalVec2, kreinJordanRootVec, kreinMetric4, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- **`MCP₆` Turn 13 Biquadratic Minimal Polynomial of `M(ω̄, Δω, g)` & Secular Propagator Group Law:**
1. The full Krein–Hamiltonian–Hopf generator `M = kreinHopfGenerator wBar dw g` satisfies the
   exact quartic / biquadratic characteristic identity
   `(M² + (ω̄² + Δω² - g²) I₄)² = 4 ω̄² (Δω² - g²) I₄`, collapsing at `g = Δω` to `(M² + ω̄² I₄)² = 0`!
2. At the Krein crash `g = Δω`, the truncated secular propagator `U(t) = I₄ + t N_nil(Δω)`
   satisfies the exact 1-parameter group law `U(t₁) U(t₂) = U(t₁ + t₂)`. -/
theorem kreinHopf_biquadratic_and_secular_group_law (wBar dw g t1 t2 : R) :
    (kreinHopfGenerator wBar dw g * kreinHopfGenerator wBar dw g +
      (wBar ^ 2 + dw ^ 2 - g ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R)) *
    (kreinHopfGenerator wBar dw g * kreinHopfGenerator wBar dw g +
      (wBar ^ 2 + dw ^ 2 - g ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R)) =
      (4 * wBar ^ 2 * (dw ^ 2 - g ^ 2)) • (1 : Matrix (Fin 4) (Fin 4) R) ∧
    (1 + t1 • kreinCrashNilpotent dw) * (1 + t2 • kreinCrashNilpotent dw) =
      1 + (t1 + t2) • kreinCrashNilpotent dw := by
  refine ⟨?_, ?_⟩ <;>
    { ext i j
      simp only [kreinHopfGenerator, kreinHopfSemi, kreinHopfNilPart, kreinCrashNilpotent,
        Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.one_apply, Fin.sum_univ_four]
      fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1] <;> ring }

/-- **`MCP₆` Pass-3 Puiseux Square-Root Perturbation & Gelfand–Lidskii Krein Residue:**
1. **Exact Perturbed Operator Decomposition**:
   `kreinHopfNilPart dw (dw - eps) = kreinCrashNilpotent dw - eps • jwE1`.
2. **Puiseux Branch-Point Square Law**:
   `kreinHopfNilPart dw (dw - eps) * kreinHopfNilPart dw (dw - eps) = -((2 * dw * eps - eps ^ 2) • 1)`,
   with leading `O(eps)` anticommutator `anticomm (kreinCrashNilpotent dw) (-jwE1) = -((2 * dw) • 1)`.
3. **Gelfand–Lidskii Krein Perturbation Residue**:
   `dotProduct kreinExceptionalVec (Matrix.mulVec (kreinMetric4 * (-jwE1)) kreinJordanRootVec) = 1`
   and `dotProduct kreinExceptionalVec2 (Matrix.mulVec (kreinMetric4 * (-jwE1)) kreinJordanRootVec2) = 1`. -/
theorem krein_puiseux_perturbation_and_gelfand_lidskii_residue (dw eps : R) :
    kreinHopfNilPart dw (dw - eps) = kreinCrashNilpotent dw - eps • jwE1 ∧
    kreinHopfNilPart dw (dw - eps) * kreinHopfNilPart dw (dw - eps) =
      -((2 * dw * eps - eps ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R)) ∧
    anticomm (kreinCrashNilpotent dw) (-jwE1) =
      -((2 * dw) • (1 : Matrix (Fin 4) (Fin 4) R)) ∧
    dotProduct kreinExceptionalVec
      (Matrix.mulVec (kreinMetric4 * (-jwE1)) kreinJordanRootVec) = (1 : R) ∧
    dotProduct kreinExceptionalVec2
      (Matrix.mulVec (kreinMetric4 * (-jwE1)) kreinJordanRootVec2) = (1 : R) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    simp only [kreinHopfNilPart, kreinCrashNilpotent, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply]
    fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1]
  · ext i j
    simp only [kreinHopfNilPart, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1] <;> ring
  · ext i j
    simp only [anticomm, kreinCrashNilpotent, kreinHopfNilPart, Matrix.add_apply,
      Matrix.neg_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1] <;> ring
  · simp [kreinExceptionalVec, kreinJordanRootVec, kreinMetric4, jwE1,
      Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_four]
  · simp [kreinExceptionalVec2, kreinJordanRootVec2, kreinMetric4, jwE1,
      Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_four]

/-- Forward-sheet vector `u_+(x₀, x₁) = ![x₀, x₁, 0, 0] ∈ V_+`. -/
def kreinPosVec (x0 x1 : R) : Fin 4 → R := ![x0, x1, 0, 0]

/-- Cache-sheet vector `v_-(y₀, y₁) = ![0, 0, y₀, y₁] ∈ V_-`. -/
def kreinNegVec (y0 y1 : R) : Fin 4 → R := ![0, 0, y0, y1]

/-- General vector `w_EP(a, b) = a Ψ_EP^{(1)} + b Ψ_EP^{(2)} = ![a, b, b, -a]` in `ker(N_nil(1))`. -/
def kreinLagrangianKernelVec (a b : R) : Fin 4 → R := ![a, b, b, -a]

/-- **`MCP₆` Pass-3 Definite Krein Subspaces `V_+ ⊕ V_-` vs. Neutral Lagrangian Kernel at the Crash:**
1. **Definite Krein Signatures Away from Crash**:
   `⟨u_+(x₀, x₁), J₄ u_+(x₀, x₁)⟩ = x₀² + x₁²`,
   `⟨v_-(y₀, y₁), J₄ v_-(y₀, y₁)⟩ = -(y₀² + y₁²)`, and `⟨u_+, J₄ v_-⟩ = 0`.
2. **Sheet Invariance at Uncoupled Limit (`g = 0`)**:
   `N_part(Δω, 0) u_+(x₀, x₁) = u_+(-Δω x₁, Δω x₀)` and
   `N_part(Δω, 0) v_-(y₀, y₁) = v_-(Δω y₁, -Δω y₀)`.
3. **Neutral Lagrangian Coalescence at the Krein Crash (`g = Δω = 1`)**:
   Every `w_EP(a, b)` lies in `ker(N_nil(1))`, and any two vectors `w_EP(a₁, b₁), w_EP(a₂, b₂)`
   in this 2D kernel are mutually Krein-orthogonal (`⟨w_EP(a₁, b₁), J₄ w_EP(a₂, b₂)⟩ = 0`). -/
theorem krein_definite_subspaces_vs_neutral_lagrangian_kernel
    (dw x0 x1 y0 y1 a1 b1 a2 b2 : R) :
    dotProduct (kreinPosVec x0 x1) (Matrix.mulVec kreinMetric4 (kreinPosVec x0 x1)) =
      x0 ^ 2 + x1 ^ 2 ∧
    dotProduct (kreinNegVec y0 y1) (Matrix.mulVec kreinMetric4 (kreinNegVec y0 y1)) =
      -(y0 ^ 2 + y1 ^ 2) ∧
    dotProduct (kreinPosVec x0 x1) (Matrix.mulVec kreinMetric4 (kreinNegVec y0 y1)) = 0 ∧
    Matrix.mulVec (kreinHopfNilPart dw 0) (kreinPosVec x0 x1) =
      kreinPosVec (-dw * x1) (dw * x0) ∧
    Matrix.mulVec (kreinHopfNilPart dw 0) (kreinNegVec y0 y1) =
      kreinNegVec (dw * y1) (-dw * y0) ∧
    Matrix.mulVec (kreinCrashNilpotent (1 : R)) (kreinLagrangianKernelVec a1 b1) = ![0, 0, 0, 0] ∧
    dotProduct (kreinLagrangianKernelVec a1 b1)
      (Matrix.mulVec kreinMetric4 (kreinLagrangianKernelVec a2 b2)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [kreinPosVec, kreinMetric4, Matrix.mulVec, dotProduct, Fin.sum_univ_four]; ring
  · simp [kreinNegVec, kreinMetric4, Matrix.mulVec, dotProduct, Fin.sum_univ_four]; ring
  · simp [kreinPosVec, kreinNegVec, kreinMetric4, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  · ext i
    simp only [kreinHopfNilPart, Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.smul_apply,
      Fin.sum_univ_four]
    fin_cases i <;> simp [kreinPosVec, jwGamma2, jwE1]
  · ext i
    simp only [kreinHopfNilPart, Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.smul_apply,
      Fin.sum_univ_four]
    fin_cases i <;> simp [kreinNegVec, jwGamma2, jwE1]
  · ext i
    simp only [kreinCrashNilpotent, kreinHopfNilPart, Matrix.mulVec, dotProduct, Matrix.add_apply,
      Matrix.smul_apply, Fin.sum_univ_four]
    fin_cases i <;> simp [kreinLagrangianKernelVec, jwGamma2, jwE1]
  · simp [kreinLagrangianKernelVec, kreinMetric4, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- Canonical `4 × 4` Jordan basis matrix `P_Jordan` at the Krein crash (`g = Δω`), whose columns
are `(Ψ_EP^{(1)}, Φ_gen^{(1)}, Ψ_EP^{(2)}, Φ_gen^{(2)})`. -/
def kreinJordanBasis : Matrix (Fin 4) (Fin 4) R :=
  !![1,  0,  0, 1;
     0, -1,  1, 0;
     0,  0,  1, 0;
    -1,  0,  0, 0]

/-- Exact integer inverse `P_Jordan⁻¹` of `kreinJordanBasis` (`P_Jordan⁻¹ * P_Jordan = I₄`). -/
def kreinJordanBasisInv : Matrix (Fin 4) (Fin 4) R :=
  !![0,  0, 0, -1;
     0, -1, 1,  0;
     0,  0, 1,  0;
     1,  0, 0,  1]

/-- **`MCP₆` Pass-4 Full `4 × 4` Cayley–Hamilton Theorem, Index-2 Nilpotency & Canonical Jordan Normal Form:**
1. **Degree-4 Cayley–Hamilton Identity of `M(ω̄, Δω, g)`**:
   `M⁴ + (2 * (ω̄² + Δω² - g²)) • M² + ((ω̄² - (Δω² - g²))²) • I₄ = 0`.
2. **Invertibility of `kreinJordanBasis` over `R`**:
   `kreinJordanBasisInv * kreinJordanBasis = 1` and `kreinJordanBasis * kreinJordanBasisInv = 1`.
3. **Exact Similarity Transformation to Direct-Sum Jordan Normal Form**:
   `kreinJordanBasisInv * kreinCrashNilpotent dw * kreinJordanBasis = !![0, dw, 0, 0; 0, 0, 0, 0; 0, 0, 0, dw; 0, 0, 0, 0]`.
4. **Krein Metric Form in the Canonical Jordan Basis**:
   `kreinJordanBasisᵀ * kreinMetric4 * kreinJordanBasis = !![0, 0, 0, 1; 0, 1, -1, 0; 0, -1, 0, 0; 1, 0, 0, 1]`. -/
theorem kreinCrash_cayley_hamilton_and_canonical_jordan_form (wBar dw g : R) :
    let M := kreinHopfGenerator wBar dw g
    M * M * (M * M) + (2 * (wBar ^ 2 + dw ^ 2 - g ^ 2)) • (M * M) +
      ((wBar ^ 2 - (dw ^ 2 - g ^ 2)) ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R) = 0 ∧
    (kreinJordanBasisInv : Matrix (Fin 4) (Fin 4) R) * kreinJordanBasis = 1 ∧
    (kreinJordanBasis : Matrix (Fin 4) (Fin 4) R) * kreinJordanBasisInv = 1 ∧
    kreinJordanBasisInv * kreinCrashNilpotent dw * kreinJordanBasis =
      !![0, dw, 0, 0;
         0, 0,  0, 0;
         0, 0,  0, dw;
         0, 0,  0, 0] ∧
    (kreinJordanBasis : Matrix (Fin 4) (Fin 4) R)ᵀ * kreinMetric4 * kreinJordanBasis =
      !![0,  0,  0, 1;
         0,  1, -1, 0;
         0, -1,  0, 0;
         1,  0,  0, 1] := by
  intro M
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    simp only [M, kreinHopfGenerator, kreinHopfSemi, kreinHopfNilPart,
      Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.one_apply, Matrix.zero_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1] <;> ring
  · ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [kreinJordanBasisInv, kreinJordanBasis]
  · ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [kreinJordanBasisInv, kreinJordanBasis]
  · ext i j
    simp only [kreinCrashNilpotent, kreinHopfNilPart,
      Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;>
      simp [kreinJordanBasisInv, kreinJordanBasis, jwGamma2, jwE1]
  · ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [kreinJordanBasis, kreinMetric4]

/-- Non-vanishing of `kreinCrashNilpotent 1` and `kreinHopfGenerator 1 1 1` over `[Nontrivial R]`. -/
theorem kreinCrash_strict_index_two_nilpotency_witness [Nontrivial R] :
    (kreinCrashNilpotent (1 : R)) ≠ 0 ∧
    (kreinHopfGenerator (1 : R) 1 1) ≠ 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    have h02 := congrArg (fun A : Matrix (Fin 4) (Fin 4) R => A 0 2) h
    simp [kreinCrashNilpotent, kreinHopfNilPart, jwGamma2, jwE1] at h02
  · intro h
    have h02 := congrArg (fun A : Matrix (Fin 4) (Fin 4) R => A 0 2) h
    simp [kreinHopfGenerator, kreinHopfSemi, kreinHopfNilPart, jwGamma2, jwE1] at h02

/-- Canonical `4 × 4` real Jordan normal form `J₄(w̄, Δω) = I₂ ⊗ !![0, Δω; 0, 0] + !![0, -w̄; w̄, 0] ⊗ I₂`
of the full Krein–Hopf generator at the Krein crash `g = Δω` (Turn 13 Section 3.1). -/
def kreinFullCanonicalJordan4 (wBar dw : R) : Matrix (Fin 4) (Fin 4) R :=
  !![0,    dw,   -wBar, 0;
     0,    0,    0,     -wBar;
     wBar, 0,    0,     dw;
     0,    wBar, 0,     0]

/-- **`MCP₆` Pass-5 Full Generator Canonical Jordan Form & Degenerate Minimal Polynomial at Krein Crash (Turn 13 Section 3):**
Conjugating the full Krein–Hopf generator `kreinHopfGenerator wBar dw dw` at the Krein crash (`g = dw`)
by `kreinJordanBasis` simultaneously transforms the semisimple frequency carrier `kreinHopfSemi wBar`
into `!![0, -wBar; wBar, 0] ⊗ I₂` and puts the full generator into canonical real Jordan
normal form `kreinFullCanonicalJordan4 wBar dw = I₂ ⊗ !![0, dw; 0, 0] + !![0, -wBar; wBar, 0] ⊗ I₂`:
1. `kreinJordanBasisInv * kreinHopfSemi wBar * kreinJordanBasis = !![0, 0, -wBar, 0; 0, 0, 0, -wBar; wBar, 0, 0, 0; 0, wBar, 0, 0]`,
2. `kreinJordanBasisInv * kreinHopfGenerator wBar dw dw * kreinJordanBasis = kreinFullCanonicalJordan4 wBar dw`,
3. `(J₄² + wBar² I₄)² = 0`, whereas `J₄² + wBar² I₄ = !![0, 0, 0, -2 wBar dw; 0, 0, 0, 0; 0, 2 wBar dw, 0, 0; 0, 0, 0, 0]`. -/
theorem kreinCrash_full_generator_jordan_normal_form (wBar dw : R) :
    kreinJordanBasisInv * kreinHopfSemi wBar * kreinJordanBasis =
      !![0,    0,    -wBar, 0;
         0,    0,    0,     -wBar;
         wBar, 0,    0,     0;
         0,    wBar, 0,     0] ∧
    kreinJordanBasisInv * kreinHopfGenerator wBar dw dw * kreinJordanBasis =
      kreinFullCanonicalJordan4 wBar dw ∧
    (kreinFullCanonicalJordan4 wBar dw * kreinFullCanonicalJordan4 wBar dw +
      (wBar ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R)) *
      (kreinFullCanonicalJordan4 wBar dw * kreinFullCanonicalJordan4 wBar dw +
       (wBar ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R)) = 0 ∧
    kreinFullCanonicalJordan4 wBar dw * kreinFullCanonicalJordan4 wBar dw +
      (wBar ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R) =
      !![0, 0,            0, -(2 * wBar * dw);
         0, 0,            0, 0;
         0, 2 * wBar * dw, 0, 0;
         0, 0,            0, 0] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    simp only [kreinHopfSemi, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [kreinJordanBasisInv, kreinJordanBasis, jwGamma2]
  · ext i j
    simp only [kreinHopfGenerator, kreinHopfSemi, kreinHopfNilPart, kreinFullCanonicalJordan4,
      Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;>
      simp [kreinJordanBasisInv, kreinJordanBasis, jwGamma2, jwE1] <;> ring
  · ext i j
    simp only [kreinFullCanonicalJordan4, Matrix.add_apply, Matrix.smul_apply,
      Matrix.mul_apply, Matrix.one_apply, Matrix.zero_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp <;> ring
  · ext i j
    simp only [kreinFullCanonicalJordan4, Matrix.add_apply, Matrix.smul_apply,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp <;> ring

/-- At the Krein crash (`g = dw`), the resolvent `(z I₄ - kreinHopfGenerator wBar dw dw)⁻¹`
transitions from a simple pole `(z² + wBar²)⁻¹` to a **double pole** `(z² + wBar²)⁻²` with exact
polynomial adjugate identity. -/
theorem kreinCrash_resolvent_double_pole (z wBar dw : R) :
    (z • (1 : Matrix (Fin 4) (Fin 4) R) - kreinHopfGenerator wBar dw dw) *
      ((z • (1 : Matrix (Fin 4) (Fin 4) R) + kreinHopfSemi wBar) *
       (z • (1 : Matrix (Fin 4) (Fin 4) R) + kreinHopfSemi wBar) *
       (z • (1 : Matrix (Fin 4) (Fin 4) R) - kreinHopfSemi wBar + kreinCrashNilpotent dw)) =
      ((z ^ 2 + wBar ^ 2) ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R) := by
  ext i j
  simp only [kreinHopfGenerator, kreinHopfSemi, kreinHopfNilPart, kreinCrashNilpotent,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.one_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1] <;> ring

/-- **`MCP₆` Pass-5 Krein Crash Double-Pole Resolvent Identity & `KreinXiStarDefect` Reuse:**
1. At the Krein crash (`g = dw`), the resolvent `(z I₄ - kreinHopfGenerator wBar dw dw)⁻¹` transitions
   from a simple pole `(z² + wBar²)⁻¹` to a **double pole** `(z² + wBar²)⁻²` with exact polynomial
   adjugate identity:
   `(z • 1 - kreinHopfGenerator wBar dw dw) * ((z • 1 + kreinHopfSemi wBar) * (z • 1 + kreinHopfSemi wBar) * (z • 1 - kreinHopfSemi wBar + kreinCrashNilpotent dw)) = ((z² + wBar²)²) • 1`.
2. Reuses `KreinXiStarDefect.krein_xi_star_input_defect` and `krein_xi_star_input_eq_iff_square_eq`
   to quantify the exact non-commutative Krein reflection defect of the quadratic Xi operator. -/
theorem kreinCrash_resolvent_double_pole_and_xi_star_defect
    {B : Type*} [Ring B] [StarRing B] {P : B} (hP : P * P = P) (X : B)
    (z wBar dw : R) :
    (z • (1 : Matrix (Fin 4) (Fin 4) R) - kreinHopfGenerator wBar dw dw) *
      ((z • (1 : Matrix (Fin 4) (Fin 4) R) + kreinHopfSemi wBar) *
       (z • (1 : Matrix (Fin 4) (Fin 4) R) + kreinHopfSemi wBar) *
       (z • (1 : Matrix (Fin 4) (Fin 4) R) - kreinHopfSemi wBar + kreinCrashNilpotent dw)) =
      ((z ^ 2 + wBar ^ 2) ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R) ∧
    kreinReflect P (xiCenteredOp (star X)) - xiCenteredOp (kreinReflect P X) =
      invS P * (star X * star X - X * X) * invS P ∧
    (kreinReflect P (xiCenteredOp (star X)) = xiCenteredOp (kreinReflect P X) ↔
      star X * star X = X * X) :=
  ⟨kreinCrash_resolvent_double_pole z wBar dw,
   krein_xi_star_input_defect hP,
   krein_xi_star_input_eq_iff_square_eq hP⟩

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

/-- **`MCP₇` Full Parametric Spectral Braided Quantum Yang–Baxter Equation over `[Ring B]`:**
For any two involutive braid generators `P₁₂, P₂₃ ∈ B` (`P₁₂² = 1`, `P₂₃² = 1`,
`P₁₂ P₂₃ P₁₂ = P₂₃ P₁₂ P₂₃`) and any integer spectral parameters `u, v, η ∈ ℤ`,
`Ř₁₂(u, η) Ř₂₃(u + v, η) Ř₁₂(v, η) = Ř₂₃(v, η) Ř₁₂(u + v, η) Ř₂₃(u, η)`
where `Ř(P, w, η) = η · 1 + w · P`! -/
theorem yangian_parametric_braided_qybe {B : Type*} [Ring B]
    (P12 P23 : B) (u v eta : ℤ)
    (h12_sq : P12 * P12 = 1)
    (h23_sq : P23 * P23 = 1)
    (h_braid : P12 * P23 * P12 = P23 * P12 * P23) :
    (eta • (1 : B) + u • P12) * (eta • (1 : B) + (u + v) • P23) * (eta • (1 : B) + v • P12) =
      (eta • (1 : B) + v • P23) * (eta • (1 : B) + (u + v) • P12) * (eta • (1 : B) + u • P23) := by
  have h_braid' : P12 * (P23 * P12) = P23 * (P12 * P23) := by
    simpa [mul_assoc] using h_braid
  simp only [add_smul, smul_add, mul_add, add_mul,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    mul_assoc, h12_sq, h23_sq, h_braid', smul_smul]
  simp only [Int.mul_comm, Int.mul_left_comm]
  abel

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
  simpa only [one_smul, Int.reduceAdd] using
    yangian_parametric_braided_qybe P12 P23 1 1 1 h12_sq h23_sq h_braid

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

/-- `3 × 3` adjacent transposition matrix `P₁₂ = !![0, 1, 0; 1, 0, 0; 0, 0, 1]` on `R³`. -/
def perm12_3 : Matrix (Fin 3) (Fin 3) R :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

/-- `3 × 3` adjacent transposition matrix `P₂₃ = !![1, 0, 0; 0, 0, 1; 0, 1, 0]` on `R³`. -/
def perm23_3 : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

/-- `3 × 3` non-adjacent transposition matrix `P₁₃ = P₁₂ P₂₃ P₁₂ = !![0, 0, 1; 0, 1, 0; 1, 0, 0]` on `R³`. -/
def perm13_3 : Matrix (Fin 3) (Fin 3) R :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

/-- Adjacent `3 × 3` transposition matrices `perm12_3` and `perm23_3` do not commute over any nontrivial ring `R`. -/
theorem perm12_3_perm23_3_noncommute [Nontrivial R] :
    (perm12_3 : Matrix (Fin 3) (Fin 3) R) * perm23_3 ≠
      perm23_3 * perm12_3 := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M 0 1) h
  simp [perm12_3, perm23_3, Matrix.mul_apply, Fin.sum_univ_three] at h01

/-- **`MCP₇` Concrete `3 × 3` Matrix Realization of the Spectral Braided Quantum Yang–Baxter Equation:**
The adjacent permutation matrices `perm12_3` and `perm23_3` satisfy `P₁₂² = I₃`, `P₂₃² = I₃`,
`P₁₂ P₂₃ P₁₂ = P₂₃ P₁₂ P₂₃`, and the full spectral-parameter braided Yang–Baxter Equation
for arbitrary spectral parameters `u, v, η ∈ R`! -/
theorem matrix3_braid_and_parametric_qybe (u v eta : R) :
    (perm12_3 : Matrix (Fin 3) (Fin 3) R) * perm12_3 = 1 ∧
    (perm23_3 : Matrix (Fin 3) (Fin 3) R) * perm23_3 = 1 ∧
    (perm12_3 : Matrix (Fin 3) (Fin 3) R) * perm23_3 * perm12_3 =
      perm23_3 * perm12_3 * perm23_3 ∧
    (eta • (1 : Matrix (Fin 3) (Fin 3) R) + u • perm12_3) *
      (eta • 1 + (u + v) • perm23_3) *
      (eta • 1 + v • perm12_3) =
      (eta • 1 + v • perm23_3) *
        (eta • 1 + (u + v) • perm12_3) *
        (eta • 1 + u • perm23_3) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [perm12_3]
  · ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [perm23_3]
  · ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [perm12_3, perm23_3]
  · ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [perm12_3, perm23_3] <;> ring

/-- Two-site Yangian monodromy upper-left block `A₁₂(u) = A₂(u) A₁(u) + B C` (Turn 15 Section 1.1). -/
def monodromyA2 (u theta1 theta2 eta : R) : Matrix (Fin 2) (Fin 2) R :=
  laxBlockA u theta2 eta * laxBlockA u theta1 eta + laxBlockB eta * laxBlockC eta

/-- Two-site Yangian monodromy lower-left annihilation block `C₁₂(u) = C A₁(u) + D₂(u) C`. -/
def monodromyC2 (u theta1 theta2 eta : R) : Matrix (Fin 2) (Fin 2) R :=
  laxBlockC eta * laxBlockA u theta1 eta + laxBlockD u theta2 eta * laxBlockC eta

/-- Two-site Yangian monodromy lower-right block `D₁₂(u) = C B + D₂(u) D₁(u)`. -/
def monodromyD2 (u theta1 theta2 eta : R) : Matrix (Fin 2) (Fin 2) R :=
  laxBlockC eta * laxBlockB eta + laxBlockD u theta2 eta * laxBlockD u theta1 eta

/-- **`MCP₇` Turn 15 Algebraic Bethe Ansatz Pseudovacuum Triangularity, Magnon Creation & Two-Site Eigenvalue Factorization:**
On the ferromagnetic Bethe pseudovacuum `|0⟩ = ![1, 0]`:
1. `C_lax |0⟩ = 0` (the annihilation block annihilates the pseudovacuum),
2. `B_lax |0⟩ = ![0, η]` (the creation block excites a single spin-flip magnon),
3. `A(u) |0⟩ = (u - θ + η) |0⟩` and `D(u) |0⟩ = (u - θ) |0⟩`,
4. For the 2-site monodromy coproduct, `C₁₂(u) |0⟩ = 0` and
   `A₁₂(u) |0⟩ = ((u - θ₂ + η)(u - θ₁ + η)) |0⟩` (multiplicative Bethe vacuum eigenvalue!). -/
theorem bethe_pseudovacuum_and_twoSite_monodromy (u theta1 theta2 eta : R) :
    Matrix.mulVec (laxBlockC eta) (![1, 0] : Fin 2 → R) = ![0, 0] ∧
    Matrix.mulVec (laxBlockB eta) (![1, 0] : Fin 2 → R) = ![0, eta] ∧
    Matrix.mulVec (laxBlockA u theta1 eta) (![1, 0] : Fin 2 → R) =
      (u - theta1 + eta) • (![1, 0] : Fin 2 → R) ∧
    Matrix.mulVec (laxBlockD u theta1 eta) (![1, 0] : Fin 2 → R) =
      (u - theta1) • (![1, 0] : Fin 2 → R) ∧
    Matrix.mulVec (monodromyC2 u theta1 theta2 eta) (![1, 0] : Fin 2 → R) = ![0, 0] ∧
    Matrix.mulVec (monodromyA2 u theta1 theta2 eta) (![1, 0] : Fin 2 → R) =
      ((u - theta2 + eta) * (u - theta1 + eta)) • (![1, 0] : Fin 2 → R) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    { ext i
      fin_cases i <;>
        simp [monodromyC2, monodromyA2, laxBlockA, laxBlockD, laxBlockB, laxBlockC,
          Matrix.mulVec, dotProduct, Fin.sum_univ_two] }

/-- Two-site Yangian monodromy upper-right creation block `B₁₂(u) = A₂(u) B + B D₁(u)` (Turn 15 Section 1.1). -/
def monodromyB2 (u theta1 theta2 eta : R) : Matrix (Fin 2) (Fin 2) R :=
  laxBlockA u theta2 eta * laxBlockB eta + laxBlockB eta * laxBlockD u theta1 eta

/-- **`MCP₇` Turn 14 Unbraided Spectral Quantum Yang–Baxter Equation & Resonant Young Symmetrizers:**
1. The unbraided Yang operators `R_{ij}(w) = w I₃ + η P_{ij}` on `R³` satisfy the exact
   unbraided spectral Quantum Yang–Baxter Equation:
   `R₁₂(u) R₁₃(u + v) R₂₃(v) = R₂₃(v) R₁₃(u + v) R₁₂(u)`.
2. At the resonant points `u = ±η`, `R(η, η)` and `R(-η, η)` satisfy the Young symmetrizer
   projector identities `R(η, η)² = (2 η) R(η, η)` and `R(-η, η)² = (-2 η) R(-η, η)`. -/
theorem yangian_unbraided_qybe_and_resonant_projectors (u v eta : R) :
    (u • (1 : Matrix (Fin 3) (Fin 3) R) + eta • perm12_3) *
      ((u + v) • 1 + eta • perm13_3) *
      (v • 1 + eta • perm23_3) =
      (v • 1 + eta • perm23_3) *
        ((u + v) • 1 + eta • perm13_3) *
        (u • 1 + eta • perm12_3) ∧
    yangR4 eta eta * yangR4 eta eta = (2 * eta) • yangR4 eta eta ∧
    yangR4 (-eta) eta * yangR4 (-eta) eta = (-2 * eta) • yangR4 (-eta) eta := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [perm12_3, perm13_3, perm23_3] <;> ring
  · ext i j
    simp only [yangR4, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [swap4] <;> ring
  · ext i j
    simp only [yangR4, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [swap4] <;> ring

/-- **`MCP₇` Turn 15 Algebraic Bethe Ansatz Creation Exchange Relation & Two-Site Transfer Matrix Commutativity:**
1. **Creation Exchange Identity**: `(u - v) A(u) B_lax = (u - v - η) B_lax A(u) + η B_lax A(v)`.
2. **Two-Site Transfer Commutativity**: The two-site transfer block `T₁₂(u) = A₁₂(u) + D₁₂(u)`
   commutes for all spectral parameters `u, v`, `[T₁₂(u), T₁₂(v)] = 0`, and so does the
   Krein-twisted transfer block `A₁₂(u) - D₁₂(u)`! -/
theorem bethe_creation_bracket_and_twoSite_transfer_comm (u v theta1 theta2 eta : R) :
    (u - v) • (laxBlockA u theta1 eta * laxBlockB eta) =
      (u - v - eta) • (laxBlockB eta * laxBlockA u theta1 eta) +
        eta • (laxBlockB eta * laxBlockA v theta1 eta) ∧
    comm (monodromyA2 u theta1 theta2 eta + monodromyD2 u theta1 theta2 eta)
         (monodromyA2 v theta1 theta2 eta + monodromyD2 v theta1 theta2 eta) = 0 ∧
    comm (monodromyA2 u theta1 theta2 eta - monodromyD2 u theta1 theta2 eta)
         (monodromyA2 v theta1 theta2 eta - monodromyD2 v theta1 theta2 eta) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    { ext i j
      simp only [comm, monodromyA2, monodromyD2, laxBlockA, laxBlockD, laxBlockB, laxBlockC,
        Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.zero_apply, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;> simp <;> ring }

/-- **`MCP₇` Pass-3 Sklyanin Quantum Determinant Centrality & Antisymmetrizer Fusion:**
1. **Antisymmetrizer & Symmetrizer Resonant Fusion Annihilation**:
   `(I₄ - P₁₂) R₁₂(η, η) = 0`, `R₁₂(η, η) (I₄ - P₁₂) = 0`, and `(I₄ + P₁₂) R₁₂(-η, η) = 0`.
2. **Dual Sklyanin Quantum Determinant Formula**:
   `D(u) A(u - η) - C B = ((u - θ)² - η²) I₂`.
3. **Centrality of `qdet L(u) = A(u) D(u - η) - B C`**:
   `qdet L(u)` commutes with all four Lax blocks `A(v), B, C, D(v)` for all `u, v`. -/
theorem yangian_qdet_centrality_and_antisymmetrizer_fusion (u v theta eta : R) :
    ((1 : Matrix (Fin 4) (Fin 4) R) - swap4) * yangR4 eta eta = 0 ∧
    yangR4 eta eta * ((1 : Matrix (Fin 4) (Fin 4) R) - swap4) = 0 ∧
    ((1 : Matrix (Fin 4) (Fin 4) R) + swap4) * yangR4 (-eta) eta = 0 ∧
    laxBlockD u theta eta * laxBlockA (u - eta) theta eta -
      laxBlockC eta * laxBlockB eta =
      ((u - theta) ^ 2 - eta ^ 2) • (1 : Matrix (Fin 2) (Fin 2) R) ∧
    comm (laxBlockA u theta eta * laxBlockD (u - eta) theta eta - laxBlockB eta * laxBlockC eta)
         (laxBlockA v theta eta) = 0 ∧
    comm (laxBlockA u theta eta * laxBlockD (u - eta) theta eta - laxBlockB eta * laxBlockC eta)
         (laxBlockB eta) = 0 ∧
    comm (laxBlockA u theta eta * laxBlockD (u - eta) theta eta - laxBlockB eta * laxBlockC eta)
         (laxBlockC eta) = 0 ∧
    comm (laxBlockA u theta eta * laxBlockD (u - eta) theta eta - laxBlockB eta * laxBlockC eta)
         (laxBlockD v theta eta) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [yangR4, swap4, Matrix.mul_apply, Fin.sum_univ_four]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [yangR4, swap4, Matrix.mul_apply, Fin.sum_univ_four]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [yangR4, swap4, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals
    ext i j
    simp only [comm, laxBlockA, laxBlockB, laxBlockC, laxBlockD,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply,
      Matrix.zero_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp <;> ring

/-- **`MCP₇` Pass-3 Yangian Coproduct Coassociativity & 2-Magnon Bethe Symmetry:**
1. **Non-Commutative Matrix Coproduct Coassociativity**: `(T₁ * T₂) * T₃ = T₁ * (T₂ * T₃)` over `[Ring B]`.
2. **2-Magnon Bethe Creation & Annihilation Commutativity**:
   `[B₁₂(v₁), B₁₂(v₂)] = 0` and `[C₁₂(v₁), C₁₂(v₂)] = 0`.
3. **2-Site Monodromy Diagonal Commutativity**:
   `[A₁₂(u), A₁₂(v)] = 0`, `[D₁₂(u), D₁₂(v)] = 0`, and `[A₁₂(u), D₁₂(v)] = 0`. -/
theorem yangian_coproduct_coassociativity_and_twoMagnon_bethe_commutativity
    {B : Type*} [Ring B] (T1 T2 T3 : Matrix (Fin 2) (Fin 2) B)
    (u v v1 v2 theta1 theta2 eta : R) :
    (T1 * T2) * T3 = T1 * (T2 * T3) ∧
    comm (monodromyB2 v1 theta1 theta2 eta) (monodromyB2 v2 theta1 theta2 eta) = 0 ∧
    comm (monodromyC2 v1 theta1 theta2 eta) (monodromyC2 v2 theta1 theta2 eta) = 0 ∧
    comm (monodromyA2 u theta1 theta2 eta) (monodromyA2 v theta1 theta2 eta) = 0 ∧
    comm (monodromyD2 u theta1 theta2 eta) (monodromyD2 v theta1 theta2 eta) = 0 ∧
    comm (monodromyA2 u theta1 theta2 eta) (monodromyD2 v theta1 theta2 eta) = 0 := by
  refine ⟨Matrix.mul_assoc T1 T2 T3, ?_, ?_, ?_, ?_, ?_⟩ <;>
    { ext i j
      simp only [comm, monodromyA2, monodromyB2, monodromyC2, monodromyD2,
        laxBlockA, laxBlockB, laxBlockC, laxBlockD,
        Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;> simp <;> ring }

/-- **`MCP₇` Pass-4 Dual `D(u)` Creation Exchange, 1-Magnon Eigenvalues & Two-Site `qdet` Multiplicativity:**
1. **Dual `D(u)` Creation Exchange Relation**:
   `(u - v) • (D(u) * B_lax) = (u - v + η) • (B_lax * D(u)) - η • (B_lax * D(v))`.
2. **1-Magnon State `|Ψ₁⟩ = B_lax |0⟩ = ![0, η]` Pauli Exclusion & Two-Site Eigenvalues**:
   `B_lax |Ψ₁⟩ = 0`, `A₁₂(u) |Ψ₁⟩ = ((u - θ₂)(u - θ₁) + η²) • |Ψ₁⟩`, and
   `D₁₂(u) |Ψ₁⟩ = ((u - θ₂ + η)(u - θ₁ + η)) • |Ψ₁⟩`.
3. **Two-Site Quantum Determinant Multiplicative Homomorphism**:
   `(A(u, θ₂) D(u - η, θ₂) - B C) * (A(u, θ₁) D(u - η, θ₁) - B C) = (((u - θ₂)² - η²)((u - θ₁)² - η²)) • I₂`. -/
theorem yangian_dual_bethe_exchange_oneMagnon_and_twoSite_qdet
    (u v theta1 theta2 eta : R) :
    (u - v) • (laxBlockD u theta1 eta * laxBlockB eta) =
      (u - v + eta) • (laxBlockB eta * laxBlockD u theta1 eta) -
        eta • (laxBlockB eta * laxBlockD v theta1 eta) ∧
    Matrix.mulVec (laxBlockB eta) (![0, eta] : Fin 2 → R) = ![0, 0] ∧
    Matrix.mulVec (monodromyA2 u theta1 theta2 eta) (![0, eta] : Fin 2 → R) =
      ((u - theta2) * (u - theta1) + eta ^ 2) • (![0, eta] : Fin 2 → R) ∧
    Matrix.mulVec (monodromyD2 u theta1 theta2 eta) (![0, eta] : Fin 2 → R) =
      ((u - theta2 + eta) * (u - theta1 + eta)) • (![0, eta] : Fin 2 → R) ∧
    (laxBlockA u theta2 eta * laxBlockD (u - eta) theta2 eta - laxBlockB eta * laxBlockC eta) *
      (laxBlockA u theta1 eta * laxBlockD (u - eta) theta1 eta - laxBlockB eta * laxBlockC eta) =
      (((u - theta2) ^ 2 - eta ^ 2) * ((u - theta1) ^ 2 - eta ^ 2)) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    simp only [laxBlockD, laxBlockB, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
      Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp; ring
  · ext i; fin_cases i <;> simp [laxBlockB, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · ext i; fin_cases i
    · simp [monodromyA2, laxBlockA, laxBlockB, laxBlockC,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · simp [monodromyA2, laxBlockA, laxBlockB, laxBlockC,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
  · ext i; fin_cases i <;>
      simp [monodromyD2, laxBlockD, laxBlockB, laxBlockC,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · ext i j
    simp only [laxBlockA, laxBlockD, laxBlockB, laxBlockC,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp <;> ring

/-- **`MCP₇` Pass-5 Complete Two-Site & Single-Site Yangian RTT Creation/Annihilation/Cross Commutator Table (Turns 14–15):**
For the two-site `Y(gl₂)` monodromy blocks `A₁₂(u)`, `B₁₂(u)`, `C₁₂(u)`, `D₁₂(u)` and single-site Lax blocks:
1. **Cartan Block Difference**:
   `A₁₂(u) - D₁₂(u) = (η * (2 u - θ₁ - θ₂)) • sigmaZ`,
2. **Two-Site Creation & Annihilation Scaling Laws**:
   `B₁₂(u) = (2 u - θ₁ - θ₂) • laxBlockB η` and `C₁₂(u) = (2 u - θ₁ - θ₂) • laxBlockC η`,
3. **`[C_lax, A(u)]` RTT Annihilation Exchange Relation**:
   `(u - v) • (laxBlockC η * laxBlockA u θ₁ η) = (u - v - η) • (laxBlockA u θ₁ η * laxBlockC η) + η • (laxBlockA v θ₁ η * laxBlockC η)`,
4. **`[C_lax, D(u)]` RTT Dual Annihilation Exchange Relation**:
   `(u - v) • (laxBlockC η * laxBlockD u θ₁ η) = (u - v + η) • (laxBlockD u θ₁ η * laxBlockC η) - η • (laxBlockD v θ₁ η * laxBlockC η)`,
5. **Two-Site `[B₁₂(u), C₁₂(v)]` Cross-Channel Commutator**:
   `comm (B₁₂(u)) (C₁₂(v)) = -(2 v - θ₁ - θ₂) * η • (A₁₂(u) - D₁₂(u))`. -/
theorem yangian_twoSite_full_rtt_commutator_table (u v theta1 theta2 eta : R) :
    monodromyA2 u theta1 theta2 eta - monodromyD2 u theta1 theta2 eta =
      (eta * (2 * u - theta1 - theta2)) • sigmaZ ∧
    monodromyB2 u theta1 theta2 eta =
      (2 * u - theta1 - theta2) • laxBlockB eta ∧
    monodromyC2 u theta1 theta2 eta =
      (2 * u - theta1 - theta2) • laxBlockC eta ∧
    (u - v) • (laxBlockC eta * laxBlockA u theta1 eta) =
      (u - v - eta) • (laxBlockA u theta1 eta * laxBlockC eta) +
        eta • (laxBlockA v theta1 eta * laxBlockC eta) ∧
    (u - v) • (laxBlockC eta * laxBlockD u theta1 eta) =
      (u - v + eta) • (laxBlockD u theta1 eta * laxBlockC eta) -
        eta • (laxBlockD v theta1 eta * laxBlockC eta) ∧
    comm (monodromyB2 u theta1 theta2 eta) (monodromyC2 v theta1 theta2 eta) =
      -((2 * v - theta1 - theta2) * eta) •
        (monodromyA2 u theta1 theta2 eta - monodromyD2 u theta1 theta2 eta) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    { ext i j
      simp only [comm, monodromyA2, monodromyB2, monodromyC2, monodromyD2,
        laxBlockA, laxBlockB, laxBlockC, laxBlockD, sigmaZ,
        Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
        Matrix.mul_apply, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;> simp <;> ring }

/-- **`MCP₇` Pass-5 Codebase Reuse (`ChiralEulerFactors`):**
Directly reuses `InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralEulerFactors` to establish:
1. Equivalence of the chiral factor product `(1 - Σ)(1 + Σ)` and the metric zeta factor product
   `(1 - V)(1 + V) = 1 - V²` (`chiral_factor_product`),
2. Even-grade supercharge factorizations `evenGrade P ((1 + J)(1 - Φ)) = 1 - Σ` and
   `evenGrade P ((1 - Φ)(1 + J)) = 1 + Σ` (`even_grade_supercharge_factorizations`),
3. Ordered four-factor non-commutative supercharge product `(1 - Φ)(1 - J)(1 + J)(1 + Φ) = 1 - V²`
   and its identity with the four Peirce-cycle product `(1 - q_+)(1 - q_-)(1 + q_+)(1 + q_-)`
   (`supercharge_four_factor_product`, `supercharge_chiral_cycle_product`). -/
theorem peirce_chiral_euler_and_supercharge_cycle_bridge
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B) :
    (chiralFactor P A C * chiralConjugateFactor P A C =
       zetaFactor P A C * zetaPlusFactor P A C ∧
     chiralFactor P A C * chiralConjugateFactor P A C =
       1 - genV P A C * genV P A C) ∧
    (evenGrade P ((1 + genJ P A C) * (1 - genPhi P A C)) = chiralFactor P A C ∧
     evenGrade P ((1 - genPhi P A C) * (1 + genJ P A C)) = chiralConjugateFactor P A C) ∧
    (1 - genPhi P A C) * (1 - genJ P A C) * (1 + genJ P A C) * (1 + genPhi P A C) =
      1 - genV P A C * genV P A C ∧
    (1 - genPhi P A C) * (1 - genJ P A C) * (1 + genJ P A C) * (1 + genPhi P A C) =
      (1 - qgtPlus P A C) * (1 - qgtMinus P A C) *
        (1 + qgtPlus P A C) * (1 + qgtMinus P A C) :=
  ⟨chiral_factor_product hP A C,
   even_grade_supercharge_factorizations hP A C,
   supercharge_four_factor_product hP A C,
   supercharge_chiral_cycle_product hP A C⟩

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

/-- General off-crash Dirac–Krein propagator `U(Δω, g; c, s) = c I₄ + s N_part(Δω, g)`
(representing `cos(Ω t) I₄ + (sin(Ω t) / Ω) N_part(Δω, g)` for `Ω² = Δω² - g²`, and
specializing at `g = Δω, c = 1, s = t` to the critical crash propagator `I₄ + t N_nil(Δω)`). -/
def diracKreinPropagator (dw g c s : R) : Matrix (Fin 4) (Fin 4) R :=
  c • 1 + s • kreinHopfNilPart dw g

/-- **`MCP₈` Turn 16 Off-Crash Propagator Unitarity, Drift Stationarity, Double-Frequency Zitterbewegung Oscillation & Crash Degeneration:**
For any parameters `dw g c s t : R`:
1. **Mass-Shell Norm Identity**:
   `U(c, -s) U(c, s) = (c² + (Δω² - g²) s²) I₄` (unitary inverse on the mass shell `c² + Ω² s² = 1`),
2. **Exact Stationarity of Classical Drift**:
   `U(c, -s) A_drift U(c, s) = (c² + (Δω² - g²) s²) A_drift` (constant along the trajectory),
3. **Double-Frequency Zitterbewegung Oscillation of Trembling Component**:
   `U(c, -s) A_tremble U(c, s) = (c² - (Δω² - g²) s²) A_tremble - (2 c s) (N_part A_tremble)`
   (oscillating at `cos(2 Ω t) = c² - Ω² s²` and `sin(2 Ω t) / Ω = 2 c s`),
4. **Continuous Degeneration to the Critical Crash Propagator (`g = Δω, c = 1, s = t`)**:
   `diracKreinPropagator dw dw 1 t = 1 + t • kreinCrashNilpotent dw`. -/
theorem diracKrein_offCrash_propagator_and_zitter_oscillation (dw g c s t : R) :
    diracKreinPropagator dw g c (-s) * diracKreinPropagator dw g c s =
      (c ^ 2 + (dw ^ 2 - g ^ 2) * s ^ 2) • 1 ∧
    diracKreinPropagator dw g c (-s) * diracKreinDriftScaled dw g *
        diracKreinPropagator dw g c s =
      (c ^ 2 + (dw ^ 2 - g ^ 2) * s ^ 2) • diracKreinDriftScaled dw g ∧
    diracKreinPropagator dw g c (-s) * diracKreinTrembleScaled dw g *
        diracKreinPropagator dw g c s =
      (c ^ 2 - (dw ^ 2 - g ^ 2) * s ^ 2) • diracKreinTrembleScaled dw g -
        (2 * c * s) • (kreinHopfNilPart dw g * diracKreinTrembleScaled dw g) ∧
    diracKreinPropagator dw dw 1 t = 1 + t • kreinCrashNilpotent dw := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    simp only [diracKreinPropagator, kreinHopfNilPart, Matrix.add_apply,
      Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1] <;> ring
  · ext i j
    simp only [diracKreinPropagator, diracKreinDriftScaled, kreinHopfNilPart,
      Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1] <;> ring
  · ext i j
    simp only [diracKreinPropagator, diracKreinTrembleScaled, kreinHopfNilPart, diracKreinA,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1] <;> ring
  · ext i j
    simp [diracKreinPropagator, kreinCrashNilpotent]

/-- Scaled cubic secular position trajectory `3 X(t) = 3 t A + (3 Δω t²) V_vel + (2 Δω t³) N_nil`
at the critical Krein crash `g = Δω` (Turn 16 Section 2). -/
def diracKreinSecularPosition3 (dw t : R) : Matrix (Fin 4) (Fin 4) R :=
  (3 * t) • diracKreinA + (3 * dw * t ^ 2) • diracKreinVelocity +
    (2 * dw * t ^ 3) • kreinCrashNilpotent dw

/-- **`MCP₈` Turn 16 Velocity Involutivity, Acceleration Commutator & Krein Pseudo-Unitarity of `diracKreinPropagator`:**
1. `V_vel² = +I₄` and `[N_part(Δω, g), V_vel] = -2 Δω B - 2 g A`,
2. At the Krein crash `g = Δω`, `[N_nil(Δω), [N_nil(Δω), A]] = 4 Δω N_nil(Δω)` (constant secular acceleration),
3. The off-crash propagator satisfies exact scaled Krein `J₄`-isometry:
   `U(c, s) J₄ U(c, s)ᵀ = (c² + (Δω² - g²) s²) J₄`! -/
theorem diracKrein_acceleration_unitarity_and_krein_breathing (dw g c s : R) :
    (diracKreinVelocity : Matrix (Fin 4) (Fin 4) R) * diracKreinVelocity = 1 ∧
    comm (kreinHopfNilPart dw g) diracKreinVelocity =
      -(2 * dw) • diracKreinB - (2 * g) • diracKreinA ∧
    comm (kreinCrashNilpotent dw) (comm (kreinCrashNilpotent dw) diracKreinA) =
      (4 * dw) • kreinCrashNilpotent dw ∧
    diracKreinPropagator dw g c s * kreinMetric4 *
        (diracKreinPropagator dw g c s)ᵀ =
      (c ^ 2 + (dw ^ 2 - g ^ 2) * s ^ 2) • kreinMetric4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    { ext i j
      simp only [comm, diracKreinPropagator, kreinCrashNilpotent, kreinHopfNilPart,
        diracKreinVelocity, diracKreinA, diracKreinB,
        Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_four]
      fin_cases i <;> fin_cases j <;> simp [kreinMetric4, jwGamma2, jwE1] <;> ring }

/-- **`MCP₈` Turn 16 Exact Cubic Secular Position Increment Identity:**
The scaled cubic secular position trajectory `diracKreinSecularPosition3 dw t` has exact
first-order increment `3 U(-t) A U(t) dt`:
`diracKreinSecularPosition3 dw (t + dt) - diracKreinSecularPosition3 dw t = (3 dt) U(-t) A U(t) + dt² ((3 Δω) V_vel + (6 Δω t + 2 Δω dt) N_nil)`. -/
theorem diracKrein_cubic_secular_position_increment (dw t dt : R) :
    diracKreinSecularPosition3 dw (t + dt) - diracKreinSecularPosition3 dw t =
      (3 * dt) • ((1 - t • kreinCrashNilpotent dw) * diracKreinA * (1 + t • kreinCrashNilpotent dw)) +
      (dt ^ 2) • ((3 * dw) • diracKreinVelocity +
        (6 * dw * t + 2 * dw * dt) • kreinCrashNilpotent dw) := by
  ext i j
  simp only [diracKreinSecularPosition3, kreinCrashNilpotent, kreinHopfNilPart,
    diracKreinVelocity, diracKreinA, diracKreinB,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.one_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1] <;> ring

/-- Cleared Newton–Wigner / Foldy–Wouthuysen mean position operator
`X_NW(t) = (Δω² - g²) X₀ + t A_drift(Δω, g)`. -/
def diracKreinNewtonWignerPos (X0 : Matrix (Fin 4) (Fin 4) R) (dw g t : R) :
    Matrix (Fin 4) (Fin 4) R :=
  (dw ^ 2 - g ^ 2) • X0 + t • diracKreinDriftScaled dw g

/-- **`MCP₈` Pass-3 Newton–Wigner Mean Position & Zero Zitterbewegung Acceleration:**
1. **Constant Mean Velocity**: `[N_part(Δω, g), A_drift] = 0`.
2. **Harmonic Oscillator Equation for Trembling Velocity**:
   `[N_part(Δω, g), [N_part(Δω, g), A_tremble]] = -(4 * (Δω² - g²)) • A_tremble`.
3. **Exact Linear Drift of Newton–Wigner Mean Position**:
   `X_NW(t₁ + t₂) - X_NW(t₁) = t₂ • A_drift`, and if `[N_part, X₀] = 0`, then `[N_part, X_NW(t)] = 0`. -/
theorem newtonWigner_mean_position_zero_zitterbewegung
    (X0 : Matrix (Fin 4) (Fin 4) R) (dw g t1 t2 : R)
    (hX0 : comm (kreinHopfNilPart dw g) X0 = 0) :
    comm (kreinHopfNilPart dw g) (diracKreinDriftScaled dw g) = 0 ∧
    comm (kreinHopfNilPart dw g) (comm (kreinHopfNilPart dw g) (diracKreinTrembleScaled dw g)) =
      -(4 * (dw ^ 2 - g ^ 2)) • diracKreinTrembleScaled dw g ∧
    diracKreinNewtonWignerPos X0 dw g (t1 + t2) -
      diracKreinNewtonWignerPos X0 dw g t1 =
      t2 • diracKreinDriftScaled dw g ∧
    comm (kreinHopfNilPart dw g) (diracKreinNewtonWignerPos X0 dw g t1) = 0 := by
  have hDrift : comm (kreinHopfNilPart dw g) (diracKreinDriftScaled dw g) = 0 :=
    (diracKrein_zitter_split dw g).2.1
  refine ⟨hDrift, ?_, ?_, ?_⟩
  · ext i j
    simp only [comm, diracKreinTrembleScaled, kreinHopfNilPart, diracKreinA,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1] <;> ring
  · ext i j
    simp [diracKreinNewtonWignerPos, add_smul]
  · have h_lin : comm (kreinHopfNilPart dw g) (diracKreinNewtonWignerPos X0 dw g t1) =
        (dw ^ 2 - g ^ 2) • comm (kreinHopfNilPart dw g) X0 +
          t1 • comm (kreinHopfNilPart dw g) (diracKreinDriftScaled dw g) := by
      dsimp [comm, diracKreinNewtonWignerPos]
      ext i j
      simp [Matrix.mul_apply, Fin.sum_univ_four]
      ring
    rw [h_lin, hX0, hDrift, smul_zero, smul_zero, add_zero]

/-- Inter-sheet axial exchange current `J_axial = ε ⊗ I₂ = -diracKreinB * kreinMetric4`. -/
def diracKreinAxialCurrent : Matrix (Fin 4) (Fin 4) R :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     -1, 0, 0, 0;
     0, -1, 0, 0]

/-- **`MCP₈` Pass-3 Chiral Sheet-Current Non-Conservation vs. Vector Carrier Conservation:**
1. **Vector Carrier Current Conservation**: `[N_part(Δω, g), S_semi(1)] = 0`.
2. **Chiral Sheet-Grading Non-Conservation (Mass-Induced Axial Source)**:
   `[N_part(Δω, g), J₄] = -(2 * g) • diracKreinAxialCurrent`, which vanishes at `g = 0`.
3. `J_axial² = -I₄` and `{J₄, J_axial} = 0`. -/
theorem diracKrein_chiral_axial_nonconservation_and_carrier_conservation (dw g : R) :
    comm (kreinHopfNilPart dw g) (kreinHopfSemi 1) = 0 ∧
    comm (kreinHopfNilPart dw g) kreinMetric4 = -(2 * g) • diracKreinAxialCurrent ∧
    comm (kreinHopfNilPart dw 0) kreinMetric4 = 0 ∧
    (diracKreinAxialCurrent : Matrix (Fin 4) (Fin 4) R) * diracKreinAxialCurrent = -1 ∧
    anticomm (kreinMetric4 : Matrix (Fin 4) (Fin 4) R) diracKreinAxialCurrent = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    { ext i j
      simp only [comm, anticomm, kreinHopfNilPart, kreinHopfSemi, kreinMetric4,
        diracKreinAxialCurrent, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
        Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply, Matrix.zero_apply, Fin.sum_univ_four]
      fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1] <;> ring }

/-- **`MCP₈` Pass-3 Codebase Reuse (`ZitterbewegungVelocity`): Chiral Zitterbewegung Velocity & Two-Connection Square:**
Directly reuses `InfoGeometry.OperatorAlgebra.PeirceSpine` (`ZitterbewegungVelocity.lean`) to establish:
1. `zitterVelocity P A C = -(2 : ℤ) • genJ P A C` (`zitterVelocity_genJ`),
2. `zitterVelocity P A C * zitterVelocity P A C = -(4 : ℤ) • genV P A C` (`zitterVelocity_square`),
3. `comm (peirceMassDirac P A C) (comm (peirceMassDirac P A C) (genJ P A C)) = 4 • (D² * J)` (`zitter_velocity_oscillation`),
4. `(Φ₁ + J₂)² = (V₁ - V₂) + crossConnectionAnticommutator P A₁ C₁ A₂ C₂` (`twoConnectionDiracSquare`). -/
theorem peirce_zitterbewegung_velocity_reuse
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C A₁ C₁ A₂ C₂ : B) :
    zitterVelocity P A C = -(2 : ℤ) • genJ P A C ∧
    zitterVelocity P A C * zitterVelocity P A C = -(4 : ℤ) • genV P A C ∧
    comm (peirceMassDirac P A C) (comm (peirceMassDirac P A C) (genJ P A C)) =
      (4 : ℤ) • (peirceMassDirac P A C * peirceMassDirac P A C * genJ P A C) ∧
    (genPhi P A₁ C₁ + genJ P A₂ C₂) * (genPhi P A₁ C₁ + genJ P A₂ C₂) =
      (genV P A₁ C₁ - genV P A₂ C₂) + crossConnectionAnticommutator P A₁ C₁ A₂ C₂ :=
  ⟨zitterVelocity_genJ hP A C,
   zitterVelocity_square hP A C,
   zitter_velocity_oscillation hP A C,
   twoConnectionDiracSquare hP A₁ C₁ A₂ C₂⟩

/-- General matrix identity: if `P` is a scaled `J`-isometry (`Pᵀ * J * P = a • J`) and
commutes with `N` (`N * P = P * N`), then `P` preserves the form `J * N` with scale `a`. -/
theorem propagator_conserves_metric_mul {J N P : Matrix (Fin 4) (Fin 4) R} {a : R}
    (hJ : Pᵀ * J * P = a • J) (hComm : N * P = P * N) :
    Pᵀ * (J * N) * P = a • (J * N) := by
  calc Pᵀ * (J * N) * P
    _ = (Pᵀ * J) * (N * P) := by simp only [Matrix.mul_assoc]
    _ = (Pᵀ * J * P) * N := by rw [hComm]; simp only [Matrix.mul_assoc]
    _ = (a • J) * N := by rw [hJ]
    _ = a • (J * N) := smul_mul_assoc a J N

/-- **`MCP₈` Pass-4 Heisenberg Velocity/Acceleration Equations of Motion & Krein Energy Conservation:**
1. **Velocity Anticommutation**: `{N_part(Δω, g), V_vel} = 0`.
2. **First Heisenberg Velocity Derivative**:
   `[N_part(Δω, g), V_vel] = -((2 * dw) • diracKreinB + (2 * g) • diracKreinA)`.
3. **Second Heisenberg Velocity Derivative (Zitterbewegung Harmonic Oscillator at `2 Ω`)**:
   `[N_part(Δω, g), [N_part(Δω, g), V_vel]] = -(4 * (dw ^ 2 - g ^ 2)) • V_vel`.
4. **Skew-Symmetry & Propagator Conservation of `J₄ * N_part(Δω, g)`**:
   `(J₄ * N_part(Δω, g))ᵀ = -(J₄ * N_part(Δω, g))` and
   `(U(c, s))ᵀ * (J₄ * N_part(Δω, g)) * U(c, s) = (c² + (Δω² - g²) s²) • (J₄ * N_part(Δω, g))`. -/
theorem diracKrein_velocity_heisenberg_eom_and_energy_conservation (dw g c s : R) :
    anticomm (kreinHopfNilPart dw g) diracKreinVelocity = 0 ∧
    comm (kreinHopfNilPart dw g) diracKreinVelocity =
      -((2 * dw) • diracKreinB + (2 * g) • diracKreinA) ∧
    comm (kreinHopfNilPart dw g) (comm (kreinHopfNilPart dw g) diracKreinVelocity) =
      -(4 * (dw ^ 2 - g ^ 2)) • diracKreinVelocity ∧
    (kreinMetric4 * kreinHopfNilPart dw g)ᵀ = -(kreinMetric4 * kreinHopfNilPart dw g) ∧
    (diracKreinPropagator dw g c s)ᵀ * (kreinMetric4 * kreinHopfNilPart dw g) *
        diracKreinPropagator dw g c s =
      (c ^ 2 + (dw ^ 2 - g ^ 2) * s ^ 2) • (kreinMetric4 * kreinHopfNilPart dw g) := by
  have h1 : anticomm (kreinHopfNilPart dw g) diracKreinVelocity = 0 := by
    ext i j
    simp only [anticomm, kreinHopfNilPart, diracKreinVelocity, diracKreinA, diracKreinB,
      Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.zero_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1]
  have h2 : comm (kreinHopfNilPart dw g) diracKreinVelocity =
      -((2 * dw) • diracKreinB + (2 * g) • diracKreinA) := by
    ext i j
    simp only [comm, kreinHopfNilPart, diracKreinVelocity, diracKreinA, diracKreinB,
      Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.mul_apply,
      Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1] <;> ring
  have h3 : comm (kreinHopfNilPart dw g) (comm (kreinHopfNilPart dw g) diracKreinVelocity) =
      -(4 * (dw ^ 2 - g ^ 2)) • diracKreinVelocity := by
    rw [h2]
    ext i j
    simp only [comm, kreinHopfNilPart, diracKreinVelocity, diracKreinA, diracKreinB,
      Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.mul_apply,
      Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1] <;> ring
  have h4 : (kreinMetric4 * kreinHopfNilPart dw g)ᵀ = -(kreinMetric4 * kreinHopfNilPart dw g) := by
    ext i j
    simp only [kreinMetric4, kreinHopfNilPart,
      Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1]
  have hComm : kreinHopfNilPart dw g * diracKreinPropagator dw g c s =
      diracKreinPropagator dw g c s * kreinHopfNilPart dw g := by
    simp only [diracKreinPropagator, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  have hJ : (diracKreinPropagator dw g c s)ᵀ * kreinMetric4 * diracKreinPropagator dw g c s =
      (c ^ 2 + (dw ^ 2 - g ^ 2) * s ^ 2) • kreinMetric4 := by
    ext i j
    simp only [diracKreinPropagator, kreinHopfNilPart, kreinMetric4,
      Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1] <;> ring
  exact ⟨h1, h2, h3, h4, propagator_conserves_metric_mul hJ hComm⟩

/-- Explicit `4 × 4` matrix presentation of `diracKreinVelocity = diracKreinA * diracKreinB = -ε ⊗ ε`. -/
theorem diracKreinVelocity_eq :
    (diracKreinVelocity : Matrix (Fin 4) (Fin 4) R) =
      !![0, 0, 0, -1;
         0, 0, 1, 0;
         0, 1, 0, 0;
         -1, 0, 0, 0] := by
  ext i j
  simp only [diracKreinVelocity, diracKreinA, diracKreinB, Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1]

/-- Dual Zitterbewegung velocity-precession generator `N_dual(Δω, g) = Δω B + g A` (Turn 16 Section 2). -/
def diracKreinPartDual (dw g : R) : Matrix (Fin 4) (Fin 4) R :=
  dw • diracKreinB + g • diracKreinA

/-- `so(2,1) ≅ sl(2)` Lie bracket table and quadratic Casimir `B² + V_vel² - A² = 3 I₄`
for `(diracKreinA, diracKreinB, diracKreinVelocity)`. -/
theorem diracKrein_so21_triad_and_casimir :
    comm (diracKreinA : Matrix (Fin 4) (Fin 4) R) diracKreinB = (2 : R) • diracKreinVelocity ∧
    comm (diracKreinB : Matrix (Fin 4) (Fin 4) R) diracKreinVelocity = -(2 : R) • diracKreinA ∧
    comm (diracKreinVelocity : Matrix (Fin 4) (Fin 4) R) diracKreinA = (2 : R) • diracKreinB ∧
    (diracKreinB : Matrix (Fin 4) (Fin 4) R) * diracKreinB +
      diracKreinVelocity * diracKreinVelocity - diracKreinA * diracKreinA = (3 : R) • 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    { ext i j
      simp only [comm, diracKreinVelocity_eq, diracKreinA, diracKreinB,
        Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
        Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four]
      fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1] <;> ring }

/-- Dual Zitterbewegung precession generator identities for `diracKreinPartDual dw g`. -/
theorem diracKreinPartDual_identities (dw g : R) :
    diracKreinPartDual dw g = -(kreinHopfNilPart dw g * diracKreinVelocity) ∧
    diracKreinPartDual dw g * diracKreinPartDual dw g =
      (dw ^ 2 - g ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R) ∧
    anticomm (kreinHopfNilPart dw g) (diracKreinPartDual dw g) = 0 ∧
    comm (kreinHopfNilPart dw g) (diracKreinPartDual dw g) =
      (2 * (dw ^ 2 - g ^ 2)) • diracKreinVelocity := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    simp only [diracKreinPartDual, kreinHopfNilPart, diracKreinVelocity_eq,
      diracKreinA, diracKreinB, Matrix.add_apply, Matrix.neg_apply,
      Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1] <;> ring
  · ext i j
    simp only [diracKreinPartDual, diracKreinA, diracKreinB,
      Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1] <;> ring
  · ext i j
    simp only [anticomm, diracKreinPartDual, kreinHopfNilPart,
      diracKreinA, diracKreinB, Matrix.add_apply, Matrix.smul_apply,
      Matrix.mul_apply, Matrix.zero_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1] <;> ring
  · ext i j
    simp only [comm, diracKreinPartDual, kreinHopfNilPart, diracKreinVelocity_eq,
      diracKreinA, diracKreinB, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1] <;> ring

/-- **`MCP₈` Pass-5 `so(2,1)` Lie Algebra Triad, Quadratic Casimir, Dual Precession Generator & `CurvatureDoubleCommutator` Reuse:**
1. The triad `(diracKreinA, diracKreinB, diracKreinVelocity)` closes into an exact `so(2,1) ≅ sl(2)`
   Lie algebra with `[A, B] = 2 V_vel`, `[B, V_vel] = -2 A`, `[V_vel, A] = 2 B`, and quadratic Casimir
   `B² + V_vel² - A² = 3 I₄`.
2. The dual precession generator `N_dual = Δω B + g A = -N_part V_vel` satisfies
   `N_dual² = (Δω² - g²) I₄`, `{N_part, N_dual} = 0`, and `[N_part, N_dual] = 2(Δω² - g²) V_vel`.
3. Reuses `CurvatureDoubleCommutator` (`curvatureDoubleCommutator_quadratic_phi`,
   `curvatureDoubleCommutator_quadratic_j`, and `curvatureDoubleCommutator_mul_genV_defect_iterate`). -/
theorem diracKrein_so21_lie_algebra_and_casimir_and_curvature_reuse
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C X : B) (n : ℕ)
    (dw g : R) :
    (comm (diracKreinA : Matrix (Fin 4) (Fin 4) R) diracKreinB = (2 : R) • diracKreinVelocity ∧
     comm (diracKreinB : Matrix (Fin 4) (Fin 4) R) diracKreinVelocity = -(2 : R) • diracKreinA ∧
     comm (diracKreinVelocity : Matrix (Fin 4) (Fin 4) R) diracKreinA = (2 : R) • diracKreinB ∧
     (diracKreinB : Matrix (Fin 4) (Fin 4) R) * diracKreinB +
       diracKreinVelocity * diracKreinVelocity - diracKreinA * diracKreinA = (3 : R) • 1) ∧
    (diracKreinPartDual dw g = -(kreinHopfNilPart dw g * diracKreinVelocity) ∧
     diracKreinPartDual dw g * diracKreinPartDual dw g =
       (dw ^ 2 - g ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R) ∧
     anticomm (kreinHopfNilPart dw g) (diracKreinPartDual dw g) = 0 ∧
     comm (kreinHopfNilPart dw g) (diracKreinPartDual dw g) =
       (2 * (dw ^ 2 - g ^ 2)) • diracKreinVelocity) ∧
    (curvatureDoubleCommutator P A C (curvatureDoubleCommutator P A C (genPhi P A C)) +
       (4 : ℤ) • (genV P A C * curvatureDoubleCommutator P A C (genPhi P A C)) -
       (4 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C) = 0 ∧
     curvatureDoubleCommutator P A C (curvatureDoubleCommutator P A C (genJ P A C)) +
       (4 : ℤ) • (genV P A C * curvatureDoubleCommutator P A C (genJ P A C)) -
       (4 : ℤ) • ((genV P A C * genV P A C) * genJ P A C) = 0 ∧
     curvatureDoubleCommutator P A C
       (X * InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[n] (genV P A C)) =
       curvatureDoubleCommutator P A C X *
         InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[n] (genV P A C)) :=
  ⟨diracKrein_so21_triad_and_casimir,
   diracKreinPartDual_identities dw g,
   ⟨curvatureDoubleCommutator_quadratic_phi hP A C,
    curvatureDoubleCommutator_quadratic_j hP A C,
    curvatureDoubleCommutator_mul_genV_defect_iterate hP A C X n⟩⟩

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

/-- `4 × 4` Cayley–Foldy–Wouthuysen transformation operator `U_FW(u, v) = u I₄ + v V_vel`
generated by the velocity bivector `V_vel = diracKreinVelocity = -ε ⊗ ε` (`V_vel² = +I₄`). -/
def fwTransform4 (u v : R) : Matrix (Fin 4) (Fin 4) R :=
  u • 1 + v • diracKreinVelocity

/-- **`MCP₉` `4 × 4` Foldy–Wouthuysen Block-Diagonalization of the Dirac–Krein Generator & Crash Obstruction (Turn 17):**
For any rational rapidity parameters `u, v, κ ∈ R` with `Δω = (u² + v²) κ` and `g = 2 u v κ`
(representing `tanh(2θ) = 2(v/u) / (1 + (v/u)²) = g / Δω`):
1. **Unimodular Normalization Factor**:
   `fwTransform4 u (-v) * fwTransform4 u v = (u² - v²) I₄` (proportional to the Plabic Schur denominator `1 + f = 1 - (v/u)²`),
2. **Exact General Conjugation Action**:
   `fwTransform4 u (-v) * kreinHopfNilPart dw g * fwTransform4 u v = ((u² + v²) dw - 2 u v g) A + ((u² + v²) g - 2 u v dw) B`,
3. **Exact Block-Diagonalization (Elimination of Cross-Sheet Boost `B = σ_x ⊗ I₂`)**:
   At `dw = (u² + v²) κ` and `g = 2 u v κ`, the cross-sheet term `B` vanishes identically:
   `fwTransform4 u (-v) * kreinHopfNilPart ((u² + v²) * κ) (2 * u * v * κ) * fwTransform4 u v = ((u² - v²)² * κ) • diracKreinA`,
4. **Breakdown at the Critical Krein Crash (`v = u`, `f = -1`)**:
   At `v = u`, `fwTransform4 u (-u) * fwTransform4 u u = 0`, proving that the Foldy–Wouthuysen
   diagonalization becomes singular precisely at the Plabic Schur pole `1 + f = 0` (`g = Δω`)! -/
theorem foldyWouthuysen_cl22_diagonalization_and_crash_obstruction (u v kappa dw g : R) :
    fwTransform4 u (-v) * fwTransform4 u v = (u ^ 2 - v ^ 2) • 1 ∧
    fwTransform4 u (-v) * kreinHopfNilPart dw g * fwTransform4 u v =
      ((u ^ 2 + v ^ 2) * dw - 2 * u * v * g) • diracKreinA +
        ((u ^ 2 + v ^ 2) * g - 2 * u * v * dw) • diracKreinB ∧
    fwTransform4 u (-v) * kreinHopfNilPart ((u ^ 2 + v ^ 2) * kappa) (2 * u * v * kappa) *
        fwTransform4 u v =
      ((u ^ 2 - v ^ 2) ^ 2 * kappa) • diracKreinA ∧
    fwTransform4 u (-u) * fwTransform4 u u = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    simp only [fwTransform4, diracKreinVelocity, diracKreinA, diracKreinB,
      Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1] <;> ring
  · ext i j
    simp only [fwTransform4, kreinHopfNilPart, diracKreinVelocity, diracKreinA, diracKreinB,
      Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1] <;> ring
  · ext i j
    simp only [fwTransform4, kreinHopfNilPart, diracKreinVelocity, diracKreinA, diracKreinB,
      Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1] <;> ring
  · ext i j
    simp only [fwTransform4, diracKreinVelocity, diracKreinA, diracKreinB,
      Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.one_apply, Matrix.zero_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1]

/-- **`MCP₉` Finite Group-Level Non-Collinear Boost Holonomy & Thomas–Wigner RoPE Rotation (Turn 17 Section 4):**
For two finite Cayley boosts `B₁(v₁) = I₄ + v₁ K₁` and `B₂(v₂) = I₄ + v₂ K₂` along the
orthogonal cross-sheet directions `K₁ = jwE1` and `K₂ = fwBoost2`:
1. `B₁(v₁) B₂(v₂) = I₄ + v₁ K₁ + v₂ K₂ + v₁ v₂ diracKreinA`,
2. Their group-level non-commutativity defect `B₁(v₁) B₂(v₂) - B₂(v₂) B₁(v₁)` is purely the
   elliptic RoPE phase generator `(2 v₁ v₂) (σ_z ⊗ ε) = (2 v₁ v₂) diracKreinA`! -/
theorem thomasWigner_finite_boost_holonomy (v1 v2 : R) :
    ((1 : Matrix (Fin 4) (Fin 4) R) + v1 • jwE1) * (1 + v2 • fwBoost2) =
      1 + v1 • jwE1 + v2 • fwBoost2 + (v1 * v2) • diracKreinA ∧
    ((1 : Matrix (Fin 4) (Fin 4) R) + v1 • jwE1) * (1 + v2 • fwBoost2) -
      (1 + v2 • fwBoost2) * (1 + v1 • jwE1) =
      (2 * v1 * v2) • diracKreinA := by
  refine ⟨?_, ?_⟩ <;>
    { ext i j
      simp only [diracKreinA, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four]
      fin_cases i <;> fin_cases j <;>
        simp [jwE1, fwBoost2, jwGamma2] <;>
        ring }

/-- **`MCP₉` Turn 17 Krein `J₄`-Pseudo-Unitarity of `fwTransform4` & Thomas–Wigner Boost Conjugation:**
1. The Foldy–Wouthuysen operator `fwTransform4 u v = u I₄ + v V_vel` is a scaled Krein `J₄`-isometry:
   `fwTransform4 u (-v) * J₄ * (fwTransform4 u (-v))ᵀ = (u² - v²) J₄`!
2. Conjugating the second boost `I₄ + v₂ K₂` by the orthogonal boost `I₄ + v₁ K₁` yields
   `(I₄ + v₁ K₁) (I₄ + v₂ K₂) (I₄ - v₁ K₁) = (1 - v₁²) I₄ + ((1 + v₁²) v₂) K₂ + (2 v₁ v₂) diracKreinA`! -/
theorem foldyWouthuysen_krein_unitarity_and_thomas_polar (u v v1 v2 : R) :
    fwTransform4 u (-v) * kreinMetric4 * (fwTransform4 u (-v))ᵀ =
      (u ^ 2 - v ^ 2) • kreinMetric4 ∧
    ((1 : Matrix (Fin 4) (Fin 4) R) + v1 • jwE1) * (1 + v2 • fwBoost2) * (1 - v1 • jwE1) =
      (1 - v1 ^ 2) • 1 +
        ((1 + v1 ^ 2) * v2) • fwBoost2 +
        (2 * v1 * v2) • diracKreinA := by
  refine ⟨?_, ?_⟩ <;>
    { ext i j
      simp only [fwTransform4, diracKreinVelocity, diracKreinA, diracKreinB,
        Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_four]
      fin_cases i <;> fin_cases j <;> simp [kreinMetric4, jwE1, fwBoost2, jwGamma2] <;> ring }

/-- **`MCP₉` Codebase Reuse (`FoldyWouthuysenPlabicRapidityBridge`): Inverse Rapidity Map, Bare Log-Strand Jacobian & Dressed Strands:**
Directly reuses `InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge` to establish:
1. For `f ∈ (-1, 0)`, `loopWeight (artanh(√(-f))) = f` (`loopWeight_artanh_sqrt`),
2. For `0 < θ`, the bare log-strand 2-form Jacobian is `4 / sinh(2θ)` (`bare_log_strand_jacobian`),
3. Multiplying by the Plabic loop prefactor `(1 - f)/(1 + f)` yields `4 cosh(2θ) / sinh(2θ)` (`loopPrefactor_mul_bare_log_jacobian`),
4. The dressed lower and upper strands equal `(1/2) sinh(2θ) e^{-χ}` and `(1/2) sinh(2θ) e^{+χ}` (`lowerDressedStrand_eq`, `upperDressedStrand_eq`). -/
theorem foldyWouthuysen_rapidity_inversion_and_jacobian_reuse
    (f θ χ : ℝ) (hf₀ : -1 < f) (hf₁ : f < 0) (hθ : 0 < θ) :
    InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.loopWeight
        (Real.artanh (Real.sqrt (-f))) = f ∧
    deriv (fun t : ℝ => InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.lowerLogCoordinate t χ) θ *
        deriv (fun t : ℝ => InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.upperLogCoordinate θ t) χ -
      deriv (fun t : ℝ => InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.lowerLogCoordinate θ t) χ *
        deriv (fun t : ℝ => InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.upperLogCoordinate t χ) θ =
        4 / Real.sinh (2 * θ) ∧
    ((1 - InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.loopWeight θ) /
      (1 + InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.loopWeight θ)) *
      (4 / Real.sinh (2 * θ)) =
        4 * Real.cosh (2 * θ) / Real.sinh (2 * θ) ∧
    InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.lowerStrand θ χ /
      (1 + InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.loopWeight θ) =
        (1 / 2 : ℝ) * Real.sinh (2 * θ) * Real.exp (-χ) ∧
    InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.upperStrand θ χ /
      (1 + InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.loopWeight θ) =
        (1 / 2 : ℝ) * Real.sinh (2 * θ) * Real.exp χ :=
  ⟨InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.loopWeight_artanh_sqrt f hf₀ hf₁,
   InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.bare_log_strand_jacobian θ χ hθ,
   InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.loopPrefactor_mul_bare_log_jacobian θ χ,
   InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.lowerDressedStrand_eq θ χ,
   InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge.upperDressedStrand_eq θ χ⟩

/-- Cleared Eriksen sign operator `Λ_scaled(Δω, g) = S_semi(1) * N_part(Δω, g)`
satisfying `Λ_scaled(Δω, g)² = (Δω² - g²) I₄ = Ω² I₄`. -/
def eriksenSignScaled (dw g : R) : Matrix (Fin 4) (Fin 4) R :=
  kreinHopfSemi 1 * kreinHopfNilPart dw g

/-- Cleared Eriksen positive-sheet projector `P_+(Ω, Δω, g) = Ω I₄ + Λ_scaled(Δω, g)`. -/
def eriksenProjectorPosScaled (Omega dw g : R) : Matrix (Fin 4) (Fin 4) R :=
  Omega • 1 + eriksenSignScaled dw g

/-- Cleared Eriksen negative-sheet projector `P_-(Ω, Δω, g) = Ω I₄ - Λ_scaled(Δω, g)`. -/
def eriksenProjectorNegScaled (Omega dw g : R) : Matrix (Fin 4) (Fin 4) R :=
  Omega • 1 - eriksenSignScaled dw g

/-- Cleared Eriksen closed-form Foldy–Wouthuysen operator
`U_Eriksen(Ω, Δω, g) = Ω I₄ + Λ_scaled(Δω, g) * (-J₄) = (Ω + Δω) I₄ + g V_vel`. -/
def eriksenUnitaryScaled (Omega dw g : R) : Matrix (Fin 4) (Fin 4) R :=
  Omega • 1 + eriksenSignScaled dw g * (-kreinMetric4)

/-- **`MCP₉` Pass-3 Eriksen Closed-Form Foldy–Wouthuysen Sign Operator, Exact Projectors & Crash Breakdown:**
Under the mass-shell dispersion relation `dw ^ 2 - g ^ 2 = Omega ^ 2`:
1. **Eriksen Sign Involution**: `eriksenSignScaled dw g * eriksenSignScaled dw g = (Omega ^ 2) • 1`.
2. **Exact Orthogonal Projector Algebra**:
   `P_+ + P_- = (2 * Omega) • 1`, `P_+ * P_- = 0`, and `P_+ * P_+ = (2 * Omega) • P_+`.
3. **Closed-Form Foldy–Wouthuysen Equivalence**:
   `eriksenUnitaryScaled Omega dw g = fwTransform4 (Omega + dw) g`.
4. **Closed-Form Block-Diagonalization Without Series Truncation**:
   `U_Eriksen(Ω, Δω, -g) * U_Eriksen(Ω, Δω, g) = (2 * Ω * (Ω + Δω)) • 1` and
   `U_Eriksen(Ω, Δω, -g) * N_part(Δω, g) * U_Eriksen(Ω, Δω, g) = (2 * Ω² * (Ω + Δω)) • diracKreinA`.
5. **Krein Crash Breakdown at `Ω = 0, Δω = g`**:
   `eriksenUnitaryScaled 0 g (-g) * eriksenUnitaryScaled 0 g g = 0`. -/
theorem eriksen_closed_form_foldy_wouthuysen_and_crash_breakdown
    (Omega dw g : R) (hShell : dw ^ 2 - g ^ 2 = Omega ^ 2) :
    eriksenSignScaled dw g * eriksenSignScaled dw g =
      (Omega ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R) ∧
    eriksenProjectorPosScaled Omega dw g + eriksenProjectorNegScaled Omega dw g =
      (2 * Omega) • (1 : Matrix (Fin 4) (Fin 4) R) ∧
    eriksenProjectorPosScaled Omega dw g * eriksenProjectorNegScaled Omega dw g = 0 ∧
    eriksenProjectorPosScaled Omega dw g * eriksenProjectorPosScaled Omega dw g =
      (2 * Omega) • eriksenProjectorPosScaled Omega dw g ∧
    eriksenUnitaryScaled Omega dw g = fwTransform4 (Omega + dw) g ∧
    eriksenUnitaryScaled Omega dw (-g) * eriksenUnitaryScaled Omega dw g =
      (2 * Omega * (Omega + dw)) • (1 : Matrix (Fin 4) (Fin 4) R) ∧
    eriksenUnitaryScaled Omega dw (-g) * kreinHopfNilPart dw g *
        eriksenUnitaryScaled Omega dw g =
      (2 * Omega ^ 2 * (Omega + dw)) • diracKreinA ∧
    eriksenUnitaryScaled 0 g (-g) * eriksenUnitaryScaled 0 g g = 0 := by
  have hg2 : g ^ 2 = dw ^ 2 - Omega ^ 2 := by
    calc g ^ 2 = dw ^ 2 - (dw ^ 2 - g ^ 2) := by ring
      _ = dw ^ 2 - Omega ^ 2 := by rw [hShell]
  have h_sign_sq :
      eriksenSignScaled dw g * eriksenSignScaled dw g =
        (Omega ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R) := by
    have h_raw :
        eriksenSignScaled dw g * eriksenSignScaled dw g =
          (dw ^ 2 - g ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R) := by
      ext i j
      simp only [eriksenSignScaled, kreinHopfSemi, kreinHopfNilPart,
        Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four]
      fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1] <;> ring
    rw [h_raw, hShell]
  have h_fw : ∀ (O' dw' g' : R), eriksenUnitaryScaled O' dw' g' = fwTransform4 (O' + dw') g' := by
    intro O' dw' g'
    ext i j
    simp only [eriksenUnitaryScaled, eriksenSignScaled, fwTransform4, diracKreinVelocity,
      diracKreinA, diracKreinB, kreinMetric4, kreinHopfSemi, kreinHopfNilPart,
      Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1]
  refine ⟨h_sign_sq, ?_, ?_, ?_, h_fw Omega dw g, ?_, ?_, ?_⟩
  · ext i j
    simp [eriksenProjectorPosScaled, eriksenProjectorNegScaled]
    ring
  · calc eriksenProjectorPosScaled Omega dw g * eriksenProjectorNegScaled Omega dw g
      _ = (Omega ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R) -
            eriksenSignScaled dw g * eriksenSignScaled dw g := by
          ext i j
          simp only [eriksenProjectorPosScaled, eriksenProjectorNegScaled,
            Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
            Matrix.one_apply, Fin.sum_univ_four]
          fin_cases i <;> fin_cases j <;> simp <;> ring
      _ = 0 := by rw [h_sign_sq, sub_self]
  · calc eriksenProjectorPosScaled Omega dw g * eriksenProjectorPosScaled Omega dw g
      _ = (Omega ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R) +
            (2 * Omega) • eriksenSignScaled dw g +
            eriksenSignScaled dw g * eriksenSignScaled dw g := by
          ext i j
          simp only [eriksenProjectorPosScaled,
            Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
            Matrix.one_apply, Fin.sum_univ_four]
          fin_cases i <;> fin_cases j <;> simp <;> ring
      _ = (Omega ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R) +
            (2 * Omega) • eriksenSignScaled dw g +
            (Omega ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R) := by rw [h_sign_sq]
      _ = (2 * Omega) • eriksenProjectorPosScaled Omega dw g := by
          ext i j
          simp [eriksenProjectorPosScaled]
          ring
  · rw [h_fw Omega dw (-g), h_fw Omega dw g,
        (foldyWouthuysen_cl22_diagonalization_and_crash_obstruction (Omega + dw) g 1 dw g).1]
    have h_scalar : (Omega + dw) ^ 2 - g ^ 2 = 2 * Omega * (Omega + dw) := by
      rw [hg2]; ring
    rw [h_scalar]
  · rw [h_fw Omega dw (-g), h_fw Omega dw g,
        (foldyWouthuysen_cl22_diagonalization_and_crash_obstruction (Omega + dw) g 1 dw g).2.1]
    have h_A : ((Omega + dw) ^ 2 + g ^ 2) * dw - 2 * (Omega + dw) * g * g =
        2 * Omega ^ 2 * (Omega + dw) := by
      calc ((Omega + dw) ^ 2 + g ^ 2) * dw - 2 * (Omega + dw) * g * g
        _ = ((Omega + dw) ^ 2 + g ^ 2) * dw - 2 * (Omega + dw) * (g ^ 2) := by ring
        _ = ((Omega + dw) ^ 2 + (dw ^ 2 - Omega ^ 2)) * dw -
              2 * (Omega + dw) * (dw ^ 2 - Omega ^ 2) := by rw [hg2]
        _ = 2 * Omega ^ 2 * (Omega + dw) := by ring
    have h_B : ((Omega + dw) ^ 2 + g ^ 2) * g - 2 * (Omega + dw) * g * dw = 0 := by
      rw [hg2]; ring
    rw [h_A, h_B, zero_smul, add_zero]
  · rw [h_fw 0 g (-g), h_fw 0 g g, zero_add]
    exact (foldyWouthuysen_cl22_diagonalization_and_crash_obstruction g g 1 g g).2.2.2

/-- **`MCP₉` Pass-4 Non-Commutative Foldy–Wouthuysen Odd-Operator Commutator Series over `[Ring B]`:**
For any involution `S * S = 1` and odd operator `O` (`anticomm S O = 0`) in `[Ring B]`:
1. `comm S (O * O) = 0` (`O²` is strictly even),
2. `comm (comm S O) O = (4 : ℤ) • (S * (O * O))` (the quadratic FW correction is purely even),
3. `comm S (comm (comm S O) O) = 0`,
4. `comm (comm (comm S O) O) O = (8 : ℤ) • (S * (O * O * O))` (the cubic FW correction is purely odd),
5. On the Peirce spine (`S = invS P`, `O = genPhi P A C`),
   `comm (comm (invS P) (genPhi P A C)) (genPhi P A C) = (4 : ℤ) • (invS P * genV P A C)`. -/
theorem foldyWouthuysen_noncommutative_odd_commutator_series
    {B : Type*} [Ring B] (S O : B) (hS : S * S = 1) (hOdd : anticomm S O = 0)
    {P : B} (hP : P * P = P) (A C : B) :
    comm S (O * O) = 0 ∧
    comm (comm S O) O = (4 : ℤ) • (S * (O * O)) ∧
    comm S (comm (comm S O) O) = 0 ∧
    comm (comm (comm S O) O) O = (8 : ℤ) • (S * (O * O * O)) ∧
    comm (comm (invS P) (genPhi P A C)) (genPhi P A C) =
      (4 : ℤ) • (invS P * genV P A C) := by
  have hSO : S * O = -(O * S) := eq_neg_of_add_eq_zero_left hOdd
  have hSO' : ∀ x : B, S * (O * x) = -(O * (S * x)) := fun x => by
    rw [← mul_assoc, hSO, neg_mul, mul_assoc]
  have hS' : ∀ x : B, S * (S * x) = x := fun x => by
    rw [← mul_assoc, hS, one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [comm]; noncomm_ring [hS, hS', hSO, hSO']
  · dsimp [comm]; noncomm_ring [hS, hS', hSO, hSO']
  · dsimp [comm]; noncomm_ring [hS, hS', hSO, hSO']
  · dsimp [comm]; noncomm_ring [hS, hS', hSO, hSO']
  · peirce_nf hP

/-- General matrix identity: the product `M₁ * M₂` of two scaled `J`-isometries
(`M₁ * J * M₁ᵀ = s₁ • J` and `M₂ * J * M₂ᵀ = s₂ • J`) is a scaled `J`-isometry
with scale factor `s₁ * s₂`. -/
theorem krein_isometry_mul {J M1 M2 : Matrix (Fin 4) (Fin 4) R} {s1 s2 : R}
    (h1 : M1 * J * M1ᵀ = s1 • J) (h2 : M2 * J * M2ᵀ = s2 • J) :
    (M1 * M2) * J * (M1 * M2)ᵀ = (s1 * s2) • J := by
  calc (M1 * M2) * J * (M1 * M2)ᵀ
    _ = M1 * (M2 * J * M2ᵀ) * M1ᵀ := by
        rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = M1 * (s2 • J) * M1ᵀ := by rw [h2]
    _ = s2 • (M1 * J * M1ᵀ) := by
        rw [mul_smul_comm, smul_mul_assoc]
    _ = s2 • (s1 • J) := by rw [h1]
    _ = (s1 * s2) • J := by
        rw [smul_smul, mul_comm]

/-- **`MCP₉` Pass-4 Collinear Foldy–Wouthuysen Hyperbolic Addition Law & Non-Collinear Wigner Decomposition:**
1. **Collinear FW Hyperbolic Addition Law**:
   `fwTransform4 u1 v1 * fwTransform4 u2 v2 = fwTransform4 (u1 * u2 + v1 * v2) (u1 * v2 + v1 * u2)`
   and `comm (fwTransform4 u1 v1) (fwTransform4 u2 v2) = 0`.
2. **Non-Collinear Orthogonal Boost Symmetric + Symplectic Decomposition**:
   For `B₁ = u₁ I₄ + v₁ K₁` (`K₁ = jwE1`) and `B₂ = u₂ I₄ + v₂ K₂` (`K₂ = fwBoost2`),
   `anticomm B₁ B₂ = (2 * u1 * u2) • 1 + (2 * u2 * v1) • jwE1 + (2 * u1 * v2) • fwBoost2` and
   `comm B₁ B₂ = (2 * v1 * v2) • diracKreinA`.
3. **Composite Non-Collinear Boost Krein `J₄`-Isometry**:
   `(u₁ I₄ - v₁ K₁) * (u₂ I₄ - v₂ K₂) * J₄ * ((u₁ I₄ - v₁ K₁) * (u₂ I₄ - v₂ K₂))ᵀ = ((u₁² - v₁²)(u₂² - v₂²)) • J₄`. -/
theorem foldyWouthuysen_boost_composition_and_wigner_decomposition (u1 v1 u2 v2 : R) :
    fwTransform4 u1 v1 * fwTransform4 u2 v2 =
      fwTransform4 (u1 * u2 + v1 * v2) (u1 * v2 + v1 * u2) ∧
    comm (fwTransform4 u1 v1) (fwTransform4 u2 v2) = 0 ∧
    anticomm (u1 • (1 : Matrix (Fin 4) (Fin 4) R) + v1 • jwE1)
             (u2 • (1 : Matrix (Fin 4) (Fin 4) R) + v2 • fwBoost2) =
      (2 * u1 * u2) • 1 + (2 * u2 * v1) • jwE1 + (2 * u1 * v2) • fwBoost2 ∧
    comm (u1 • (1 : Matrix (Fin 4) (Fin 4) R) + v1 • jwE1)
         (u2 • (1 : Matrix (Fin 4) (Fin 4) R) + v2 • fwBoost2) =
      (2 * v1 * v2) • diracKreinA ∧
    ((u1 • (1 : Matrix (Fin 4) (Fin 4) R) - v1 • jwE1) * (u2 • 1 - v2 • fwBoost2)) *
      kreinMetric4 *
      ((u1 • (1 : Matrix (Fin 4) (Fin 4) R) - v1 • jwE1) * (u2 • 1 - v2 • fwBoost2))ᵀ =
      ((u1 ^ 2 - v1 ^ 2) * (u2 ^ 2 - v2 ^ 2)) • kreinMetric4 := by
  have h1 : ∀ a1 b1 a2 b2 : R,
      fwTransform4 a1 b1 * fwTransform4 a2 b2 =
        fwTransform4 (a1 * a2 + b1 * b2) (a1 * b2 + b1 * a2) := by
    intro a1 b1 a2 b2
    ext i j
    simp only [fwTransform4, diracKreinVelocity, diracKreinA, diracKreinB,
      Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1] <;> ring
  have h2 : comm (fwTransform4 u1 v1) (fwTransform4 u2 v2) = 0 := by
    dsimp [comm]
    rw [h1 u1 v1 u2 v2, h1 u2 v2 u1 v1]
    have h_u : u1 * u2 + v1 * v2 = u2 * u1 + v2 * v1 := by ring
    have h_v : u1 * v2 + v1 * u2 = u2 * v1 + v2 * u1 := by ring
    rw [h_u, h_v, sub_self]
  have h3 : anticomm (u1 • (1 : Matrix (Fin 4) (Fin 4) R) + v1 • jwE1)
               (u2 • (1 : Matrix (Fin 4) (Fin 4) R) + v2 • fwBoost2) =
      (2 * u1 * u2) • 1 + (2 * u2 * v1) • jwE1 + (2 * u1 * v2) • fwBoost2 := by
    ext i j
    simp only [anticomm, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [jwE1, fwBoost2] <;> ring
  have h4 : comm (u1 • (1 : Matrix (Fin 4) (Fin 4) R) + v1 • jwE1)
            (u2 • (1 : Matrix (Fin 4) (Fin 4) R) + v2 • fwBoost2) =
      (2 * v1 * v2) • diracKreinA := by
    ext i j
    simp only [comm, diracKreinA, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [jwE1, fwBoost2, jwGamma2] <;> ring
  have hB1 : (u1 • (1 : Matrix (Fin 4) (Fin 4) R) - v1 • jwE1) * kreinMetric4 *
      (u1 • (1 : Matrix (Fin 4) (Fin 4) R) - v1 • jwE1)ᵀ =
      (u1 ^ 2 - v1 ^ 2) • kreinMetric4 := by
    ext i j
    simp only [kreinMetric4, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [jwE1] <;> ring
  have hB2 : (u2 • (1 : Matrix (Fin 4) (Fin 4) R) - v2 • fwBoost2) * kreinMetric4 *
      (u2 • (1 : Matrix (Fin 4) (Fin 4) R) - v2 • fwBoost2)ᵀ =
      (u2 ^ 2 - v2 ^ 2) • kreinMetric4 := by
    ext i j
    simp only [kreinMetric4, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [fwBoost2] <;> ring
  exact ⟨h1 u1 v1 u2 v2, h2, h3, h4, krein_isometry_mul hB1 hB2⟩

/-- **`MCP₉` Pass-5 Foldy–Wouthuysen Velocity Invariance, Dual Precession Diagonalization & Eriksen Spectral Decomposition (Turn 17):**
1. The Foldy–Wouthuysen transformation `fwTransform4 u v = u I₄ + v V_vel` commutes with the
   Zitterbewegung velocity generator `diracKreinVelocity`, scaling it by `u² - v²` under sandwiching:
   `fwTransform4 u v * diracKreinVelocity * fwTransform4 u (-v) = (u² - v²) • diracKreinVelocity`.
2. Sandwiching the dual precession generator `diracKreinPartDual dw g = Δω B + g A` rotates the
   `(B, A)` plane by the hyperbolic boost `(u² + v², -2 u v)`.
3. Under the Foldy–Wouthuysen odd-block annihilation condition `(u² + v²) * g = 2 * u * v * dw`,
   `diracKreinPartDual dw g` simultaneously diagonalizes to `((u² + v²) * dw - 2 * u * v * g) • diracKreinB`.
4. The scaled Eriksen projectors resolve the identity and the Dirac–Krein relative Hamiltonian:
   `P_+ + P_- = 2 Ω I₄`, `P_+ - P_- = 2 eriksenSignScaled dw g`, and
   `(P_+ - P_-) * (-kreinHopfSemi 1) = 2 kreinHopfNilPart dw g`. -/
theorem foldyWouthuysen_velocity_dual_and_eriksen_spectral_decomposition
    (u v Om dw g : R) :
    fwTransform4 u v * diracKreinVelocity * fwTransform4 u (-v) =
      (u ^ 2 - v ^ 2) • diracKreinVelocity ∧
    fwTransform4 u (-v) * diracKreinPartDual dw g * fwTransform4 u v =
      ((u ^ 2 + v ^ 2) * dw - 2 * u * v * g) • diracKreinB +
        ((u ^ 2 + v ^ 2) * g - 2 * u * v * dw) • diracKreinA ∧
    ((u ^ 2 + v ^ 2) * g = 2 * u * v * dw →
      fwTransform4 u (-v) * diracKreinPartDual dw g * fwTransform4 u v =
        ((u ^ 2 + v ^ 2) * dw - 2 * u * v * g) • diracKreinB) ∧
    eriksenProjectorPosScaled Om dw g + eriksenProjectorNegScaled Om dw g =
      (2 * Om) • (1 : Matrix (Fin 4) (Fin 4) R) ∧
    eriksenProjectorPosScaled Om dw g - eriksenProjectorNegScaled Om dw g =
      (2 : R) • eriksenSignScaled dw g ∧
    (eriksenProjectorPosScaled Om dw g - eriksenProjectorNegScaled Om dw g) * (-kreinHopfSemi 1) =
      (2 : R) • kreinHopfNilPart dw g := by
  have hDual :
      fwTransform4 u (-v) * diracKreinPartDual dw g * fwTransform4 u v =
        ((u ^ 2 + v ^ 2) * dw - 2 * u * v * g) • diracKreinB +
          ((u ^ 2 + v ^ 2) * g - 2 * u * v * dw) • diracKreinA := by
    ext i j
    simp only [fwTransform4, diracKreinPartDual, diracKreinVelocity_eq, diracKreinA, diracKreinB,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [jwGamma2, jwE1] <;> ring
  have hDiff :
      eriksenProjectorPosScaled Om dw g - eriksenProjectorNegScaled Om dw g =
        (2 : R) • eriksenSignScaled dw g := by
    ext i j
    simp only [eriksenProjectorPosScaled, eriksenProjectorNegScaled,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
    fin_cases i <;> fin_cases j <;> simp <;> ring
  have hSignSemi :
      eriksenSignScaled dw g * (-kreinHopfSemi 1) = kreinHopfNilPart dw g := by
    ext i j
    simp only [eriksenSignScaled, kreinHopfNilPart,
      Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [kreinHopfSemi, jwGamma2, jwE1] <;> ring
  refine ⟨?_, hDual, ?_, ?_, hDiff, ?_⟩
  · ext i j
    simp only [fwTransform4, diracKreinVelocity_eq,
      Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp <;> ring
  · intro hCond
    rw [hDual, hCond, sub_self, zero_smul, add_zero]
  · ext i j
    simp only [eriksenProjectorPosScaled, eriksenProjectorNegScaled,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
    fin_cases i <;> fin_cases j <;> simp <;> ring
  · rw [hDiff, smul_mul_assoc, hSignSemi]

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

/-- **`MCP₁₀` Pass-3 Master Synthesis Across All 17 Turns (BCH Splitting, Rota–Baxter, `sl(2)` Casimir,
Clifford `Cl(1,1)` $\to$ Matrix $\to$ Tensor-Tower $\to$ Colimit Spine, Recursive FWHT, `Gr^≥0(2,4)` Plücker
Positivity, Puiseux–Gelfand–Lidskii Residue, `qdet` Centrality, Newton–Wigner Zitterbewegung Cancellation
& Eriksen Closed-Form Foldy–Wouthuysen):**
Coagulates the Pass-3 extractions across `StageMCP1`–`StageMCP9` into a single non-commutative,
Clifford-to-Tensor-Tower, and `Cl(2,2)` operator synthesis. -/
theorem causalMatrix_pass3_master_synthesis
    {R : Type*} [CommRing R]
    (S K : B) (n k : ℕ)
    (X_stage Y_stage : InfoGeometry.Clifford.Cl11TensorTower.MatStage n)
    (px py : Bool)
    (X3 Y3 : Matrix (Fin 3) (Fin 3) R)
    (C24 : Matrix (Fin 2) (Fin 4) R)
    (X0 : Matrix (Fin 4) (Fin 4) R)
    (dw g Omega u v theta eta t1 : R)
    (hShell : dw ^ 2 - g ^ 2 = Omega ^ 2)
    (hX0 : comm (kreinHopfNilPart dw g) X0 = 0) :
    ((1 + S) * (1 + K) - (1 + K) * (1 + S) = comm S K) ∧
    (matStrictLower (matStrictLower X3 * Y3 + X3 * matStrictLower Y3 - X3 * Y3) =
      matStrictLower X3 * matStrictLower Y3) ∧
    (InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat
        (CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (1, 0)) =
      InfoGeometry.Clifford.Cl11Matrix.Eplus ∧
     InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace (n + k)
        (InfoGeometry.Clifford.Cl11TensorTowerIteration.iteratedStageEmbed n k X_stage) =
      InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace n X_stage ∧
     InfoGeometry.Clifford.Cl11TensorTowerSupergraded.ofStage n
        (InfoGeometry.Clifford.Cl11TensorTowerSupergraded.stageSuperBracket px py X_stage Y_stage) =
      InfoGeometry.Algebra.SupergradedBracket.superBracket px py
        (InfoGeometry.Clifford.Cl11TensorTowerSupergraded.ofStage n X_stage)
        (InfoGeometry.Clifford.Cl11TensorTowerSupergraded.ofStage n Y_stage)) ∧
    (towerWalshHadamard B n * towerWalshHadamard B n =
      (2 ^ n : ℕ) • (1 : OpMatTower B n)) ∧
    (pluckerMinor24 C24 0 1 * pluckerMinor24 C24 2 3 -
      pluckerMinor24 C24 0 2 * pluckerMinor24 C24 1 3 +
      pluckerMinor24 C24 0 3 * pluckerMinor24 C24 1 2 = 0) ∧
    (dotProduct (kreinExceptionalVec (R := R))
      (Matrix.mulVec (kreinMetric4 * (-jwE1)) kreinJordanRootVec) = (1 : R)) ∧
    (comm (laxBlockA u theta eta * laxBlockD (u - eta) theta eta - laxBlockB eta * laxBlockC eta)
          (laxBlockA v theta eta) = 0) ∧
    (comm (kreinHopfNilPart dw g) (diracKreinNewtonWignerPos X0 dw g t1) = 0) ∧
    (eriksenSignScaled dw g * eriksenSignScaled dw g =
      (Omega ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R) ∧
     eriksenUnitaryScaled Omega dw g = fwTransform4 (Omega + dw) g) := by
  exact ⟨(bch_zassenhaus_quadratic_splitting_defect S K).1,
         (rota_baxter_weight_neg_one_and_gohberg_krein_leakage X3 Y3).2.1,
         ⟨InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat_iota_pos,
          InfoGeometry.Clifford.Cl11TensorTowerIteration.iteratedStageEmbed_normalizedTrace n k X_stage,
          InfoGeometry.Clifford.Cl11TensorTowerSupergraded.ofStage_superBracket px py X_stage Y_stage⟩,
         towerWalshHadamard_mul_self B n,
         (plabic_positroid_gr24_all_six_plucker_and_total_positivity
           C24 1 1 1 1 1 1 1 1 zero_lt_one zero_lt_one zero_lt_one zero_lt_one).1,
         (krein_puiseux_perturbation_and_gelfand_lidskii_residue (R := R) dw 0).2.2.2.1,
         (yangian_qdet_centrality_and_antisymmetrizer_fusion u v theta eta).2.2.2.2.1,
         (newtonWigner_mean_position_zero_zitterbewegung X0 dw g t1 0 hX0).2.2.2,
         ⟨(eriksen_closed_form_foldy_wouthuysen_and_crash_breakdown Omega dw g hShell).1,
          (eriksen_closed_form_foldy_wouthuysen_and_crash_breakdown Omega dw g hShell).2.2.2.2.1⟩⟩

/-- **`MCP₁₀` Pass-4 Master Synthesis Across All 17 Turns (Morrison Casimir Degeneracy, Quartic Meta-Aporia,
Wiener–Hopf Resolvent, `sp(2)` Trace & `Cl(1,1)` Star-Colimit Filtration, Recursive FWHT Diagonal/XOR Duality,
`Gr_+(2,4)` Twisted Cyclic Shift, Canonical `4 × 4` Jordan Form, Dual Bethe Exchange & Two-Site `qdet`,
Heisenberg Velocity EOM, Non-Commutative FW Odd Series & Hyperbolic Boost Group Law):**
Coagulates the Pass-4 archetypes across `StageMCP1`–`StageMCP9` and the `Cl(1,1)` Star-Algebra Colimit
filtration spine into a single master theorem. -/
theorem causalMatrix_pass4_master_synthesis
    {R : Type*} [CommRing R]
    {P : B} (hP : P * P = P) (A C X : B)
    (n : ℕ) (i j : Fin n)
    (D₀ D₁ : OpMatTower B n)
    (X3 Y3 : Matrix (Fin 3) (Fin 3) R)
    (X2 : Matrix (Fin 2) (Fin 2) R)
    (C24 : Matrix (Fin 2) (Fin 4) R)
    (wBar dw g u v theta1 theta2 eta u1 v1 u2 v2 : R) :
    (metaAporiaIter X 1 = (X * X - X) * (X * X - X - 1) ∧
     towerJWChirality B n i * towerJWChirality B n i = (1 : OpMatTower B n)) ∧
    (((1 - matStrictLower X3) * (1 - matStrictUpper Y3)) *
       ((1 + matStrictUpper Y3 + matStrictUpper Y3 * matStrictUpper Y3) *
        (1 + matStrictLower X3 + matStrictLower X3 * matStrictLower X3)) = 1 ∧
     matDiscreteHilbert (matStrictLower X3 + matStrictUpper X3) *
       matDiscreteHilbert (matStrictLower X3 + matStrictUpper X3) =
       -((matStrictLower X3 + matStrictUpper X3) * (matStrictLower X3 + matStrictUpper X3)) +
         matDiscreteHilbert (anticomm (matStrictLower X3 + matStrictUpper X3)
           (matDiscreteHilbert (matStrictLower X3 + matStrictUpper X3)))) ∧
    (X2ᵀ * (epsSymp : Matrix (Fin 2) (Fin 2) R) + epsSymp * X2 =
       Matrix.trace X2 • (epsSymp : Matrix (Fin 2) (Fin 2) R) ∧
     InfoGeometry.Clifford.Cl11StarAlgebraFiltration.stageImage n <
       InfoGeometry.Clifford.Cl11StarAlgebraFiltration.stageImage (n + 1) ∧
     Module.finrank ℝ (InfoGeometry.Clifford.Cl11StarAlgebraFiltration.stageImage n) = 4 ^ n ∧
     InfoGeometry.Clifford.Cl11TensorTower.jwAnnihilation n i *
         InfoGeometry.Clifford.Cl11TensorTower.jwCreation n j +
       InfoGeometry.Clifford.Cl11TensorTower.jwCreation n j *
         InfoGeometry.Clifford.Cl11TensorTower.jwAnnihilation n i =
       (if i = j then 1 else 0)) ∧
    (towerWalshHadamard B (n + 1) * (!![D₀, 0; 0, D₁] : OpMatTower B (n + 1)) *
       towerWalshHadamard B (n + 1) =
       (!![towerWalshHadamard B n * (D₀ + D₁) * towerWalshHadamard B n,
           towerWalshHadamard B n * (D₀ - D₁) * towerWalshHadamard B n;
           towerWalshHadamard B n * (D₀ - D₁) * towerWalshHadamard B n,
           towerWalshHadamard B n * (D₀ + D₁) * towerWalshHadamard B n] : OpMatTower B (n + 1))) ∧
    (pluckerMinor24 (C24 * gr24TwistedCyclicShift) 0 1 = pluckerMinor24 C24 0 3 ∧
     (gr24TwistedCyclicShift : Matrix (Fin 4) (Fin 4) R) * gr24TwistedCyclicShift *
       (gr24TwistedCyclicShift * gr24TwistedCyclicShift) = -1) ∧
    (kreinJordanBasisInv * kreinCrashNilpotent dw * kreinJordanBasis =
       !![0, dw, 0, 0; 0, 0, 0, 0; 0, 0, 0, dw; 0, 0, 0, 0]) ∧
    ((u - v) • (laxBlockD u theta1 eta * laxBlockB eta) =
       (u - v + eta) • (laxBlockB eta * laxBlockD u theta1 eta) -
         eta • (laxBlockB eta * laxBlockD v theta1 eta) ∧
     (laxBlockA u theta2 eta * laxBlockD (u - eta) theta2 eta - laxBlockB eta * laxBlockC eta) *
       (laxBlockA u theta1 eta * laxBlockD (u - eta) theta1 eta - laxBlockB eta * laxBlockC eta) =
       (((u - theta2) ^ 2 - eta ^ 2) * ((u - theta1) ^ 2 - eta ^ 2)) • (1 : Matrix (Fin 2) (Fin 2) R)) ∧
    (comm (kreinHopfNilPart dw g) (comm (kreinHopfNilPart dw g) diracKreinVelocity) =
       -(4 * (dw ^ 2 - g ^ 2)) • diracKreinVelocity) ∧
    (comm (comm (invS P) (genPhi P A C)) (genPhi P A C) =
       (4 : ℤ) • (invS P * genV P A C) ∧
     fwTransform4 u1 v1 * fwTransform4 u2 v2 =
       fwTransform4 (u1 * u2 + v1 * v2) (u1 * v2 + v1 * u2)) := by
  have hS : invS P * invS P = 1 := by peirce_nf hP
  have hOdd : anticomm (invS P) (genPhi P A C) = 0 := by peirce_nf hP
  exact ⟨⟨(metaAporiaIter_quartic_goldenRatio_and_idempotent X 0).2.1,
          (towerJWChirality_involution_and_occupation_projectors B n i).1⟩,
         ⟨(matStrictLower3_neumann_inverse_and_wienerHopf X3 Y3).2.2.2.2,
          (matDiscreteHilbert3_riesz_and_cotlarTricomi_second_form X3).2.2.2⟩,
         ⟨(sp2_trace_law_and_hyperbolic_vs_elliptic_cayley X2 0).1,
          InfoGeometry.Clifford.Cl11StarAlgebraFiltration.stageImage_lt_succ n,
          InfoGeometry.Clifford.Cl11StarAlgebraFiltration.stageImage_finrank n,
          InfoGeometry.Clifford.Cl11JordanWignerCARBridge.jwAnnihilation_creation_anticommutator n i j⟩,
         (towerWalshHadamard_conjugation_diag_and_xor B n D₀ D₁ D₀ D₁).1,
         ⟨(gr24_twisted_cyclic_shift_plucker_rotation C24).1,
          (gr24_twisted_cyclic_shift_plucker_rotation C24).2.2.2.2.2.2⟩,
         (kreinCrash_cayley_hamilton_and_canonical_jordan_form wBar dw g).2.2.2.1,
         ⟨(yangian_dual_bethe_exchange_oneMagnon_and_twoSite_qdet u v theta1 theta2 eta).1,
          (yangian_dual_bethe_exchange_oneMagnon_and_twoSite_qdet u v theta1 theta2 eta).2.2.2.2⟩,
         (diracKrein_velocity_heisenberg_eom_and_energy_conservation dw g 0 0).2.2.1,
         ⟨(foldyWouthuysen_noncommutative_odd_commutator_series (invS P) (genPhi P A C) hS hOdd hP A C).2.2.2.2,
          (foldyWouthuysen_boost_composition_and_wigner_decomposition u1 v1 u2 v2).1⟩⟩

/-- **`MCP₁₀` Pass-5 Master Synthesis (Polar Gramian Intertwining, Chiral/Equilibrium Anticommutation,
Riesz Holomorphic Projectors, Multi-Hop Kramers–Kronig Hierarchy, Keldysh Contour Decoupling,
Walsh–Hadamard Light-Cone Metric Rotation, `so(n, n)` Quadratic Bivector Lie Closure,
Markov–Jones Trace Stability, Cyclic-Shift Butterfly Carry CNOT Factorization, Square Plabic
Disjoint-Path Loop Cancellation, `Gr(2,4)` Gale Duality, Full Generator Jordan Form & Double-Pole
Resolvent, Two-Site Yangian RTT Commutator Table, `so(2,1)` Lie Algebra & Casimir, and
Foldy–Wouthuysen Dual Precession Diagonalization):**
Coagulates the Pass-5 archetypes and codebase reuse across `StageMCP1`–`StageMCP9` into a single
master theorem. -/
theorem causalMatrix_pass5_master_synthesis
    {R : Type*} [CommRing R]
    {P : B} (hP : P * P = P) (A C S K G_R G_A : B)
    (n : ℕ) {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (X4 : Matrix (Fin 4) (Fin 4) R)
    (A_stage : InfoGeometry.Clifford.Cl11TensorTower.MatStage n)
    (a1 a2 a3 a4 a b c d z wBar dw g u v theta1 theta2 eta Om : R) :
    (causalForward S K * gramianIn S K = gramianOut S K * causalForward S K ∧
     anticomm (chiralDiracBlock S K) kreinJ = 0 ∧
     transferMoment P A C (n + 2) =
       transferMoment P A C (n + 1) + genV P A C * transferMoment P A C n) ∧
    (matRieszPosDoubled (matRieszNegDoubled X4) = matDiagPart X4 ∧
     matDiscreteHilbert (matStrictLower X4 * matStrictLower X4 +
                         matStrictUpper X4 * matStrictUpper X4) =
       matStrictLower X4 * matStrictLower X4 - matStrictUpper X4 * matStrictUpper X4 ∧
     hadamardBlock * metriplecticBlock (G_R + G_A) (G_R - G_A) * hadamardBlock =
       !![(4 : ℤ) • G_R, 0; 0, (4 : ℤ) • G_A]) ∧
    ((hadamardBlock : Matrix (Fin 2) (Fin 2) R)ᵀ * sigmaZ * hadamardBlock = (2 : R) • sigmaX ∧
     comm (towerJWPos B n i * towerJWPos B n j) (towerJWPos B n j * towerJWPos B n k) =
       (2 : ℤ) • (towerJWPos B n i * towerJWPos B n k) ∧
     InfoGeometry.Clifford.Cl11MarkovJonesEngine.cl11MarkovTraceNet.trace (n + 1)
       (InfoGeometry.Clifford.Cl11MarkovJonesEngine.cl11InductiveAlgebraNet.embed n A_stage) =
       InfoGeometry.Clifford.Cl11MarkovJonesEngine.cl11MarkovTraceNet.trace n A_stage) ∧
    ((butterflyLSBFlip4 : Matrix (Fin 4) (Fin 4) R) * butterflyCarryCNOT4 = cyclicShiftMat4 ∧
     (plabicSquareTransferNum a1 a2 a3 a4).det = -(a1 * a3) * (1 + a1 * a2 * a3 * a4)) ∧
    ((1 + genPhi P A C) * (1 - genPhi P A C) = zetaFactor P A C ∧
     plabicPositroidCanon24 a b c d * (plabicPositroidDual24 a b c d)ᵀ = 0 ∧
     pluckerMinor24 (plabicPositroidDual24 a b c d) 0 1 =
       pluckerMinor24 (plabicPositroidCanon24 a b c d) 2 3) ∧
    (kreinJordanBasisInv * kreinHopfGenerator wBar dw dw * kreinJordanBasis =
       kreinFullCanonicalJordan4 wBar dw ∧
     (z • (1 : Matrix (Fin 4) (Fin 4) R) - kreinHopfGenerator wBar dw dw) *
       ((z • (1 : Matrix (Fin 4) (Fin 4) R) + kreinHopfSemi wBar) *
        (z • (1 : Matrix (Fin 4) (Fin 4) R) + kreinHopfSemi wBar) *
        (z • (1 : Matrix (Fin 4) (Fin 4) R) - kreinHopfSemi wBar + kreinCrashNilpotent dw)) =
       ((z ^ 2 + wBar ^ 2) ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R)) ∧
    (comm (monodromyB2 u theta1 theta2 eta) (monodromyC2 v theta1 theta2 eta) =
       -((2 * v - theta1 - theta2) * eta) •
         (monodromyA2 u theta1 theta2 eta - monodromyD2 u theta1 theta2 eta) ∧
     (1 - genPhi P A C) * (1 - genJ P A C) * (1 + genJ P A C) * (1 + genPhi P A C) =
       (1 - qgtPlus P A C) * (1 - qgtMinus P A C) *
         (1 + qgtPlus P A C) * (1 + qgtMinus P A C)) ∧
    (comm (diracKreinA : Matrix (Fin 4) (Fin 4) R) diracKreinB = (2 : R) • diracKreinVelocity ∧
     (diracKreinB : Matrix (Fin 4) (Fin 4) R) * diracKreinB +
       diracKreinVelocity * diracKreinVelocity - diracKreinA * diracKreinA = (3 : R) • 1 ∧
     comm (kreinHopfNilPart dw g) (diracKreinPartDual dw g) =
       (2 * (dw ^ 2 - g ^ 2)) • diracKreinVelocity) ∧
    (fwTransform4 u v * diracKreinVelocity * fwTransform4 u (-v) =
       (u ^ 2 - v ^ 2) • diracKreinVelocity ∧
     (eriksenProjectorPosScaled Om dw g - eriksenProjectorNegScaled Om dw g) * (-kreinHopfSemi 1) =
       (2 : R) • kreinHopfNilPart dw g) :=
  ⟨⟨(causalForward_backward_gramian_intertwining S K).1,
    (chiralDiracBlock_equilibriumFlowRoot_anticomm_and_comm S K).1,
    transferMoment_recurrence hP A C n⟩,
   ⟨(matRieszDoubled_projector_orthogonality_and_idempotency X4).2.2.1,
    (multiHop_kramersKronig_hierarchy_lock_fin4 X4).1,
    (schwingerKeldysh_retarded_advanced_contour_decoupling G_R G_A).2.2⟩,
   ⟨(walshHadamard2_krein_lightCone_metric_rotation (0 : R) 0).1,
    (towerJW_quadratic_bivector_sonn_lie_closure B n hij hjk hik).1,
    InfoGeometry.Clifford.Cl11MarkovJonesEngine.cl11_normalizedTrace_one_step n A_stage⟩,
   ⟨(cyclicShiftMat4_butterfly_carry_factorization (R := R)).1,
    (plabicSquareTransferNum_loop_cancellation_and_factorization a1 a2 a3 a4).2.2⟩,
   ⟨(peirce_cayley_rotor_and_bergman_hua_bridge hP A C).1,
    (gr24_gale_dual_orthogonality_and_plucker_duality a b c d).1,
    (gr24_gale_dual_orthogonality_and_plucker_duality a b c d).2.2.1⟩,
   ⟨(kreinCrash_full_generator_jordan_normal_form wBar dw).2.1,
    kreinCrash_resolvent_double_pole z wBar dw⟩,
   ⟨(yangian_twoSite_full_rtt_commutator_table u v theta1 theta2 eta).2.2.2.2.2,
    supercharge_chiral_cycle_product hP A C⟩,
   ⟨(diracKrein_so21_lie_algebra_and_casimir_and_curvature_reuse hP A C 0 0 dw g).1.1,
    (diracKrein_so21_lie_algebra_and_casimir_and_curvature_reuse hP A C 0 0 dw g).1.2.2.2,
    (diracKrein_so21_lie_algebra_and_casimir_and_curvature_reuse hP A C 0 0 dw g).2.1.2.2.2⟩,
   ⟨(foldyWouthuysen_velocity_dual_and_eriksen_spectral_decomposition u v Om dw g).1,
    (foldyWouthuysen_velocity_dual_and_eriksen_spectral_decomposition u v Om dw g).2.2.2.2.2⟩⟩

end StageMCP10

end InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalPlabicKreinYangianPoset
