/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ModularSurprisalClockingLocksPoset
import InfoGeometry.Canonical.ModularSurprisalQuadraticLogVolume

/-!
# The Radon–Nikodym / Kähler / Para-Kähler Binary Cut, Unipotent Exponential Truncation, Chiral Coordinate Derivations, Non-Commutative Schwarz Defect, Legendre–Peirce Resolvent Duality, Operator Bregman Divergence Series, and BKM Metriplectic Closure (`ℜ₁ → ℜ₈`)

This module formalizes in native Mathlib (Lean 4) the 8-stage acyclic causal poset
(`ℜ₁ ≺ ℜ₂ ≺ ℜ₃ ≺ ℜ₄ ≺ ℜ₅ ≺ ℜ₆ ≺ ℜ₇ ≺ ℜ₈`) governing the **Radon–Nikodym / Kähler /
Para-Kähler Binary Cut** over an arbitrary non-commutative associative ring `[Ring B]` equipped
with `[Algebra ℝ B]`, together with exact scalar logarithmic/Bregman calculus on `ℝ` and concrete
finite-matrix Fréchet log-determinant and BKM resolvent integration bridges:

* **Phase I (The Fundamental Binary Cut `T ↔ S`)**:
  The commutative Schwarz-symmetric thesis (`[δ_+, δ_-] = 0`) vs. the non-commutative operator
  Radon–Nikodym cocycle and chiral Kähler / para-Kähler 2-jet shadow
  (`2 N_+ N_- = V + Σ`, `[δ_+, δ_-](Y) = [Σ, Y]`).
* **Phase II (The Fourfold Relational Anatomy)**:
  1. *Internal Consistency*: Two-sheet Radon–Nikodym surprisal normal form
     `K_RN = ū • 1 - (Δu / 2) • S_P` (`∈ 𝔨`) and the Kähler (`K_+(V)`) / para-Kähler (`K_-(V)`)
     polynomial partial-sum and scalar logarithmic potentials.
  2. *Outward Projection*: Primal natural `e`-coordinates `N_+ = P A (1 - P)` with exact degree-1
     unipotent exponential truncation `(1 - N_+) P (1 + N_+) = P + N_+` and primal derivation
     `δ_+ = [N_+, ·]`.
  3. *Inward Shadow-Intrusion*: Dual expectation `m`-coordinates `N_- = (1 - P) C P`, dual
     derivation `δ_- = [N_-, ·]`, and the Legendre-dual Peirce–Banks–Casher resolvent map
     `η_±(Φ) = W_± * Φ` where `(1 ± V) * W_± = 1`.
  4. *Autonomous Ground*: The Legendre-dual Bregman / Umegaki divergence partial-sum series
     `D_-(V) = ∑_{n=2}^N ((n - 1) / n) V^n` and exact scalar divergence
     `v * (1 - v)⁻¹ + log(1 - v)`.
* **Phase III (The Transcendent Function — Legendre Duality & Chiral 2-Jet)**:
  The chiral 2-jet decomposition `2 • (N_+ * N_-) = V + Σ`, the non-commutative Schwarz defect
  `[δ_+, δ_-](Y) = [Σ, Y]`, the universal symmetric Hessian split
  `δ_Φ²(Y) - δ_J²(Y) = 2 • {δ_+, δ_-}(Y)`, and the eigen-actions on `Φ` and `J`:
  `[δ_+, δ_-](Φ) = 2 • (V * J)` (symplectic curvature) and
  `{δ_+, δ_-}(Φ) = 2 • (V * Φ)` (Riemannian metric Hessian).
* **Phase IV (Socratic Aporia & The 5-Rung Tower of Meta-Cognition, Rung 0–Rung 4)**:
  Rung 0 proves that if Schwarz symmetry holds on the primal and dual chiral coordinates
  (`[δ_+, δ_-](N_+) = 0` and `[δ_+, δ_-](N_-) = 0`), then `2 • Q_+² = 0`, `2 • (V * Φ) = 0`,
  `2 • (V * J) = 0`, and `2 • V² = 0`, collapsing the metric strain.
* **Phase V (The 8-Stage Acyclic Causal Poset `ℜ₁ ≺ ℜ₂ ≺ ⋯ ≺ ℜ₈`, Lemmas 1–2, Theorems 1–3,
  and Master Structural Synthesis)**.

### Three-Bucket Audit Map

#### BUCKET 1 — Unconditional Kernel Truth
- `RadonNikodymKahlerStage`, `rank_injective`, `causalEdge_strict_rank_mono`, `causalEdge_irrefl`,
  `transGen_causalEdge_strict_rank_mono`, `causalEdge_acyclic`, `causalEdge_chain_and_diamond`.

#### BUCKET 2 — Conditional Kernel Theorems with Explicit Hypotheses
- Chiral coordinate derivations `deltaPlus`/`deltaMinus`, non-commutative Schwarz defect
  `[δ_+, δ_-](Y) = [Σ, Y]`, Kähler/para-Kähler partial sums, Legendre–Peirce resolvent identities,
  and scalar/operator Bregman divergence theorems under explicit idempotent and domain hypotheses.

#### BUCKET 3 — Open / Beyond-Scope Obligations
- Full infinite-dimensional Tomita–Takesaki relative modular operator $\Delta_{\psi|\phi}$ and
  Araki relative entropy on von Neumann algebras remain outside this finite-stage/algebraic scope.

## i. Overview
Formalizes the 8-stage Radon–Nikodym / Kähler / Para-Kähler binary cut and Bregman divergence poset (`ℜ₁ ≺ ⋯ ≺ ℜ₈`).

## ii. Key results
- `RadonNikodymKahlerStage.causalEdge_acyclic`
- `RadonNikodymKahlerStage.causalEdge_chain_and_diamond`

## iii. Table of contents
- Section 1: The 8-Stage Acyclic Causal Poset (`ℜ₁ ≺ ⋯ ≺ ℜ₈`)
- Section 2: Core Chiral Coordinate Derivations, Chiral 2-Jet, and Legendre–Bregman Closure

## iv. References
- S. Amari, *Information Geometry and Its Applications* (2016).
-/

namespace InfoGeometry.Canonical.RadonNikodymKahlerParaKahlerBregmanPoset

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.ModularSurprisalClockingLocksPoset
open InfoGeometry.Canonical.ModularSurprisalQuadraticLogVolume
open InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon
open scoped BigOperators Matrix

/-!
## 1. The 8-Stage Acyclic Causal Poset (`ℜ₁ ≺ ℜ₂ ≺ ⋯ ≺ ℜ₈`)
-/

/-- The 8-stage causal poset of the Radon–Nikodym / Kähler / Para-Kähler Binary Cut, Unipotent
Exponential Truncation, Chiral Coordinate Derivations, Non-Commutative Schwarz Defect,
Legendre–Peirce Resolvent Duality, Operator Bregman Divergence Series, and BKM Metriplectic
Closure (`ℜ₁ → ℜ₈`). -/
inductive RadonNikodymKahlerStage : Type
  | R1_unipotent_exponential_charts_and_chiral_derivations
  | R2_sheet_radon_nikodym_normal_form
  | R3_kahler_and_parakahler_log_potentials
  | R4_noncommutative_schwarz_defect_and_hessian_split
  | R5_chiral_two_jet_eigen_action_on_solder_bridge
  | R6_legendre_dual_expectation_peirce_resolvent
  | R7_operator_bregman_umegaki_divergence_positivity
  | R8_bkm_hessian_integration_and_metriplectic_cramer_rao
  deriving DecidableEq, Repr, Inhabited

namespace RadonNikodymKahlerStage

/-- Numerical topological rank of each stage `ℜ₁..ℜ₈`. -/
def rank : RadonNikodymKahlerStage → ℕ
  | R1_unipotent_exponential_charts_and_chiral_derivations => 1
  | R2_sheet_radon_nikodym_normal_form => 2
  | R3_kahler_and_parakahler_log_potentials => 3
  | R4_noncommutative_schwarz_defect_and_hessian_split => 4
  | R5_chiral_two_jet_eigen_action_on_solder_bridge => 5
  | R6_legendre_dual_expectation_peirce_resolvent => 6
  | R7_operator_bregman_umegaki_divergence_positivity => 7
  | R8_bkm_hessian_integration_and_metriplectic_cramer_rao => 8

/-- The stage rank map `rank` is injective on `RadonNikodymKahlerStage`. -/
theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> revert h <;> decide

instance instLinearOrderRadonNikodymKahlerStage : LinearOrder RadonNikodymKahlerStage :=
  LinearOrder.lift' rank rank_injective

/-- Directed causal dependency edges of the `ℜ₁ → ℜ₈` poset:
`ℜ₁ ≺ ℜ₂`, `ℜ₁ ≺ ℜ₃`, `ℜ₂ ≺ ℜ₄`, `ℜ₃ ≺ ℜ₄`, and `ℜ₄ ≺ ℜ₅ ≺ ℜ₆ ≺ ℜ₇ ≺ ℜ₈`. -/
def causalEdge : RadonNikodymKahlerStage → RadonNikodymKahlerStage → Prop
  | R1_unipotent_exponential_charts_and_chiral_derivations, R2_sheet_radon_nikodym_normal_form => True
  | R1_unipotent_exponential_charts_and_chiral_derivations, R3_kahler_and_parakahler_log_potentials => True
  | R2_sheet_radon_nikodym_normal_form, R4_noncommutative_schwarz_defect_and_hessian_split => True
  | R3_kahler_and_parakahler_log_potentials, R4_noncommutative_schwarz_defect_and_hessian_split => True
  | R4_noncommutative_schwarz_defect_and_hessian_split, R5_chiral_two_jet_eigen_action_on_solder_bridge => True
  | R5_chiral_two_jet_eigen_action_on_solder_bridge, R6_legendre_dual_expectation_peirce_resolvent => True
  | R6_legendre_dual_expectation_peirce_resolvent, R7_operator_bregman_umegaki_divergence_positivity => True
  | R7_operator_bregman_umegaki_divergence_positivity, R8_bkm_hessian_integration_and_metriplectic_cramer_rao => True
  | _, _ => False

/-- Every directed causal edge strictly increases the numerical rank. -/
theorem causalEdge_strict_rank_mono {a b : RadonNikodymKahlerStage}
    (h : causalEdge a b) : rank a < rank b := by
  cases a <;> cases b <;> simp [causalEdge, rank] at h ⊢

/-- No stage has a self-loop under `causalEdge`. -/
theorem causalEdge_irrefl (a : RadonNikodymKahlerStage) : ¬ causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (causalEdge_strict_rank_mono h)

/-- Any transitive path of causal edges strictly increases the numerical rank. -/
theorem transGen_causalEdge_strict_rank_mono {a b : RadonNikodymKahlerStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_strict_rank_mono hab
  | tail _ hbc ih => exact lt_trans ih (causalEdge_strict_rank_mono hbc)

/-- The 8-stage `RadonNikodymKahlerStage` poset is strictly acyclic. -/
theorem causalEdge_acyclic (a : RadonNikodymKahlerStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_strict_rank_mono h)

/-- Complete diamond-and-chain edge witness for `ℜ₁ ≺ ⋯ ≺ ℜ₈`. -/
theorem causalEdge_chain_and_diamond :
    causalEdge .R1_unipotent_exponential_charts_and_chiral_derivations
      .R2_sheet_radon_nikodym_normal_form ∧
    causalEdge .R1_unipotent_exponential_charts_and_chiral_derivations
      .R3_kahler_and_parakahler_log_potentials ∧
    causalEdge .R2_sheet_radon_nikodym_normal_form
      .R4_noncommutative_schwarz_defect_and_hessian_split ∧
    causalEdge .R3_kahler_and_parakahler_log_potentials
      .R4_noncommutative_schwarz_defect_and_hessian_split ∧
    causalEdge .R4_noncommutative_schwarz_defect_and_hessian_split
      .R5_chiral_two_jet_eigen_action_on_solder_bridge ∧
    causalEdge .R5_chiral_two_jet_eigen_action_on_solder_bridge
      .R6_legendre_dual_expectation_peirce_resolvent ∧
    causalEdge .R6_legendre_dual_expectation_peirce_resolvent
      .R7_operator_bregman_umegaki_divergence_positivity ∧
    causalEdge .R7_operator_bregman_umegaki_divergence_positivity
      .R8_bkm_hessian_integration_and_metriplectic_cramer_rao := by
  repeat' constructor

end RadonNikodymKahlerStage

/-!
## 2. Core Chiral Coordinate Derivations, Chiral 2-Jet, and Rung 0 (Socratic Aporia of Commutative Schwarz Symmetry)
-/

section ChiralDerivationsAndRung0

variable {B : Type*} [Ring B]

/-- Primal chiral coordinate derivation `δ_+(Y) := [N_+(P, A), Y]`. -/
def deltaPlus (P A Y : B) : B :=
  OperatorAlgebra.PeirceSpine.comm (conePlus P A) Y

/-- Dual chiral coordinate derivation `δ_-(Y) := [N_-(P, C), Y]`. -/
def deltaMinus (P C Y : B) : B :=
  OperatorAlgebra.PeirceSpine.comm (coneMinus P C) Y

/-- Symmetric bridge derivation `δ_Φ(Y) := [Φ(P, A, C), Y]`. -/
def deltaPhi (P A C Y : B) : B :=
  OperatorAlgebra.PeirceSpine.comm (genPhi P A C) Y

/-- Skew current derivation `δ_J(Y) := [J(P, A, C), Y]`. -/
def deltaJ (P A C Y : B) : B :=
  OperatorAlgebra.PeirceSpine.comm (genJ P A C) Y

/-- Antisymmetric mixed chiral derivation commutator
`[δ_+, δ_-](Y) := δ_+(δ_-(Y)) - δ_-(δ_+(Y))` (the non-commutative Schwarz defect / 2-form). -/
def chiralSchwarzComm (P A C Y : B) : B :=
  deltaPlus P A (deltaMinus P C Y) - deltaMinus P C (deltaPlus P A Y)

/-- Symmetric mixed chiral derivation anticommutator
`{δ_+, δ_-}(Y) := δ_+(δ_-(Y)) + δ_-(δ_+(Y))` (the Riemannian metric Hessian operator). -/
def chiralHessianAnticomm (P A C Y : B) : B :=
  deltaPlus P A (deltaMinus P C Y) + deltaMinus P C (deltaPlus P A Y)

/-- Positive ordered Peirce round-trip `Q₊ = N₊ N₋`. -/
def genQPlus (P A C : B) : B := conePlus P A * coneMinus P C

/-- Reverse ordered Peirce round-trip `Q₋ = N₋ N₊`. -/
def genQMinus (P A C : B) : B := coneMinus P C * conePlus P A

/-- Forward chiral 2-jet `2 • (N_+ * N_-)`. -/
def chiralTwoJetPlus (P A C : B) : B :=
  (2 : ℤ) • (conePlus P A * coneMinus P C)

/-- Backward chiral 2-jet `2 • (N_- * N_+)`. -/
def chiralTwoJetMinus (P A C : B) : B :=
  (2 : ℤ) • (coneMinus P C * conePlus P A)

/-- Upper-sheet Gramian corner `Q_+(P, A, C) := N_+(P, A) * N_-(P, C)`. -/
def chiralQPlus (P A C : B) : B :=
  conePlus P A * coneMinus P C

/-- **Full Chiral 2-Jet Decomposition**:
`2 • (N_+ * N_-) = V + Σ` and `2 • (N_- * N_+) = V - Σ`, where `V = {N_+, N_-}` is the
symmetric metric strain and `Σ = [N_+, N_-]` is the antisymmetric curvature. -/
theorem chiralTwoJet_decomposition (P A C : B) :
    chiralTwoJetPlus P A C = genV P A C + genSig P A C ∧
    chiralTwoJetMinus P A C = genV P A C - genSig P A C := by
  refine ⟨?_, ?_⟩
  · dsimp only [chiralTwoJetPlus, genV, genSig, anticomm, OperatorAlgebra.PeirceSpine.comm]
    rw [two_zsmul]
    noncomm_ring
  · dsimp only [chiralTwoJetMinus, genV, genSig, anticomm, OperatorAlgebra.PeirceSpine.comm]
    rw [two_zsmul]
    noncomm_ring

/-- **Rung 0 (The Socratic Aporia of Commutative Schwarz Symmetry)**:
1. In any associative ring `B`, the mixed chiral derivation commutator is the inner derivation
   of the curvature operator `Σ = [N_+, N_-]`:
   `chiralSchwarzComm P A C Y = [Σ, Y]`.
2. For an idempotent `P * P = P`, evaluating `[δ_+, δ_-]` on the primal coordinate `N_+` and
   dual coordinate `N_-` yields:
   `[δ_+, δ_-](N_+) = 2 • (V * N_+)` and `[δ_+, δ_-](N_-) = -(2 • (V * N_-))`.
3. Consequently, if commutative Schwarz symmetry holds on `N_+` and `N_-`
   (`chiralSchwarzComm P A C (conePlus P A) = 0` and
   `chiralSchwarzComm P A C (coneMinus P C) = 0`), then:
   - `2 • (Q_+ * Q_+) = 0` (`Q_+ = N_+ * N_-`),
   - `2 • (V * Φ) = 0` and `2 • (V * J) = 0`,
   - `2 • (V * V) = 0` (the doubled square of the symmetric Fisher/BKM metric `V` collapses to `0`). -/
theorem rung0_schwarz_symmetry_aporia
    {P : B} (hP : P * P = P) (A C Y : B)
    (hSchwarzPlus : chiralSchwarzComm P A C (conePlus P A) = 0)
    (hSchwarzMinus : chiralSchwarzComm P A C (coneMinus P C) = 0) :
    chiralSchwarzComm P A C Y = OperatorAlgebra.PeirceSpine.comm (genSig P A C) Y ∧
    chiralSchwarzComm P A C (conePlus P A) = (2 : ℤ) • (genV P A C * conePlus P A) ∧
    chiralSchwarzComm P A C (coneMinus P C) = -((2 : ℤ) • (genV P A C * coneMinus P C)) ∧
    (2 : ℤ) • (chiralQPlus P A C * chiralQPlus P A C) = 0 ∧
    (2 : ℤ) • (genV P A C * genPhi P A C) = 0 ∧
    (2 : ℤ) • (genV P A C * genJ P A C) = 0 ∧
    (2 : ℤ) • (genV P A C * genV P A C) = 0 := by
  have hJacobi : chiralSchwarzComm P A C Y =
      OperatorAlgebra.PeirceSpine.comm (genSig P A C) Y := by
    dsimp only [chiralSchwarzComm, deltaPlus, deltaMinus, genSig,
      OperatorAlgebra.PeirceSpine.comm]
    noncomm_ring
  have hEvalPlus : chiralSchwarzComm P A C (conePlus P A) =
      (2 : ℤ) • (genV P A C * conePlus P A) := by
    dsimp only [chiralSchwarzComm, deltaPlus, deltaMinus]
    peirce_nf hP
  have hEvalMinus : chiralSchwarzComm P A C (coneMinus P C) =
      -((2 : ℤ) • (genV P A C * coneMinus P C)) := by
    dsimp only [chiralSchwarzComm, deltaPlus, deltaMinus]
    peirce_nf hP
  have hVNp : (2 : ℤ) • (genV P A C * conePlus P A) = 0 := by
    rw [← hEvalPlus, hSchwarzPlus]
  have hVNm : (2 : ℤ) • (genV P A C * coneMinus P C) = 0 := by
    have hNeg : -((2 : ℤ) • (genV P A C * coneMinus P C)) = 0 := by
      rw [← hEvalMinus, hSchwarzMinus]
    exact neg_eq_zero.mp hNeg
  have hQPlusSqId :
      ((2 : ℤ) • (genV P A C * conePlus P A)) * coneMinus P C =
        (2 : ℤ) • (chiralQPlus P A C * chiralQPlus P A C) := by
    dsimp only [chiralQPlus]
    peirce_nf hP
  have hQPlusSq : (2 : ℤ) • (chiralQPlus P A C * chiralQPlus P A C) = 0 := by
    rw [← hQPlusSqId, hVNp, zero_mul]
  have hVPhi : (2 : ℤ) • (genV P A C * genPhi P A C) = 0 := by
    have hSplit :
        (2 : ℤ) • (genV P A C * genPhi P A C) =
          (2 : ℤ) • (genV P A C * conePlus P A) +
            (2 : ℤ) • (genV P A C * coneMinus P C) := by
      dsimp only [genPhi]
      rw [mul_add, zsmul_add]
    rw [hSplit, hVNp, hVNm, add_zero]
  have hVJ : (2 : ℤ) • (genV P A C * genJ P A C) = 0 := by
    have hSplit :
        (2 : ℤ) • (genV P A C * genJ P A C) =
          (2 : ℤ) • (genV P A C * conePlus P A) -
            (2 : ℤ) • (genV P A C * coneMinus P C) := by
      dsimp only [genJ]
      rw [mul_sub, zsmul_sub]
    rw [hSplit, hVNp, hVNm, sub_zero]
  have hVSqId :
      ((2 : ℤ) • (genV P A C * genPhi P A C)) * genPhi P A C =
        (2 : ℤ) • (genV P A C * genV P A C) := by
    peirce_nf hP
  have hVSq : (2 : ℤ) • (genV P A C * genV P A C) = 0 := by
    rw [← hVSqId, hVPhi, zero_mul]
  exact ⟨hJacobi, hEvalPlus, hEvalMinus, hQPlusSq, hVPhi, hVJ, hVSq⟩

/-!
## 3. Stage `ℜ₁`, Axiom I (Part 1), and Lemma 1: Unipotent Exponential Truncation & Chiral Grading
-/

/-- Truncated unipotent exponential `exp(N_+) := 1 + N_+(P, A)`. -/
def unipotentExpPlus (P A : B) : B :=
  1 + conePlus P A

/-- Inverse truncated unipotent exponential `exp(-N_+) := 1 - N_+(P, A)`. -/
def unipotentExpPlusInv (P A : B) : B :=
  1 - conePlus P A

/-- Dual truncated unipotent exponential `exp(N_-) := 1 + N_-(P, C)`. -/
def unipotentExpMinus (P C : B) : B :=
  1 + coneMinus P C

/-- Inverse dual truncated unipotent exponential `exp(-N_-) := 1 - N_-(P, C)`. -/
def unipotentExpMinusInv (P C : B) : B :=
  1 - coneMinus P C

/-- **Stage `ℜ₁` / Axiom I / Lemma 1 (Exact Truncation of the Unipotent Exponential Family)**:
For any idempotent `P * P = P` and elements `A, C : B`:
1. **Square-Zero Nilpotency**: `N_+² = 0` and `N_-² = 0`.
2. **Exact Two-Sided Unipotent Inversion**:
   `(1 + N_+) * (1 - N_+) = 1`, `(1 - N_+) * (1 + N_+) = 1`,
   `(1 + N_-) * (1 - N_-) = 1`, and `(1 - N_-) * (1 + N_-) = 1`.
3. **Exact Adjoint Unipotent Grassmannian Charts**:
   `(1 + N_+) * P * (1 - N_+) = P - N_+`,
   `(1 - N_+) * P * (1 + N_+) = P + N_+`,
   `(1 + N_-) * P * (1 - N_-) = P + N_-`, and
   `(1 - N_-) * P * (1 + N_-) = P - N_-`.
4. **Chiral Grading Eigen-Relations (`T^(1,0)` vs. `T^(0,1)`)**:
   `S_P * N_+ = N_+`, `N_+ * S_P = -N_+`, `S_P * N_- = -N_-`, and `N_- * S_P = N_-`. -/
theorem lemma1_unipotent_exponential_truncation
    {P : B} (hP : P * P = P) (A C : B) :
    conePlus P A * conePlus P A = 0 ∧
    coneMinus P C * coneMinus P C = 0 ∧
    unipotentExpPlus P A * unipotentExpPlusInv P A = 1 ∧
    unipotentExpPlusInv P A * unipotentExpPlus P A = 1 ∧
    unipotentExpMinus P C * unipotentExpMinusInv P C = 1 ∧
    unipotentExpMinusInv P C * unipotentExpMinus P C = 1 ∧
    unipotentExpPlus P A * P * unipotentExpPlusInv P A = P - conePlus P A ∧
    unipotentExpPlusInv P A * P * unipotentExpPlus P A = P + conePlus P A ∧
    unipotentExpMinus P C * P * unipotentExpMinusInv P C = P + coneMinus P C ∧
    unipotentExpMinusInv P C * P * unipotentExpMinus P C = P - coneMinus P C ∧
    invS P * conePlus P A = conePlus P A ∧
    conePlus P A * invS P = -conePlus P A ∧
    invS P * coneMinus P C = -coneMinus P C ∧
    coneMinus P C * invS P = coneMinus P C := by
  dsimp only [unipotentExpPlus, unipotentExpPlusInv, unipotentExpMinus, unipotentExpMinusInv]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-!
## 4. Stage `ℜ₂`, Axiom I (Part 2), and Lemma 2: Two-Sheet Operator Radon–Nikodym Normal Form
-/

section TwoSheetRadonNikodym

variable [Algebra ℝ B]

/-- Two-sheet operator Radon–Nikodym derivative
`ρ * ρ₀⁻¹ = (p / p₀) • P + (q / q₀) • (1 - P)`. -/
noncomputable def sheetRadonNikodymDeriv (p q p₀ q₀ : ℝ) (P : B) : B :=
  sheetRho (p / p₀) (q / q₀) P

/-- Two-sheet operator Radon–Nikodym surprisal
`K_RN(p, q, p₀, q₀, P) := (-log(p / p₀)) • P + (-log(q / q₀)) • (1 - P)`. -/
noncomputable def sheetRadonNikodymSurprisal (p q p₀ q₀ : ℝ) (P : B) : B :=
  sheetOperatorSurprisal (p / p₀) (q / q₀) P

/-- Mean Radon–Nikodym sheet surprisal `ū(p, q, p₀, q₀) := -(log(p / p₀) + log(q / q₀)) / 2`. -/
noncomputable def sheetRNMean (p q p₀ q₀ : ℝ) : ℝ :=
  sheetSurprisalMean (p / p₀) (q / q₀)

/-- Relative Radon–Nikodym log-likelihood gap
`Δu(p, q, p₀, q₀) := log(p / p₀) - log(q / q₀)`. -/
noncomputable def sheetRNGap (p q p₀ q₀ : ℝ) : ℝ :=
  sheetSurprisalGap (p / p₀) (q / q₀)

/-- **Stage `ℜ₂` / Axiom I / Lemma 2 (Two-Sheet Operator Radon–Nikodym Normal Form)**:
For strictly positive sheet weights `0 < p, q, p₀, q₀` and an idempotent `P * P = P`:
1. **Exact Reference Inversion**:
   `sheetRho p₀ q₀ P * sheetRho p₀⁻¹ q₀⁻¹ P = 1` and
   `sheetRho p₀⁻¹ q₀⁻¹ P * sheetRho p₀ q₀ P = 1`.
2. **Exact Radon–Nikodym Product**:
   `sheetRho p q P * sheetRho p₀⁻¹ q₀⁻¹ P = sheetRadonNikodymDeriv p q p₀ q₀ P`.
3. **Exact Chiral Normal Form of `K_RN`**:
   `sheetRadonNikodymSurprisal p q p₀ q₀ P = sheetRNMean p q p₀ q₀ • 1 - (sheetRNGap p q p₀ q₀ / 2) • S_P`,
   with `sheetRNMean p q p₀ q₀ = -(Real.log ((p * q) / (p₀ * q₀)) / 2)` and
   `sheetRNGap p q p₀ q₀ = Real.log ((p / p₀) / (q / q₀))`.
4. **Even Chiral Subalgebra Membership (`K_RN ∈ 𝔨`)**:
   `[S_P, K_RN] = 0`.
5. **Modular Precession of `K_RN` on the Solder Bridge**:
   `[K_RN, Φ] = (-Δu) • J` and `[K_RN, J] = (-Δu) • Φ`. -/
theorem lemma2_two_sheet_radon_nikodym_normal_form
    {P : B} (hP : P * P = P) (A C : B)
    (p q p₀ q₀ : ℝ) (hp : 0 < p) (hq : 0 < q) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) :
    sheetRho p₀ q₀ P * sheetRho p₀⁻¹ q₀⁻¹ P = 1 ∧
    sheetRho p₀⁻¹ q₀⁻¹ P * sheetRho p₀ q₀ P = 1 ∧
    sheetRho p q P * sheetRho p₀⁻¹ q₀⁻¹ P = sheetRadonNikodymDeriv p q p₀ q₀ P ∧
    sheetRadonNikodymSurprisal p q p₀ q₀ P =
      sheetRNMean p q p₀ q₀ • (1 : B) - (sheetRNGap p q p₀ q₀ / 2) • invS P ∧
    sheetRNMean p q p₀ q₀ = -(Real.log ((p * q) / (p₀ * q₀)) / 2) ∧
    sheetRNGap p q p₀ q₀ = Real.log ((p / p₀) / (q / q₀)) ∧
    OperatorAlgebra.PeirceSpine.comm (invS P) (sheetRadonNikodymSurprisal p q p₀ q₀ P) = 0 ∧
    OperatorAlgebra.PeirceSpine.comm (sheetRadonNikodymSurprisal p q p₀ q₀ P) (genPhi P A C) =
      (-sheetRNGap p q p₀ q₀) • genJ P A C ∧
    OperatorAlgebra.PeirceSpine.comm (sheetRadonNikodymSurprisal p q p₀ q₀ P) (genJ P A C) =
      (-sheetRNGap p q p₀ q₀) • genPhi P A C := by
  have hp₀_ne : p₀ ≠ 0 := ne_of_gt hp₀
  have hq₀_ne : q₀ ≠ 0 := ne_of_gt hq₀
  have hpp₀ : 0 < p / p₀ := div_pos hp hp₀
  have hqq₀ : 0 < q / q₀ := div_pos hq hq₀
  have hOne : sheetRho 1 1 P = 1 := by
    dsimp [sheetRho]
    rw [one_smul, one_smul]
    abel
  have hT1 := theorem1_normal_form_sheet_operator_surprisal (p / p₀) (q / q₀) hpp₀ hqq₀ P
  have hT3 := theorem3_modular_automorphism_precession_flow (P := P) hP (p / p₀) (q / q₀) A C
  refine ⟨?_, ?_, ?_, hT1.1, ?_, hT1.2.2.1, ?_, hT3.1, hT3.2.1⟩
  · rw [sheetRho_mul_sheetRho hP, mul_inv_cancel₀ hp₀_ne, mul_inv_cancel₀ hq₀_ne, hOne]
  · rw [sheetRho_mul_sheetRho hP, inv_mul_cancel₀ hp₀_ne, inv_mul_cancel₀ hq₀_ne, hOne]
  · dsimp [sheetRadonNikodymDeriv]
    rw [sheetRho_mul_sheetRho hP, ← div_eq_mul_inv, ← div_eq_mul_inv]
  · dsimp [sheetRNMean]
    rw [hT1.2.1]
    have hMulDiv : (p / p₀) * (q / q₀) = (p * q) / (p₀ * q₀) := by ring
    rw [hMulDiv]
  · dsimp [sheetRadonNikodymSurprisal, sheetOperatorSurprisal, OperatorAlgebra.PeirceSpine.comm]
    have hSP : invS P * P = P * invS P := by peirce_nf hP
    have hS1mP : invS P * (1 - P) = (1 - P) * invS P := by peirce_nf hP
    rw [mul_add, add_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
      hSP, hS1mP, sub_self]

/-!
## 5. Stage `ℜ₃`: Kähler & Para-Kähler Log-Generating Potentials
-/

/-- Degree-`N` polynomial partial sum of the elliptic Kähler potential
`K_+(V) = ∑_{k=1}^N ((-1)^(k-1) / k) • V^k`. -/
noncomputable def kahlerPotentialPartialSum (N : ℕ) (V : B) : B :=
  ∑ k ∈ Finset.Icc 1 N, (((-1 : ℝ) ^ (k - 1) / (k : ℝ)) • V ^ k)

/-- Degree-`N` polynomial partial sum of the hyperbolic para-Kähler potential
`K_-(V) = ∑_{k=1}^N (1 / k) • V^k`. -/
noncomputable def paraKahlerPotentialPartialSum (N : ℕ) (V : B) : B :=
  ∑ k ∈ Finset.Icc 1 N, ((1 / (k : ℝ)) • V ^ k)

/-- Exact scalar elliptic Kähler potential `K_+(v) = log(1 + v)` on `ℝ`. -/
noncomputable def scalarKahlerPotential (v : ℝ) : ℝ :=
  Real.log (1 + v)

/-- Exact scalar hyperbolic para-Kähler potential `K_-(v) = -log(1 - v)` on `ℝ`. -/
noncomputable def scalarParaKahlerPotential (v : ℝ) : ℝ :=
  -Real.log (1 - v)

omit [Algebra ℝ B] in
/-- **Helper Lemma**: Every power `V^k` of `V = genV P A C` commutes with `S_P = invS P`. -/
theorem comm_invS_genV_pow {P : B} (hP : P * P = P) (A C : B) :
    ∀ k : ℕ, OperatorAlgebra.PeirceSpine.comm (invS P) (genV P A C ^ k) = 0
  | 0 => by
      dsimp [OperatorAlgebra.PeirceSpine.comm]
      noncomm_ring
  | k + 1 => by
      have hBase : invS P * genV P A C = genV P A C * invS P := by peirce_nf hP
      have hIH : invS P * (genV P A C ^ k) = (genV P A C ^ k) * invS P :=
        sub_eq_zero.mp (comm_invS_genV_pow hP A C k)
      apply sub_eq_zero.mpr
      rw [pow_succ]
      calc
        invS P * (genV P A C ^ k * genV P A C)
            = (invS P * genV P A C ^ k) * genV P A C := by noncomm_ring
        _ = (genV P A C ^ k * invS P) * genV P A C := by rw [hIH]
        _ = genV P A C ^ k * (invS P * genV P A C) := by noncomm_ring
        _ = genV P A C ^ k * (genV P A C * invS P) := by rw [hBase]
        _ = (genV P A C ^ k * genV P A C) * invS P := by noncomm_ring

/-- **Stage `ℜ₃` (Kähler & Para-Kähler Log-Generating Potentials)**:
1. **Shared First-Jet Metric Seed (`N = 1`)**:
   `kahlerPotentialPartialSum 1 V = V` and `paraKahlerPotentialPartialSum 1 V = V`.
2. **Opposite Second-Order Curvature Sign (`N = 2`)**:
   `kahlerPotentialPartialSum 2 V = V - (1 / 2 : ℝ) • V ^ 2`,
   `paraKahlerPotentialPartialSum 2 V = V + (1 / 2 : ℝ) • V ^ 2`, and
   `paraKahlerPotentialPartialSum 2 V - kahlerPotentialPartialSum 2 V = V ^ 2`.
3. **Even Chiral Subalgebra Membership (`K_±(V) ∈ 𝔨`)**:
   For `P * P = P`, `[S_P, kahlerPotentialPartialSum 2 (genV P A C)] = 0` and
   `[S_P, paraKahlerPotentialPartialSum 2 (genV P A C)] = 0`.
4. The scalar logarithmic derivative results are proved separately, outside
   this generic operator-algebra section. -/
theorem stage3_kahler_and_parakahler_log_potentials
    {P : B} (hP : P * P = P) (A C V : B) :
    kahlerPotentialPartialSum 1 V = V ∧
    paraKahlerPotentialPartialSum 1 V = V ∧
    kahlerPotentialPartialSum 2 V = V - (1 / 2 : ℝ) • (V ^ 2) ∧
    paraKahlerPotentialPartialSum 2 V = V + (1 / 2 : ℝ) • (V ^ 2) ∧
    paraKahlerPotentialPartialSum 2 V - kahlerPotentialPartialSum 2 V = V ^ 2 ∧
    OperatorAlgebra.PeirceSpine.comm (invS P) (kahlerPotentialPartialSum 2 (genV P A C)) = 0 ∧
    OperatorAlgebra.PeirceSpine.comm (invS P) (paraKahlerPotentialPartialSum 2 (genV P A C)) = 0 := by
  have hIcc1 : (Finset.Icc 1 1 : Finset ℕ) = {1} := rfl
  have hIcc2 : (Finset.Icc 1 2 : Finset ℕ) = insert 1 {2} := rfl
  have hK1 : kahlerPotentialPartialSum 1 V = V := by
    dsimp [kahlerPotentialPartialSum]
    rw [hIcc1, Finset.sum_singleton]
    simp
  have hPK1 : paraKahlerPotentialPartialSum 1 V = V := by
    dsimp [paraKahlerPotentialPartialSum]
    rw [hIcc1, Finset.sum_singleton]
    simp
  have hK2All : ∀ X : B, kahlerPotentialPartialSum 2 X = X - (1 / 2 : ℝ) • (X ^ 2) := by
    intro X
    dsimp [kahlerPotentialPartialSum]
    rw [hIcc2, Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num
    module
  have hPK2All : ∀ X : B, paraKahlerPotentialPartialSum 2 X = X + (1 / 2 : ℝ) • (X ^ 2) := by
    intro X
    dsimp [paraKahlerPotentialPartialSum]
    rw [hIcc2, Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num
  have hK2 : kahlerPotentialPartialSum 2 V = V - (1 / 2 : ℝ) • (V ^ 2) := hK2All V
  have hPK2 : paraKahlerPotentialPartialSum 2 V = V + (1 / 2 : ℝ) • (V ^ 2) := hPK2All V
  have hDiff : paraKahlerPotentialPartialSum 2 V - kahlerPotentialPartialSum 2 V = V ^ 2 := by
    rw [hPK2, hK2]
    module
  have hCommV1 : invS P * genV P A C = genV P A C * invS P := by peirce_nf hP
  have hCommV2 : invS P * (genV P A C ^ 2) = (genV P A C ^ 2) * invS P :=
    sub_eq_zero.mp (comm_invS_genV_pow hP A C 2)
  refine ⟨hK1, hPK1, hK2, hPK2, hDiff, ?_, ?_⟩
  · rw [hK2All (genV P A C)]
    dsimp [OperatorAlgebra.PeirceSpine.comm]
    rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, hCommV1, hCommV2, sub_self]
  · rw [hPK2All (genV P A C)]
    dsimp [OperatorAlgebra.PeirceSpine.comm]
    rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hCommV1, hCommV2, sub_self]
end TwoSheetRadonNikodym

/-- Derivative of the scalar elliptic logarithmic potential. -/
theorem scalarKahlerPotential_hasDerivAt (v : ℝ) (h : 1 + v ≠ 0) :
    HasDerivAt scalarKahlerPotential (1 + v)⁻¹ v := by
  change HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 + v)⁻¹ v
  have hInner : HasDerivAt (fun x : ℝ => 1 + x) 1 v :=
    (hasDerivAt_id v).const_add 1
  have hLog := (Real.hasDerivAt_log h).comp v hInner
  convert hLog using 1
  · ext x
    rfl
  · ring

/-- Derivative of the scalar hyperbolic para-Kähler logarithmic potential. -/
theorem scalarParaKahlerPotential_hasDerivAt (v : ℝ) (h : 1 - v ≠ 0) :
    HasDerivAt scalarParaKahlerPotential (1 - v)⁻¹ v := by
  change HasDerivAt (fun x : ℝ => -Real.log (1 - x)) (1 - v)⁻¹ v
  have hInner : HasDerivAt (fun x : ℝ => 1 - x) (-1) v :=
    (hasDerivAt_id v).const_sub 1
  have hLog := (Real.hasDerivAt_log h).comp v hInner
  convert hLog.neg using 1
  · ext x
    rfl
  · ring

/-!
## 6. Stage `ℜ₄`, Deduction 1 (Part 1), and Theorem 1: Non-Commutative Schwarz Defect & Symmetric Hessian Split
-/

/-- **Stage `ℜ₄` / Deduction 1 / Theorem 1 (The Non-Commutative Schwarz Defect & Symmetric Hessian Split)**:
1. **Universal Non-Commutative Schwarz Defect (Jacobi Identity)**:
   For every `Y : B`, `[δ_+, δ_-](Y) = [Σ, Y]`.
2. **Universal Symmetric Hessian Split**:
   For every `Y : B`, `δ_Φ(δ_Φ(Y)) - δ_J(δ_J(Y)) = 2 • {δ_+, δ_-}(Y)`.
3. **Vanishing of Nilpotent Double Derivations on the Even Block `𝔨`**:
   For any idempotent `P * P = P` and any block-diagonal operator
   `D = P * D₁ * P + (1 - P) * D₂ * (1 - P)`,
   `δ_+(δ_+(D)) = 0`, `δ_-(δ_-(D)) = 0`,
   `δ_Φ(δ_Φ(D)) + δ_J(δ_J(D)) = 0`, and `δ_Φ(δ_Φ(D)) = {δ_+, δ_-}(D)`. -/
theorem theorem1_noncommutative_schwarz_defect_and_hessian_split
    {P : B} (hP : P * P = P) (A C Y D₁ D₂ : B) :
    chiralSchwarzComm P A C Y = OperatorAlgebra.PeirceSpine.comm (genSig P A C) Y ∧
    deltaPhi P A C (deltaPhi P A C Y) - deltaJ P A C (deltaJ P A C Y) =
      (2 : ℤ) • chiralHessianAnticomm P A C Y ∧
    deltaPlus P A (deltaPlus P A (P * D₁ * P + (1 - P) * D₂ * (1 - P))) = 0 ∧
    deltaMinus P C (deltaMinus P C (P * D₁ * P + (1 - P) * D₂ * (1 - P))) = 0 ∧
    deltaPhi P A C (deltaPhi P A C (P * D₁ * P + (1 - P) * D₂ * (1 - P))) +
      deltaJ P A C (deltaJ P A C (P * D₁ * P + (1 - P) * D₂ * (1 - P))) = 0 ∧
    deltaPhi P A C (deltaPhi P A C (P * D₁ * P + (1 - P) * D₂ * (1 - P))) =
      chiralHessianAnticomm P A C (P * D₁ * P + (1 - P) * D₂ * (1 - P)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [chiralSchwarzComm, deltaPlus, deltaMinus, genSig,
      OperatorAlgebra.PeirceSpine.comm]
    noncomm_ring
  · dsimp only [deltaPhi, deltaJ, chiralHessianAnticomm, deltaPlus, deltaMinus,
      genPhi, genJ, OperatorAlgebra.PeirceSpine.comm]
    rw [two_zsmul]
    noncomm_ring
  · dsimp only [deltaPlus]
    peirce_nf hP
  · dsimp only [deltaMinus]
    peirce_nf hP
  · dsimp only [deltaPhi, deltaJ]
    peirce_nf hP
  · dsimp only [deltaPhi, chiralHessianAnticomm, deltaPlus, deltaMinus]
    peirce_nf hP

/-!
## 7. Stage `ℜ₅`, Deduction 1 (Part 2), and Theorem 2: Exact Eigen-Action of the Chiral 2-Jet on `Φ` and `J`
-/

/-- **Stage `ℜ₅` / Deduction 1 / Theorem 2 (Exact Eigen-Action of the Chiral 2-Jet on `Φ` and `J`)**:
For any idempotent `P * P = P` and `A, C : B`:
1. **Individual Mixed-Derivation Projections**:
   `δ_+(δ_-(Φ)) = 2 • (V * N_+)`, `δ_-(δ_+(Φ)) = 2 • (V * N_-)`,
   `δ_+(δ_-(J)) = 2 • (V * N_+)`, and `δ_-(δ_+(J)) = -(2 • (V * N_-))`.
2. **Symplectic Curvature Action (`[δ_+, δ_-]`)**:
   `[δ_+, δ_-](Φ) = 2 • (V * J)` and `[δ_+, δ_-](J) = 2 • (V * Φ)`.
3. **Riemannian Metric Hessian Action (`{δ_+, δ_-}`)**:
   `{δ_+, δ_-}(Φ) = 2 • (V * Φ)` and `{δ_+, δ_-}(J) = 2 • (V * J)`. -/
theorem theorem2_chiral_two_jet_eigen_action
    {P : B} (hP : P * P = P) (A C : B) :
    deltaPlus P A (deltaMinus P C (genPhi P A C)) =
      (2 : ℤ) • (genV P A C * conePlus P A) ∧
    deltaMinus P C (deltaPlus P A (genPhi P A C)) =
      (2 : ℤ) • (genV P A C * coneMinus P C) ∧
    deltaPlus P A (deltaMinus P C (genJ P A C)) =
      (2 : ℤ) • (genV P A C * conePlus P A) ∧
    deltaMinus P C (deltaPlus P A (genJ P A C)) =
      -((2 : ℤ) • (genV P A C * coneMinus P C)) ∧
    chiralSchwarzComm P A C (genPhi P A C) =
      (2 : ℤ) • (genV P A C * genJ P A C) ∧
    chiralSchwarzComm P A C (genJ P A C) =
      (2 : ℤ) • (genV P A C * genPhi P A C) ∧
    chiralHessianAnticomm P A C (genPhi P A C) =
      (2 : ℤ) • (genV P A C * genPhi P A C) ∧
    chiralHessianAnticomm P A C (genJ P A C) =
      (2 : ℤ) • (genV P A C * genJ P A C) := by
  dsimp only [chiralSchwarzComm, chiralHessianAnticomm, deltaPlus, deltaMinus]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

end ChiralDerivationsAndRung0

/-!
## 8. Stage `ℜ₆`, Stage `ℜ₇`, Deduction 2, and Theorem 3: Legendre–Peirce Resolvent Duality & Operator Bregman Divergence Positivity
-/

section LegendreAndBregman

variable {B : Type*} [Ring B] [Algebra ℝ B]

/-- Elliptic Kähler Legendre-dual expectation coordinate `η_+(W_+, P, A, C) := W_+ * Φ`,
where `W_+` is a two-sided inverse of `1 + V`. -/
def legendreDualExpectationPlus (W_plus P A C : B) : B :=
  W_plus * genPhi P A C

/-- Hyperbolic para-Kähler Legendre-dual expectation coordinate `η_-(W_-, P, A, C) := W_- * Φ`,
where `W_-` is a two-sided inverse of `1 - V`. -/
def legendreDualExpectationMinus (W_minus P A C : B) : B :=
  W_minus * genPhi P A C

/-- Degree-`N` geometric series partial sum `∑_{n=1}^N V^n` for `V * (1 - V)⁻¹`. -/
def geometricSeriesPartialSum (N : ℕ) (V : B) : B :=
  ∑ n ∈ Finset.Icc 1 N, V ^ n

/-- Degree-`N` polynomial partial sum of the operator Bregman / Umegaki divergence
`D_-(V) = ∑_{n=1}^N ((n - 1) / n) • V^n` (whose `n = 1` term vanishes identically). -/
noncomputable def bregmanDivergenceMinusPartialSum (N : ℕ) (V : B) : B :=
  ∑ n ∈ Finset.Icc 1 N, ((((n : ℝ) - 1) / (n : ℝ)) • V ^ n)

/-- Exact scalar para-Kähler Bregman divergence `D_-(v) = v * (1 - v)⁻¹ + log(1 - v)` on `ℝ`. -/
noncomputable def scalarBregmanMinus (v : ℝ) : ℝ :=
  v * (1 - v)⁻¹ + Real.log (1 - v)

/-- The scalar para-Kähler Bregman divergence is nonnegative on its natural
positive resolvent domain. This scalar conclusion does not assert positivity
of an operator-valued expression before a positive trace or order structure is
specified. -/
theorem scalarBregmanMinus_nonneg_of_lt_one {v : ℝ}
    (hv1 : v < 1) : 0 ≤ scalarBregmanMinus v := by
  have hd : 0 < 1 - v := sub_pos.mpr hv1
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hd)
  rw [Real.log_inv] at hlog
  have hfrac : (1 - v)⁻¹ - 1 = v * (1 - v)⁻¹ := by
    field_simp
    ring
  unfold scalarBregmanMinus
  rw [hfrac] at hlog
  linarith

/-- Conditional nonnegativity of the trace evaluation of the finite Bregman
series, from the nonnegativity of each power moment in its finite support. -/
theorem bregmanTracePartialSum_nonneg {B : Type*} [Ring B] [Algebra ℝ B]
    (N : ℕ) (V : B) (τ : B → ℝ)
    (hτ : ∀ n ∈ Finset.Icc 1 N, 0 ≤ τ (V ^ n)) :
    0 ≤ ∑ n ∈ Finset.Icc 1 N,
      ((((n : ℝ) - 1) / (n : ℝ)) * τ (V ^ n)) := by
  refine Finset.sum_nonneg (fun n hn => ?_)
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnReal : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn1
  have hCoeff : 0 ≤ ((n : ℝ) - 1) / (n : ℝ) :=
    div_nonneg (by linarith) (by linarith)
  exact mul_nonneg hCoeff (hτ n hn)

/-- **Stage `ℜ₆` & `ℜ₇` / Deduction 2 / Theorem 3 (Legendre Transformation as Peirce–Banks–Casher
Resolvent & Operator Bregman Divergence Positivity)**:
1. **Elliptic & Hyperbolic Legendre Resolvent Recovery**:
   If `(1 + V) * W_+ = 1` and `W_+ * (1 + V) = 1`, then `(1 + V) * η_+ = Φ` and
   `W_+ * Φ = Φ * W_+`.
   If `(1 - V) * W_- = 1` and `W_- * (1 - V) = 1`, then `(1 - V) * η_- = Φ` and
   `W_- * Φ = Φ * W_-`.
2. **Exact Cancellation of the `n = 1` Linear Term in the Operator Bregman Divergence Series**:
   For every degree `N : ℕ` and every `V : B`,
   `geometricSeriesPartialSum N V - paraKahlerPotentialPartialSum N V = bregmanDivergenceMinusPartialSum N V`.
3. **Explicit Quartic Expansion (`N = 4`) with Zero Linear Term**:
   `bregmanDivergenceMinusPartialSum 4 V = (1 / 2 : ℝ) • V ^ 2 + (2 / 3 : ℝ) • V ^ 3 + (3 / 4 : ℝ) • V ^ 4`.
4. **Exact Scalar Legendre–Bregman Identity**:
   `scalarBregmanMinus v = v * (1 - v)⁻¹ - scalarParaKahlerPotential v`.
   Conditional trace nonnegativity is the separate theorem `bregmanTracePartialSum_nonneg`; the
   scalar derivative is separately proved outside this generic operator section. -/
theorem theorem3_legendre_resolvent_and_bregman_divergence
    {P : B} (hP : P * P = P) (A C W_plus W_minus V : B) (N : ℕ)
    (hW_plus_r : (1 + genV P A C) * W_plus = 1)
    (hW_plus_l : W_plus * (1 + genV P A C) = 1)
    (hW_minus_r : (1 - genV P A C) * W_minus = 1)
    (hW_minus_l : W_minus * (1 - genV P A C) = 1)
    (v : ℝ) :
    (1 + genV P A C) * legendreDualExpectationPlus W_plus P A C = genPhi P A C ∧
    W_plus * genPhi P A C = genPhi P A C * W_plus ∧
    (1 - genV P A C) * legendreDualExpectationMinus W_minus P A C = genPhi P A C ∧
    W_minus * genPhi P A C = genPhi P A C * W_minus ∧
    geometricSeriesPartialSum N V - paraKahlerPotentialPartialSum N V =
      bregmanDivergenceMinusPartialSum N V ∧
    bregmanDivergenceMinusPartialSum 4 V =
      (1 / 2 : ℝ) • V ^ 2 + (2 / 3 : ℝ) • V ^ 3 + (3 / 4 : ℝ) • V ^ 4 ∧
    scalarBregmanMinus v = v * (1 - v)⁻¹ - scalarParaKahlerPotential v := by
  have hVPhi : genV P A C * genPhi P A C = genPhi P A C * genV P A C := by peirce_nf hP
  have h1pVPhi : (1 + genV P A C) * genPhi P A C = genPhi P A C * (1 + genV P A C) := by
    rw [add_mul, one_mul, mul_add, mul_one, hVPhi]
  have h1mVPhi : (1 - genV P A C) * genPhi P A C = genPhi P A C * (1 - genV P A C) := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hVPhi]
  have hWPlusComm : W_plus * genPhi P A C = genPhi P A C * W_plus := by
    calc
      W_plus * genPhi P A C = W_plus * genPhi P A C * ((1 + genV P A C) * W_plus) := by
        rw [hW_plus_r, mul_one]
      _ = W_plus * (genPhi P A C * (1 + genV P A C)) * W_plus := by noncomm_ring
      _ = W_plus * ((1 + genV P A C) * genPhi P A C) * W_plus := by rw [← h1pVPhi]
      _ = (W_plus * (1 + genV P A C)) * genPhi P A C * W_plus := by noncomm_ring
      _ = genPhi P A C * W_plus := by rw [hW_plus_l, one_mul]
  have hWMinusComm : W_minus * genPhi P A C = genPhi P A C * W_minus := by
    calc
      W_minus * genPhi P A C = W_minus * genPhi P A C * ((1 - genV P A C) * W_minus) := by
        rw [hW_minus_r, mul_one]
      _ = W_minus * (genPhi P A C * (1 - genV P A C)) * W_minus := by noncomm_ring
      _ = W_minus * ((1 - genV P A C) * genPhi P A C) * W_minus := by rw [← h1mVPhi]
      _ = (W_minus * (1 - genV P A C)) * genPhi P A C * W_minus := by noncomm_ring
      _ = genPhi P A C * W_minus := by rw [hW_minus_l, one_mul]
  refine ⟨?_, hWPlusComm, ?_, hWMinusComm, ?_, ?_, ?_⟩
  · dsimp [legendreDualExpectationPlus]
    rw [← mul_assoc, hW_plus_r, one_mul]
  · dsimp [legendreDualExpectationMinus]
    rw [← mul_assoc, hW_minus_r, one_mul]
  · dsimp [geometricSeriesPartialSum, paraKahlerPotentialPartialSum,
      bregmanDivergenceMinusPartialSum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hCoeff : (1 : ℝ) - 1 / (n : ℝ) = ((n : ℝ) - 1) / (n : ℝ) := by
      field_simp [hn_ne]
    calc
      V ^ n - (1 / (n : ℝ)) • V ^ n
          = (1 : ℝ) • V ^ n - (1 / (n : ℝ)) • V ^ n := by rw [one_smul]
      _ = ((1 : ℝ) - 1 / (n : ℝ)) • V ^ n := by rw [sub_smul]
      _ = (((n : ℝ) - 1) / (n : ℝ)) • V ^ n := by rw [hCoeff]
  · have hIcc4 : (Finset.Icc 1 4 : Finset ℕ) = insert 1 (insert 2 (insert 3 {4})) := rfl
    dsimp [bregmanDivergenceMinusPartialSum]
    rw [hIcc4, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num
    abel
  · dsimp [scalarBregmanMinus, scalarParaKahlerPotential]
    ring

/-- Derivative of the scalar para-Kähler Bregman potential on its natural
domain `1 - v ≠ 0`. -/
theorem scalarBregmanMinus_hasDerivAt (v : ℝ) (hv : 1 - v ≠ 0) :
    HasDerivAt scalarBregmanMinus (v / (1 - v) ^ 2) v := by
  change HasDerivAt (fun x : ℝ => x * (1 - x)⁻¹ + Real.log (1 - x))
    (v / (1 - v) ^ 2) v
  have hSub : HasDerivAt (fun x : ℝ => 1 - x) (-1) v :=
    (hasDerivAt_id v).const_sub 1
  have hInv : HasDerivAt (fun x : ℝ => (1 - x)⁻¹) ((1 - v) ^ 2)⁻¹ v := by
    have h1 := (hasDerivAt_inv hv).comp v hSub
    convert h1 using 1
    · ext x
      rfl
    · ring
  have hProd : HasDerivAt (fun x : ℝ => x * (1 - x)⁻¹)
      (1 * (1 - v)⁻¹ + v * ((1 - v) ^ 2)⁻¹) v :=
    (hasDerivAt_id v).mul hInv
  have hLog : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-(1 - v)⁻¹) v := by
    have h1 := (Real.hasDerivAt_log hv).comp v hSub
    convert h1 using 1
    · ext x
      rfl
    · ring
  have hSum := hProd.add hLog
  convert hSum using 1
  field_simp [hv]
  ring

/-!
## 9. Stage `ℜ₈` & Master Structural Synthesis (`ℜ₁ ≺ ℜ₂ ≺ ⋯ ≺ ℜ₈`)
-/

/-- **Master Structural Synthesis (`ℜ₁ ≺ ℜ₂ ≺ ⋯ ≺ ℜ₈`)**:
Unifies the acyclic 8-stage causal poset (`RadonNikodymKahlerStage.causalEdge_acyclic`),
Stage `ℜ₁` unipotent exponential chart truncation `(1 - N_+) * P * (1 + N_+) = P + N_+`,
Stage `ℜ₂` two-sheet Radon–Nikodym normal form `K_RN = ū • 1 - (Δu / 2) • S_P`,
Stage `ℜ₃` Kähler and para-Kähler potential curvings `K_-(V) - K_+(V) = V²`,
Stage `ℜ₄` non-commutative Schwarz defect `[δ_+, δ_-](Y) = [Σ, Y]` and symmetric Hessian split
`δ_Φ²(Y) - δ_J²(Y) = 2 • {δ_+, δ_-}(Y)`,
Stage `ℜ₅` eigen-actions `[δ_+, δ_-](Φ) = 2 • (V * J)` and `{δ_+, δ_-}(Φ) = 2 • (V * Φ)`,
Stage `ℜ₆` Legendre–Peirce resolvent recovery `(1 ± V) * η_± = Φ`,
Stage `ℜ₇` operator Bregman divergence-series cancellation, and
Stage `ℜ₈` BKM resolvent factorization and Metriplectic Cramér–Rao bound. -/
theorem master_radon_nikodym_kahler_parakahler_bregman_synthesis
    {P : B} (hP : P * P = P) (A C W_plus W_minus V X Y : B)
    (tr : B → ℝ) (g Ω : B → B → ℝ) (N : ℕ)
    (p q p₀ q₀ s : ℝ) (hp : 0 < p) (hq : 0 < q) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀)
    (hpq : p ≠ q) (hps : p + s ≠ 0) (hqs : q + s ≠ 0) (htrV : 0 < tr (genV P A C))
    (hW_plus_r : (1 + genV P A C) * W_plus = 1)
    (hW_plus_l : W_plus * (1 + genV P A C) = 1)
    (hW_minus_r : (1 - genV P A C) * W_minus = 1)
    (hW_minus_l : W_minus * (1 - genV P A C) = 1)
    (hRS : (1 / 4 : ℝ) * (Ω X Y) ^ 2 ≤ g X X * g Y Y - (g X Y) ^ 2) :
    (∀ st : RadonNikodymKahlerStage,
      ¬ Relation.TransGen RadonNikodymKahlerStage.causalEdge st st) ∧
    unipotentExpPlusInv P A * P * unipotentExpPlus P A = P + conePlus P A ∧
    sheetRadonNikodymSurprisal p q p₀ q₀ P =
      sheetRNMean p q p₀ q₀ • (1 : B) - (sheetRNGap p q p₀ q₀ / 2) • invS P ∧
    paraKahlerPotentialPartialSum 2 V - kahlerPotentialPartialSum 2 V = V ^ 2 ∧
    chiralSchwarzComm P A C Y = OperatorAlgebra.PeirceSpine.comm (genSig P A C) Y ∧
    deltaPhi P A C (deltaPhi P A C Y) - deltaJ P A C (deltaJ P A C Y) =
      (2 : ℤ) • chiralHessianAnticomm P A C Y ∧
    chiralSchwarzComm P A C (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C) ∧
    chiralHessianAnticomm P A C (genPhi P A C) = (2 : ℤ) • (genV P A C * genPhi P A C) ∧
    (1 + genV P A C) * legendreDualExpectationPlus W_plus P A C = genPhi P A C ∧
    (1 - genV P A C) * legendreDualExpectationMinus W_minus P A C = genPhi P A C ∧
    geometricSeriesPartialSum N V - paraKahlerPotentialPartialSum N V =
      bregmanDivergenceMinusPartialSum N V ∧
    genPhi P A C * sheetResolvent p q s P * genPhi P A C * sheetResolvent p q s P =
      ((p + s) * (q + s))⁻¹ • genV P A C ∧
    0 < bkmMetricEval tr p q P A C ∧
    (1 / 4 : ℝ) * (Ω X Y) ^ 2 ≤ g X X * g Y Y := by
  have hL1 := lemma1_unipotent_exponential_truncation (P := P) hP A C
  have hL2 := lemma2_two_sheet_radon_nikodym_normal_form
    (P := P) hP A C p q p₀ q₀ hp hq hp₀ hq₀
  have hS3 := stage3_kahler_and_parakahler_log_potentials
    (P := P) hP A C V
  have hT1 := theorem1_noncommutative_schwarz_defect_and_hessian_split
    (P := P) hP A C Y 0 0
  have hT2 := theorem2_chiral_two_jet_eigen_action (P := P) hP A C
  have hT3 := theorem3_legendre_resolvent_and_bregman_divergence
    (P := P) hP A C W_plus W_minus V N hW_plus_r hW_plus_l hW_minus_r hW_minus_l
    0
  have hBKM := theorem5_bkm_resolvent_factorization_and_divided_difference
    (P := P) hP A C tr p q s hp hq hpq hps hqs htrV
  have hCR := stage8_metriplectic_cramer_rao_bound g Ω X Y hRS
  exact ⟨RadonNikodymKahlerStage.causalEdge_acyclic,
    hL1.2.2.2.2.2.2.2.1,
    hL2.2.2.2.1,
    hS3.2.2.2.2.1,
    hT1.1,
    hT1.2.1,
    hT2.2.2.2.2.1,
    hT2.2.2.2.2.2.2.1,
    hT3.1,
    hT3.2.2.1,
    hT3.2.2.2.2.1,
    hBKM.2.2.1,
    hBKM.2.2.2.2.2.2.2,
    hCR.2⟩

end LegendreAndBregman

/-!
## 10. Concrete Non-Commutative Matrix & Zorn Witnesses (`T16`)
-/

section ConcreteWitnesses

/-- Concrete upper-right matrix unit `E₁₂` in `M₂(ℝ)`. -/
def rnMatrixPlus : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

/-- Concrete lower-left matrix unit `E₂₁` in `M₂(ℝ)`. -/
def rnMatrixMinus : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

/-- **Non-Commutative Schwarz Defect Witness (`T16`)**:
In the concrete matrix algebra `M₂(ℝ)` and the Zorn supergraded color algebra `ZornMatrix ℝ`,
the primal coordinate `rnMatrixPlus = E₁₂` and dual coordinate `rnMatrixMinus = E₂₁` do not
commute, and the Zorn grade-`+1` and grade-`-1` coordinates `clockingZornPlus` and
`clockingZornMinus` do not commute. -/
theorem rnMatrix_noncommutative_and_schwarz_defect_ne_zero :
    rnMatrixPlus * rnMatrixMinus ≠ rnMatrixMinus * rnMatrixPlus ∧
    clockingZornPlus * clockingZornMinus ≠ clockingZornMinus * clockingZornPlus := by
  refine ⟨?_, clockingZorn_noncommutative⟩
  intro h
  have h00 := congr_arg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [rnMatrixPlus, rnMatrixMinus, Matrix.mul_apply] at h00

end ConcreteWitnesses

end InfoGeometry.Canonical.RadonNikodymKahlerParaKahlerBregmanPoset
