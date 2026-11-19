/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceBruhatAporiaTowerAndMatrixGeometry
import InfoGeometry.Core.IdempotentDefectIteration
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.ArchetypePipeline
import InfoGeometry.Meta.EpistemicCompilerChain
import InfoGeometry.Meta.MetaEpistemicCompiler
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Porous Bi-Projection Compression, Berezin–Toeplitz Duality, and Multiscale Contraction Poset

Epistemic compilation (`solve et coagula`) formalized in native Mathlib + Lean 4 over
arbitrary noncommutative `[Ring B] [StarRing B]` operator algebras and noncommutative block
matrix algebras `Matrix (Fin 1) (Fin m) B`, `Matrix (Fin m) (Fin m) B`, `Matrix (Fin 2) (Fin 2) A`,
and `Matrix (Fin 4) (Fin 4) A` (canonical reference carrier `Mat2C := Matrix (Fin 2) (Fin 2) ℂ`):

## Causal Diamond Poset (`PorousGaborArchetype`)

`K1_porousVariance ≤ K2_berezinToeplitz ≤ K4_moritaMultiplier ≤ K5_cayleyWeylGabor ≤ K6_cantorContractionLadder`
and
`K1_porousVariance ≤ K3_multiscaleTelescope ≤ K5_cayleyWeylGabor ≤ K6_cantorContractionLadder`

with `{K2_berezinToeplitz, K4_moritaMultiplier}` incomparable to `{K3_multiscaleTelescope}`:

* **K1 (`K1_porousVariance`)**: Bi-projection compression `biCompress P_Ω U P_T = P_Ω * U * P_T`,
  complementary pore uncertainty conservation, and exact coincidence of symmetric-compression
  `idempotencyDefect (porousSymCompress P Q)` with both pore leakage `((1 - P) * Q * P)⋆ ((1 - P) * Q * P)`
  and the Lie-commutator square `(P * ⁅P, Q⁆⋆) * (⁅P, Q⁆ * P)`.
* **K2 (`K2_berezinToeplitz`)**: Isometric range projections `rangeProj V = V * V⋆` (`V⋆ * V = 1`),
  Berezin compression `berezinOp V S = V⋆ * S * V`, Toeplitz compression `toeplitzOp V S`, and
  all-powers intertwining `toeplitzOp V S ^ (n + 1) = V * berezinOp V S ^ (n + 1) * V⋆`.
* **K3 (`K3_multiscaleTelescope`)**: Ordered `k`-scale localization products `multiscaleLoc L k`
  and cumulative Hermitian-square pore escape `multiscalePoreEscape L R k`, proving exact
  telescoping `1 - (multiscaleLoc L k)⋆ * multiscaleLoc L k = multiscalePoreEscape L R k`.
* **K4 (`K4_moritaMultiplier`)**: Rectangular synthesis/analysis bimodules `synMat φ ∈ M_{1,m}(B)`,
  frame/Gram Morita duality `(synMat φ * (synMat φ)ᴴ) 0 0 = frameOp φ`,
  `(synMat φ)ᴴ * synMat φ = gramMat φ`, and all-powers multiplier intertwining
  `genMultiplier φ 𝓜 ^ (n + 1) = synMat φ * 𝓜 * (gramMat φ * 𝓜) ^ n * (synMat φ)ᴴ`.
* **K5 (`K5_cayleyWeylGabor`)**: Non-diagonal `M₂(A)` Weyl–Clifford unitaries
  `{1, weylGamma1, weylSigma, weylOmega}`, Weyl conditional expectation, non-diagonal Cayley–Fourier
  operator `cayleyF2 = 1 + weylOmega`, strictly nonzero commutator `⁅peircePlus2, Q₊^{(2)}⁆ = -weylOmega`,
  and coherent Gabor frame contraction (`4 • 1` down to `2 • 1`).
* **K6 (`K6_cantorContractionLadder`)**: Dense `2`-scale Kronecker–Cayley operator `U2_mat4 ∈ M₄(A)`
  (`U2_mat4ᴴ * U2_mat4 = 4 • 1`) and strict Sierpiński-to-Cantor contraction ladder
  `4 • Pi_C2 → 3 • Pi_C2 → 2 • Pi_C2 → 1 • Pi_C2`.

## Three-Bucket Audit Map

* **BUCKET 1 (Reused upstream owners)**:
  - `InfoGeometry.Core.IdempotentGraphGrassmannian`: `idempotencyDefect`, `idempotencyDefect_eq_zero_iff`.
  - `InfoGeometry.OperatorAlgebra.PeirceBruhatAporiaTowerAndMatrixGeometry`: `peirceCut2`, `peirceCut2_idempotent`.
  - `InfoGeometry.Algebra.FiniteSpin`: `Mat2C`, `J_plus`, `J_minus`, `j_plus_j_minus_ne`.
  - `InfoGeometry.MetaCompiler` / `InfoGeometry.Causal`: `TypedArchetype`, `Status`, `Phase`,
    `ValidSchedule`, `compile`, `ProofRules`, `executable_certified_compilation`,
    `#register_archetype`, `#audit_archetype`.
* **BUCKET 2 (New theorems proved here)**:
  - `PorousGaborArchetype` diamond poset, `porousGaborPoset_diamond_structure`, and
    `two_distinct_valid_topological_schedules`.
  - Noncommutative `K1`–`K6` algebraic, Berezin–Toeplitz, multiscale telescoping, Morita bimodule,
    Cayley–Fourier, and `4 → 3 → 2 → 1` Cantor contraction theorems.
  - Explicit noncommutativity witnesses over `Mat2C`, `Matrix (Fin 1) (Fin 1) Mat2C`,
    `Matrix (Fin 2) (Fin 2) A`, `Matrix (Fin 2) (Fin 2) Mat2C`, `Matrix (Fin 4) (Fin 4) A`,
    and `Matrix (Fin 4) (Fin 4) Mat2C`, plus nonzero `idempotencyDefect (porousSymCompress P Q)`.
  - Six QMS `TypedArchetype`s (`archK1PorousVariance` .. `archK6CantorLadder`) and certified
    `executable_certified_compilation` theorem `porous_gabor_executable_certified_compilation`.
* **BUCKET 3 (Out-of-scope / excluded)**:
  - Analytic Hilbert-space norm bounds, Bourgain–Dyatlov spectral pressure estimates,
    and continuous STFT integral operators on `L²(ℝ)`.
-/

set_option autoImplicit false

namespace InfoGeometry.OperatorAlgebra.PorousBerezinToeplitzAndMultiscalePoset

open Matrix
open InfoGeometry.Core.IdempotentGraphGrassmannian
open InfoGeometry.OperatorAlgebra.PeirceBruhatAporiaTowerAndMatrixGeometry
open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.Causal.FiniteDependencySchedule
open InfoGeometry.Causal.FiniteDependencyCompiler
open InfoGeometry.Causal.ProofCarryingSchedule
open InfoGeometry.MetaCompiler

/-! ## Section 1: Bounded Acyclic Diamond Causal Poset (`PorousGaborArchetype`) -/

/-- Six-stage noncommutative porous Gabor–Toeplitz causal poset forming a diamond DAG:
`K1` → `{K2 → K4, K3}` → `K5` → `K6`. -/
inductive PorousGaborArchetype
  | K1_porousVariance
  | K2_berezinToeplitz
  | K3_multiscaleTelescope
  | K4_moritaMultiplier
  | K5_cayleyWeylGabor
  | K6_cantorContractionLadder
  deriving DecidableEq, Repr, Inhabited

namespace PorousGaborArchetype

private def equivFin : PorousGaborArchetype ≃ Fin 6 where
  toFun
    | .K1_porousVariance => 0
    | .K2_berezinToeplitz => 1
    | .K3_multiscaleTelescope => 2
    | .K4_moritaMultiplier => 3
    | .K5_cayleyWeylGabor => 4
    | .K6_cantorContractionLadder => 5
  invFun
    | 0 => .K1_porousVariance
    | 1 => .K2_berezinToeplitz
    | 2 => .K3_multiscaleTelescope
    | 3 => .K4_moritaMultiplier
    | 4 => .K5_cayleyWeylGabor
    | _ => .K6_cantorContractionLadder
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance instFintype : Fintype PorousGaborArchetype :=
  Fintype.ofEquiv (Fin 6) equivFin.symm

/-- Downward-closed causal prerequisites defining the six-stage porous-Gabor diamond poset. -/
def prerequisites : PorousGaborArchetype → Finset PorousGaborArchetype
  | .K1_porousVariance => {.K1_porousVariance}
  | .K2_berezinToeplitz => {.K1_porousVariance, .K2_berezinToeplitz}
  | .K3_multiscaleTelescope => {.K1_porousVariance, .K3_multiscaleTelescope}
  | .K4_moritaMultiplier =>
      {.K1_porousVariance, .K2_berezinToeplitz, .K4_moritaMultiplier}
  | .K5_cayleyWeylGabor =>
      {.K1_porousVariance, .K2_berezinToeplitz, .K3_multiscaleTelescope,
       .K4_moritaMultiplier, .K5_cayleyWeylGabor}
  | .K6_cantorContractionLadder =>
      {.K1_porousVariance, .K2_berezinToeplitz, .K3_multiscaleTelescope,
       .K4_moritaMultiplier, .K5_cayleyWeylGabor, .K6_cantorContractionLadder}

instance instPartialOrder : PartialOrder PorousGaborArchetype where
  le a b := prerequisites a ⊆ prerequisites b
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro a b
    cases a <;> cases b <;> decide

instance instDecidableLE : DecidableLE PorousGaborArchetype := fun a b =>
  inferInstanceAs (Decidable (prerequisites a ⊆ prerequisites b))

instance instDecidableLT : DecidableLT PorousGaborArchetype := fun a b =>
  decidable_of_iff (a ≤ b ∧ ¬ b ≤ a) lt_iff_le_not_ge.symm

/-- The causal poset has unique bottom `K1_porousVariance`, unique top
`K6_cantorContractionLadder`, cover edges `K1 < K2 < K4 < K5 < K6` and
`K1 < K3 < K5`, and incomparable parallel lanes `{K2, K4} ∥ {K3}`. -/
theorem porousGaborPoset_diamond_structure :
    (∀ x : PorousGaborArchetype,
      PorousGaborArchetype.K1_porousVariance ≤ x ∧
        x ≤ PorousGaborArchetype.K6_cantorContractionLadder) ∧
    (PorousGaborArchetype.K1_porousVariance < PorousGaborArchetype.K2_berezinToeplitz ∧
      PorousGaborArchetype.K1_porousVariance < PorousGaborArchetype.K3_multiscaleTelescope ∧
      PorousGaborArchetype.K2_berezinToeplitz < PorousGaborArchetype.K4_moritaMultiplier ∧
      PorousGaborArchetype.K4_moritaMultiplier < PorousGaborArchetype.K5_cayleyWeylGabor ∧
      PorousGaborArchetype.K3_multiscaleTelescope < PorousGaborArchetype.K5_cayleyWeylGabor ∧
      PorousGaborArchetype.K5_cayleyWeylGabor < PorousGaborArchetype.K6_cantorContractionLadder) ∧
    (¬ (PorousGaborArchetype.K2_berezinToeplitz ≤ PorousGaborArchetype.K3_multiscaleTelescope) ∧
      ¬ (PorousGaborArchetype.K3_multiscaleTelescope ≤ PorousGaborArchetype.K2_berezinToeplitz) ∧
      ¬ (PorousGaborArchetype.K4_moritaMultiplier ≤ PorousGaborArchetype.K3_multiscaleTelescope) ∧
      ¬ (PorousGaborArchetype.K3_multiscaleTelescope ≤ PorousGaborArchetype.K4_moritaMultiplier)) := by
  decide

/-- Reversed worklist forcing `compile` to recover a valid topological linearization. -/
def canonicalPending : List PorousGaborArchetype :=
  [.K6_cantorContractionLadder, .K5_cayleyWeylGabor, .K4_moritaMultiplier,
   .K3_multiscaleTelescope, .K2_berezinToeplitz, .K1_porousVariance]

/-- Schedule completing the Berezin–Toeplitz / Morita lane before multiscale telescoping. -/
def scheduleMoritaFirst : List PorousGaborArchetype :=
  [.K1_porousVariance, .K2_berezinToeplitz, .K4_moritaMultiplier,
   .K3_multiscaleTelescope, .K5_cayleyWeylGabor, .K6_cantorContractionLadder]

/-- Schedule completing multiscale telescoping before the Berezin–Toeplitz / Morita lane. -/
def scheduleTelescopeFirst : List PorousGaborArchetype :=
  [.K1_porousVariance, .K3_multiscaleTelescope, .K2_berezinToeplitz,
   .K4_moritaMultiplier, .K5_cayleyWeylGabor, .K6_cantorContractionLadder]

theorem canonicalPending_nodup : canonicalPending.Nodup := by
  decide

theorem canonicalPending_univ : canonicalPending.toFinset = Finset.univ := by
  decide

/-- Both parallel schedules are valid topological linearizations of `PorousGaborArchetype`
and are distinct, witnessing true concurrency between `{K2, K4}` and `{K3}`. -/
theorem two_distinct_valid_topological_schedules :
    ValidSchedule ∅ scheduleMoritaFirst ∧
    ValidSchedule ∅ scheduleTelescopeFirst ∧
    scheduleMoritaFirst ≠ scheduleTelescopeFirst := by
  decide

end PorousGaborArchetype

/-! ## Section 2 (`K1_porousVariance`): Bi-Projection Compression & Commutator Variance -/

section Stage1_PorousVariance

variable {B : Type*} [Ring B] [StarRing B]

/-- Noncommutative bi-projection compression `P_Ω * U * P_T` in an associative `⋆`-ring `B`. -/
def biCompress (P_Ω U P_T : B) : B := P_Ω * U * P_T

/-- Symmetric compression `P * Q * P` of two self-adjoint idempotent cuts `P, Q ∈ B`. -/
def porousSymCompress (P Q : B) : B := P * Q * P

/-- Exact pore uncertainty conservation for an isometry `U⋆ * U = 1` partitioned between
`P_Ω` and its complement `1 - P_Ω` restricted to the temporal projection `P_T`. -/
theorem pore_uncertainty_conservation
    {P_Ω U P_T : B} (hU : star U * U = 1)
    (hT_idem : P_T * P_T = P_T) (hT_sa : star P_T = P_T)
    (hΩ_idem : P_Ω * P_Ω = P_Ω) (hΩ_sa : star P_Ω = P_Ω) :
    star (biCompress P_Ω U P_T) * biCompress P_Ω U P_T +
    star (biCompress (1 - P_Ω) U P_T) * biCompress (1 - P_Ω) U P_T = P_T := by
  dsimp [biCompress]
  simp only [star_mul, star_sub, star_one, hT_sa, hΩ_sa]
  have hP_sum : P_Ω * P_Ω + (1 - P_Ω) * (1 - P_Ω) = 1 := by
    calc P_Ω * P_Ω + (1 - P_Ω) * (1 - P_Ω)
      _ = 1 - P_Ω - P_Ω + (P_Ω * P_Ω + P_Ω * P_Ω) := by noncomm_ring
      _ = 1 - P_Ω - P_Ω + (P_Ω + P_Ω) := by rw [hΩ_idem]
      _ = 1 := by noncomm_ring
  calc P_T * (star U * P_Ω) * (P_Ω * U * P_T) +
        P_T * (star U * (1 - P_Ω)) * ((1 - P_Ω) * U * P_T)
    _ = P_T * star U * (P_Ω * P_Ω + (1 - P_Ω) * (1 - P_Ω)) * U * P_T := by noncomm_ring
    _ = P_T * star U * 1 * U * P_T := by rw [hP_sum]
    _ = P_T * (star U * U) * P_T := by noncomm_ring
    _ = P_T * 1 * P_T := by rw [hU]
    _ = P_T * P_T := by noncomm_ring
    _ = P_T := hT_idem

/-- Symmetric compression variance `T - T^2` equals the Hermitian square of pore leakage
`((1 - P) * Q * P)⋆ ((1 - P) * Q * P)`. -/
theorem porousSymCompress_variance_eq_pore_leakage
    {P Q : B} (hP_idem : P * P = P) (hP_sa : star P = P)
    (hQ_idem : Q * Q = Q) (hQ_sa : star Q = Q) :
    porousSymCompress P Q - porousSymCompress P Q * porousSymCompress P Q =
      star ((1 - P) * Q * P) * ((1 - P) * Q * P) := by
  dsimp [porousSymCompress]
  simp only [star_mul, star_sub, star_one, hP_sa, hQ_sa]
  have h1P : (1 - P) * (1 - P) = 1 - P := by
    calc (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hP_idem]; noncomm_ring
  have hLHS : P * Q * P - P * Q * P * (P * Q * P) =
      P * (Q * Q) * P - P * Q * P * Q * P := by
    calc P * Q * P - P * Q * P * (P * Q * P)
      _ = P * Q * P - P * Q * (P * P) * Q * P := by noncomm_ring
      _ = P * Q * P - P * Q * P * Q * P := by rw [hP_idem]
      _ = P * (Q * Q) * P - P * Q * P * Q * P := by rw [hQ_idem]
  have hRHS : P * (Q * (1 - P)) * ((1 - P) * Q * P) =
      P * (Q * Q) * P - P * Q * P * Q * P := by
    calc P * (Q * (1 - P)) * ((1 - P) * Q * P)
      _ = P * Q * ((1 - P) * (1 - P)) * Q * P := by noncomm_ring
      _ = P * Q * (1 - P) * Q * P := by rw [h1P]
      _ = P * (Q * Q) * P - P * Q * P * Q * P := by noncomm_ring
  exact hLHS.trans hRHS.symm

/-- Exact coincidence of symmetric compression variance, Lie-commutator square `(P ⁅P, Q⁆⋆)(⁅P, Q⁆ P)`,
and negated `idempotencyDefect (porousSymCompress P Q)`. -/
theorem porousSymCompress_variance_and_idempotencyDefect
    {P Q : B} (hP_idem : P * P = P) (hP_sa : star P = P)
    (hQ_idem : Q * Q = Q) (hQ_sa : star Q = Q) :
    porousSymCompress P Q - porousSymCompress P Q * porousSymCompress P Q =
      (P * star ⁅P, Q⁆) * (⁅P, Q⁆ * P) ∧
    idempotencyDefect (porousSymCompress P Q) =
      -(star ((1 - P) * Q * P) * ((1 - P) * Q * P)) ∧
    idempotencyDefect (porousSymCompress P Q) =
      -((P * star ⁅P, Q⁆) * (⁅P, Q⁆ * P)) := by
  have hLeak := porousSymCompress_variance_eq_pore_leakage hP_idem hP_sa hQ_idem hQ_sa
  have hComm : ⁅P, Q⁆ * P = -((1 - P) * Q * P) := by
    rw [Ring.lie_def]
    calc (P * Q - Q * P) * P = P * Q * P - Q * (P * P) := by noncomm_ring
      _ = P * Q * P - Q * P := by rw [hP_idem]
      _ = -((1 - P) * Q * P) := by noncomm_ring
  have hStar : P * star ⁅P, Q⁆ = -star ((1 - P) * Q * P) := by
    calc P * star ⁅P, Q⁆ = star (⁅P, Q⁆ * P) := by simp [star_mul, hP_sa]
      _ = -star ((1 - P) * Q * P) := by rw [hComm, star_neg]
  have hEq : porousSymCompress P Q - porousSymCompress P Q * porousSymCompress P Q =
      (P * star ⁅P, Q⁆) * (⁅P, Q⁆ * P) := by
    rw [hLeak, hComm, hStar, neg_mul_neg]
  have hDef1 : idempotencyDefect (porousSymCompress P Q) =
      -(star ((1 - P) * Q * P) * ((1 - P) * Q * P)) := by
    rw [idempotencyDefect, ← hLeak]
    abel
  have hDef2 : idempotencyDefect (porousSymCompress P Q) =
      -((P * star ⁅P, Q⁆) * (⁅P, Q⁆ * P)) := by
    rw [hDef1, ← hLeak, hEq]
  exact ⟨hEq, hDef1, hDef2⟩

end Stage1_PorousVariance

/-! ## Section 3 (`K2_berezinToeplitz`): Isometric Range Projections & All-Powers Intertwining -/

section Stage2_BerezinToeplitz

variable {B : Type*} [Ring B] [StarRing B]

/-- Range projection `V * star V` associated with an operator `V ∈ B`. -/
def rangeProj (V : B) : B := V * star V

/-- Berezin pullback compression `star V * S * V`. -/
def berezinOp (V S : B) : B := star V * S * V

/-- Toeplitz compression `rangeProj V * S * rangeProj V`. -/
def toeplitzOp (V S : B) : B := rangeProj V * S * rangeProj V

/-- Every isometry `V⋆ * V = 1` generates a self-adjoint idempotent range projection
with vanishing `idempotencyDefect`. -/
theorem rangeProj_idem_sa_and_zero_defect {V : B} (hV : star V * V = 1) :
    rangeProj V * rangeProj V = rangeProj V ∧
    star (rangeProj V) = rangeProj V ∧
    idempotencyDefect (rangeProj V) = 0 := by
  have hIdem : rangeProj V * rangeProj V = rangeProj V := by
    dsimp [rangeProj]
    calc (V * star V) * (V * star V)
      _ = V * (star V * V) * star V := by noncomm_ring
      _ = V * 1 * star V := by rw [hV]
      _ = V * star V := by noncomm_ring
  have hSa : star (rangeProj V) = rangeProj V := by
    dsimp [rangeProj]
    simp [star_mul]
  exact ⟨hIdem, hSa, idempotencyDefect_eq_zero_iff.2 hIdem⟩

/-- Exact degree-1 Berezin–Toeplitz intertwining and complementary pore additivity. -/
theorem berezin_toeplitz_intertwining {V S : B} (hV : star V * V = 1) :
    V * berezinOp V S = toeplitzOp V S * V ∧
    V * berezinOp V S * star V = toeplitzOp V S ∧
    star V * toeplitzOp V S * V = berezinOp V S ∧
    berezinOp V S + berezinOp V (1 - S) = 1 ∧
    toeplitzOp V S + toeplitzOp V (1 - S) = rangeProj V := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [berezinOp, toeplitzOp, rangeProj]
    calc V * (star V * S * V)
      _ = V * star V * S * V * 1 := by noncomm_ring
      _ = V * star V * S * V * (star V * V) := by rw [hV]
      _ = (V * star V) * S * (V * star V) * V := by noncomm_ring
  · dsimp [berezinOp, toeplitzOp, rangeProj]
    noncomm_ring
  · dsimp [berezinOp, toeplitzOp, rangeProj]
    calc star V * ((V * star V) * S * (V * star V)) * V
      _ = (star V * V) * star V * S * V * (star V * V) := by noncomm_ring
      _ = 1 * star V * S * V * 1 := by rw [hV]
      _ = star V * S * V := by noncomm_ring
  · dsimp [berezinOp]
    calc star V * S * V + star V * (1 - S) * V = star V * V := by noncomm_ring
      _ = 1 := hV
  · dsimp [toeplitzOp, rangeProj]
    calc (V * star V) * S * (V * star V) + (V * star V) * (1 - S) * (V * star V)
      _ = V * (star V * V) * star V := by noncomm_ring
      _ = V * 1 * star V := by rw [hV]
      _ = V * star V := by noncomm_ring

/-- All-powers Toeplitz-from-Berezin pushforward: `T_V(S)^{n+1} = V * D_V(S)^{n+1} * V⋆`. -/
theorem toeplitzOp_pow_succ {V S : B} (hV : star V * V = 1) (n : ℕ) :
    toeplitzOp V S ^ (n + 1) = V * (berezinOp V S ^ (n + 1)) * star V := by
  induction n with
  | zero =>
      simp only [zero_add, pow_one]
      exact (berezin_toeplitz_intertwining hV).2.1.symm
  | succ n ih =>
      rw [pow_succ (toeplitzOp V S), ih, ← (berezin_toeplitz_intertwining hV).2.1]
      calc (V * berezinOp V S ^ (n + 1) * star V) * (V * berezinOp V S * star V)
        _ = V * berezinOp V S ^ (n + 1) * (star V * V) * berezinOp V S * star V := by noncomm_ring
        _ = V * berezinOp V S ^ (n + 1) * 1 * berezinOp V S * star V := by rw [hV]
        _ = V * (berezinOp V S ^ (n + 1) * berezinOp V S) * star V := by noncomm_ring
        _ = V * (berezinOp V S ^ (n + 2)) * star V := by rw [← pow_succ]

/-- All-powers Berezin pullback from Toeplitz powers: `D_V(S)^n = V⋆ * T_V(S)^n * V`. -/
theorem berezinOp_pow_eq_pullback {V S : B} (hV : star V * V = 1) (n : ℕ) :
    berezinOp V S ^ n = star V * (toeplitzOp V S ^ n) * V := by
  cases n with
  | zero =>
      simp [hV]
  | succ n =>
      rw [toeplitzOp_pow_succ hV n]
      calc berezinOp V S ^ (n + 1)
        _ = 1 * berezinOp V S ^ (n + 1) * 1 := by noncomm_ring
        _ = (star V * V) * berezinOp V S ^ (n + 1) * (star V * V) := by rw [hV]
        _ = star V * (V * berezinOp V S ^ (n + 1) * star V) * V := by noncomm_ring

end Stage2_BerezinToeplitz

/-! ## Section 4 (`K3_multiscaleTelescope`): Noncommutative Multiscale Defect Telescoping -/

section Stage3_MultiscaleTelescope

variable {B : Type*} [Ring B] [StarRing B]

/-- Ordered `k`-scale localization product `L_{k-1} * ... * L_0` of noncommuting steps. -/
def multiscaleLoc (L : ℕ → B) : ℕ → B
  | 0 => 1
  | k + 1 => L k * multiscaleLoc L k

/-- Cumulative Hermitian-square pore-escape operator `∑_{j < k} (R j * M j)⋆ (R j * M j)`. -/
def multiscalePoreEscape (L R : ℕ → B) (k : ℕ) : B :=
  ∑ j ∈ Finset.range k, star (R j * multiscaleLoc L j) * (R j * multiscaleLoc L j)

/-- Exact noncommutative telescoping identity inside the algebraic sum-of-Hermitian-squares
cone: `1 - M_k⋆ M_k = ∑_{j < k} (R_j M_j)⋆ (R_j M_j)`. -/
theorem multiscale_telescoping_defect
    {L R : ℕ → B} (h_part : ∀ j : ℕ, star (L j) * L j + star (R j) * R j = 1) (k : ℕ) :
    1 - star (multiscaleLoc L k) * multiscaleLoc L k = multiscalePoreEscape L R k := by
  induction k with
  | zero =>
      simp [multiscaleLoc, multiscalePoreEscape]
  | succ k ih =>
      rw [multiscalePoreEscape, Finset.sum_range_succ, ← multiscalePoreEscape]
      have hL : star (L k) * L k = 1 - star (R k) * R k := eq_sub_of_add_eq (h_part k)
      dsimp [multiscaleLoc]
      calc 1 - star (L k * multiscaleLoc L k) * (L k * multiscaleLoc L k)
        _ = 1 - star (multiscaleLoc L k) * (star (L k) * L k) * multiscaleLoc L k := by
            simp only [star_mul]; noncomm_ring
        _ = 1 - star (multiscaleLoc L k) * (1 - star (R k) * R k) * multiscaleLoc L k := by
            rw [hL]
        _ = (1 - star (multiscaleLoc L k) * multiscaleLoc L k) +
            star (multiscaleLoc L k) * star (R k) * (R k * multiscaleLoc L k) := by
            noncomm_ring
        _ = multiscalePoreEscape L R k +
            star (R k * multiscaleLoc L k) * (R k * multiscaleLoc L k) := by
            rw [ih]; simp only [star_mul, mul_assoc]

/-- Sequences of porous self-adjoint idempotents `P j` paired with noncommuting isometries
`U j` (`(U j)⋆ * U j = 1`) satisfy the exact multiscale telescoping pore-escape law. -/
theorem multiscale_projection_isometry_telescoping
    {P U : ℕ → B}
    (hU : ∀ j, star (U j) * U j = 1)
    (hP_idem : ∀ j, P j * P j = P j) (hP_sa : ∀ j, star (P j) = P j) (k : ℕ) :
    let L := fun j => P j * U j
    let R := fun j => (1 - P j) * U j
    1 - star (multiscaleLoc L k) * multiscaleLoc L k = multiscalePoreEscape L R k := by
  apply multiscale_telescoping_defect
  intro j
  have h := pore_uncertainty_conservation (hU j) (mul_one (1 : B)) (star_one (R := B))
    (hP_idem j) (hP_sa j)
  simpa [biCompress] using h

end Stage3_MultiscaleTelescope

/-! ## Section 5 (`K4_moritaMultiplier`): Matrix-Bimodule Frame/Gram Morita Duality -/

section Stage4_MoritaMultiplier

variable {B : Type*} [Ring B] [StarRing B] {m : ℕ}

/-- Rectangular `1 × m` synthesis row packaging `φ : Fin m → B`. -/
def synMat (φ : Fin m → B) : Matrix (Fin 1) (Fin m) B := Matrix.of fun _ j => φ j

/-- Abstract frame operator `∑ i, φ i * star (φ i) ∈ B`. -/
def frameOp (φ : Fin m → B) : B := ∑ i : Fin m, φ i * star (φ i)

/-- Bimodule Gram matrix `((star (φ i) * φ j))_{i,j} ∈ M_m(B)`. -/
def gramMat (φ : Fin m → B) : Matrix (Fin m) (Fin m) B := Matrix.of fun i j => star (φ i) * φ j

/-- Generalized matrix-symbol multiplier `Φ 𝓜 Φᴴ ∈ M_1(B)` for non-diagonal `𝓜 ∈ M_m(B)`. -/
def genMultiplier (φ : Fin m → B) (𝓜 : Matrix (Fin m) (Fin m) B) : Matrix (Fin 1) (Fin 1) B :=
  synMat φ * 𝓜 * (synMat φ)ᴴ

/-- Outer product `(Φ Φᴴ)_{0,0}` recovers `frameOp φ` and inner product `Φᴴ Φ` is `gramMat φ`. -/
theorem synMat_outer_and_inner (φ : Fin m → B) :
    (synMat φ * (synMat φ)ᴴ) 0 0 = frameOp φ ∧
    (synMat φ)ᴴ * synMat φ = gramMat φ := by
  constructor
  · simp [synMat, frameOp, Matrix.mul_apply]
  · ext i j; simp [synMat, gramMat, Matrix.mul_apply]

/-- Morita–Toeplitz compression and all-powers intertwining for arbitrary non-diagonal matrix
symbols `𝓜 ∈ M_m(B)`, plus Gram idempotency (`idempotencyDefect (gramMat φ) = 0`) under
Parseval framing `frameOp φ = 1`. -/
theorem morita_toeplitz_multiplier_intertwining
    (φ : Fin m → B) (𝓜 : Matrix (Fin m) (Fin m) B) (n : ℕ) :
    (synMat φ)ᴴ * genMultiplier φ 𝓜 * synMat φ = gramMat φ * 𝓜 * gramMat φ ∧
    genMultiplier φ 𝓜 ^ (n + 1) =
      synMat φ * 𝓜 * (gramMat φ * 𝓜) ^ n * (synMat φ)ᴴ ∧
    (frameOp φ = 1 →
      gramMat φ * gramMat φ = gramMat φ ∧
      (gramMat φ)ᴴ = gramMat φ ∧
      idempotencyDefect (gramMat φ) = 0) := by
  have hG : (synMat φ)ᴴ * synMat φ = gramMat φ := (synMat_outer_and_inner φ).2
  refine ⟨?_, ?_, ?_⟩
  · dsimp [genMultiplier]
    calc (synMat φ)ᴴ * (synMat φ * 𝓜 * (synMat φ)ᴴ) * synMat φ
      _ = ((synMat φ)ᴴ * synMat φ) * 𝓜 * ((synMat φ)ᴴ * synMat φ) := by
          simp only [Matrix.mul_assoc]
      _ = gramMat φ * 𝓜 * gramMat φ := by rw [hG]
  · induction n with
    | zero =>
        simp [genMultiplier]
    | succ n ih =>
        rw [pow_succ (genMultiplier φ 𝓜), ih]
        dsimp [genMultiplier]
        calc (synMat φ * 𝓜 * (gramMat φ * 𝓜) ^ n * (synMat φ)ᴴ) *
              (synMat φ * 𝓜 * (synMat φ)ᴴ)
          _ = synMat φ * 𝓜 * ((gramMat φ * 𝓜) ^ n *
              (((synMat φ)ᴴ * synMat φ) * 𝓜)) * (synMat φ)ᴴ := by
              simp only [Matrix.mul_assoc]
          _ = synMat φ * 𝓜 * ((gramMat φ * 𝓜) ^ n *
              (gramMat φ * 𝓜)) * (synMat φ)ᴴ := by rw [hG]
          _ = synMat φ * 𝓜 * (gramMat φ * 𝓜) ^ (n + 1) * (synMat φ)ᴴ := by
              rw [← pow_succ]
  · intro h_pars
    have hF : synMat φ * (synMat φ)ᴴ = 1 := by
      ext i j; fin_cases i; fin_cases j
      have h00 : (synMat φ * (synMat φ)ᴴ) 0 0 = 1 := (synMat_outer_and_inner φ).1.trans h_pars
      simp [h00]
    have hIdem : gramMat φ * gramMat φ = gramMat φ := by
      calc gramMat φ * gramMat φ
        _ = ((synMat φ)ᴴ * synMat φ) * ((synMat φ)ᴴ * synMat φ) := by rw [hG]
        _ = (synMat φ)ᴴ * (synMat φ * (synMat φ)ᴴ) * synMat φ := by
            simp only [Matrix.mul_assoc]
        _ = (synMat φ)ᴴ * (1 : Matrix (Fin 1) (Fin 1) B) * synMat φ := by rw [hF]
        _ = (synMat φ)ᴴ * synMat φ := by rw [Matrix.mul_one]
        _ = gramMat φ := hG
    have hSa : (gramMat φ)ᴴ = gramMat φ := by
      ext i j; simp [gramMat, star_mul]
    exact ⟨hIdem, hSa, idempotencyDefect_eq_zero_iff.2 hIdem⟩

end Stage4_MoritaMultiplier

/-! ## Section 6 (`K5_cayleyWeylGabor` & `K6_cantorContractionLadder`): Cayley–Weyl & Cantor Hierarchy -/

section Stage5_K6_CliffordCayleyAndCantor

variable {A : Type*} [Ring A] [StarRing A]

/-- Diagonal chirality generator `diag(1, -1)` in `M₂(A)`. -/
def weylGamma1 : Matrix (Fin 2) (Fin 2) A := Matrix.of fun i j =>
  match i, j with
  | 0, 0 => 1
  | 1, 1 => -1
  | _, _ => 0

/-- Swap involution `![![0, 1], ![1, 0]]` in `M₂(A)`. -/
def weylSigma : Matrix (Fin 2) (Fin 2) A := Matrix.of fun i j =>
  match i, j with
  | 0, 1 | 1, 0 => 1
  | _, _ => 0

/-- Skew-symmetric Weyl phase-swap generator `![![0, -1], ![1, 0]]` in `M₂(A)`. -/
def weylOmega : Matrix (Fin 2) (Fin 2) A := Matrix.of fun i j =>
  match i, j with
  | 0, 1 => -1
  | 1, 0 => 1
  | _, _ => 0

/-- Rank-1 coordinate idempotent `![![1, 0], ![0, 0]]` in `M₂(A)` (matches `peirceCut2`). -/
def peircePlus2 : Matrix (Fin 2) (Fin 2) A := Matrix.of fun i j =>
  match i, j with
  | 0, 0 => 1
  | _, _ => 0

/-- Non-diagonal Cayley–Fourier operator `1 + weylOmega` in `M₂(A)`. -/
def cayleyF2 : Matrix (Fin 2) (Fin 2) A := 1 + weylOmega

/-- Scalar-block fiber embedding `a ↦ diag(a, a)` in `M₂(A)`. -/
def fiberEmbed2 (a : A) : Matrix (Fin 2) (Fin 2) A := Matrix.of fun i j =>
  if i = j then a else 0

/-- Over `Mat2C`, `peircePlus2` coincides identically with `PeirceBruhatAporiaTowerAndMatrixGeometry.peirceCut2`. -/
theorem peircePlus2_eq_peirceCut2 :
    (peircePlus2 : Matrix (Fin 2) (Fin 2) Mat2C) = peirceCut2 := by
  ext i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [peircePlus2, peirceCut2]

/-- **Non-Diagonal Cayley–Fourier Uncertainty, Weyl Expectation & Coherent Gabor Contraction (`K5`)**:
1. Weyl expectation averages any `M ∈ M₂(A)` to `fiberEmbed2 (2 * (M 0 0 + M 1 1))`,
2. `cayleyF2ᴴ * cayleyF2 = 2 • 1`, carrying `peircePlus2` to the non-diagonal dual spectral operator
   `Q₊^{(2)} = 1 + weylSigma` with strictly nonzero Lie commutator `⁅peircePlus2, Q₊^{(2)}⁆ = -weylOmega`,
3. Non-diagonal coherent Gabor atoms contract from `4 • 1` on `{1, Γ₁, Σ, Ω}` to `2 • 1` on `{1, Γ₁}`. -/
theorem cayley_fourier_noncommutativity_and_coherent_gabor (M : Matrix (Fin 2) (Fin 2) A) :
    let Q_plus2 := (cayleyF2 : Matrix (Fin 2) (Fin 2) A) * peircePlus2 * cayleyF2ᴴ
    let φ0 := (cayleyF2 : Matrix (Fin 2) (Fin 2) A) * peircePlus2
    (1 * M * (1 : Matrix (Fin 2) (Fin 2) A)ᴴ + weylGamma1 * M * weylGamma1ᴴ +
     weylSigma * M * weylSigmaᴴ + weylOmega * M * weylOmegaᴴ =
      fiberEmbed2 (2 * (M 0 0 + M 1 1))) ∧
    (cayleyF2 : Matrix (Fin 2) (Fin 2) A)ᴴ * cayleyF2 = 2 • (1 : Matrix (Fin 2) (Fin 2) A) ∧
    Q_plus2 = 1 + weylSigma ∧
    ⁅(peircePlus2 : Matrix (Fin 2) (Fin 2) A), Q_plus2⁆ = -weylOmega ∧
    (φ0 * φ0ᴴ + (weylGamma1 * φ0) * (weylGamma1 * φ0)ᴴ +
     (weylSigma * φ0) * (weylSigma * φ0)ᴴ + (weylOmega * φ0) * (weylOmega * φ0)ᴴ =
      4 • (1 : Matrix (Fin 2) (Fin 2) A)) ∧
    (φ0 * φ0ᴴ + (weylGamma1 * φ0) * (weylGamma1 * φ0)ᴴ =
      2 • (1 : Matrix (Fin 2) (Fin 2) A)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    simp only [one_mul, Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;>
      dsimp [weylGamma1, weylSigma, weylOmega, fiberEmbed2] <;>
      (try simp) <;>
      (try noncomm_ring)
  · rw [show (2 : ℕ) • (1 : Matrix (Fin 2) (Fin 2) A) = 1 + 1 by abel]
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.add_apply,
      Matrix.one_apply, Fin.sum_univ_two, cayleyF2]
    fin_cases i <;> fin_cases j <;>
      dsimp [weylOmega] <;>
      (try simp)
  · ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Fin.sum_univ_two, cayleyF2, Matrix.add_apply]
    fin_cases i <;> fin_cases j <;>
      dsimp [weylOmega, peircePlus2, weylSigma] <;>
      (try simp)
  · rw [Ring.lie_def]
    ext i j
    simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fin.sum_univ_two, cayleyF2, Matrix.add_apply]
    fin_cases i <;> fin_cases j <;>
      dsimp [weylOmega, peircePlus2] <;>
      (try simp)
  · rw [show (4 : ℕ) • (1 : Matrix (Fin 2) (Fin 2) A) = 1 + 1 + 1 + 1 by abel]
    ext i j
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fin.sum_univ_two, cayleyF2]
    fin_cases i <;> fin_cases j <;>
      dsimp [weylOmega, peircePlus2, weylGamma1, weylSigma] <;>
      (try simp)
  · rw [show (2 : ℕ) • (1 : Matrix (Fin 2) (Fin 2) A) = 1 + 1 by abel]
    ext i j
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fin.sum_univ_two, cayleyF2]
    fin_cases i <;> fin_cases j <;>
      dsimp [weylOmega, peircePlus2, weylGamma1] <;>
      (try simp)

/-- Dense 2-scale Kronecker–Cayley unitary-scaled transform `U2_mat4 ∈ M₄(A)`:
entries match `![![1, -1, -1, 1], ![1, 1, -1, -1], ![1, -1, 1, -1], ![1, 1, 1, 1]]`. -/
def U2_mat4 : Matrix (Fin 4) (Fin 4) A := Matrix.of fun i j =>
  if (i = 0 ∧ (j = 1 ∨ j = 2)) ∨ (i = 1 ∧ (j = 2 ∨ j = 3)) ∨ (i = 2 ∧ (j = 1 ∨ j = 3))
  then -1 else 1

/-- Sierpiński rank-3 porous mask in `M₄(A)`. -/
def Pi_S2 : Matrix (Fin 4) (Fin 4) A := Matrix.of fun i j =>
  if i = j ∧ i.1 < 3 then 1 else 0

/-- Single-scale rank-2 porous mask in `M₄(A)`. -/
def Pi_1 : Matrix (Fin 4) (Fin 4) A := Matrix.of fun i j =>
  if i = j ∧ i.1 < 2 then 1 else 0

/-- Two-scale rank-1 Cantor porous mask in `M₄(A)`. -/
def Pi_C2 : Matrix (Fin 4) (Fin 4) A := Matrix.of fun i j =>
  if i = 0 ∧ j = 0 then 1 else 0

/-- All three Cantor/Sierpiński masks are self-adjoint idempotents with vanishing
`idempotencyDefect` and form a nested descending chain `Pi_C2 ⊂ Pi_1 ⊂ Pi_S2`. -/
theorem cantor_masks_idempotent_and_nested :
    Pi_S2 * (Pi_S2 : Matrix (Fin 4) (Fin 4) A) = Pi_S2 ∧
    Pi_1 * (Pi_1 : Matrix (Fin 4) (Fin 4) A) = Pi_1 ∧
    Pi_C2 * (Pi_C2 : Matrix (Fin 4) (Fin 4) A) = Pi_C2 ∧
    (Pi_S2 : Matrix (Fin 4) (Fin 4) A)ᴴ = Pi_S2 ∧
    (Pi_1 : Matrix (Fin 4) (Fin 4) A)ᴴ = Pi_1 ∧
    (Pi_C2 : Matrix (Fin 4) (Fin 4) A)ᴴ = Pi_C2 ∧
    Pi_1 * (Pi_S2 : Matrix (Fin 4) (Fin 4) A) = Pi_1 ∧
    Pi_C2 * (Pi_1 : Matrix (Fin 4) (Fin 4) A) = Pi_C2 ∧
    idempotencyDefect (Pi_S2 : Matrix (Fin 4) (Fin 4) A) = 0 ∧
    idempotencyDefect (Pi_1 : Matrix (Fin 4) (Fin 4) A) = 0 ∧
    idempotencyDefect (Pi_C2 : Matrix (Fin 4) (Fin 4) A) = 0 := by
  have hS2 : Pi_S2 * (Pi_S2 : Matrix (Fin 4) (Fin 4) A) = Pi_S2 := by
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [Pi_S2]
  have hP1 : Pi_1 * (Pi_1 : Matrix (Fin 4) (Fin 4) A) = Pi_1 := by
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [Pi_1]
  have hC2 : Pi_C2 * (Pi_C2 : Matrix (Fin 4) (Fin 4) A) = Pi_C2 := by
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [Pi_C2]
  have hS2sa : (Pi_S2 : Matrix (Fin 4) (Fin 4) A)ᴴ = Pi_S2 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Pi_S2]
  have hP1sa : (Pi_1 : Matrix (Fin 4) (Fin 4) A)ᴴ = Pi_1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Pi_1]
  have hC2sa : (Pi_C2 : Matrix (Fin 4) (Fin 4) A)ᴴ = Pi_C2 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Pi_C2]
  have h1S : Pi_1 * (Pi_S2 : Matrix (Fin 4) (Fin 4) A) = Pi_1 := by
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [Pi_1, Pi_S2]
  have hC1 : Pi_C2 * (Pi_1 : Matrix (Fin 4) (Fin 4) A) = Pi_C2 := by
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [Pi_C2, Pi_1]
  exact ⟨hS2, hP1, hC2, hS2sa, hP1sa, hC2sa, h1S, hC1,
    idempotencyDefect_eq_zero_iff.2 hS2,
    idempotencyDefect_eq_zero_iff.2 hP1,
    idempotencyDefect_eq_zero_iff.2 hC2⟩

/-- **Two-Scale Non-Diagonal Clifford–Cantor Contraction Hierarchy (`K6`)**:
Over any `[Ring A] [StarRing A]`, `U2_mat4ᴴ * U2_mat4 = 4 • 1`, and compressing `U2_mat4 * Pi_C2`
by `Pi_S2`, `Pi_1`, and `Pi_C2` strictly contracts the Gram square along
`4 • Pi_C2 → 3 • Pi_C2 → 2 • Pi_C2 → 1 • Pi_C2`. -/
theorem two_scale_clifford_cantor_contraction_ladder :
    (U2_mat4 : Matrix (Fin 4) (Fin 4) A)ᴴ * U2_mat4 = 4 • (1 : Matrix (Fin 4) (Fin 4) A) ∧
    (Pi_S2 * U2_mat4 * Pi_C2 : Matrix (Fin 4) (Fin 4) A)ᴴ * (Pi_S2 * U2_mat4 * Pi_C2) =
      3 • (Pi_C2 : Matrix (Fin 4) (Fin 4) A) ∧
    (Pi_1 * U2_mat4 * Pi_C2 : Matrix (Fin 4) (Fin 4) A)ᴴ * (Pi_1 * U2_mat4 * Pi_C2) =
      2 • (Pi_C2 : Matrix (Fin 4) (Fin 4) A) ∧
    (Pi_C2 * U2_mat4 * Pi_C2 : Matrix (Fin 4) (Fin 4) A)ᴴ * (Pi_C2 * U2_mat4 * Pi_C2) =
      (Pi_C2 : Matrix (Fin 4) (Fin 4) A) := by
  let col0Ones : Matrix (Fin 4) (Fin 4) A := Matrix.of fun _ j => if j = 0 then 1 else 0
  let s2Col : Matrix (Fin 4) (Fin 4) A := Matrix.of fun i j => if i.1 < 3 ∧ j = 0 then 1 else 0
  let p1Col : Matrix (Fin 4) (Fin 4) A := Matrix.of fun i j => if i.1 < 2 ∧ j = 0 then 1 else 0
  have hU2C2 : (U2_mat4 * Pi_C2 : Matrix (Fin 4) (Fin 4) A) = col0Ones := by
    ext i j
    by_cases hj : j = 0
    · fin_cases i <;> subst hj <;>
        simp [Matrix.mul_apply, U2_mat4, Pi_C2, col0Ones]
    · simp [Matrix.mul_apply, Pi_C2, col0Ones, hj]
  have hS2v : (Pi_S2 * col0Ones : Matrix (Fin 4) (Fin 4) A) = s2Col := by
    ext i j
    by_cases hj : j = 0
    · fin_cases i <;> subst hj <;>
        simp [Matrix.mul_apply, Pi_S2, col0Ones, s2Col]
    · simp [Matrix.mul_apply, col0Ones, s2Col, hj]
  have hP1v : (Pi_1 * col0Ones : Matrix (Fin 4) (Fin 4) A) = p1Col := by
    ext i j
    by_cases hj : j = 0
    · fin_cases i <;> subst hj <;>
        simp [Matrix.mul_apply, Pi_1, col0Ones, p1Col]
    · simp [Matrix.mul_apply, col0Ones, p1Col, hj]
  have hC2v : (Pi_C2 * col0Ones : Matrix (Fin 4) (Fin 4) A) = Pi_C2 := by
    ext i j
    by_cases hj : j = 0
    · fin_cases i <;> subst hj <;>
        simp [Matrix.mul_apply, Pi_C2, col0Ones]
    · simp [Matrix.mul_apply, col0Ones, Pi_C2, hj]
  have hS2m : (Pi_S2 * U2_mat4 * Pi_C2 : Matrix (Fin 4) (Fin 4) A) = s2Col := by
    rw [Matrix.mul_assoc, hU2C2, hS2v]
  have hP1m : (Pi_1 * U2_mat4 * Pi_C2 : Matrix (Fin 4) (Fin 4) A) = p1Col := by
    rw [Matrix.mul_assoc, hU2C2, hP1v]
  have hC2m : (Pi_C2 * U2_mat4 * Pi_C2 : Matrix (Fin 4) (Fin 4) A) = Pi_C2 := by
    rw [Matrix.mul_assoc, hU2C2, hC2v]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show (4 : ℕ) • (1 : Matrix (Fin 4) (Fin 4) A) = 1 + 1 + 1 + 1 by abel]
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.add_apply,
      Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;>
      dsimp [U2_mat4] <;>
      (try simp)
  · rw [hS2m, show (3 : ℕ) • (Pi_C2 : Matrix (Fin 4) (Fin 4) A) = Pi_C2 + Pi_C2 + Pi_C2 by abel]
    ext i j
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · subst hi; subst hj
      simp [Matrix.mul_apply, Fin.sum_univ_four, s2Col, Pi_C2]
    · simp [Matrix.mul_apply, s2Col, Pi_C2, hi, hj]
    · simp [Matrix.mul_apply, s2Col, Pi_C2, hi, hj]
    · simp [Matrix.mul_apply, s2Col, Pi_C2, hi, hj]
  · rw [hP1m, show (2 : ℕ) • (Pi_C2 : Matrix (Fin 4) (Fin 4) A) = Pi_C2 + Pi_C2 by abel]
    ext i j
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · subst hi; subst hj
      simp [Matrix.mul_apply, Fin.sum_univ_four, p1Col, Pi_C2]
    · simp [Matrix.mul_apply, p1Col, Pi_C2, hi, hj]
    · simp [Matrix.mul_apply, p1Col, Pi_C2, hi, hj]
    · simp [Matrix.mul_apply, p1Col, Pi_C2, hi, hj]
  · rw [hC2m]
    have hMasks := cantor_masks_idempotent_and_nested (A := A)
    rw [hMasks.2.2.2.2.2.1, hMasks.2.2.1]

end Stage5_K6_CliffordCayleyAndCantor

/-! ## Section 7: Noncommutativity Refutation Witnesses & Concrete Defect Nonvanishing -/

section NoncommutativityWitnesses

/-- Concrete noncommutativity witness inside `Mat2C` refuting abelian/diagonal reductions. -/
theorem mat2c_noncommutative_witness :
    ∃ X Y : Mat2C, X * Y ≠ Y * X :=
  ⟨J_plus, J_minus, j_plus_j_minus_ne⟩

/-- Concrete noncommutativity witness inside `Matrix (Fin 1) (Fin 1) Mat2C` showing scalar-sized
matrix multiplier rings inherit noncommutativity from the coefficient ring `Mat2C`. -/
theorem matrix1_mat2c_noncommutative_witness :
    ∃ X Y : Matrix (Fin 1) (Fin 1) Mat2C, X * Y ≠ Y * X := by
  refine ⟨Matrix.of ![![J_plus]], Matrix.of ![![J_minus]], ?_⟩
  intro hEq
  have hEntry := congrArg (fun M : Matrix (Fin 1) (Fin 1) Mat2C => M 0 0) hEq
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.of_apply, Matrix.cons_val_zero] at hEntry
  exact j_plus_j_minus_ne hEntry

/-- Generic noncommutativity witness for `Matrix (Fin 2) (Fin 2) A` over any nontrivial ring `A`. -/
theorem matrix2_noncommutative_witness (A : Type*) [Ring A] [Nontrivial A] :
    ∃ X Y : Matrix (Fin 2) (Fin 2) A, X * Y ≠ Y * X := by
  refine ⟨peircePlus2, weylSigma, ?_⟩
  intro hEq
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) A => M 0 1) hEq
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h01
  dsimp [peircePlus2, weylSigma] at h01
  simp at h01

/-- Concrete noncommutativity witness inside `Matrix (Fin 2) (Fin 2) Mat2C`. -/
theorem matrix2_mat2c_noncommutative_witness :
    ∃ X Y : Matrix (Fin 2) (Fin 2) Mat2C, X * Y ≠ Y * X := by
  refine ⟨Matrix.of ![![J_plus, 0], ![0, 0]], Matrix.of ![![J_minus, 0], ![0, 0]], ?_⟩
  intro hEq
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) Mat2C => M 0 0) hEq
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00
  exact j_plus_j_minus_ne h00

/-- Generic noncommutativity witness for `Matrix (Fin 4) (Fin 4) A` over any nontrivial ring `A`. -/
theorem matrix4_noncommutative_witness (A : Type*) [Ring A] [Nontrivial A] :
    ∃ X Y : Matrix (Fin 4) (Fin 4) A, X * Y ≠ Y * X := by
  refine ⟨Pi_C2, U2_mat4, ?_⟩
  intro hEq
  have h03 := congrArg (fun M : Matrix (Fin 4) (Fin 4) A => M 0 3) hEq
  simp only [Matrix.mul_apply, Fin.sum_univ_four] at h03
  dsimp [Pi_C2, U2_mat4] at h03
  simp at h03

/-- Concrete noncommutativity witness inside `Matrix (Fin 4) (Fin 4) Mat2C`. -/
theorem matrix4_mat2c_noncommutative_witness :
    ∃ X Y : Matrix (Fin 4) (Fin 4) Mat2C, X * Y ≠ Y * X := by
  refine ⟨Pi_S2, U2_mat4, ?_⟩
  intro hEq
  have h03 := congrArg (fun M : Matrix (Fin 4) (Fin 4) Mat2C => (M 0 3) 0 0) hEq
  simp only [Matrix.mul_apply, Fin.sum_univ_four] at h03
  dsimp [Pi_S2, U2_mat4] at h03
  simp at h03

/-- Concrete noncommuting self-adjoint idempotent cuts `P, Q ∈ Mat2C` constructed from the
Cayley–Fourier dual projection `(1/2) • (1 + weylSigma)`, yielding strictly nonzero porous
compression defect `idempotencyDefect (porousSymCompress P Q) ≠ 0`. -/
theorem concrete_mat2c_porous_idempotencyDefect_nonzero :
    ∃ P Q : Mat2C,
      P * P = P ∧ star P = P ∧
      Q * Q = Q ∧ star Q = Q ∧
      P * Q ≠ Q * P ∧
      idempotencyDefect (porousSymCompress P Q) ≠ 0 ∧
      porousSymCompress P Q - porousSymCompress P Q * porousSymCompress P Q =
        (P * star ⁅P, Q⁆) * (⁅P, Q⁆ * P) := by
  let P : Mat2C := peircePlus2
  let Q : Mat2C := Matrix.of fun _ _ => (1 / 2 : ℂ)
  have hPp : P * P = P := by
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [P, peircePlus2]
  have hPs : star P = P := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [P, peircePlus2]
  have hQp : Q * Q = Q := by
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [Q] <;> norm_num
  have hQs : star Q = Q := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Q]
  have hPQ : P * Q ≠ Q * P := by
    intro hEq
    have h01 := congrArg (fun M : Mat2C => M 0 1) hEq
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at h01
    dsimp [P, peircePlus2, Q] at h01
    norm_num at h01
  have hDef : idempotencyDefect (porousSymCompress P Q) ≠ 0 := by
    intro hZero
    have h00 := congrArg (fun M : Mat2C => M 0 0) hZero
    simp only [idempotencyDefect, porousSymCompress, Matrix.sub_apply, Matrix.mul_apply,
      Fin.sum_univ_two] at h00
    dsimp [P, peircePlus2, Q] at h00
    norm_num at h00
  have hVar := (porousSymCompress_variance_and_idempotencyDefect hPp hPs hQp hQs).1
  exact ⟨P, Q, hPp, hPs, hQp, hQs, hPQ, hDef, hVar⟩

end NoncommutativityWitnesses

/-! ## Section 8: QMS `TypedArchetype`s & Certified `MetaEpistemicCompiler` Execution -/

section QMSArchetypes

open PorousGaborArchetype

/-- Node `K1` proved `TypedArchetype` certifying noncommutative pore conservation,
Lie-commutator defect equality, and a non-diagonal `Mat2C` counterexample with nonzero
`idempotencyDefect (porousSymCompress P Q)`. -/
noncomputable def archK1PorousVariance : TypedArchetype Unit .proved where
  name := `InfoGeometry.OperatorAlgebra.PorousBerezinToeplitzAndMultiscalePoset.archK1PorousVariance
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ =>
    (∀ P Q : Matrix (Fin 2) (Fin 2) Mat2C,
      P * P = P → star P = P → Q * Q = Q → star Q = Q →
      idempotencyDefect (porousSymCompress P Q) =
        -(star ((1 - P) * Q * P) * ((1 - P) * Q * P)) ∧
      idempotencyDefect (porousSymCompress P Q) =
        -((P * star ⁅P, Q⁆) * (⁅P, Q⁆ * P))) ∧
    (∃ P Q : Mat2C, P * Q ≠ Q * P ∧ idempotencyDefect (porousSymCompress P Q) ≠ 0)
  evidence := fun _ => by
    refine ⟨?_, ?_⟩
    · intro P Q hPp hPs hQp hQs
      have h := porousSymCompress_variance_and_idempotencyDefect hPp hPs hQp hQs
      exact ⟨h.2.1, h.2.2⟩
    · obtain ⟨P, Q, _, _, _, _, hPQ, hDef, _⟩ := concrete_mat2c_porous_idempotencyDefect_nonzero
      exact ⟨P, Q, hPQ, hDef⟩

/-- Node `K2` proved `TypedArchetype` on `M₂(Mat2C) × M₂(Mat2C) × ℕ`: isometric range projection
and all-powers Berezin–Toeplitz pushforward/pullback intertwining. -/
noncomputable def archK2BerezinToeplitz :
    TypedArchetype (Matrix (Fin 2) (Fin 2) Mat2C × Matrix (Fin 2) (Fin 2) Mat2C × ℕ) .proved where
  name := `InfoGeometry.OperatorAlgebra.PorousBerezinToeplitzAndMultiscalePoset.archK2BerezinToeplitz
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun vsn =>
    star vsn.1 * vsn.1 = 1 →
      idempotencyDefect (rangeProj vsn.1) = 0 ∧
      toeplitzOp vsn.1 vsn.2.1 ^ (vsn.2.2 + 1) =
        vsn.1 * (berezinOp vsn.1 vsn.2.1 ^ (vsn.2.2 + 1)) * star vsn.1 ∧
      berezinOp vsn.1 vsn.2.1 ^ vsn.2.2 =
        star vsn.1 * (toeplitzOp vsn.1 vsn.2.1 ^ vsn.2.2) * vsn.1
  evidence := fun vsn hV =>
    ⟨(rangeProj_idem_sa_and_zero_defect hV).2.2,
     toeplitzOp_pow_succ hV vsn.2.2,
     berezinOp_pow_eq_pullback hV vsn.2.2⟩

/-- Node `K3` proved `TypedArchetype` on multiscale sequences over `Mat2C`: exact Hermitian-squares
pore-escape telescoping `1 - M_k⋆ M_k = multiscalePoreEscape L R k`. -/
noncomputable def archK3MultiscaleTelescope :
    TypedArchetype ((ℕ → Mat2C) × (ℕ → Mat2C) × ℕ) .proved where
  name := `InfoGeometry.OperatorAlgebra.PorousBerezinToeplitzAndMultiscalePoset.archK3MultiscaleTelescope
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun puk =>
    (∀ j, star (puk.2.1 j) * puk.2.1 j = 1) →
    (∀ j, puk.1 j * puk.1 j = puk.1 j) →
    (∀ j, star (puk.1 j) = puk.1 j) →
    let L := fun j => puk.1 j * puk.2.1 j
    let R := fun j => (1 - puk.1 j) * puk.2.1 j
    1 - star (multiscaleLoc L puk.2.2) * multiscaleLoc L puk.2.2 =
      multiscalePoreEscape L R puk.2.2
  evidence := fun puk hU hPidem hPsa =>
    multiscale_projection_isometry_telescoping hU hPidem hPsa puk.2.2

/-- Node `K4` proved `TypedArchetype` on `M_{1,2}(Mat2C)`: matrix-symbol multiplier all-powers
Morita–Toeplitz intertwining and Parseval Gram idempotency. -/
noncomputable def archK4MoritaMultiplier :
    TypedArchetype ((Fin 2 → Mat2C) × Matrix (Fin 2) (Fin 2) Mat2C × ℕ) .proved where
  name := `InfoGeometry.OperatorAlgebra.PorousBerezinToeplitzAndMultiscalePoset.archK4MoritaMultiplier
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun pmn =>
    (synMat pmn.1)ᴴ * genMultiplier pmn.1 pmn.2.1 * synMat pmn.1 =
      gramMat pmn.1 * pmn.2.1 * gramMat pmn.1 ∧
    genMultiplier pmn.1 pmn.2.1 ^ (pmn.2.2 + 1) =
      synMat pmn.1 * pmn.2.1 * (gramMat pmn.1 * pmn.2.1) ^ pmn.2.2 * (synMat pmn.1)ᴴ ∧
    (frameOp pmn.1 = 1 → idempotencyDefect (gramMat pmn.1) = 0)
  evidence := fun pmn => by
    have hM := morita_toeplitz_multiplier_intertwining pmn.1 pmn.2.1 pmn.2.2
    exact ⟨hM.1, hM.2.1, fun hp => (hM.2.2 hp).2.2⟩

/-- Node `K5` proved `TypedArchetype` on `M₂(Mat2C)`: Weyl conditional expectation,
Cayley–Fourier `peircePlus2` rotation to `1 + weylSigma`, nonzero Lie bracket `-weylOmega`,
and Gabor contraction `4 • 1 → 2 • 1`. -/
noncomputable def archK5CayleyWeylGabor : TypedArchetype (Matrix (Fin 2) (Fin 2) Mat2C) .proved where
  name := `InfoGeometry.OperatorAlgebra.PorousBerezinToeplitzAndMultiscalePoset.archK5CayleyWeylGabor
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun M =>
    let Q_plus2 := (cayleyF2 : Matrix (Fin 2) (Fin 2) Mat2C) * peircePlus2 * cayleyF2ᴴ
    let φ0 := (cayleyF2 : Matrix (Fin 2) (Fin 2) Mat2C) * peircePlus2
    (1 * M * (1 : Matrix (Fin 2) (Fin 2) Mat2C)ᴴ + weylGamma1 * M * weylGamma1ᴴ +
     weylSigma * M * weylSigmaᴴ + weylOmega * M * weylOmegaᴴ =
      fiberEmbed2 (2 * (M 0 0 + M 1 1))) ∧
    Q_plus2 = 1 + weylSigma ∧
    ⁅(peircePlus2 : Matrix (Fin 2) (Fin 2) Mat2C), Q_plus2⁆ = -weylOmega ∧
    (φ0 * φ0ᴴ + (weylGamma1 * φ0) * (weylGamma1 * φ0)ᴴ =
      2 • (1 : Matrix (Fin 2) (Fin 2) Mat2C)) ∧
    (peircePlus2 : Matrix (Fin 2) (Fin 2) Mat2C) = peirceCut2
  evidence := fun M => by
    have hCG := cayley_fourier_noncommutativity_and_coherent_gabor M
    exact ⟨hCG.1, hCG.2.2.1, hCG.2.2.2.1, hCG.2.2.2.2.2, peircePlus2_eq_peirceCut2⟩

/-- Node `K6` proved `TypedArchetype` certifying the two-scale `4 → 3 → 2 → 1` Clifford–Cantor
contraction ladder on `M₄(Mat2C)` paired with noncommutativity witnesses across every carrier. -/
noncomputable def archK6CantorLadder : TypedArchetype Unit .proved where
  name := `InfoGeometry.OperatorAlgebra.PorousBerezinToeplitzAndMultiscalePoset.archK6CantorLadder
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ =>
    ((U2_mat4 : Matrix (Fin 4) (Fin 4) Mat2C)ᴴ * U2_mat4 = 4 • (1 : Matrix (Fin 4) (Fin 4) Mat2C) ∧
     (Pi_S2 * U2_mat4 * Pi_C2 : Matrix (Fin 4) (Fin 4) Mat2C)ᴴ * (Pi_S2 * U2_mat4 * Pi_C2) =
       3 • (Pi_C2 : Matrix (Fin 4) (Fin 4) Mat2C) ∧
     (Pi_1 * U2_mat4 * Pi_C2 : Matrix (Fin 4) (Fin 4) Mat2C)ᴴ * (Pi_1 * U2_mat4 * Pi_C2) =
       2 • (Pi_C2 : Matrix (Fin 4) (Fin 4) Mat2C) ∧
     (Pi_C2 * U2_mat4 * Pi_C2 : Matrix (Fin 4) (Fin 4) Mat2C)ᴴ * (Pi_C2 * U2_mat4 * Pi_C2) =
       (Pi_C2 : Matrix (Fin 4) (Fin 4) Mat2C)) ∧
    idempotencyDefect (Pi_S2 : Matrix (Fin 4) (Fin 4) Mat2C) = 0 ∧
    (∃ X Y : Mat2C, X * Y ≠ Y * X) ∧
    (∃ X Y : Matrix (Fin 2) (Fin 2) Mat2C, X * Y ≠ Y * X) ∧
    (∃ X Y : Matrix (Fin 4) (Fin 4) Mat2C, X * Y ≠ Y * X)
  evidence := fun _ =>
    ⟨two_scale_clifford_cantor_contraction_ladder,
     (cantor_masks_idempotent_and_nested (A := Mat2C)).2.2.2.2.2.2.2.2.1,
     mat2c_noncommutative_witness,
     matrix2_mat2c_noncommutative_witness,
     matrix4_mat2c_noncommutative_witness⟩

#register_archetype archK1PorousVariance
#register_archetype archK2BerezinToeplitz
#register_archetype archK3MultiscaleTelescope
#register_archetype archK4MoritaMultiplier
#register_archetype archK5CayleyWeylGabor
#register_archetype archK6CantorLadder

#audit_archetype archK1PorousVariance
#audit_archetype archK2BerezinToeplitz
#audit_archetype archK3MultiscaleTelescope
#audit_archetype archK4MoritaMultiplier
#audit_archetype archK5CayleyWeylGabor
#audit_archetype archK6CantorLadder

/-- Target proposition map on the `PorousGaborArchetype` diamond causal poset. -/
noncomputable def porousGaborStatement : PorousGaborArchetype → Prop
  | .K1_porousVariance => archK1PorousVariance.claim ()
  | .K2_berezinToeplitz => ∀ vsn, archK2BerezinToeplitz.claim vsn
  | .K3_multiscaleTelescope => ∀ puk, archK3MultiscaleTelescope.claim puk
  | .K4_moritaMultiplier => ∀ pmn, archK4MoritaMultiplier.claim pmn
  | .K5_cayleyWeylGabor => ∀ M, archK5CayleyWeylGabor.claim M
  | .K6_cantorContractionLadder => archK6CantorLadder.claim ()

lemma porousGaborPosetRules : ProofRules porousGaborStatement := by
  intro target prereqs
  cases target with
  | K1_porousVariance => exact archK1PorousVariance.discharge ()
  | K2_berezinToeplitz =>
      have _ := prereqs .K1_porousVariance (by decide)
      exact fun vsn => archK2BerezinToeplitz.discharge vsn
  | K3_multiscaleTelescope =>
      have _ := prereqs .K1_porousVariance (by decide)
      exact fun puk => archK3MultiscaleTelescope.discharge puk
  | K4_moritaMultiplier =>
      have _ := prereqs .K2_berezinToeplitz (by decide)
      exact fun pmn => archK4MoritaMultiplier.discharge pmn
  | K5_cayleyWeylGabor =>
      have _ := prereqs .K3_multiscaleTelescope (by decide)
      have _ := prereqs .K4_moritaMultiplier (by decide)
      exact fun M => archK5CayleyWeylGabor.discharge M
  | K6_cantorContractionLadder =>
      have _ := prereqs .K5_cayleyWeylGabor (by decide)
      exact archK6CantorLadder.discharge ()

/-- **Certified Execution of `MetaEpistemicCompiler` on `PorousGaborArchetype`**:
Compiles `canonicalPending` into a valid diamond-respecting schedule discharging every stage
`K1`–`K6` across `Mat2C`, `M₂(Mat2C)`, and `M₄(Mat2C)`. -/
theorem porous_gabor_executable_certified_compilation :
    ∃ schedule : List PorousGaborArchetype,
      compile ∅ PorousGaborArchetype.canonicalPending = some schedule ∧
      ValidSchedule ∅ schedule ∧
      schedule.Pairwise (fun earlier later => ¬ later ≤ earlier) ∧
      schedule.Nodup ∧
      schedule.length = Fintype.card PorousGaborArchetype ∧
      schedule.toFinset = Finset.univ ∧
      ∀ target, porousGaborStatement target :=
  executable_certified_compilation
    porousGaborStatement
    porousGaborPosetRules
    PorousGaborArchetype.canonicalPending
    PorousGaborArchetype.canonicalPending_nodup
    PorousGaborArchetype.canonicalPending_univ

end QMSArchetypes

end InfoGeometry.OperatorAlgebra.PorousBerezinToeplitzAndMultiscalePoset
