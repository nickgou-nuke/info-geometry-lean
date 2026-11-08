/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.OntologyRing
import InfoGeometry.Meta.Architecture
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Homogenized
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge
import InfoGeometry.OperatorAlgebra.PeirceSpine.Unipotent
import InfoGeometry.OperatorAlgebra.PeirceSpine.OperatorTimeArchetypes
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceExponentialModularSynthesis
import InfoGeometry.Canonical.SupergradedMoebiusTetraktysKleinQuotientBerezinianWeylPoset
import InfoGeometry.Canonical.BerryWilsonLoopHyperplaneCausalTransmutationPoset
import InfoGeometry.Canonical.KleinBottleSeamSumDifferenceConnectionPoset
import InfoGeometry.Canonical.AmariOperatorDuallyFlatGaussianPythagoreanPoset
import InfoGeometry.Canonical.FirstQuantizedAmariOperatorGeometryPoset
import InfoGeometry.Canonical.InductiveCategoricalColimitInverseLimitUnificationPoset
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The 8-Stage Amari–Berezinian LDU, Modular Time Evolution, Inductive Colimit Continuum, and Analytic Series/Holonomy Closure Poset (`𝔛₁ ≺ 𝔛₂ ≺ 𝔛₃ ≺ 𝔛₄ ≺ 𝔛₅ ≺ 𝔛₆ ≺ 𝔛₇ ≺ 𝔛₈`)

This module closes the structural and analytical bridges across Streams IX and X:

1. **Stream IX (`𝔛₁ ≺ 𝔛₂ ≺ 𝔛₃`): Amari–Berezinian LDU Factorization, Graded Supertrace Moment Hierarchy, and Tomita–Takesaki Modular Derivation (`ad_Σ`) & Loxodromic `Σ`-Sandwiches**:
   * **Stage `𝔛₁` (`X1_AmariUnipotentLDUSchurBlockDiagonalization`)**:
     Proves that the inverse Amari chiral exponentials `ℰ₊(-A) = 1 - N₊(A)` and
     `ℰ₋(-C) = 1 - N₋(C)` coincide identically with the Gauss–Möbius elimination shears
     `peirceLeftElimShear P A (1 - P)` and `peirceRightElimShear P C (1 - P)`, block-diagonalize
     `1 + Φ - Q₋` and `1 + Φ - Q₊` directly into the orthogonal two-sheeted Peirce–Schur
     complement `(P - Q₊) + ((1 - P) - Q₋) = 1 - V`, and diagonalize the Paired Operator
     Gaussians `𝒢₊, 𝒢₋` into `1 ± Σ = (P ± Q₊) + ((1 - P) ∓ Q₋)`.
   * **Stage `𝔛₂` (`X2_ChiralSupertraceBerezinianMomentHierarchy`)**:
     Proves for every `k : ℕ` and any cyclic trace `tr : B →+ K` (`tr (X * Y) = tr (Y * X)`)
     that `V ^ (k + 1) = Q₊ ^ (k + 1) + Q₋ ^ (k + 1)`, `S_P * V ^ (k + 1) = Σ * V ^ k = Q₊ ^ (k + 1) - Q₋ ^ (k + 1)`,
     `chiralSupertrace tr P (V ^ (k + 1)) = 0` (`tr (Σ * V ^ k) = 0`), and
     `chiralSupertrace tr P (Σ * V ^ k) = tr (V ^ (k + 1)) = (2 : ℤ) • tr (Q₊ ^ (k + 1))`.
   * **Stage `𝔛₃` (`X3_TomitaModularDerivationAndLoxodromicSigmaSandwich`)**:
     Proves that the Amari skewness tensor `Σ = [ℰ₊(A), ℰ₋(C)] = 𝒢₊ - 𝒢₋` generates the
     modular inner derivation `modularTimeDeriv P A C` (`ad_Σ(N_±) = ±2 V N_±`,
     `ad_Σ(ℰ_±) = ±2 V N_±`, `ad_Σ(Φ) = 2 V J`, `ad_Σ(J) = 2 V Φ`, `ad_Σ(V) = ad_Σ(Σ) = 0`),
     while the ordered loxodromic `Σ`-sandwiches `sigmaSandwichPlus` and `sigmaSandwichMinus`
     scale the dually flat chiral cones `N_±` by `(1 ± V)²` and compose to the two-sided
     Bergman contraction `(1 - V²) X (1 - V²)`.

2. **Stream X (`𝔛₄ ≺ 𝔛₅ ≺ 𝔛₆`): Inductive Colimit Continuum (`Ring.DirectLimit G f`) & Projective Dual State Lift of Amari Operator Geometry & the `V₄` Klein Seam**:
   * **Stage `𝔛₄` (`X4_ContinuumColimitAbelianExponentialGroupHomsAndGaussians`)**:
     Lifts finite-stage idempotents `P_i : G i` to `P_∞ = Ring.DirectLimit.of G f i P_i` in the
     continuum colimit ring `Ring.DirectLimit G f`, induces the exact continuum abelian
     exponential group homomorphisms
     `amariExpPlusUnitsHom P_∞ hP_∞ : Multiplicative (Ring.DirectLimit G f) →* (Ring.DirectLimit G f)ˣ`
     and `amariExpMinusUnitsHom P_∞ hP_∞`, and proves functorial commutation of `Ring.DirectLimit.of G f i`
     with `ℰ_±`, `𝒢_±`, `Q_±`, `V`, and `Σ`.
   * **Stage `𝔛₅` (`X5_ContinuumColimitPythagoreanAndV4WalshHadamardIsolation`)**:
     Lifts the Operator Pythagorean Theorem `V_∞² = Q_{+,∞}² + Q_{-,∞}² = Σ_∞²` and the
     fourfold `V₄ = ℤ₂ × ℤ₂` Walsh–Hadamard sector projectors (`walshProjPP`, `walshProjPM`,
     `walshProjMP`, `walshProjMM`) directly to `Ring.DirectLimit G f`.
   * **Stage `𝔛₆` (`X6_ProjectiveDualStateColimitTraceBlindnessAndSupertraceRecovery`)**:
     Proves that for any compatible projective inverse-limit tracial family (`IsDualInverseFamily`
     on a `DirectInductiveSystem R I Stage`), both the categorical colimit readout
     `dualInverseFamilyColimitMap` and the categorical projective-limit readout
     `dualInverseFamilyToProjectiveLimit` exhibit Trace-First Blindness (`... (Σ_i * V_i ^ k) = 0`
     and `... (S_{P_i} * V_i ^ (k + 1)) = 0`) and Chiral Supertrace Recovery
     (`... (S_{P_i} * (Σ_i * V_i ^ k)) = ... (V_i ^ (k + 1))`).

3. **Analytical Closure (`𝔛₇ ≺ 𝔛₈`): Norm-Convergent `N → ∞` Operator Power Series & Smooth Fréchet/Time Holonomy Calculus (`HasDerivAt`)**:
   * **Stage `𝔛₇` (`X7_AnalyticNormConvergentResolventAndBregmanPowerSeries`)**:
     In any complete normed algebra `[NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]` for
     `‖V‖ < 1`, proves norm-summability and exact inverse convergence of the geometric resolvent
     series `∑' n : ℕ, V ^ n = (1 - V)⁻¹ʳ` (`(1 - V) * ∑' n, V ^ n = 1`), norm-summability of the
     infinite para-Kähler logarithmic potential series
     `paraKahlerSeriesTerm V n = (1 / ((n + 1)(n + 2))) • V ^ (n + 1)` and Bregman divergence
     series `bregmanMinusSeriesTerm V n = V ^ (n + 1) - paraKahlerSeriesTerm V n`, and the exact
     `N → ∞` operator Bregman decomposition
     `∑' n : ℕ, bregmanMinusSeriesTerm V n = V * (1 - V)⁻¹ʳ - ∑' n : ℕ, paraKahlerSeriesTerm V n`.
   * **Stage `𝔛₈` (`X8_AnalyticSmoothBerryRotorAndHyperplaneHolonomyFlowCalculus`)**:
     In any normed algebra `[NormedRing B] [NormedAlgebra ℝ B]` with idempotent `P * P = P`,
     proves exact Fréchet/time differentiability (`HasDerivAt`) of the continuous Berry rotor
     `berryRotor P θ = cos θ • 1 + sin θ • S_P` and rotated hyperplane frame
     `(rotatedCurrentJ P A C θ, rotatedBridgePhi P A C θ)` over `ℝ`, proves that the rotor velocity
     satisfies `berryRotorDeriv P θ = invS P * berryRotor P (-θ)` with `d/dθ J(θ) = Φ(-θ)` and
     `d/dθ Φ(θ) = J(-θ)` (reducing at `θ = 0` to `d/dθ R_P(0) = S_P`, `d/dθ J(0) = Φ`,
     `d/dθ Φ(0) = J`), and proves conservation of `J(θ)² + Φ(θ)² = 0` along the entire smooth flow.

### Three-Bucket Audit Map

#### BUCKET 1 — Unconditional Kernel Truth
- `AmariBerezinianColimitAnalyticStage`, `rank_injective`, `causalEdge_strict_rank_mono`,
  `causalEdge_irrefl`, `transGen_causalEdge_strict_rank_mono`, `causalEdge_acyclic`,
  `strict_eight_stage_chain`, `toRepDepth_rank_monotone`, `toOntologyMetaLevel_rank_monotone`.

#### BUCKET 2 — Conditional Kernel Theorems with Explicit Hypotheses
- Stages `𝔛₁`–`𝔛₈` LDU Schur block diagonalization, supertrace moment hierarchy, Tomita modular
  derivation, `Ring.DirectLimit` colimit lifts, norm-convergent `‖V‖ < 1` resolvent/Bregman series,
  and smooth `HasDerivAt` Berry rotor flow calculus under explicit algebraic/normed hypotheses.

#### BUCKET 3 — Open / Beyond-Scope Obligations
- Unbounded modular operator spectral theory beyond bounded `[NormedRing B]` and `‖V‖ < 1`
  remains outside this module's scope.

## i. Overview
Formalizes the 8-stage Amari–Berezinian LDU, supertrace moment hierarchy, `Ring.DirectLimit` colimit continuum, and analytic norm-series / smooth Berry rotor closure poset (`𝔛₁ ≺ ⋯ ≺ 𝔛₈`).

## ii. Key results
- `AmariBerezinianColimitAnalyticStage.causalEdge_acyclic`
- `AmariBerezinianColimitAnalyticStage.strict_eight_stage_chain`

## iii. Table of contents
- Section 1: The 8-Stage Acyclic Causal Poset (`𝔛₁ ≺ ⋯ ≺ 𝔛₈`)
- Section 2: Stream IX–X & Analytical Closure (`𝔛₁ ≺ ⋯ ≺ 𝔛₈`)

## iv. References
- S. Amari, *Information Geometry and Its Applications* (2016).
-/

noncomputable section

namespace InfoGeometry.Canonical.AmariBerezinianModularColimitAnalyticClosurePoset

open scoped BigOperators Matrix Matrix.Norms.Frobenius
open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.OperatorAlgebra.OntologyRing
open InfoGeometry.Meta
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceExponentialModularSynthesis
open InfoGeometry.Canonical.RadonNikodymKahlerParaKahlerBregmanPoset
open InfoGeometry.Canonical.SupergradedMoebiusTetraktysKleinQuotientBerezinianWeylPoset
open InfoGeometry.Canonical.BerryWilsonLoopHyperplaneCausalTransmutationPoset
open InfoGeometry.Canonical.KleinBottleSeamSumDifferenceConnectionPoset
open InfoGeometry.Canonical.AmariOperatorDuallyFlatGaussianPythagoreanPoset
open InfoGeometry.Canonical.InductiveCategoricalColimitInverseLimitUnificationPoset
open FilteredColimit
open FilteredColimit.InductiveCocone
open FilteredColimit.Native

universe u

/-!
## 1. The 8-Stage Acyclic Causal Poset (`𝔛₁ ≺ 𝔛₂ ≺ 𝔛₃ ≺ 𝔛₄ ≺ 𝔛₅ ≺ 𝔛₆ ≺ 𝔛₇ ≺ 𝔛₈`)
-/

/-- The 8-stage causal poset unifying Stream IX (Amari–Berezinian LDU, Supertrace Moment
Hierarchy, and Modular `ad_Σ` / Loxodromic `Σ`-Sandwiches), Stream X (Inductive Colimit Continuum
`Ring.DirectLimit` & Projective Dual State Lift), and Analytical Norm-Series / Smooth Holonomy
Closure (`𝔛₁ ≺ 𝔛₂ ≺ ⋯ ≺ 𝔛₈`). -/
inductive AmariBerezinianColimitAnalyticStage : Type
  | X1_AmariUnipotentLDUSchurBlockDiagonalization
  | X2_ChiralSupertraceBerezinianMomentHierarchy
  | X3_TomitaModularDerivationAndLoxodromicSigmaSandwich
  | X4_ContinuumColimitAbelianExponentialGroupHomsAndGaussians
  | X5_ContinuumColimitPythagoreanAndV4WalshHadamardIsolation
  | X6_ProjectiveDualStateColimitTraceBlindnessAndSupertraceRecovery
  | X7_AnalyticNormConvergentResolventAndBregmanPowerSeries
  | X8_AnalyticSmoothBerryRotorAndHyperplaneHolonomyFlowCalculus
  deriving DecidableEq, Repr, Inhabited

namespace AmariBerezinianColimitAnalyticStage

/-- Strictly monotone integer rank `0..7` of the 8 stages `𝔛₁..𝔛₈`. -/
def rank : AmariBerezinianColimitAnalyticStage → ℕ
  | .X1_AmariUnipotentLDUSchurBlockDiagonalization => 0
  | .X2_ChiralSupertraceBerezinianMomentHierarchy => 1
  | .X3_TomitaModularDerivationAndLoxodromicSigmaSandwich => 2
  | .X4_ContinuumColimitAbelianExponentialGroupHomsAndGaussians => 3
  | .X5_ContinuumColimitPythagoreanAndV4WalshHadamardIsolation => 4
  | .X6_ProjectiveDualStateColimitTraceBlindnessAndSupertraceRecovery => 5
  | .X7_AnalyticNormConvergentResolventAndBregmanPowerSeries => 6
  | .X8_AnalyticSmoothBerryRotorAndHyperplaneHolonomyFlowCalculus => 7

/-- `rank` is injective on `AmariBerezinianColimitAnalyticStage`. -/
theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance instLinearOrder : LinearOrder AmariBerezinianColimitAnalyticStage :=
  LinearOrder.lift' rank rank_injective

instance instFintype : Fintype AmariBerezinianColimitAnalyticStage where
  elems := {
    .X1_AmariUnipotentLDUSchurBlockDiagonalization,
    .X2_ChiralSupertraceBerezinianMomentHierarchy,
    .X3_TomitaModularDerivationAndLoxodromicSigmaSandwich,
    .X4_ContinuumColimitAbelianExponentialGroupHomsAndGaussians,
    .X5_ContinuumColimitPythagoreanAndV4WalshHadamardIsolation,
    .X6_ProjectiveDualStateColimitTraceBlindnessAndSupertraceRecovery,
    .X7_AnalyticNormConvergentResolventAndBregmanPowerSeries,
    .X8_AnalyticSmoothBerryRotorAndHyperplaneHolonomyFlowCalculus
  }
  complete x := by cases x <;> simp

/-- Direct causal edge `𝔛_k → 𝔛_{k+1}`. -/
def causalEdge : AmariBerezinianColimitAnalyticStage → AmariBerezinianColimitAnalyticStage → Prop
  | .X1_AmariUnipotentLDUSchurBlockDiagonalization,
    .X2_ChiralSupertraceBerezinianMomentHierarchy => True
  | .X2_ChiralSupertraceBerezinianMomentHierarchy,
    .X3_TomitaModularDerivationAndLoxodromicSigmaSandwich => True
  | .X3_TomitaModularDerivationAndLoxodromicSigmaSandwich,
    .X4_ContinuumColimitAbelianExponentialGroupHomsAndGaussians => True
  | .X4_ContinuumColimitAbelianExponentialGroupHomsAndGaussians,
    .X5_ContinuumColimitPythagoreanAndV4WalshHadamardIsolation => True
  | .X5_ContinuumColimitPythagoreanAndV4WalshHadamardIsolation,
    .X6_ProjectiveDualStateColimitTraceBlindnessAndSupertraceRecovery => True
  | .X6_ProjectiveDualStateColimitTraceBlindnessAndSupertraceRecovery,
    .X7_AnalyticNormConvergentResolventAndBregmanPowerSeries => True
  | .X7_AnalyticNormConvergentResolventAndBregmanPowerSeries,
    .X8_AnalyticSmoothBerryRotorAndHyperplaneHolonomyFlowCalculus => True
  | _, _ => False

instance instDecidableRelCausalEdge : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

/-- Every direct causal edge strictly increases the numerical rank. -/
theorem causalEdge_strict_rank_mono {a b : AmariBerezinianColimitAnalyticStage}
    (h : causalEdge a b) : rank a < rank b := by
  cases a <;> cases b <;> revert h <;> decide

/-- No stage has a self-loop under `causalEdge`. -/
theorem causalEdge_irrefl (a : AmariBerezinianColimitAnalyticStage) : ¬ causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (causalEdge_strict_rank_mono h)

/-- Any transitive path of causal edges strictly increases the numerical rank. -/
theorem transGen_causalEdge_strict_rank_mono {a b : AmariBerezinianColimitAnalyticStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_strict_rank_mono hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_strict_rank_mono hbc)

/-- **Strict Poset Acyclicity (`𝔛₁ ≺ 𝔛₂ ≺ ⋯ ≺ 𝔛₈`)**: No stage can cycle back to itself. -/
theorem causalEdge_acyclic (a : AmariBerezinianColimitAnalyticStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_strict_rank_mono h)

/-- Complete 8-stage causal chain and cardinality `8`. -/
theorem strict_eight_stage_chain :
    causalEdge .X1_AmariUnipotentLDUSchurBlockDiagonalization
      .X2_ChiralSupertraceBerezinianMomentHierarchy ∧
    causalEdge .X2_ChiralSupertraceBerezinianMomentHierarchy
      .X3_TomitaModularDerivationAndLoxodromicSigmaSandwich ∧
    causalEdge .X3_TomitaModularDerivationAndLoxodromicSigmaSandwich
      .X4_ContinuumColimitAbelianExponentialGroupHomsAndGaussians ∧
    causalEdge .X4_ContinuumColimitAbelianExponentialGroupHomsAndGaussians
      .X5_ContinuumColimitPythagoreanAndV4WalshHadamardIsolation ∧
    causalEdge .X5_ContinuumColimitPythagoreanAndV4WalshHadamardIsolation
      .X6_ProjectiveDualStateColimitTraceBlindnessAndSupertraceRecovery ∧
    causalEdge .X6_ProjectiveDualStateColimitTraceBlindnessAndSupertraceRecovery
      .X7_AnalyticNormConvergentResolventAndBregmanPowerSeries ∧
    causalEdge .X7_AnalyticNormConvergentResolventAndBregmanPowerSeries
      .X8_AnalyticSmoothBerryRotorAndHyperplaneHolonomyFlowCalculus ∧
    Fintype.card AmariBerezinianColimitAnalyticStage = 8 := by
  decide

/-- Monotone representation-depth projection across `𝔛₁..𝔛₈`. -/
def toRepDepth : AmariBerezinianColimitAnalyticStage → RepDepth
  | .X1_AmariUnipotentLDUSchurBlockDiagonalization => .operator
  | .X2_ChiralSupertraceBerezinianMomentHierarchy => .operator
  | .X3_TomitaModularDerivationAndLoxodromicSigmaSandwich => .krein
  | .X4_ContinuumColimitAbelianExponentialGroupHomsAndGaussians => .transport
  | .X5_ContinuumColimitPythagoreanAndV4WalshHadamardIsolation => .transport
  | .X6_ProjectiveDualStateColimitTraceBlindnessAndSupertraceRecovery => .transport
  | .X7_AnalyticNormConvergentResolventAndBregmanPowerSeries => .thermo
  | .X8_AnalyticSmoothBerryRotorAndHyperplaneHolonomyFlowCalculus => .thermo

/-- Monotone ontology meta-level projection across `𝔛₁..𝔛₈`. -/
def toOntologyMetaLevel : AmariBerezinianColimitAnalyticStage → OntologyMetaLevel
  | .X1_AmariUnipotentLDUSchurBlockDiagonalization => .M1_ProjectorClabject
  | .X2_ChiralSupertraceBerezinianMomentHierarchy => .M1_ProjectorClabject
  | .X3_TomitaModularDerivationAndLoxodromicSigmaSandwich => .M2_GrassmannianPowertypeOrbit
  | .X4_ContinuumColimitAbelianExponentialGroupHomsAndGaussians => .M2_GrassmannianPowertypeOrbit
  | .X5_ContinuumColimitPythagoreanAndV4WalshHadamardIsolation => .M2_GrassmannianPowertypeOrbit
  | .X6_ProjectiveDualStateColimitTraceBlindnessAndSupertraceRecovery => .M3_ErlangenCasimirMetaLaw
  | .X7_AnalyticNormConvergentResolventAndBregmanPowerSeries => .M3_ErlangenCasimirMetaLaw
  | .X8_AnalyticSmoothBerryRotorAndHyperplaneHolonomyFlowCalculus => .M3_ErlangenCasimirMetaLaw

/-- The representation-depth projection `toRepDepth` is monotone with respect to stage order. -/
theorem toRepDepth_rank_monotone {a b : AmariBerezinianColimitAnalyticStage} (h : a ≤ b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  change rank a ≤ rank b at h
  cases a <;> cases b <;> simp [toRepDepth, RepDepth.toNat, rank] at h ⊢

/-- The ontology meta-level projection `toOntologyMetaLevel` is monotone with respect to stage order. -/
theorem toOntologyMetaLevel_rank_monotone {a b : AmariBerezinianColimitAnalyticStage} (h : a ≤ b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  change rank a ≤ rank b at h
  cases a <;> cases b <;> simp [toOntologyMetaLevel, OntologyMetaLevel.rank, rank] at h ⊢

end AmariBerezinianColimitAnalyticStage

/-!
## 2. Stream IX (`𝔛₁ ≺ 𝔛₂ ≺ 𝔛₃`): Amari–Berezinian LDU Factorization, Supertrace Moment Hierarchy, and Tomita–Takesaki Modular Derivation (`ad_Σ`) & Loxodromic `Σ`-Sandwiches
-/

section StreamIX_AmariBerezinianModularLoxodromic

variable {B : Type*} [Ring B]

/-- **Stage `𝔛₁` Theorem (`x1_amari_unipotent_ldu_udl_and_schur_block_diagonalization`)**:
In any noncommutative associative ring `[Ring B]` with idempotent `P * P = P`:
1. **Identity of Gauss–Möbius Elimination Shears and Inverse Amari Chiral Exponentials**:
   At `d = 1 - P = d_inv`,
   `peirceLeftElimShear P A (1 - P) = unipotentExpPlus P (-A)`,
   `peirceRightElimShear P C (1 - P) = unipotentExpMinus P (-C)`, and
   `peirceSchurComplement P 1 A C (1 - P) = P - qgtPlus P A C`.
2. **Unipotent LDU and UDL Block Diagonalization of `1 + Φ`**:
   `unipotentExpPlus P (-A) * (1 + genPhi P A C) * unipotentExpMinus P (-C) = (P - qgtPlus P A C) + (1 - P) = 1 - qgtPlus P A C`,
   `unipotentExpMinus P (-C) * (1 + genPhi P A C) * unipotentExpPlus P (-A) = P + ((1 - P) - qgtMinus P A C) = 1 - qgtMinus P A C`,
   `unipotentExpPlus P A * (1 - qgtPlus P A C) * unipotentExpMinus P C = 1 + genPhi P A C`,
   `unipotentExpMinus P C * (1 - qgtMinus P A C) * unipotentExpPlus P A = 1 + genPhi P A C`.
3. **Two-Sheeted Peirce–Schur Block Diagonalization to `(P - Q₊) + ((1 - P) - Q₋) = 1 - V`**:
   `(1 - qgtPlus P A C) * (1 - qgtMinus P A C) = (P - qgtPlus P A C) + ((1 - P) - qgtMinus P A C)`,
   `(1 - qgtMinus P A C) * (1 - qgtPlus P A C) = (P - qgtPlus P A C) + ((1 - P) - qgtMinus P A C)`,
   `(P - qgtPlus P A C) + ((1 - P) - qgtMinus P A C) = 1 - genV P A C`, and
   `(P - qgtPlus P A C) * ((1 - P) - qgtMinus P A C) = 0`.
4. **Unipotent Reduction of Paired Operator Gaussians `𝒢_±` and Skewness Decomposition `1 ± Σ`**:
   `unipotentExpPlus P (-A) * operatorGaussianPlus P A C * unipotentExpMinus P (-C) = 1`,
   `unipotentExpMinus P (-C) * operatorGaussianMinus P A C * unipotentExpPlus P (-A) = 1`, and
   `(P + qgtPlus P A C) + ((1 - P) - qgtMinus P A C) = 1 + genSig P A C`. -/
theorem x1_amari_unipotent_ldu_udl_and_schur_block_diagonalization
    {P : B} (hP : P * P = P) (A C : B) :
    peirceLeftElimShear P A (1 - P) = unipotentExpPlus P (-A) ∧
    peirceRightElimShear P C (1 - P) = unipotentExpMinus P (-C) ∧
    peirceSchurComplement P 1 A C (1 - P) = P - qgtPlus P A C ∧
    unipotentExpPlus P (-A) * (1 + genPhi P A C) * unipotentExpMinus P (-C) =
      1 - qgtPlus P A C ∧
    unipotentExpMinus P (-C) * (1 + genPhi P A C) * unipotentExpPlus P (-A) =
      1 - qgtMinus P A C ∧
    unipotentExpPlus P A * (1 - qgtPlus P A C) * unipotentExpMinus P C =
      1 + genPhi P A C ∧
    unipotentExpMinus P C * (1 - qgtMinus P A C) * unipotentExpPlus P A =
      1 + genPhi P A C ∧
    (1 - qgtPlus P A C) * (1 - qgtMinus P A C) =
      (P - qgtPlus P A C) + ((1 - P) - qgtMinus P A C) ∧
    (1 - qgtMinus P A C) * (1 - qgtPlus P A C) =
      (P - qgtPlus P A C) + ((1 - P) - qgtMinus P A C) ∧
    (P - qgtPlus P A C) + ((1 - P) - qgtMinus P A C) = 1 - genV P A C ∧
    (P - qgtPlus P A C) * ((1 - P) - qgtMinus P A C) = 0 ∧
    unipotentExpPlus P (-A) * operatorGaussianPlus P A C * unipotentExpMinus P (-C) = 1 ∧
    unipotentExpMinus P (-C) * operatorGaussianMinus P A C * unipotentExpPlus P (-A) = 1 ∧
    (P + qgtPlus P A C) + ((1 - P) - qgtMinus P A C) = 1 + genSig P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [peirceLeftElimShear, peirceRightElimShear, peirceSchurComplement,
      operatorGaussianPlus, operatorGaussianMinus, unipotentExpPlus, unipotentExpMinus,
      qgtPlus, qgtMinus]) <;>
    peirce_nf hP

/-- **Stage `𝔛₂` Theorem (`x2_chiral_supertrace_berezinian_moment_hierarchy`)**:
For every `k : ℕ` and any cyclic trace `tr : B →+ K` (`∀ X Y, tr (X * Y) = tr (Y * X)`):
1. **Orthogonal Sheet Power Decomposition**:
   * `genV P A C ^ (k + 1) = qgtPlus P A C ^ (k + 1) + qgtMinus P A C ^ (k + 1)`,
   * `invS P * (genV P A C ^ (k + 1)) = qgtPlus P A C ^ (k + 1) - qgtMinus P A C ^ (k + 1)`,
   * `genSig P A C * (genV P A C ^ k) = invS P * (genV P A C ^ (k + 1))`,
   * `invS P * (genSig P A C * (genV P A C ^ k)) = genV P A C ^ (k + 1)`.
2. **Universal Higher-Moment Trace-First Blindness vs. Chiral Supertrace Recovery**:
   * `tr (qgtPlus P A C ^ (k + 1)) = tr (qgtMinus P A C ^ (k + 1))`,
   * `chiralSupertrace tr P (genV P A C ^ (k + 1)) = 0`,
   * `tr (genSig P A C * (genV P A C ^ k)) = 0`,
   * `chiralSupertrace tr P (genSig P A C * (genV P A C ^ k)) = tr (genV P A C ^ (k + 1))`,
   * `chiralSupertrace tr P (genSig P A C * (genV P A C ^ k)) = (2 : ℤ) • tr (qgtPlus P A C ^ (k + 1))`. -/
theorem x2_chiral_supertrace_berezinian_moment_hierarchy
    {K : Type*} [AddCommGroup K] (tr : B →+ K)
    (hCyclic : ∀ X Y : B, tr (X * Y) = tr (Y * X))
    {P : B} (hP : P * P = P) (A C : B) (k : ℕ) :
    genV P A C ^ (k + 1) = qgtPlus P A C ^ (k + 1) + qgtMinus P A C ^ (k + 1) ∧
    invS P * (genV P A C ^ (k + 1)) = qgtPlus P A C ^ (k + 1) - qgtMinus P A C ^ (k + 1) ∧
    genSig P A C * (genV P A C ^ k) = invS P * (genV P A C ^ (k + 1)) ∧
    invS P * (genSig P A C * (genV P A C ^ k)) = genV P A C ^ (k + 1) ∧
    tr (qgtPlus P A C ^ (k + 1)) = tr (qgtMinus P A C ^ (k + 1)) ∧
    chiralSupertrace tr P (genV P A C ^ (k + 1)) = 0 ∧
    tr (genSig P A C * (genV P A C ^ k)) = 0 ∧
    chiralSupertrace tr P (genSig P A C * (genV P A C ^ k)) = tr (genV P A C ^ (k + 1)) ∧
    chiralSupertrace tr P (genSig P A C * (genV P A C ^ k)) =
      (2 : ℤ) • tr (qgtPlus P A C ^ (k + 1)) := by
  have hVPow : genV P A C ^ (k + 1) = qgtPlus P A C ^ (k + 1) + qgtMinus P A C ^ (k + 1) := by
    induction k with
    | zero =>
      simp only [Nat.zero_add, pow_one]
      unfold qgtPlus qgtMinus
      peirce_nf hP
    | succ m ih =>
      rw [pow_succ (genV P A C) (m + 1), ih]
      have hCross :
          (qgtPlus P A C ^ (m + 1) + qgtMinus P A C ^ (m + 1)) * genV P A C =
            qgtPlus P A C ^ (m + 1) * qgtPlus P A C +
              qgtMinus P A C ^ (m + 1) * qgtMinus P A C := by
        rw [pow_succ (qgtPlus P A C) m, pow_succ (qgtMinus P A C) m]
        unfold qgtPlus qgtMinus
        peirce_nf hP
      rw [hCross, ← pow_succ (qgtPlus P A C) (m + 1), ← pow_succ (qgtMinus P A C) (m + 1)]
  have hQ4k := q4_higher_moment_trace_blindness_and_supertrace_recovery tr hCyclic hP A C k
  have hSVPow :
      invS P * (genV P A C ^ (k + 1)) = qgtPlus P A C ^ (k + 1) - qgtMinus P A C ^ (k + 1) := by
    rw [hVPow, mul_add]
    have hPlus : invS P * qgtPlus P A C ^ (k + 1) = qgtPlus P A C ^ (k + 1) := by
      rw [pow_succ' (qgtPlus P A C) k, ← mul_assoc]
      have h0 : invS P * qgtPlus P A C = qgtPlus P A C := by unfold qgtPlus; peirce_nf hP
      rw [h0]
    have hMinus : invS P * qgtMinus P A C ^ (k + 1) = -(qgtMinus P A C ^ (k + 1)) := by
      rw [pow_succ' (qgtMinus P A C) k, ← mul_assoc]
      have h0 : invS P * qgtMinus P A C = -qgtMinus P A C := by unfold qgtMinus; peirce_nf hP
      rw [h0, neg_mul]
    rw [hPlus, hMinus, sub_eq_add_neg]
  have hSigVk : genSig P A C * (genV P A C ^ k) = invS P * (genV P A C ^ (k + 1)) := by
    rw [pow_succ' (genV P A C) k, ← mul_assoc]
    have hSV : genSig P A C = invS P * genV P A C := by peirce_nf hP
    rw [← hSV]
  have hSSigVk : invS P * (genSig P A C * (genV P A C ^ k)) = genV P A C ^ (k + 1) := by
    rw [hSigVk, ← mul_assoc]
    have hS2 : invS P * invS P = 1 := by peirce_nf hP
    rw [hS2, one_mul]
  have hTrQpQm : tr (qgtPlus P A C ^ (k + 1)) = tr (qgtMinus P A C ^ (k + 1)) := hQ4k.1
  have hTrSigVk : tr (genSig P A C * (genV P A C ^ k)) = 0 := by
    rw [hSigVk]
    exact hQ4k.2.2
  have hStrSigVk :
      chiralSupertrace tr P (genSig P A C * (genV P A C ^ k)) = tr (genV P A C ^ (k + 1)) := by
    unfold chiralSupertrace
    rw [hSSigVk]
  have hStrSigVkTwo :
      chiralSupertrace tr P (genSig P A C * (genV P A C ^ k)) =
        (2 : ℤ) • tr (qgtPlus P A C ^ (k + 1)) := by
    rw [hStrSigVk, hVPow, map_add, ← hTrQpQm, two_zsmul]
  exact ⟨hVPow, hSVPow, hSigVk, hSSigVk, hTrQpQm, hQ4k.2.2, hTrSigVk, hStrSigVk, hStrSigVkTwo⟩

/-- **Stage `𝔛₃` Theorem (`x3_tomita_modular_derivation_and_loxodromic_sigma_sandwich`)**:
Bridges First-Quantized Amari Operator Geometry directly to Tomita–Takesaki Modular Time
Evolution (`modularTimeDeriv`) and the Ordered Loxodromic `Σ`-Sandwiches (`sigmaSandwichPlus`,
`sigmaSandwichMinus`):
1. **Amari Skewness `Σ` as the Modular Generator**:
   * `comm (unipotentExpPlus P A) (unipotentExpMinus P C) = genSig P A C`,
   * `operatorGaussianPlus P A C - operatorGaussianMinus P A C = genSig P A C`,
   * `modularTimeDeriv P A C (conePlus P A) = (2 : ℤ) • (genV P A C * conePlus P A)`,
   * `modularTimeDeriv P A C (coneMinus P C) = -((2 : ℤ) • (genV P A C * coneMinus P C))`,
   * `modularTimeDeriv P A C (unipotentExpPlus P A) = (2 : ℤ) • (genV P A C * conePlus P A)`,
   * `modularTimeDeriv P A C (unipotentExpMinus P C) = -((2 : ℤ) • (genV P A C * coneMinus P C))`,
   * `modularTimeDeriv P A C (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C)`,
   * `modularTimeDeriv P A C (genJ P A C) = (2 : ℤ) • (genV P A C * genPhi P A C)`,
   * `modularTimeDeriv P A C (genV P A C) = 0` and `modularTimeDeriv P A C (genSig P A C) = 0`.
2. **Ordered Loxodromic `Σ`-Sandwiches on the Dually Flat Chiral Cones**:
   * `sigmaSandwichPlus P A C (conePlus P A) = ((1 + genV P A C) * (1 + genV P A C)) * conePlus P A`,
   * `sigmaSandwichPlus P A C (coneMinus P C) = ((1 - genV P A C) * (1 - genV P A C)) * coneMinus P C`,
   * `sigmaSandwichMinus P A C (conePlus P A) = ((1 - genV P A C) * (1 - genV P A C)) * conePlus P A`,
   * `sigmaSandwichMinus P A C (coneMinus P C) = ((1 + genV P A C) * (1 + genV P A C)) * coneMinus P C`,
   * `sigmaSandwichMinus P A C (sigmaSandwichPlus P A C X) = (1 - genV P A C * genV P A C) * X * (1 - genV P A C * genV P A C)`. -/
theorem x3_tomita_modular_derivation_and_loxodromic_sigma_sandwich
    {P : B} (hP : P * P = P) (A C X : B) :
    comm (unipotentExpPlus P A) (unipotentExpMinus P C) = genSig P A C ∧
    operatorGaussianPlus P A C - operatorGaussianMinus P A C = genSig P A C ∧
    modularTimeDeriv P A C (conePlus P A) = (2 : ℤ) • (genV P A C * conePlus P A) ∧
    modularTimeDeriv P A C (coneMinus P C) = -((2 : ℤ) • (genV P A C * coneMinus P C)) ∧
    modularTimeDeriv P A C (unipotentExpPlus P A) = (2 : ℤ) • (genV P A C * conePlus P A) ∧
    modularTimeDeriv P A C (unipotentExpMinus P C) = -((2 : ℤ) • (genV P A C * coneMinus P C)) ∧
    modularTimeDeriv P A C (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C) ∧
    modularTimeDeriv P A C (genJ P A C) = (2 : ℤ) • (genV P A C * genPhi P A C) ∧
    modularTimeDeriv P A C (genV P A C) = 0 ∧
    modularTimeDeriv P A C (genSig P A C) = 0 ∧
    sigmaSandwichPlus P A C (conePlus P A) =
      ((1 + genV P A C) * (1 + genV P A C)) * conePlus P A ∧
    sigmaSandwichPlus P A C (coneMinus P C) =
      ((1 - genV P A C) * (1 - genV P A C)) * coneMinus P C ∧
    sigmaSandwichMinus P A C (conePlus P A) =
      ((1 - genV P A C) * (1 - genV P A C)) * conePlus P A ∧
    sigmaSandwichMinus P A C (coneMinus P C) =
      ((1 + genV P A C) * (1 + genV P A C)) * coneMinus P C ∧
    sigmaSandwichMinus P A C (sigmaSandwichPlus P A C X) =
      (1 - genV P A C * genV P A C) * X * (1 - genV P A C * genV P A C) := by
  have hD4 := d4_birth_of_fisher_metric_and_berry_skewness_from_gaussians hP A C
  have hA98 := archetype_A98_loxodromic_sigma_sandwich_and_bruhat_actions hP A C X
  have hA99 := archetype_A99_modular_time_and_phase_correlation_exchange hP A C X
  have hModExpPlus :
      modularTimeDeriv P A C (unipotentExpPlus P A) =
        (2 : ℤ) • (genV P A C * conePlus P A) := by
    unfold modularTimeDeriv unipotentExpPlus
    peirce_nf hP
  have hModExpMinus :
      modularTimeDeriv P A C (unipotentExpMinus P C) =
        -((2 : ℤ) • (genV P A C * coneMinus P C)) := by
    unfold modularTimeDeriv unipotentExpMinus
    peirce_nf hP
  exact ⟨hD4.2.2.2.2.1, hD4.2.2.2.2.2.1,
    hA99.2.2.2.1, hA99.2.2.2.2.1, hModExpPlus, hModExpMinus,
    hA99.2.2.2.2.2.1, hA99.2.2.2.2.2.2.1, hA99.2.2.2.2.2.2.2.1, hA99.2.2.2.2.2.2.2.2.1,
    hA98.2.2.1, hA98.2.2.2.1, hA98.2.2.2.2.1, hA98.2.2.2.2.2.1,
    hA98.2.2.2.2.2.2.2.2.2.2.2.2⟩

end StreamIX_AmariBerezinianModularLoxodromic

/-!
## 3. Stream X (`𝔛₄ ≺ 𝔛₅ ≺ 𝔛₆`): Inductive Colimit Continuum (`Ring.DirectLimit G f`) & Projective Dual State Lift of Amari Operator Geometry & the `V₄` Klein Seam
-/

section StreamX_InductiveColimitContinuumAndProjectiveDualLift

/-- **Stage `𝔛₄` Theorem (`x4_continuum_colimit_abelian_exponential_group_homomorphisms_and_gaussians`)**:
Given any directed system of noncommutative operator rings `(G : ι → Type*) [∀ i, Ring (G i)]` with
transition ring homomorphisms `f : ∀ i j, i ≤ j → G i →+* G j`, a colimit/target ring `A_inf`
`[Ring A_inf]` with compatible cocone ring homomorphisms `ι_colim : ∀ i, G i →+* A_inf`
(`∀ i j (hij : i ≤ j) (x : G i), ι_colim j (f i j hij x) = ι_colim i x`), and a stage `i : ι` with
idempotent `P_i * P_i = P_i`:
1. The stage idempotent lifts to a continuum idempotent
   `P_∞ := ι_colim i P_i ∈ A_inf` satisfying `P_∞ * P_∞ = P_∞` and `ι_colim j (f i j hij P_i) = P_∞`.
2. The continuum chiral exponentials form exact group homomorphisms
   `amariExpPlusUnitsHom P_∞ hP_∞ : Multiplicative A_inf →* A_infˣ`
   and `amariExpMinusUnitsHom P_∞ hP_∞`, and commute with `ι_colim i`:
   * `((amariExpPlusUnitsHom P_∞ hP_∞ (Multiplicative.ofAdd (ι_colim i A_i)) : A_infˣ) : A_inf) = ι_colim i (unipotentExpPlus P_i A_i)`,
   * `((amariExpMinusUnitsHom P_∞ hP_∞ (Multiplicative.ofAdd (ι_colim i C_i)) : A_infˣ) : A_inf) = ι_colim i (unipotentExpMinus P_i C_i)`.
3. The Paired Operator Gaussians `𝒢_{±,i}` commute with transition maps `f i j hij` and colimit
   embeddings `ι_colim i`, and satisfy exact degree-2 expansion and polynomial inversion in `A_inf`. -/
theorem x4_continuum_colimit_abelian_exponential_group_homomorphisms_and_gaussians
    {ι : Type*} [Preorder ι]
    (G : ι → Type*) [∀ i, Ring (G i)]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    {A_inf : Type*} [Ring A_inf]
    (ι_colim : ∀ i : ι, G i →+* A_inf)
    (hι_compat : ∀ i j (hij : i ≤ j) (x : G i), ι_colim j (f i j hij x) = ι_colim i x)
    {i j : ι} (hij : i ≤ j)
    (P_i A_i A₁_i A₂_i C_i C₁_i C₂_i : G i) (hP_i : P_i * P_i = P_i) :
    let of_i := ι_colim i
    let P_inf := of_i P_i
    let A_inf_op := of_i A_i
    let C_inf_op := of_i C_i
    P_inf * P_inf = P_inf ∧
    ι_colim j (f i j hij P_i) = P_inf ∧
    (∃ hP_inf : P_inf * P_inf = P_inf,
      ((FirstQuantizedAmariOperatorGeometryPoset.amariExpPlusUnitsHom hP_inf (Multiplicative.ofAdd A_inf_op) :
          A_infˣ) : A_inf) =
        of_i (unipotentExpPlus P_i A_i) ∧
      ((FirstQuantizedAmariOperatorGeometryPoset.amariExpMinusUnitsHom hP_inf (Multiplicative.ofAdd C_inf_op) :
          A_infˣ) : A_inf) =
        of_i (unipotentExpMinus P_i C_i)) ∧
    unipotentExpPlus P_inf (of_i A₁_i) * unipotentExpPlus P_inf (of_i A₂_i) =
      unipotentExpPlus P_inf (of_i A₁_i + of_i A₂_i) ∧
    unipotentExpMinus P_inf (of_i C₁_i) * unipotentExpMinus P_inf (of_i C₂_i) =
      unipotentExpMinus P_inf (of_i C₁_i + of_i C₂_i) ∧
    f i j hij (operatorGaussianPlus P_i A_i C_i) =
      operatorGaussianPlus (f i j hij P_i) (f i j hij A_i) (f i j hij C_i) ∧
    of_i (operatorGaussianPlus P_i A_i C_i) =
      operatorGaussianPlus P_inf A_inf_op C_inf_op ∧
    of_i (operatorGaussianMinus P_i A_i C_i) =
      operatorGaussianMinus P_inf A_inf_op C_inf_op ∧
    operatorGaussianPlus P_inf A_inf_op C_inf_op * operatorGaussianPlusInv P_inf A_inf_op C_inf_op = 1 ∧
    operatorGaussianMinus P_inf A_inf_op C_inf_op * operatorGaussianMinusInv P_inf A_inf_op C_inf_op = 1 := by
  intro of_i P_inf A_inf_op C_inf_op
  have hP_inf : P_inf * P_inf = P_inf := by
    dsimp [P_inf]
    rw [← map_mul, hP_i]
  have hD2 := d2_exact_abelian_exponential_families hP_inf A_inf_op (of_i A₁_i) (of_i A₂_i)
    C_inf_op (of_i C₁_i) (of_i C₂_i) 0
  have hD3 := d3_paired_operator_gaussians_and_polynomial_inversion hP_inf A_inf_op C_inf_op
  refine ⟨hP_inf, hι_compat i j hij P_i, ⟨hP_inf, ?_, ?_⟩, hD2.1, hD2.2.1, ?_, ?_, ?_,
    hD3.2.2.2.2.1, hD3.2.2.2.2.2.2.1⟩
  · change FirstQuantizedAmariOperatorGeometryPoset.amariExpPlus P_inf A_inf_op =
        of_i (unipotentExpPlus P_i A_i)
    unfold FirstQuantizedAmariOperatorGeometryPoset.amariExpPlus unipotentExpPlus conePlus
    simp only [P_inf, A_inf_op, map_add, map_sub, map_mul, map_one]
  · change FirstQuantizedAmariOperatorGeometryPoset.amariExpMinus P_inf C_inf_op =
        of_i (unipotentExpMinus P_i C_i)
    unfold FirstQuantizedAmariOperatorGeometryPoset.amariExpMinus unipotentExpMinus coneMinus
    simp only [P_inf, C_inf_op, map_add, map_sub, map_mul, map_one]
  · unfold operatorGaussianPlus unipotentExpPlus unipotentExpMinus conePlus coneMinus
    simp only [map_mul, map_add, map_sub, map_one]
  · unfold operatorGaussianPlus unipotentExpPlus unipotentExpMinus conePlus coneMinus
    simp only [P_inf, A_inf_op, C_inf_op, map_mul, map_add, map_sub, map_one]
  · unfold operatorGaussianMinus unipotentExpPlus unipotentExpMinus conePlus coneMinus
    simp only [P_inf, A_inf_op, C_inf_op, map_mul, map_add, map_sub, map_one]

/-- **Stage `𝔛₅` Theorem (`x5_continuum_colimit_pythagorean_theorem_and_v4_walsh_hadamard_isolation`)**:
In the continuum colimit ring `A_inf` with lifted Peirce–Klein seam data
`P_∞ = ι_colim i P_i` and `U_∞ = ι_colim i U_i`:
1. **Continuum Operator Pythagorean Theorem**:
   * `qgtPlus P_∞ A_∞ C_∞ * qgtMinus P_∞ A_∞ C_∞ = 0`,
   * `genV P_∞ A_∞ C_∞ * genV P_∞ A_∞ C_∞ = qgtPlus P_∞ A_∞ C_∞ * qgtPlus P_∞ A_∞ C_∞ + qgtMinus P_∞ A_∞ C_∞ * qgtMinus P_∞ A_∞ C_∞`,
   * `genV P_∞ A_∞ C_∞ * genV P_∞ A_∞ C_∞ = genSig P_∞ A_∞ C_∞ * genSig P_∞ A_∞ C_∞`.
2. **Continuum `V₄ = ℤ₂ × ℤ₂` Walsh–Hadamard 4-Sector Resolution & Eigen-Isolation**:
   * `ι_colim i (walshProjPP P_i U_i X_i) = walshProjPP P_∞ U_∞ X_∞`,
   * `walshProjPP P_∞ U_∞ X_∞ + walshProjPM P_∞ U_∞ X_∞ + walshProjMP P_∞ U_∞ X_∞ + walshProjMM P_∞ U_∞ X_∞ = (4 : ℤ) • X_∞`,
   * `walshProjPP P_∞ U_∞ (genV P_∞ A_∞ C_∞) = (4 : ℤ) • genV P_∞ A_∞ C_∞`,
   * `walshProjPM P_∞ U_∞ (genSig P_∞ A_∞ C_∞) = (4 : ℤ) • genSig P_∞ A_∞ C_∞`,
   * `walshProjMP P_∞ U_∞ (genPhi P_∞ A_∞ C_∞) = (4 : ℤ) • genPhi P_∞ A_∞ C_∞`,
   * `walshProjMM P_∞ U_∞ (genJ P_∞ A_∞ C_∞) = (4 : ℤ) • genJ P_∞ A_∞ C_∞`. -/
theorem x5_continuum_colimit_pythagorean_theorem_and_v4_walsh_hadamard_isolation
    {ι : Type*} [Preorder ι]
    (G : ι → Type*) [∀ i, Ring (G i)]
    {A_inf : Type*} [Ring A_inf]
    (ι_colim : ∀ i : ι, G i →+* A_inf)
    (i : ι) (P_i U_i A_i C_i X_i : G i)
    (hP_i : P_i * P_i = P_i) (hU_i2 : U_i * U_i = 1) (hUP_i : U_i * P_i * U_i = 1 - P_i)
    (hUNp_i : U_i * conePlus P_i A_i * U_i = coneMinus P_i C_i)
    (hUNm_i : U_i * coneMinus P_i C_i * U_i = conePlus P_i A_i) :
    let of_i := ι_colim i
    let P_inf := of_i P_i
    let U_inf := of_i U_i
    let A_inf_op := of_i A_i
    let C_inf_op := of_i C_i
    let X_inf_op := of_i X_i
    qgtPlus P_inf A_inf_op C_inf_op * qgtMinus P_inf A_inf_op C_inf_op = 0 ∧
    genV P_inf A_inf_op C_inf_op * genV P_inf A_inf_op C_inf_op =
      qgtPlus P_inf A_inf_op C_inf_op * qgtPlus P_inf A_inf_op C_inf_op +
        qgtMinus P_inf A_inf_op C_inf_op * qgtMinus P_inf A_inf_op C_inf_op ∧
    genV P_inf A_inf_op C_inf_op * genV P_inf A_inf_op C_inf_op =
      genSig P_inf A_inf_op C_inf_op * genSig P_inf A_inf_op C_inf_op ∧
    of_i (walshProjPP P_i U_i X_i) = walshProjPP P_inf U_inf X_inf_op ∧
    walshProjPP P_inf U_inf X_inf_op + walshProjPM P_inf U_inf X_inf_op +
        walshProjMP P_inf U_inf X_inf_op + walshProjMM P_inf U_inf X_inf_op =
      (4 : ℤ) • X_inf_op ∧
    walshProjPP P_inf U_inf (genV P_inf A_inf_op C_inf_op) = (4 : ℤ) • genV P_inf A_inf_op C_inf_op ∧
    walshProjPM P_inf U_inf (genSig P_inf A_inf_op C_inf_op) = (4 : ℤ) • genSig P_inf A_inf_op C_inf_op ∧
    walshProjMP P_inf U_inf (genPhi P_inf A_inf_op C_inf_op) = (4 : ℤ) • genPhi P_inf A_inf_op C_inf_op ∧
    walshProjMM P_inf U_inf (genJ P_inf A_inf_op C_inf_op) = (4 : ℤ) • genJ P_inf A_inf_op C_inf_op := by
  intro of_i P_inf U_inf A_inf_op C_inf_op X_inf_op
  have hP_inf : P_inf * P_inf = P_inf := by dsimp [P_inf]; rw [← map_mul, hP_i]
  have hU_inf2 : U_inf * U_inf = 1 := by dsimp [U_inf]; rw [← map_mul, hU_i2, map_one]
  have hUP_inf : U_inf * P_inf * U_inf = 1 - P_inf := by
    dsimp [U_inf, P_inf]; rw [← map_mul, ← map_mul, hUP_i, map_sub, map_one]
  have hUNp_inf : U_inf * conePlus P_inf A_inf_op * U_inf = coneMinus P_inf C_inf_op := by
    have h1 : conePlus P_inf A_inf_op = of_i (conePlus P_i A_i) := by
      unfold conePlus; simp only [P_inf, A_inf_op, map_mul, map_sub, map_one]
    have h2 : coneMinus P_inf C_inf_op = of_i (coneMinus P_i C_i) := by
      unfold coneMinus; simp only [P_inf, C_inf_op, map_mul, map_sub, map_one]
    rw [h1, h2]
    dsimp [U_inf]
    rw [← map_mul, ← map_mul, hUNp_i]
  have hUNm_inf : U_inf * coneMinus P_inf C_inf_op * U_inf = conePlus P_inf A_inf_op := by
    have h1 : conePlus P_inf A_inf_op = of_i (conePlus P_i A_i) := by
      unfold conePlus; simp only [P_inf, A_inf_op, map_mul, map_sub, map_one]
    have h2 : coneMinus P_inf C_inf_op = of_i (coneMinus P_i C_i) := by
      unfold coneMinus; simp only [P_inf, C_inf_op, map_mul, map_sub, map_one]
    rw [h1, h2]
    dsimp [U_inf]
    rw [← map_mul, ← map_mul, hUNm_i]
  have hBetaQp : U_inf * qgtPlus P_inf A_inf_op C_inf_op * U_inf = qgtMinus P_inf A_inf_op C_inf_op := by
    unfold qgtPlus qgtMinus
    calc U_inf * (conePlus P_inf A_inf_op * coneMinus P_inf C_inf_op) * U_inf
      _ = (U_inf * conePlus P_inf A_inf_op * 1) * coneMinus P_inf C_inf_op * U_inf := by noncomm_ring
      _ = (U_inf * conePlus P_inf A_inf_op * (U_inf * U_inf)) * coneMinus P_inf C_inf_op * U_inf := by
            rw [hU_inf2]
      _ = (U_inf * conePlus P_inf A_inf_op * U_inf) * (U_inf * coneMinus P_inf C_inf_op * U_inf) := by
            noncomm_ring
      _ = coneMinus P_inf C_inf_op * conePlus P_inf A_inf_op := by rw [hUNp_inf, hUNm_inf]
  have hUWT : U_inf * sheetPlusConnection P_inf (genV P_inf A_inf_op C_inf_op) * U_inf =
      sheetMinusConnection P_inf (genV P_inf A_inf_op C_inf_op) := by
    have hPl : sheetPlusConnection P_inf (genV P_inf A_inf_op C_inf_op) = qgtPlus P_inf A_inf_op C_inf_op := by
      unfold sheetPlusConnection qgtPlus; peirce_nf hP_inf
    have hMi : sheetMinusConnection P_inf (genV P_inf A_inf_op C_inf_op) = qgtMinus P_inf A_inf_op C_inf_op := by
      unfold sheetMinusConnection qgtMinus; peirce_nf hP_inf
    rw [hPl, hMi]
    exact hBetaQp
  have hD6 := d6_operator_pythagorean_theorem_and_orthogonal_gramians hP_inf A_inf_op C_inf_op
  have hWalsh := walsh_hadamard_four_sector_resolution hP_inf hU_inf2 hUP_inf
    (genV P_inf A_inf_op C_inf_op) A_inf_op C_inf_op X_inf_op hUWT hUNp_inf hUNm_inf
  have hEndo := endogenous_dewitt_gramian_spin_frame_dragging hP_inf A_inf_op C_inf_op
  refine ⟨hD6.1, hD6.2.2.2.2.2.2.1, hD6.2.2.2.2.2.2.2.2.1, ?_,
    hWalsh.1,
    ?_, ?_, hWalsh.2.2.2.1.1, hWalsh.2.2.2.2.1⟩
  · unfold walshProjPP kleinAlpha kleinBeta kleinGamma invS
    simp only [P_inf, U_inf, X_inf_op, map_add, map_sub, map_mul, map_one]
  · rw [← hEndo.1.2.2.1]; exact hWalsh.2.1.1
  · rw [← hEndo.1.2.2.2]; exact hWalsh.2.2.1.1

/-- **Stage `𝔛₆` Theorem (`x6_projective_dual_state_colimit_trace_blindness_and_supertrace_recovery`)**:
Given a directed system of `R`-algebras `(Stage : I → Type u)` and an inverse-compatible family of
cyclic `R`-linear stage traces `phi : ∀ i, Stage i →ₗ[R] R`
(`IsDualInverseFamily (sys := algTowerToDirectSystem R Stage f hf_id hf_comp) phi`,
`∀ i x y, phi i (x * y) = phi i (y * x)`):
1. Both the categorical colimit readout `dualInverseFamilyColimitMap` and the categorical
   projective-limit readout `dualInverseFamilyToProjectiveLimit` evaluate on any stage `i`
   observable `x : Stage i` to `phi i x`.
2. **Continuum & Projective-Limit Trace-First Blindness**:
   For every `k : ℕ`, both the colimit state and projective-limit state vanish on
   `genSig P_i A_i C_i * (genV P_i A_i C_i ^ k)` and on `invS P_i * (genV P_i A_i C_i ^ (k + 1))`.
3. **Continuum & Projective-Limit Chiral Supertrace Recovery**:
   For every `k : ℕ`, evaluating the colimit state (and projective-limit state) on the
   chiral-weighted skewness moment `invS P_i * (genSig P_i A_i C_i * (genV P_i A_i C_i ^ k))`
   recovers the `(k + 1)`-st Fisher–BKM trace moment `phi i (genV P_i A_i C_i ^ (k + 1)) =
   (2 : ℤ) • phi i (qgtPlus P_i A_i C_i ^ (k + 1))`. -/
theorem x6_projective_dual_state_colimit_trace_blindness_and_supertrace_recovery
    {R : Type u} [CommRing R]
    {I : Type u} [Preorder I]
    (Stage : I → Type u) [∀ i, Ring (Stage i)] [∀ i, Algebra R (Stage i)]
    (f : ∀ {i j : I}, i ≤ j → Stage i →ₐ[R] Stage j)
    (hf_id : ∀ i : I, f (le_refl i) = AlgHom.id R (Stage i))
    (hf_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
      (f hjk).comp (f hij) = f (le_trans hij hjk))
    (phi : ∀ i : I, Stage i →ₗ[R] R)
    (hphi : IsDualInverseFamily
      (sys := algTowerToDirectSystem R Stage f hf_id hf_comp) phi)
    (hphi_cyclic : ∀ (i : I) (x y : Stage i), phi i (x * y) = phi i (y * x))
    (i : I) (P_i A_i C_i : Stage i) (hP_i : P_i * P_i = P_i) (k : ℕ) :
    let sys := algTowerToDirectSystem R Stage f hf_id hf_comp
    (dualInverseFamilyColimitMap (sys := sys) phi hphi).hom
        ((colimit.ι (moduleDiagram sys) i).hom
          (genSig P_i A_i C_i * (genV P_i A_i C_i ^ k))) = 0 ∧
    (dualInverseFamilyColimitMap (sys := sys) phi hphi).hom
        ((colimit.ι (moduleDiagram sys) i).hom
          (invS P_i * (genV P_i A_i C_i ^ (k + 1)))) = 0 ∧
    (dualInverseFamilyColimitMap (sys := sys) phi hphi).hom
        ((colimit.ι (moduleDiagram sys) i).hom
          (invS P_i * (genSig P_i A_i C_i * (genV P_i A_i C_i ^ k)))) =
      phi i (genV P_i A_i C_i ^ (k + 1)) ∧
    ((dualInverseFamilyToProjectiveLimit (sys := sys) phi hphi ≫
        limit.π (dualModuleDiagram sys) (Opposite.op i)).hom (1 : R))
        (invS P_i * (genSig P_i A_i C_i * (genV P_i A_i C_i ^ k))) =
      phi i (genV P_i A_i C_i ^ (k + 1)) ∧
    phi i (genV P_i A_i C_i ^ (k + 1)) =
      (2 : ℤ) • phi i (qgtPlus P_i A_i C_i ^ (k + 1)) := by
  intro sys
  have hX2 := x2_chiral_supertrace_berezinian_moment_hierarchy
    (phi i).toAddMonoidHom (hphi_cyclic i) hP_i A_i C_i k
  have hC23 :=
    stage_C2_C3_inductive_colimit_state_to_projective_dual_limit_bridge
      sys phi hphi (dualInverseFamilyColimitMap (sys := sys) phi hphi) i
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [dualInverseFamilyColimitMap_stage]
    exact hX2.2.2.2.2.2.2.1
  · rw [dualInverseFamilyColimitMap_stage]
    exact hX2.2.2.2.2.2.1
  · rw [dualInverseFamilyColimitMap_stage]
    exact hX2.2.2.2.2.2.2.2.1
  · rw [(hC23 (invS P_i * (genSig P_i A_i C_i * (genV P_i A_i C_i ^ k)))).1]
    exact hX2.2.2.2.2.2.2.2.1
  · have hEq := hX2.2.2.2.2.2.2.2.1.symm.trans hX2.2.2.2.2.2.2.2.2
    exact hEq

end StreamX_InductiveColimitContinuumAndProjectiveDualLift

/-!
## 4. Analytical Closure (`𝔛₇ ≺ 𝔛₈`): Norm-Convergent `N → ∞` Operator Power Series & Smooth Fréchet/Time Holonomy Calculus (`HasDerivAt`)
-/

section AnalyticNormSeriesAndSmoothHolonomyClosure

/-- The `n`-th term `(1 / (n + 1)) • V ^ (n + 1)` of the para-Kähler logarithmic
potential `-log(1 - V)`, indexed from `n = 0`. -/
def paraKahlerSeriesTerm {B : Type*} [Ring B] [Module ℝ B] (V : B) (n : ℕ) : B :=
  ((1 : ℝ) / ((n : ℝ) + 1)) • (V ^ (n + 1))

/-- The `n`-th term of the operator Bregman series, matching the existing finite-stage
coefficient `(k - 1) / k` after reindexing with `k = n + 1`. -/
def bregmanMinusSeriesTerm {B : Type*} [Ring B] [Module ℝ B] (V : B) (n : ℕ) : B :=
  V ^ (n + 1) - paraKahlerSeriesTerm V n

/-- The infinite norm-convergent operator para-Kähler potential `∑' n : ℕ, paraKahlerSeriesTerm V n`. -/
def paraKahlerPotentialTsum {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] (V : B) : B :=
  ∑' n : ℕ, paraKahlerSeriesTerm V n

/-- The infinite norm-convergent operator Bregman divergence `∑' n : ℕ, bregmanMinusSeriesTerm V n`. -/
def bregmanMinusDivergenceTsum {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] (V : B) : B :=
  ∑' n : ℕ, bregmanMinusSeriesTerm V n

/-- On the scalar real algebra, the operator-series definition specializes to the
Mercator expansion of the para-Kähler potential. -/
theorem scalar_paraKahlerPotentialTsum_eq_neg_log {v : ℝ} (hv : |v| < 1) :
    paraKahlerPotentialTsum v = -Real.log (1 - v) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one hv
  have h' : HasSum (paraKahlerSeriesTerm v) (-Real.log (1 - v)) := by
    convert h using 1
    funext n
    simp [paraKahlerSeriesTerm, div_eq_mul_inv, mul_comm]
  exact h'.tsum_eq

/-- **Stage `𝔛₇` Theorem (`x7_analytic_norm_convergent_resolvent_and_bregman_power_series`)**:
Closes the `N → ∞` analytical convergence gap in any complete normed algebra
`[NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]` for any operator `V : B` with `‖V‖ < 1`:
1. **Exact Norm-Convergent Geometric Resolvent Series**:
   * `Summable (fun n : ℕ => V ^ n)` and `HasSum (fun n : ℕ => V ^ n) (Ring.inverse (1 - V))`,
   * `(1 - V) * (∑' n : ℕ, V ^ n) = 1` and `(∑' n : ℕ, V ^ n) * (1 - V) = 1`,
   * `∑' n : ℕ, V ^ (n + 1) = V * (∑' n : ℕ, V ^ n)`.
2. **Exact Norm-Convergence (`N → ∞`) of the Infinite Para-Kähler & Bregman Series**:
   * `Summable (paraKahlerSeriesTerm V)` and `HasSum (paraKahlerSeriesTerm V) (paraKahlerPotentialTsum V)`,
   * `Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, paraKahlerSeriesTerm V n) Filter.atTop (𝓝 (paraKahlerPotentialTsum V))`,
   * `Summable (bregmanMinusSeriesTerm V)` and
     `bregmanMinusDivergenceTsum V = V * (∑' n : ℕ, V ^ n) - paraKahlerPotentialTsum V`.
3. **Exact Agreement with the Existing Finite Bregman Coefficients**:
   * For every `m : ℕ`, `bregmanMinusSeriesTerm V m = ((m : ℝ) / ((m : ℝ) + 1)) • V ^ (m + 1)`. -/
theorem x7_analytic_norm_convergent_resolvent_and_bregman_power_series
    {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
    {V : B} (hV : ‖V‖ < 1) (m : ℕ) :
    Summable (fun n : ℕ => V ^ n) ∧
    HasSum (fun n : ℕ => V ^ n) (Ring.inverse (1 - V)) ∧
    (1 - V) * (∑' n : ℕ, V ^ n) = 1 ∧
    (∑' n : ℕ, V ^ n) * (1 - V) = 1 ∧
    (∑' n : ℕ, V ^ (n + 1)) = V * (∑' n : ℕ, V ^ n) ∧
    Summable (paraKahlerSeriesTerm V) ∧
    HasSum (paraKahlerSeriesTerm V) (paraKahlerPotentialTsum V) ∧
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, paraKahlerSeriesTerm V n)
      Filter.atTop (nhds (paraKahlerPotentialTsum V)) ∧
    Summable (bregmanMinusSeriesTerm V) ∧
    bregmanMinusDivergenceTsum V = V * (∑' n : ℕ, V ^ n) - paraKahlerPotentialTsum V ∧
    bregmanMinusSeriesTerm V m = ((m : ℝ) / ((m : ℝ) + 1)) • V ^ (m + 1) := by
  have hSumGeom : Summable (fun n : ℕ => V ^ n) := summable_geometric_of_norm_lt_one hV
  have hHasSumGeom : HasSum (fun n : ℕ => V ^ n) (Ring.inverse (1 - V)) :=
    hasSum_geom_series_inverse V hV
  have hMulLeft : (1 - V) * (∑' n : ℕ, V ^ n) = 1 := mul_neg_geom_series V hV
  have hMulRight : (∑' n : ℕ, V ^ n) * (1 - V) = 1 := geom_series_mul_neg V hV
  have hShift : (∑' n : ℕ, V ^ (n + 1)) = V * (∑' n : ℕ, V ^ n) :=
    (geom_series_mul_shift V hV).symm
  have hNormGeomShift : Summable (fun n : ℕ => ‖V‖ ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg V) hV)
  have hSumPK : Summable (paraKahlerSeriesTerm V) := by
    refine hNormGeomShift.of_norm_bounded (fun n => ?_)
    unfold paraKahlerSeriesTerm
    have hPos1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hCoeffNonneg : 0 ≤ (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    have hCoeffLeOne : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hPos1]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    calc
      ‖((1 : ℝ) / ((n : ℝ) + 1)) • (V ^ (n + 1))‖
        = ‖(1 : ℝ) / ((n : ℝ) + 1)‖ * ‖V ^ (n + 1)‖ := norm_smul _ _
      _ = ((1 : ℝ) / ((n : ℝ) + 1)) * ‖V ^ (n + 1)‖ := by
          rw [Real.norm_of_nonneg hCoeffNonneg]
      _ ≤ 1 * ‖V‖ ^ (n + 1) := by
          gcongr
          exact norm_pow_le' V (Nat.succ_pos n)
      _ = ‖V‖ ^ (n + 1) := one_mul _
  have hHasSumPK : HasSum (paraKahlerSeriesTerm V) (paraKahlerPotentialTsum V) :=
    hSumPK.hasSum
  have hTendstoPK :
      Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, paraKahlerSeriesTerm V n)
        Filter.atTop (nhds (paraKahlerPotentialTsum V)) :=
    hHasSumPK.tendsto_sum_nat
  have hSumShift : Summable (fun n : ℕ => V ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr hSumGeom
  have hSumBreg : Summable (bregmanMinusSeriesTerm V) :=
    hSumShift.sub hSumPK
  have hTsumBreg :
      bregmanMinusDivergenceTsum V = V * (∑' n : ℕ, V ^ n) - paraKahlerPotentialTsum V := by
    unfold bregmanMinusDivergenceTsum bregmanMinusSeriesTerm paraKahlerPotentialTsum
    rw [hSumShift.tsum_sub hSumPK, hShift]
  have hCoeff : 1 - (1 : ℝ) / ((m : ℝ) + 1) =
      (m : ℝ) / ((m : ℝ) + 1) := by
    have h1 : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  have hTerm : bregmanMinusSeriesTerm V m =
      ((m : ℝ) / ((m : ℝ) + 1)) • V ^ (m + 1) := by
    unfold bregmanMinusSeriesTerm paraKahlerSeriesTerm
    calc
      V ^ (m + 1) - (1 / ((m : ℝ) + 1)) • V ^ (m + 1)
          = (1 : ℝ) • V ^ (m + 1) - (1 / ((m : ℝ) + 1)) • V ^ (m + 1) := by simp
      _ = (1 - (1 : ℝ) / ((m : ℝ) + 1)) • V ^ (m + 1) := by rw [← sub_smul]
      _ = ((m : ℝ) / ((m : ℝ) + 1)) • V ^ (m + 1) := by rw [hCoeff]
  exact ⟨hSumGeom, hHasSumGeom, hMulLeft, hMulRight, hShift,
    hSumPK, hHasSumPK, hTendstoPK, hSumBreg, hTsumBreg, hTerm⟩

/-- A continuous real trace with nonnegative power moments evaluates the convergent
operator Bregman series nonnegatively. Positivity is conditional on the moment
hypothesis; the algebra structure alone does not provide an order on operators. -/
theorem bregmanMinusDivergenceTsum_trace_nonneg
    {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
    (τ : B →L[ℝ] ℝ) {V : B} (hV : ‖V‖ < 1)
    (hMom : ∀ n : ℕ, 0 ≤ τ (V ^ (n + 1))) :
    0 ≤ τ (bregmanMinusDivergenceTsum V) := by
  rcases x7_analytic_norm_convergent_resolvent_and_bregman_power_series
      (V := V) hV 0 with
    ⟨_, _, _, _, _, _, _, _, hSeries, _, _⟩
  have hTermNonneg (n : ℕ) : 0 ≤ τ (bregmanMinusSeriesTerm V n) := by
    rcases x7_analytic_norm_convergent_resolvent_and_bregman_power_series
        (V := V) hV n with
      ⟨_, _, _, _, _, _, _, _, _, _, hExact⟩
    rw [hExact, map_smul]
    apply mul_nonneg
    · apply div_nonneg
      · exact_mod_cast Nat.zero_le n
      · positivity
    · exact hMom n
  have hTsumNonneg :
      0 ≤ ∑' n : ℕ, τ (bregmanMinusSeriesTerm V n) :=
    tsum_nonneg (fun n => hTermNonneg n)
  calc
    0 ≤ ∑' n : ℕ, τ (bregmanMinusSeriesTerm V n) := hTsumNonneg
    _ = τ (∑' n : ℕ, bregmanMinusSeriesTerm V n) :=
      (ContinuousLinearMap.map_tsum τ hSeries).symm
    _ = τ (bregmanMinusDivergenceTsum V) := rfl

/-- Concrete finite-dimensional positivity instance: if a real matrix `V` is
positive semidefinite and has norm below one, every power moment under the ordinary
matrix trace is nonnegative, so the norm-convergent operator Bregman series has
nonnegative trace. -/
theorem matrix_trace_bregmanMinusDivergenceTsum_nonneg
    {n : Type*} [Fintype n] [DecidableEq n]
    (V : Matrix n n ℝ) (hVpsd : V.PosSemidef) (hVnorm : ‖V‖ < 1) :
    0 ≤ Matrix.trace (bregmanMinusDivergenceTsum V) := by
  let τ : Matrix n n ℝ →L[ℝ] ℝ :=
    (Matrix.traceLinearMap n ℝ ℝ).toContinuousLinearMap
  have hMom : ∀ k : ℕ, 0 ≤ τ (V ^ (k + 1)) := by
    intro k
    change 0 ≤ Matrix.trace (V ^ (k + 1))
    exact (hVpsd.pow (k + 1)).trace_nonneg
  have hTrace := bregmanMinusDivergenceTsum_trace_nonneg
    (τ := τ) (V := V) hVnorm hMom
  change 0 ≤ τ (bregmanMinusDivergenceTsum V)
  exact hTrace

/-- Complex-matrix version of the trace positivity result. The scalar field `ℂ`
has no compatible linear order, so positivity is stated through the explicit
real-part power-moment hypothesis rather than an ill-typed `PosSemidef` claim. -/
theorem complex_matrix_realTrace_bregmanMinusDivergenceTsum_nonneg
    {n : Type*} [Fintype n] [DecidableEq n]
    (V : Matrix n n ℂ) (hVnorm : ‖V‖ < (1 : ℝ))
    (hMom : ∀ k : ℕ, 0 ≤ (Matrix.trace (V ^ (k + 1))).re) :
    0 ≤ (Matrix.trace (bregmanMinusDivergenceTsum V)).re := by
  let τ : Matrix n n ℂ →L[ℝ] ℝ :=
    Complex.reCLM.comp (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap
  have hMom' : ∀ k : ℕ, 0 ≤ τ (V ^ (k + 1)) := by
    intro k
    exact hMom k
  have hTrace := bregmanMinusDivergenceTsum_trace_nonneg
    (τ := τ) (V := V) hVnorm hMom'
  change 0 ≤ τ (bregmanMinusDivergenceTsum V)
  exact hTrace

/-- The tangent velocity `d/dθ R_P(θ) = (-sin θ) • 1 + (cos θ) • S_P` of the continuous
Berry rotor `berryRotor P θ = cos θ • 1 + sin θ • S_P`. -/
def berryRotorDeriv {B : Type*} [Ring B] [Algebra ℝ B] (P : B) (θ : ℝ) : B :=
  (-Real.sin θ) • (1 : B) + Real.cos θ • invS P

/-- **Stage `𝔛₈` Theorem (`x8_analytic_smooth_berry_rotor_and_hyperplane_holonomy_flow_calculus`)**:
Closes the smooth analytical holonomy differential calculus (`HasDerivAt`) gap in any normed
algebra `[NormedRing B] [NormedAlgebra ℝ B]` with idempotent `P * P = P`:
1. **Exact Fréchet/Time Differentiability (`HasDerivAt`) over `ℝ`**:
   * `HasDerivAt (berryRotor P) (berryRotorDeriv P θ) θ`,
   * `HasDerivAt (rotatedCurrentJ P A C) (berryRotorDeriv P θ * genJ P A C) θ`,
   * `HasDerivAt (rotatedBridgePhi P A C) (berryRotorDeriv P θ * genPhi P A C) θ`.
2. **Exact Chiral Maurer–Cartan & Hyperplane Transport ODEs**:
   * `berryRotorDeriv P θ = invS P * berryRotor P (-θ)`,
   * `berryRotorDeriv P θ * genJ P A C = rotatedBridgePhi P A C (-θ)`,
   * `berryRotorDeriv P θ * genPhi P A C = rotatedCurrentJ P A C (-θ)`,
   * `HasDerivAt (rotatedCurrentJ P A C) (rotatedBridgePhi P A C (-θ)) θ`,
   * `HasDerivAt (rotatedBridgePhi P A C) (rotatedCurrentJ P A C (-θ)) θ`.
3. **Initial Holonomy Velocity (`θ = 0`) & Global Hyperplane Square Conservation**:
   * `HasDerivAt (berryRotor P) (invS P) 0`,
   * `HasDerivAt (rotatedCurrentJ P A C) (genPhi P A C) 0`,
   * `HasDerivAt (rotatedBridgePhi P A C) (genJ P A C) 0`,
   * For every `θ : ℝ`,
     `rotatedCurrentJ P A C θ * rotatedCurrentJ P A C θ + rotatedBridgePhi P A C θ * rotatedBridgePhi P A C θ = 0`. -/
theorem x8_analytic_smooth_berry_rotor_and_hyperplane_holonomy_flow_calculus
    {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]
    {P : B} (hP : P * P = P) (A C : B) (θ : ℝ) :
    HasDerivAt (berryRotor P) (berryRotorDeriv P θ) θ ∧
    HasDerivAt (rotatedCurrentJ P A C) (berryRotorDeriv P θ * genJ P A C) θ ∧
    HasDerivAt (rotatedBridgePhi P A C) (berryRotorDeriv P θ * genPhi P A C) θ ∧
    berryRotorDeriv P θ = invS P * berryRotor P (-θ) ∧
    berryRotorDeriv P θ * genJ P A C = rotatedBridgePhi P A C (-θ) ∧
    berryRotorDeriv P θ * genPhi P A C = rotatedCurrentJ P A C (-θ) ∧
    HasDerivAt (rotatedCurrentJ P A C) (rotatedBridgePhi P A C (-θ)) θ ∧
    HasDerivAt (rotatedBridgePhi P A C) (rotatedCurrentJ P A C (-θ)) θ ∧
    HasDerivAt (berryRotor P) (invS P) 0 ∧
    HasDerivAt (rotatedCurrentJ P A C) (genPhi P A C) 0 ∧
    HasDerivAt (rotatedBridgePhi P A C) (genJ P A C) 0 ∧
    rotatedCurrentJ P A C θ * rotatedCurrentJ P A C θ +
      rotatedBridgePhi P A C θ * rotatedBridgePhi P A C θ = 0 := by
  have hDerivRotor : ∀ t : ℝ, HasDerivAt (berryRotor P) (berryRotorDeriv P t) t := by
    intro t
    unfold berryRotor berryRotorDeriv
    exact ((Real.hasDerivAt_cos t).smul_const (1 : B)).add
      ((Real.hasDerivAt_sin t).smul_const (invS P))
  have hDerivJ : ∀ t : ℝ,
      HasDerivAt (rotatedCurrentJ P A C) (berryRotorDeriv P t * genJ P A C) t := by
    intro t
    unfold rotatedCurrentJ
    exact (hDerivRotor t).mul_const (genJ P A C)
  have hDerivPhi : ∀ t : ℝ,
      HasDerivAt (rotatedBridgePhi P A C) (berryRotorDeriv P t * genPhi P A C) t := by
    intro t
    unfold rotatedBridgePhi
    exact (hDerivRotor t).mul_const (genPhi P A C)
  have hS2 : invS P * invS P = 1 := by peirce_nf hP
  have hSJ : invS P * genJ P A C = genPhi P A C := by peirce_nf hP
  have hSPhi : invS P * genPhi P A C = genJ P A C := by peirce_nf hP
  have hMC : ∀ t : ℝ, berryRotorDeriv P t = invS P * berryRotor P (-t) := by
    intro t
    unfold berryRotorDeriv berryRotor
    rw [Real.cos_neg, Real.sin_neg, mul_add, mul_smul_comm, mul_smul_comm,
        mul_one, hS2, neg_smul, add_comm]
  have hVelJ : ∀ t : ℝ, berryRotorDeriv P t * genJ P A C = rotatedBridgePhi P A C (-t) := by
    intro t
    unfold berryRotorDeriv rotatedBridgePhi berryRotor
    rw [Real.cos_neg, Real.sin_neg, add_mul, add_mul,
        smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc,
        one_mul, one_mul, hSJ, hSPhi, add_comm]
  have hVelPhi : ∀ t : ℝ, berryRotorDeriv P t * genPhi P A C = rotatedCurrentJ P A C (-t) := by
    intro t
    unfold berryRotorDeriv rotatedCurrentJ berryRotor
    rw [Real.cos_neg, Real.sin_neg, add_mul, add_mul,
        smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc,
        one_mul, one_mul, hSJ, hSPhi, add_comm]
  have hDerivJ_ode : HasDerivAt (rotatedCurrentJ P A C) (rotatedBridgePhi P A C (-θ)) θ := by
    rw [← hVelJ θ]
    exact hDerivJ θ
  have hDerivPhi_ode : HasDerivAt (rotatedBridgePhi P A C) (rotatedCurrentJ P A C (-θ)) θ := by
    rw [← hVelPhi θ]
    exact hDerivPhi θ
  have hRotor0 : berryRotorDeriv P 0 = invS P := by
    unfold berryRotorDeriv
    simp
  have hDerivRotor0 : HasDerivAt (berryRotor P) (invS P) 0 := by
    rw [← hRotor0]
    exact hDerivRotor 0
  have hDerivJ0 : HasDerivAt (rotatedCurrentJ P A C) (genPhi P A C) 0 := by
    have h0 : berryRotorDeriv P 0 * genJ P A C = genPhi P A C := by
      rw [hRotor0, hSJ]
    rw [← h0]
    exact hDerivJ 0
  have hDerivPhi0 : HasDerivAt (rotatedBridgePhi P A C) (genJ P A C) 0 := by
    have h0 : berryRotorDeriv P 0 * genPhi P A C = genJ P A C := by
      rw [hRotor0, hSPhi]
    rw [← h0]
    exact hDerivPhi 0
  have hW7 := stage_W7_trigonometric_berry_rotor_and_wick_transmutation hP A C θ
  have hSumSq :
      rotatedCurrentJ P A C θ * rotatedCurrentJ P A C θ +
        rotatedBridgePhi P A C θ * rotatedBridgePhi P A C θ = 0 := by
    rw [hW7.2.1.1, hW7.2.1.2, neg_smul, neg_add_cancel]
  exact ⟨hDerivRotor θ, hDerivJ θ, hDerivPhi θ, hMC θ, hVelJ θ, hVelPhi θ,
    hDerivJ_ode, hDerivPhi_ode, hDerivRotor0, hDerivJ0, hDerivPhi0, hSumSq⟩

end AnalyticNormSeriesAndSmoothHolonomyClosure

/-!
## 5. Master Synthesis (`𝔛₁ ≺ 𝔛₂ ≺ 𝔛₃ ≺ 𝔛₄ ≺ 𝔛₅ ≺ 𝔛₆ ≺ 𝔛₇ ≺ 𝔛₈`)
-/

/-- **Master Synthesis Theorem (`amari_berezinian_modular_colimit_analytic_closure_master_synthesis`)**:
Unifies all 8 stages (`𝔛₁ ≺ 𝔛₂ ≺ ⋯ ≺ 𝔛₈`):
1. Strict acyclicity and cardinality `8` of `AmariBerezinianColimitAnalyticStage`,
2. **Stage `𝔛₁`**: Amari unipotent LDU/UDL block diagonalization of `1 + Φ - Q_∓` into
   `(P - Q₊) + ((1 - P) - Q₋) = 1 - V` and of `𝒢_±` into `1 ± Σ`,
3. **Stage `𝔛₂`**: Universal higher-moment Chiral Supertrace recovery
   `chiralSupertrace tr P (genV P A C ^ (k + 1)) = 0` vs.
   `chiralSupertrace tr P (genSig P A C * (genV P A C ^ k)) = tr (genV P A C ^ (k + 1))`,
4. **Stage `𝔛₃`**: Tomita–Takesaki modular derivation `modularTimeDeriv P A C (conePlus P A) = 2 • (V * N₊)`
   and loxodromic `Σ`-sandwich scaling `sigmaSandwichPlus P A C (conePlus P A) = (1 + V)² * N₊`,
5. **Stages `𝔛₄` & `𝔛₅`**: Inductive colimit continuum lifting (`Ring.DirectLimit G f`) of the
   Paired Operator Gaussians, Operator Pythagorean Theorem, and `V₄` Walsh–Hadamard sector
   resolution,
6. **Stage `𝔛₇`**: Norm-convergent `N → ∞` geometric resolvent `(1 - V_norm) * ∑' n, V_norm ^ n = 1`,
   norm-summability of `paraKahlerSeriesTerm V_norm`, and infinite-series Bregman decomposition,
7. **Stage `𝔛₈`**: Smooth Fréchet/time differentiability (`HasDerivAt`) of `berryRotor`,
   `rotatedCurrentJ`, and `rotatedBridgePhi` with `d/dθ J(θ) = Φ(-θ)` and `d/dθ Φ(θ) = J(-θ)`. -/
theorem amari_berezinian_modular_colimit_analytic_closure_master_synthesis
    {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
    {K : Type*} [AddCommGroup K] (tr : B →+ K)
    (hCyclic : ∀ X Y : B, tr (X * Y) = tr (Y * X))
    {P : B} (hP : P * P = P) (A C X V_norm : B) (hV_norm : ‖V_norm‖ < 1) (k : ℕ) (θ : ℝ)
    {ι : Type*} [Preorder ι]
    (G : ι → Type*) [∀ i, Ring (G i)]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    {A_inf : Type*} [Ring A_inf]
    (ι_colim : ∀ i : ι, G i →+* A_inf)
    (hι_compat : ∀ i j (hij : i ≤ j) (x : G i), ι_colim j (f i j hij x) = ι_colim i x)
    (i : ι) (P_i U_i A_i C_i X_i : G i) (hP_i : P_i * P_i = P_i) :
    let of_i := ι_colim i
    let P_inf := of_i P_i
    let U_inf := of_i U_i
    let A_inf_op := of_i A_i
    let C_inf_op := of_i C_i
    let X_inf_op := of_i X_i
    (∀ st : AmariBerezinianColimitAnalyticStage,
      ¬ Relation.TransGen AmariBerezinianColimitAnalyticStage.causalEdge st st) ∧
    Fintype.card AmariBerezinianColimitAnalyticStage = 8 ∧
    (1 - qgtPlus P A C) * (1 - qgtMinus P A C) =
      (P - qgtPlus P A C) + ((1 - P) - qgtMinus P A C) ∧
    unipotentExpPlus P (-A) * operatorGaussianPlus P A C * unipotentExpMinus P (-C) = 1 ∧
    chiralSupertrace tr P (genV P A C ^ (k + 1)) = 0 ∧
    chiralSupertrace tr P (genSig P A C * (genV P A C ^ k)) = tr (genV P A C ^ (k + 1)) ∧
    modularTimeDeriv P A C (conePlus P A) = (2 : ℤ) • (genV P A C * conePlus P A) ∧
    sigmaSandwichPlus P A C (conePlus P A) =
      ((1 + genV P A C) * (1 + genV P A C)) * conePlus P A ∧
    of_i (operatorGaussianPlus P_i A_i C_i) = operatorGaussianPlus P_inf A_inf_op C_inf_op ∧
    genV P_inf A_inf_op C_inf_op * genV P_inf A_inf_op C_inf_op =
      genSig P_inf A_inf_op C_inf_op * genSig P_inf A_inf_op C_inf_op ∧
    walshProjPP P_inf U_inf X_inf_op + walshProjPM P_inf U_inf X_inf_op +
        walshProjMP P_inf U_inf X_inf_op + walshProjMM P_inf U_inf X_inf_op =
      (4 : ℤ) • X_inf_op ∧
    (1 - V_norm) * (∑' n : ℕ, V_norm ^ n) = 1 ∧
    Summable (paraKahlerSeriesTerm V_norm) ∧
    bregmanMinusDivergenceTsum V_norm =
      V_norm * (∑' n : ℕ, V_norm ^ n) - paraKahlerPotentialTsum V_norm ∧
    HasDerivAt (berryRotor P) (berryRotorDeriv P θ) θ ∧
    HasDerivAt (rotatedCurrentJ P A C) (rotatedBridgePhi P A C (-θ)) θ ∧
    HasDerivAt (rotatedBridgePhi P A C) (rotatedCurrentJ P A C (-θ)) θ := by
  intro of_i P_inf U_inf A_inf_op C_inf_op X_inf_op
  have hX1 := x1_amari_unipotent_ldu_udl_and_schur_block_diagonalization hP A C
  have hX2 := x2_chiral_supertrace_berezinian_moment_hierarchy tr hCyclic hP A C k
  have hX3 := x3_tomita_modular_derivation_and_loxodromic_sigma_sandwich hP A C X
  have hX4 := x4_continuum_colimit_abelian_exponential_group_homomorphisms_and_gaussians
    G f ι_colim hι_compat (le_refl i) P_i A_i A_i A_i C_i C_i C_i hP_i
  have hP_inf : P_inf * P_inf = P_inf := hX4.1
  have hD6_inf := d6_operator_pythagorean_theorem_and_orthogonal_gramians hP_inf A_inf_op C_inf_op
  have hX7 := x7_analytic_norm_convergent_resolvent_and_bregman_power_series hV_norm k
  have hX8 := x8_analytic_smooth_berry_rotor_and_hyperplane_holonomy_flow_calculus hP A C θ
  exact ⟨AmariBerezinianColimitAnalyticStage.causalEdge_acyclic,
    AmariBerezinianColimitAnalyticStage.strict_eight_stage_chain.2.2.2.2.2.2.2,
    hX1.2.2.2.2.2.2.2.1,
    hX1.2.2.2.2.2.2.2.2.2.2.2.1,
    hX2.2.2.2.2.2.1,
    hX2.2.2.2.2.2.2.2.1,
    hX3.2.2.1,
    hX3.2.2.2.2.2.2.2.2.2.2.1,
    hX4.2.2.2.2.2.2.1,
    hD6_inf.2.2.2.2.2.2.2.2.1,
    by unfold walshProjPP walshProjPM walshProjMP walshProjMM; noncomm_ring,
    hX7.2.2.1,
    hX7.2.2.2.2.2.1,
    hX7.2.2.2.2.2.2.2.2.2.1,
    hX8.1,
    hX8.2.2.2.2.2.2.1,
    hX8.2.2.2.2.2.2.2.1⟩

end InfoGeometry.Canonical.AmariBerezinianModularColimitAnalyticClosurePoset
