/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.OntologyRing
import InfoGeometry.Meta.Architecture
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectTower
import InfoGeometry.OperatorAlgebra.PeirceSpine.Homogenized
import InfoGeometry.OperatorAlgebra.PeirceSpine.EpistemicCompilerPeirceBridge
import InfoGeometry.Canonical.CausalHyperplaneBerryHolonomy
import InfoGeometry.Canonical.SupergradedMoebiusTetraktysKleinQuotientBerezinianWeylPoset
import InfoGeometry.Canonical.ModularSurprisalQuadraticLogVolume
import InfoGeometry.OperatorAlgebra.OperatorDirichlet.Resolvent
import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.Nilpotent.Exp

/-!
===============================================================================
HIVE CONSTITUTIONAL HEADER
===============================================================================
Module: InfoGeometry.Canonical.FirstQuantizedAmariOperatorGeometryPoset
Role: Canonical formalization of First-Quantized Amari Operator Geometry in a
  noncommutative associative ring `[Ring B]` with idempotent `P * P = P`:
  1. The 7-Stage Amari Dually Flat Operator Geometry Poset (`𝔇₁ ≺ 𝔇₂ ≺ ⋯ ≺ 𝔇₇`):
     - Rung 0: The Socratic Aporia of the Self-Dual Combined Space `𝔭`
       (`(1 + Φ₁)(1 + Φ₂) - (1 + Φ₁ + Φ₂) = Φ₁ Φ₂ = N₊₁ N₋₂ + N₋₁ N₊₂`,
        `[(1 + Φ₁), (1 + Φ₂)] = Σ₁₂ - Σ₂₁`, `(1 + Φ)(1 - Φ) = 1 - V`),
     - `𝔇₁`: Chiral split across `1 = P + (1 - P)` into the dually flat nilpotent
       affine subalgebras `𝔫₊ = P B (1 - P)` and `𝔫₋ = (1 - P) B P`
       (`N₊(A₁) N₊(A₂) = 0`, `N₋(C₁) N₋(C₂) = 0`),
     - `𝔇₂`: Exact abelian operator exponential families `ℰ₊(P, A) = 1 + N₊(A)`
       and `ℰ₋(P, C) = 1 + N₋(C)` with exact affine group homomorphisms
       `ℰ₊(A₁) ℰ₊(A₂) = ℰ₊(A₁ + A₂)`, `ℰ₋(C₁) ℰ₋(C₂) = ℰ₋(C₁ + C₂)` into `Bˣ`,
       series-free inversion `ℰ_±(X)⁻¹ = ℰ_±(-X)`, and zero internal curvature
       `[ℰ₊(A₁), ℰ₊(A₂)] = 0 = [ℰ₋(C₁), ℰ₋(C₂)]`,
     - `𝔇₃`: Paired Operator Gaussians `𝒢₊(P, A, C) = ℰ₊(A) ℰ₋(C) = 1 + Φ + Q₊`
       and `𝒢₋(P, A, C) = ℰ₋(C) ℰ₊(A) = 1 + Φ + Q₋` with exact polynomial
       two-sided inverses `𝒢₊⁻¹ = (1 - N₋)(1 - N₊) = 1 - Φ + Q₋` and
       `𝒢₋⁻¹ = (1 - N₊)(1 - N₋) = 1 - Φ + Q₊`,
     - `𝔇₄`: Birth of the Operator Fisher Metric `V = Q₊ + Q₋` and Berry /
       Amari–Chentsov Skewness `Σ = Q₊ - Q₋` from the cross-collision of the
       flat exponentials: `(𝒢₊ - (1 + Φ)) + (𝒢₋ - (1 + Φ)) = V` and
       `[ℰ₊(A), ℰ₋(C)] = 𝒢₊ - 𝒢₋ = Σ`,
     - `𝔇₅`: Amari Dual Connections `∇^(e) = ∇₊ = P Ω P` and
       `∇^(m) = ∇₋ = (1 - P) Ω (1 - P)`, doubled Levi-Civita midpoint
       `2 ∇^(0) = ∇^(e) + ∇^(m) = Γ_sum`, Amari–Chentsov skewness
       `∇^(e) - ∇^(m) = Γ_diff = S_P Γ_sum`, and the Sum–Difference Crossover
       `[∇^(e) - ∇^(m), Φ] = {∇^(e) + ∇^(m), J}`,
     - `𝔇₆`: The Operator Pythagorean Theorem from sheet orthogonality
       `Q₊ Q₋ = Q₋ Q₊ = 0`: `V² = (Q₊ + Q₋)² = Q₊² + Q₋² = (Q₊ - Q₋)² = Σ²`,
     - `𝔇₇`: All-Operator Legendre Resolvent Duality `η_± = W_± Φ = Φ W_±`,
       algebraic operator Bregman quadratic remainder `(1 - V)(V W₋ - V) = V²`,
       and native Fréchet log-det volume differential closure.
  2. The 6-Stage First-Quantized Operator Geometry vs. Trace-First Blindness
     Poset (`𝔔₁ ≺ 𝔔₂ ≺ ⋯ ≺ 𝔔₆`):
     - `𝔔₁–𝔔₃`: First quantization of coordinates, exponentials, Gaussians,
       metric `V`, and skewness `Σ` in faithful `2 × 2` Peirce matrix coordinates
       (`peirceCoordinateMatrix P`),
     - `𝔔₄`: The Theorem of Textbook Trace-First Blindness and Chiral Supertrace
       Recovery: for any cyclic trace `tr : B →+ K` (`tr(X Y) = tr(Y X)`),
       `tr(Q₊) = tr(Q₋)` forces `tr(𝒢₊) = tr(𝒢₋)` and `tr(Σ) = tr(Q₊ - Q₋) = 0`
       (erasing the operator skewness!), whereas the Chiral Supertrace
       `Str(Y) := tr(S_P Y)` satisfies `Str(V) = 0` and
       `Str(Σ) = tr(S_P Σ) = tr(V) = 2 • tr(Q₊)` (instantiated concretely on
       `Matrix.trace : Matrix n n R →+ R`),
     - `𝔔₅–𝔔₆`: All-operator dual connection trace/supertrace duality and
       Legendre–Bregman–Fréchet closure.
===============================================================================
-/

noncomputable section

namespace InfoGeometry.Canonical.FirstQuantizedAmariOperatorGeometryPoset

open scoped Matrix
open InfoGeometry.OperatorAlgebra.OntologyRing
open InfoGeometry.Meta
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.CausalHyperplaneBerryHolonomy
open InfoGeometry.Canonical.SupergradedMoebiusTetraktysKleinQuotientBerezinianWeylPoset
open InfoGeometry.Canonical.ModularSurprisalQuadraticLogVolume

/-! ===========================================================================
    Section 1: The Two Acyclic Causal Posets (`𝔇₁ ≺ ⋯ ≺ 𝔇₇` and `𝔔₁ ≺ ⋯ ≺ 𝔔₆`)
    =========================================================================== -/

/-- The 7 causal stages of the Amari Dually Flat Operator Geometry Poset
(`𝔇₁ ≺ 𝔇₂ ≺ 𝔇₃ ≺ (𝔇₄, 𝔇₅) ≺ 𝔇₆ ≺ 𝔇₇`). -/
inductive AmariDuallyFlatOperatorStage : Type
  | D1_ChiralSplitIntoDuallyFlatAffineSubalgebras
  | D2_ExactAbelianExponentialFamilies
  | D3_PairedOperatorGaussiansAndExactInversion
  | D4_BirthOfFisherMetricAndBerrySkewnessFromCrossCollision
  | D5_AmariDualConnectionsMidpointAndSkewnessSplit
  | D6_OperatorPythagoreanTheoremAndOrthogonalGramians
  | D7_LegendreResolventDualityBregmanAndBKMClosure
  deriving DecidableEq, Repr, Inhabited

namespace AmariDuallyFlatOperatorStage

/-- Integer topological rank `0..6` of the 7 Amari dually flat operator stages. -/
def stageIndex : AmariDuallyFlatOperatorStage → ℕ
  | .D1_ChiralSplitIntoDuallyFlatAffineSubalgebras => 0
  | .D2_ExactAbelianExponentialFamilies => 1
  | .D3_PairedOperatorGaussiansAndExactInversion => 2
  | .D4_BirthOfFisherMetricAndBerrySkewnessFromCrossCollision => 3
  | .D5_AmariDualConnectionsMidpointAndSkewnessSplit => 4
  | .D6_OperatorPythagoreanTheoremAndOrthogonalGramians => 5
  | .D7_LegendreResolventDualityBregmanAndBKMClosure => 6

-- theorem-class: transport lemma
theorem stageIndex_injective : Function.Injective stageIndex := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance instLinearOrder : LinearOrder AmariDuallyFlatOperatorStage :=
  LinearOrder.lift' stageIndex stageIndex_injective

instance instFintype : Fintype AmariDuallyFlatOperatorStage where
  elems := {
    .D1_ChiralSplitIntoDuallyFlatAffineSubalgebras,
    .D2_ExactAbelianExponentialFamilies,
    .D3_PairedOperatorGaussiansAndExactInversion,
    .D4_BirthOfFisherMetricAndBerrySkewnessFromCrossCollision,
    .D5_AmariDualConnectionsMidpointAndSkewnessSplit,
    .D6_OperatorPythagoreanTheoremAndOrthogonalGramians,
    .D7_LegendreResolventDualityBregmanAndBKMClosure
  }
  complete x := by cases x <;> simp

/-- Directed causal edges `𝔇₁ → 𝔇₂ → 𝔇₃ → (𝔇₄, 𝔇₅) → 𝔇₆ → 𝔇₇`. -/
def causalEdge : AmariDuallyFlatOperatorStage → AmariDuallyFlatOperatorStage → Prop
  | .D1_ChiralSplitIntoDuallyFlatAffineSubalgebras,
    .D2_ExactAbelianExponentialFamilies => True
  | .D2_ExactAbelianExponentialFamilies,
    .D3_PairedOperatorGaussiansAndExactInversion => True
  | .D3_PairedOperatorGaussiansAndExactInversion,
    .D4_BirthOfFisherMetricAndBerrySkewnessFromCrossCollision => True
  | .D3_PairedOperatorGaussiansAndExactInversion,
    .D5_AmariDualConnectionsMidpointAndSkewnessSplit => True
  | .D4_BirthOfFisherMetricAndBerrySkewnessFromCrossCollision,
    .D6_OperatorPythagoreanTheoremAndOrthogonalGramians => True
  | .D5_AmariDualConnectionsMidpointAndSkewnessSplit,
    .D6_OperatorPythagoreanTheoremAndOrthogonalGramians => True
  | .D6_OperatorPythagoreanTheoremAndOrthogonalGramians,
    .D7_LegendreResolventDualityBregmanAndBKMClosure => True
  | _, _ => False

instance instDecidableRelCausalEdge : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

-- theorem-class: transport lemma
theorem causalEdge_lt {s t : AmariDuallyFlatOperatorStage} (h : causalEdge s t) : s < t := by
  change stageIndex s < stageIndex t
  cases s <;> cases t <;> revert h <;> decide

-- theorem-class: transport lemma
theorem transGen_causalEdge_lt {s t : AmariDuallyFlatOperatorStage}
    (h : Relation.TransGen causalEdge s t) : s < t := by
  induction h with
  | single h1 => exact causalEdge_lt h1
  | tail _ h2 ih => exact lt_trans ih (causalEdge_lt h2)

-- theorem-class: transport lemma
theorem causalEdge_acyclic (s : AmariDuallyFlatOperatorStage) :
    ¬ Relation.TransGen causalEdge s s := by
  intro h
  exact lt_irrefl s (transGen_causalEdge_lt h)

/-- Representation-depth projection `toRepDepth : AmariDuallyFlatOperatorStage → RepDepth`. -/
def toRepDepth : AmariDuallyFlatOperatorStage → RepDepth
  | .D1_ChiralSplitIntoDuallyFlatAffineSubalgebras => .projective
  | .D2_ExactAbelianExponentialFamilies => .operator
  | .D3_PairedOperatorGaussiansAndExactInversion => .operator
  | .D4_BirthOfFisherMetricAndBerrySkewnessFromCrossCollision => .krein
  | .D5_AmariDualConnectionsMidpointAndSkewnessSplit => .transport
  | .D6_OperatorPythagoreanTheoremAndOrthogonalGramians => .transport
  | .D7_LegendreResolventDualityBregmanAndBKMClosure => .thermo

-- theorem-class: transport lemma
theorem toRepDepth_rank_monotone {a b : AmariDuallyFlatOperatorStage} (h : a ≤ b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  change stageIndex a ≤ stageIndex b at h
  cases a <;> cases b <;> revert h <;> decide

/-- Meta-level projection `toOntologyMetaLevel : AmariDuallyFlatOperatorStage → OntologyMetaLevel`. -/
def toOntologyMetaLevel : AmariDuallyFlatOperatorStage → OntologyMetaLevel
  | .D1_ChiralSplitIntoDuallyFlatAffineSubalgebras => .M1_ProjectorClabject
  | .D2_ExactAbelianExponentialFamilies => .M1_ProjectorClabject
  | .D3_PairedOperatorGaussiansAndExactInversion => .M2_GrassmannianPowertypeOrbit
  | .D4_BirthOfFisherMetricAndBerrySkewnessFromCrossCollision => .M2_GrassmannianPowertypeOrbit
  | .D5_AmariDualConnectionsMidpointAndSkewnessSplit => .M2_GrassmannianPowertypeOrbit
  | .D6_OperatorPythagoreanTheoremAndOrthogonalGramians => .M3_ErlangenCasimirMetaLaw
  | .D7_LegendreResolventDualityBregmanAndBKMClosure => .M3_ErlangenCasimirMetaLaw

-- theorem-class: transport lemma
theorem toOntologyMetaLevel_rank_monotone {a b : AmariDuallyFlatOperatorStage} (h : a ≤ b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  change stageIndex a ≤ stageIndex b at h
  cases a <;> cases b <;> revert h <;> decide

end AmariDuallyFlatOperatorStage

/-- The 6 causal stages of the First-Quantized Amari Operator Geometry vs.
Trace-First Blindness Poset (`𝔔₁ ≺ 𝔔₂ ≺ 𝔔₃ ≺ 𝔔₄ ≺ 𝔔₅ ≺ 𝔔₆`). -/
inductive FirstQuantizedAmariStage : Type
  | Q1_FirstQuantizationOfCoordinatesAndZeroBCH
  | Q2_OperatorExponentialAndGaussianMatrixMaps
  | Q3_OperatorMetricAndSkewnessCoordinatePreservation
  | Q4_TheoremOfTraceFirstBlindnessAndChiralSupertraceRecovery
  | Q5_AllOperatorDualConnectionsAndCrossover
  | Q6_AllOperatorLegendreResolventAndBregmanClosure
  deriving DecidableEq, Repr, Inhabited

namespace FirstQuantizedAmariStage

/-- Integer topological rank `0..5` of the 6 First-Quantized Amari stages. -/
def stageIndex : FirstQuantizedAmariStage → ℕ
  | .Q1_FirstQuantizationOfCoordinatesAndZeroBCH => 0
  | .Q2_OperatorExponentialAndGaussianMatrixMaps => 1
  | .Q3_OperatorMetricAndSkewnessCoordinatePreservation => 2
  | .Q4_TheoremOfTraceFirstBlindnessAndChiralSupertraceRecovery => 3
  | .Q5_AllOperatorDualConnectionsAndCrossover => 4
  | .Q6_AllOperatorLegendreResolventAndBregmanClosure => 5

-- theorem-class: transport lemma
theorem stageIndex_injective : Function.Injective stageIndex := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance instLinearOrder : LinearOrder FirstQuantizedAmariStage :=
  LinearOrder.lift' stageIndex stageIndex_injective

instance instFintype : Fintype FirstQuantizedAmariStage where
  elems := {
    .Q1_FirstQuantizationOfCoordinatesAndZeroBCH,
    .Q2_OperatorExponentialAndGaussianMatrixMaps,
    .Q3_OperatorMetricAndSkewnessCoordinatePreservation,
    .Q4_TheoremOfTraceFirstBlindnessAndChiralSupertraceRecovery,
    .Q5_AllOperatorDualConnectionsAndCrossover,
    .Q6_AllOperatorLegendreResolventAndBregmanClosure
  }
  complete x := by cases x <;> simp

/-- Directed cover edges `𝔔₁ → 𝔔₂ → 𝔔₃ → 𝔔₄ → 𝔔₅ → 𝔔₆`. -/
def causalEdge : FirstQuantizedAmariStage → FirstQuantizedAmariStage → Prop
  | .Q1_FirstQuantizationOfCoordinatesAndZeroBCH,
    .Q2_OperatorExponentialAndGaussianMatrixMaps => True
  | .Q2_OperatorExponentialAndGaussianMatrixMaps,
    .Q3_OperatorMetricAndSkewnessCoordinatePreservation => True
  | .Q3_OperatorMetricAndSkewnessCoordinatePreservation,
    .Q4_TheoremOfTraceFirstBlindnessAndChiralSupertraceRecovery => True
  | .Q4_TheoremOfTraceFirstBlindnessAndChiralSupertraceRecovery,
    .Q5_AllOperatorDualConnectionsAndCrossover => True
  | .Q5_AllOperatorDualConnectionsAndCrossover,
    .Q6_AllOperatorLegendreResolventAndBregmanClosure => True
  | _, _ => False

instance instDecidableRelCausalEdge : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

-- theorem-class: transport lemma
theorem causalEdge_lt {s t : FirstQuantizedAmariStage} (h : causalEdge s t) : s < t := by
  change stageIndex s < stageIndex t
  cases s <;> cases t <;> revert h <;> decide

-- theorem-class: transport lemma
theorem transGen_causalEdge_lt {s t : FirstQuantizedAmariStage}
    (h : Relation.TransGen causalEdge s t) : s < t := by
  induction h with
  | single h1 => exact causalEdge_lt h1
  | tail _ h2 ih => exact lt_trans ih (causalEdge_lt h2)

-- theorem-class: transport lemma
theorem causalEdge_acyclic (s : FirstQuantizedAmariStage) :
    ¬ Relation.TransGen causalEdge s s := by
  intro h
  exact lt_irrefl s (transGen_causalEdge_lt h)

/-- Representation-depth projection `toRepDepth : FirstQuantizedAmariStage → RepDepth`. -/
def toRepDepth : FirstQuantizedAmariStage → RepDepth
  | .Q1_FirstQuantizationOfCoordinatesAndZeroBCH => .projective
  | .Q2_OperatorExponentialAndGaussianMatrixMaps => .operator
  | .Q3_OperatorMetricAndSkewnessCoordinatePreservation => .krein
  | .Q4_TheoremOfTraceFirstBlindnessAndChiralSupertraceRecovery => .krein
  | .Q5_AllOperatorDualConnectionsAndCrossover => .transport
  | .Q6_AllOperatorLegendreResolventAndBregmanClosure => .thermo

-- theorem-class: transport lemma
theorem toRepDepth_rank_monotone {a b : FirstQuantizedAmariStage} (h : a ≤ b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  change stageIndex a ≤ stageIndex b at h
  cases a <;> cases b <;> revert h <;> decide

/-- Meta-level projection `toOntologyMetaLevel : FirstQuantizedAmariStage → OntologyMetaLevel`. -/
def toOntologyMetaLevel : FirstQuantizedAmariStage → OntologyMetaLevel
  | .Q1_FirstQuantizationOfCoordinatesAndZeroBCH => .M1_ProjectorClabject
  | .Q2_OperatorExponentialAndGaussianMatrixMaps => .M2_GrassmannianPowertypeOrbit
  | .Q3_OperatorMetricAndSkewnessCoordinatePreservation => .M2_GrassmannianPowertypeOrbit
  | .Q4_TheoremOfTraceFirstBlindnessAndChiralSupertraceRecovery => .M2_GrassmannianPowertypeOrbit
  | .Q5_AllOperatorDualConnectionsAndCrossover => .M3_ErlangenCasimirMetaLaw
  | .Q6_AllOperatorLegendreResolventAndBregmanClosure => .M3_ErlangenCasimirMetaLaw

-- theorem-class: transport lemma
theorem toOntologyMetaLevel_rank_monotone {a b : FirstQuantizedAmariStage} (h : a ≤ b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  change stageIndex a ≤ stageIndex b at h
  cases a <;> cases b <;> revert h <;> decide

end FirstQuantizedAmariStage

/-! ===========================================================================
    Section 2: Rung 0 — The Socratic Aporia of the Self-Dual Combined Space `𝔭`
    (`(1 + Φ₁)(1 + Φ₂) ≠ 1 + Φ₁ + Φ₂` and `(1 + Φ)(1 - Φ) = 1 - V`)
    =========================================================================== -/

section Rung0SelfDualExponentialAporia

variable {B : Type*} [Ring B]

/-- The naive combined self-dual displacement `ℰ_selfDual(P, A, C) := 1 + genPhi P A C`
on the combined odd space `𝔭 = 𝔫₊ ⊕ 𝔫₋`. -/
def selfDualUnipotentStep (P A C : B) : B :=
  1 + genPhi P A C

-- theorem-class: constructive endpoint
/-- **Rung 0 Socratic Aporia Theorem (`rung0_self_dual_exponential_aporia_and_bch_curvature`)**:
Attempting to form an affine exponential family directly on the combined symmetric space
`Φ = N₊ + N₋ ∈ 𝔭` without splitting across `P` and `1 - P` fails affine flatness:
1. **Multiplicative BCH Defect**:
   `(1 + Φ₁)(1 + Φ₂) - (1 + (Φ₁ + Φ₂)) = Φ₁ * Φ₂ = N₊(A₁) * N₋(C₂) + N₋(C₁) * N₊(A₂)`.
2. **Non-Abelian Step Commutator**:
   `comm (1 + Φ₁) (1 + Φ₂) = comm Φ₁ Φ₂ = genSig P A₁ C₂ - genSig P A₂ C₁`.
3. **Single-Mode Quadratic Obstruction & Inversion Failure**:
   * `(1 + Φ)(1 + Φ) - (1 + (2 : ℤ) • Φ) = genV P A C`,
   * `(1 + Φ)(1 - Φ) = 1 - genV P A C`,
   * `(1 + Φ)(1 - Φ) = 1 ↔ genV P A C = 0`, and `genV P A C = 0 ↔ genSig P A C = 0`
     (via `tetraktys_interaction_iff_chiral_obstruction`). -/
theorem rung0_self_dual_exponential_aporia_and_bch_curvature
    {P : B} (hP : P * P = P) (A₁ C₁ A₂ C₂ A C : B) :
    let Φ₁ := genPhi P A₁ C₁
    let Φ₂ := genPhi P A₂ C₂
    let Φ := genPhi P A C
    let V := genV P A C
    let Sig := genSig P A C
    (selfDualUnipotentStep P A₁ C₁ * selfDualUnipotentStep P A₂ C₂ -
        (1 + (Φ₁ + Φ₂)) = Φ₁ * Φ₂ ∧
      Φ₁ * Φ₂ = conePlus P A₁ * coneMinus P C₂ + coneMinus P C₁ * conePlus P A₂) ∧
    (comm (selfDualUnipotentStep P A₁ C₁) (selfDualUnipotentStep P A₂ C₂) =
        comm Φ₁ Φ₂ ∧
      comm Φ₁ Φ₂ = genSig P A₁ C₂ - genSig P A₂ C₁) ∧
    (selfDualUnipotentStep P A C * selfDualUnipotentStep P A C -
        (1 + (2 : ℤ) • Φ) = V ∧
      (1 + Φ) * (1 - Φ) = 1 - V ∧
      ((1 + Φ) * (1 - Φ) = 1 ↔ V = 0) ∧
      (V = 0 ↔ Sig = 0)) := by
  intro Φ₁ Φ₂ Φ V Sig
  have hPhiSq : Φ * Φ = V := by dsimp [Φ, V]; peirce_nf hP
  have hInvProd : (1 + Φ) * (1 - Φ) = 1 - V := by
    calc
      (1 + Φ) * (1 - Φ) = 1 - Φ * Φ := by noncomm_ring
      _ = 1 - V := by rw [hPhiSq]
  have hSelfSq :
      selfDualUnipotentStep P A C * selfDualUnipotentStep P A C -
        (1 + (2 : ℤ) • Φ) = V := by
    dsimp [selfDualUnipotentStep]
    calc
      (1 + Φ) * (1 + Φ) - (1 + (2 : ℤ) • Φ) = Φ * Φ := by noncomm_ring
      _ = V := hPhiSq
  refine ⟨⟨by dsimp [selfDualUnipotentStep]; noncomm_ring,
           twoPhi_mul_expansion hP A₁ C₁ A₂ C₂⟩,
    ⟨by dsimp [selfDualUnipotentStep, OperatorAlgebra.PeirceSpine.comm]; noncomm_ring,
     by dsimp [Φ₁, Φ₂]; exact twoPhi_comm_expansion hP A₁ C₁ A₂ C₂⟩,
    ⟨hSelfSq, hInvProd,
     ⟨fun h => by
        rw [hInvProd] at h
        have hSub : 1 - (1 - V) = 1 - 1 := congrArg (fun X : B => 1 - X) h
        calc
          V = 1 - (1 - V) := by abel
          _ = 1 - 1 := hSub
          _ = 0 := sub_self 1,
      fun h => by rw [hInvProd, h, sub_zero]⟩,
     tetraktys_interaction_iff_chiral_obstruction hP A C⟩⟩

end Rung0SelfDualExponentialAporia

/-! ===========================================================================
    Section 3: Stages `𝔇₁, 𝔇₂` & `𝔔₁` — Dually Flat Chiral Subalgebras (`𝔫₊, 𝔫₋`),
    Exact Abelian Exponential Families (`ℰ₊, ℰ₋`), & Homomorphisms into `Bˣ`
    =========================================================================== -/

section DuallyFlatChiralExponentialFamilies

variable {B : Type*} [Ring B]

/-- The Primal (`e`-Flat) Operator Exponential Map
`amariExpPlus P A := 1 + conePlus P A` (`ℰ₊(A) = I + N₊(A)`). -/
def amariExpPlus (P A : B) : B :=
  1 + conePlus P A

/-- The Dual (`m`-Flat) Operator Exponential Map
`amariExpMinus P C := 1 + coneMinus P C` (`ℰ₋(C) = I + N₋(C)`). -/
def amariExpMinus (P C : B) : B :=
  1 + coneMinus P C

/-- Equality of dual unipotent operators is exactly equality of their Peirce coordinates. -/
theorem amariExpMinus_eq_iff_coneMinus_eq (P C C' : B) :
    amariExpMinus P C = amariExpMinus P C' ↔ coneMinus P C = coneMinus P C' := by
  simp only [amariExpMinus]
  constructor
  · exact add_left_cancel
  · intro h
    rw [h]

/-- Equality of primal unipotent operators is exactly equality of their Peirce coordinates.
Thus the operator family forgets precisely the kernel directions of `conePlus P`. -/
theorem amariExpPlus_eq_iff_conePlus_eq (P A A' : B) :
    amariExpPlus P A = amariExpPlus P A' ↔ conePlus P A = conePlus P A' := by
  simp only [amariExpPlus]
  constructor
  · exact add_left_cancel
  · intro h
    rw [h]

-- theorem-class: constructive endpoint
/-- **Stages `𝔇₁, 𝔇₂` & `𝔔₁` Theorem (`stage_D1_D2_Q1_dually_flat_chiral_subalgebras_and_abelian_exponentials`)**:
In any noncommutative `[Ring B]` with idempotent `P * P = P`:
1. **Chiral Projection into `𝔫₊ = P B (1 - P)` and `𝔫₋ = (1 - P) B P` (`𝔇₁`)**:
   * `genPhi P A C + genJ P A C = (2 : ℤ) • conePlus P A`,
   * `genPhi P A C - genJ P A C = (2 : ℤ) • coneMinus P C`,
   * `(1 + invS P) * genPhi P A C = (2 : ℤ) • conePlus P A`,
   * `(1 - invS P) * genPhi P A C = (2 : ℤ) • coneMinus P C`.
2. **Same-Wing Nilpotency & Zero Internal BCH Obstruction (`𝔇₁, 𝔔₁`)**:
   * `conePlus P A₁ * conePlus P A₂ = 0` and `comm (conePlus P A₁) (conePlus P A₂) = 0`,
   * `coneMinus P C₁ * coneMinus P C₂ = 0` and `comm (coneMinus P C₁) (coneMinus P C₂) = 0`.
3. **Exact Abelian Flatness, Group Law, Series-Free Inversion, & Zero Internal Curvature of `ℰ₊` and `ℰ₋` (`𝔇₂`)**:
   * `amariExpPlus P 0 = 1` and `amariExpMinus P 0 = 1`,
   * `amariExpPlus P A₁ * amariExpPlus P A₂ = amariExpPlus P (A₁ + A₂)`,
   * `amariExpMinus P C₁ * amariExpMinus P C₂ = amariExpMinus P (C₁ + C₂)`,
   * `amariExpPlus P A₁ * amariExpPlus P (-A₁) = 1` and `amariExpPlus P (-A₁) * amariExpPlus P A₁ = 1`,
   * `amariExpMinus P C₁ * amariExpMinus P (-C₁) = 1` and `amariExpMinus P (-C₁) * amariExpMinus P C₁ = 1`,
   * `comm (amariExpPlus P A₁) (amariExpPlus P A₂) = 0` and
     `comm (amariExpMinus P C₁) (amariExpMinus P C₂) = 0`. -/
theorem stage_D1_D2_Q1_dually_flat_chiral_subalgebras_and_abelian_exponentials
    {P : B} (hP : P * P = P) (A₁ A₂ C₁ C₂ A C : B) :
    (genPhi P A C + genJ P A C = (2 : ℤ) • conePlus P A ∧
      genPhi P A C - genJ P A C = (2 : ℤ) • coneMinus P C ∧
      (1 + invS P) * genPhi P A C = (2 : ℤ) • conePlus P A ∧
      (1 - invS P) * genPhi P A C = (2 : ℤ) • coneMinus P C) ∧
    (conePlus P A₁ * conePlus P A₂ = 0 ∧
      coneMinus P C₁ * coneMinus P C₂ = 0 ∧
      comm (conePlus P A₁) (conePlus P A₂) = 0 ∧
      comm (coneMinus P C₁) (coneMinus P C₂) = 0) ∧
    (amariExpPlus P 0 = 1 ∧
      amariExpMinus P 0 = 1 ∧
      amariExpPlus P A₁ * amariExpPlus P A₂ = amariExpPlus P (A₁ + A₂) ∧
      amariExpMinus P C₁ * amariExpMinus P C₂ = amariExpMinus P (C₁ + C₂) ∧
      amariExpPlus P A₁ * amariExpPlus P (-A₁) = 1 ∧
      amariExpPlus P (-A₁) * amariExpPlus P A₁ = 1 ∧
      amariExpMinus P C₁ * amariExpMinus P (-C₁) = 1 ∧
      amariExpMinus P (-C₁) * amariExpMinus P C₁ = 1 ∧
      comm (amariExpPlus P A₁) (amariExpPlus P A₂) = 0 ∧
      comm (amariExpMinus P C₁) (amariExpMinus P C₂) = 0) := by
  have hA8 := archetype_A8_same_cone_annihilation_and_superposition hP A₁ A₂ C₁ C₂
  have hExpP : amariExpPlus P A₁ * amariExpPlus P A₂ = amariExpPlus P (A₁ + A₂) := by
    dsimp [amariExpPlus]
    calc
      (1 + conePlus P A₁) * (1 + conePlus P A₂)
        = 1 + (conePlus P A₁ + conePlus P A₂) + conePlus P A₁ * conePlus P A₂ := by
          noncomm_ring
      _ = 1 + conePlus P (A₁ + A₂) := by
          rw [hA8.1, add_zero, ← conePlus_add P A₁ A₂]
  have hExpM : amariExpMinus P C₁ * amariExpMinus P C₂ = amariExpMinus P (C₁ + C₂) := by
    dsimp [amariExpMinus]
    calc
      (1 + coneMinus P C₁) * (1 + coneMinus P C₂)
        = 1 + (coneMinus P C₁ + coneMinus P C₂) + coneMinus P C₁ * coneMinus P C₂ := by
          noncomm_ring
      _ = 1 + coneMinus P (C₁ + C₂) := by
          rw [hA8.2.1, add_zero, ← coneMinus_add P C₁ C₂]
  have hExpP0 : amariExpPlus P 0 = 1 := by
    dsimp [amariExpPlus]; rw [conePlus_zero P, add_zero]
  have hExpM0 : amariExpMinus P 0 = 1 := by
    dsimp [amariExpMinus]; rw [coneMinus_zero P, add_zero]
  refine ⟨⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP⟩,
    ⟨hA8.1, hA8.2.1, hA8.2.2.1, hA8.2.2.2.1⟩,
    ⟨hExpP0, hExpM0, hExpP, hExpM,
     by dsimp [amariExpPlus]; peirce_nf hP,
     by dsimp [amariExpPlus]; peirce_nf hP,
     by dsimp [amariExpMinus]; peirce_nf hP,
     by dsimp [amariExpMinus]; peirce_nf hP,
     by dsimp [amariExpPlus]; peirce_nf hP,
     by dsimp [amariExpMinus]; peirce_nf hP⟩⟩

/-- The raw primal parameter map is not injective for a nonzero idempotent cut:
`0` and `P` have the same Peirce projection. The exact exponential group law therefore
describes the image of the parameter map (or its kernel quotient), not an isomorphism from
the entire additive carrier `B` without an additional injectivity hypothesis. -/
theorem amariExpPlus_parameterization_not_injective_of_nonzero_idempotent
    {P : B} (hP : P * P = P) (hP0 : P ≠ 0) :
    ¬ Function.Injective (amariExpPlus P) := by
  have hcut : conePlus P P = 0 := by
    dsimp [conePlus]
    calc
      P * P * (1 - P) = P * (1 - P) := by rw [hP]
      _ = P - P * P := by noncomm_ring
      _ = 0 := by rw [hP]; simp
  have hzero : amariExpPlus P 0 = 1 := by
    simp [amariExpPlus, conePlus]
  have hPvalue : amariExpPlus P P = 1 := by
    simp [amariExpPlus, hcut]
  intro hinj
  apply hP0
  exact (hinj (hzero.trans hPvalue.symm)).symm

/-- The raw dual parameter map is not injective when the complementary idempotent is nonzero:
`0` and `1 - P` have the same lower Peirce projection. -/
theorem amariExpMinus_parameterization_not_injective_of_nonzero_complement
    {P : B} (hP : P * P = P) (hComp : 1 - P ≠ 0) :
    ¬ Function.Injective (amariExpMinus P) := by
  have hcompIdem : (1 - P) * (1 - P) = 1 - P := by
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hP]; abel
  have hcut : coneMinus P (1 - P) = 0 := by
    dsimp [coneMinus]
    calc
      (1 - P) * (1 - P) * P = (1 - P) * P := by rw [hcompIdem]
      _ = P - P * P := by noncomm_ring
      _ = 0 := by rw [hP]; simp
  have hzero : amariExpMinus P 0 = 1 := by
    simp [amariExpMinus, coneMinus]
  have hCompValue : amariExpMinus P (1 - P) = 1 := by
    simp [amariExpMinus, hcut]
  intro hinj
  apply hComp
  exact (hinj (hzero.trans hCompValue.symm)).symm

/-- The primal `e`-flat exponential `amariExpPlus P A` packaged as a unit in `Bˣ`
with exact polynomial inverse `amariExpPlus P (-A)`. -/
def amariExpPlusUnits {P : B} (hP : P * P = P) (A : B) : Bˣ where
  val := amariExpPlus P A
  inv := amariExpPlus P (-A)
  val_inv := (stage_D1_D2_Q1_dually_flat_chiral_subalgebras_and_abelian_exponentials hP A A 0 0 A 0).2.2.2.2.2.2.1
  inv_val := (stage_D1_D2_Q1_dually_flat_chiral_subalgebras_and_abelian_exponentials hP A A 0 0 A 0).2.2.2.2.2.2.2.1

/-- The primal `e`-flat exponential map as a genuine group homomorphism
`Multiplicative B →* Bˣ` sending additive displacements `A₁ + A₂` to
multiplicative products `ℰ₊(A₁) ℰ₊(A₂)`. -/
def amariExpPlusUnitsHom {P : B} (hP : P * P = P) : Multiplicative B →* Bˣ where
  toFun a := amariExpPlusUnits hP (Multiplicative.toAdd a)
  map_one' := by
    ext
    exact (stage_D1_D2_Q1_dually_flat_chiral_subalgebras_and_abelian_exponentials hP 0 0 0 0 0 0).2.2.1
  map_mul' a b := by
    ext
    exact ((stage_D1_D2_Q1_dually_flat_chiral_subalgebras_and_abelian_exponentials hP
      (Multiplicative.toAdd a) (Multiplicative.toAdd b) 0 0 0 0).2.2.2.2.1).symm

/-- The kernel of the primal unipotent group hom consists exactly of parameters whose upper
Peirce coordinate vanishes. -/
theorem amariExpPlusUnitsHom_mem_ker_iff {P : B} (hP : P * P = P)
    (a : Multiplicative B) :
    a ∈ (amariExpPlusUnitsHom hP).ker ↔
      conePlus P (Multiplicative.toAdd a) = 0 := by
  rw [MonoidHom.mem_ker]
  change amariExpPlusUnits hP (Multiplicative.toAdd a) = 1 ↔ _
  rw [Units.ext_iff]
  change amariExpPlus P (Multiplicative.toAdd a) = 1 ↔ _
  have hzero : amariExpPlus P 0 = 1 := by
    simp [amariExpPlus, conePlus]
  rw [← hzero, amariExpPlus_eq_iff_conePlus_eq, conePlus_zero]

/-- First-isomorphism description of the primal unipotent family: additive parameters modulo
the kernel of `amariExpPlusUnitsHom` are group-isomorphic to the actual subgroup of units
realized by the family. This is the precise quotient-level replacement for identifying raw
parameters in `B` with distinct unipotent operators. -/
noncomputable def amariExpPlusUnitsParameterQuotientEquiv {P : B}
    (hP : P * P = P) :
    Multiplicative B ⧸ (amariExpPlusUnitsHom hP).ker ≃*
      (amariExpPlusUnitsHom hP).range :=
  QuotientGroup.quotientKerEquivRange (amariExpPlusUnitsHom hP)

/-- The dual `m`-flat exponential `amariExpMinus P C` packaged as a unit in `Bˣ`
with exact polynomial inverse `amariExpMinus P (-C)`. -/
def amariExpMinusUnits {P : B} (hP : P * P = P) (C : B) : Bˣ where
  val := amariExpMinus P C
  inv := amariExpMinus P (-C)
  val_inv := (stage_D1_D2_Q1_dually_flat_chiral_subalgebras_and_abelian_exponentials hP 0 0 C C 0 C).2.2.2.2.2.2.2.2.1
  inv_val := (stage_D1_D2_Q1_dually_flat_chiral_subalgebras_and_abelian_exponentials hP 0 0 C C 0 C).2.2.2.2.2.2.2.2.2.1

/-- The dual `m`-flat exponential map as a genuine group homomorphism
`Multiplicative B →* Bˣ` sending additive displacements `C₁ + C₂` to
multiplicative products `ℰ₋(C₁) ℰ₋(C₂)`. -/
def amariExpMinusUnitsHom {P : B} (hP : P * P = P) : Multiplicative B →* Bˣ where
  toFun c := amariExpMinusUnits hP (Multiplicative.toAdd c)
  map_one' := by
    ext
    exact (stage_D1_D2_Q1_dually_flat_chiral_subalgebras_and_abelian_exponentials hP 0 0 0 0 0 0).2.2.2.1
  map_mul' c d := by
    ext
    exact ((stage_D1_D2_Q1_dually_flat_chiral_subalgebras_and_abelian_exponentials hP
      0 0 (Multiplicative.toAdd c) (Multiplicative.toAdd d) 0 0).2.2.2.2.2.1).symm

/-- The dual unipotent group hom has kernel exactly where the lower Peirce coordinate vanishes. -/
theorem amariExpMinusUnitsHom_mem_ker_iff {P : B} (hP : P * P = P)
    (c : Multiplicative B) :
    c ∈ (amariExpMinusUnitsHom hP).ker ↔
      coneMinus P (Multiplicative.toAdd c) = 0 := by
  rw [MonoidHom.mem_ker]
  change amariExpMinusUnits hP (Multiplicative.toAdd c) = 1 ↔ _
  rw [Units.ext_iff]
  change amariExpMinus P (Multiplicative.toAdd c) = 1 ↔ _
  have hzero : amariExpMinus P 0 = 1 := by
    simp [amariExpMinus, coneMinus]
  rw [← hzero, amariExpMinus_eq_iff_coneMinus_eq, coneMinus_zero]

/-- The first-isomorphism theorem identifies dual parameters modulo the kernel with the actual
subgroup of units realized by the `m`-flat family. -/
noncomputable def amariExpMinusUnitsParameterQuotientEquiv {P : B}
    (hP : P * P = P) :
    Multiplicative B ⧸ (amariExpMinusUnitsHom hP).ker ≃*
      (amariExpMinusUnitsHom hP).range :=
  QuotientGroup.quotientKerEquivRange (amariExpMinusUnitsHom hP)

end DuallyFlatChiralExponentialFamilies

/-! ===========================================================================
    Section 4: Stages `𝔇₃, 𝔇₄` & `𝔔₂, 𝔔₃` — Paired Operator Gaussians (`𝒢₊, 𝒢₋`),
    Series-Free Polynomial Inversion, Birth of `(V, Σ)` from Cross-Collision,
    and Faithful `2 × 2` Peirce Coordinate Matrices
    =========================================================================== -/

section PairedOperatorGaussiansAndCurvatureBirth

variable {B : Type*} [Ring B]

/-- The Forward Paired Operator Gaussian
`operatorGaussianPlus P A C := amariExpPlus P A * amariExpMinus P C`
(`𝒢₊ = (1 + N₊)(1 + N₋)`). -/
def operatorGaussianPlus (P A C : B) : B :=
  amariExpPlus P A * amariExpMinus P C

/-- The Backward Paired Operator Gaussian
`operatorGaussianMinus P A C := amariExpMinus P C * amariExpPlus P A`
(`𝒢₋ = (1 + N₋)(1 + N₊)`). -/
def operatorGaussianMinus (P A C : B) : B :=
  amariExpMinus P C * amariExpPlus P A

/-- The exact polynomial inverse of the Forward Operator Gaussian:
`operatorGaussianPlusInv P A C := amariExpMinus P (-C) * amariExpPlus P (-A)`
(`𝒢₊⁻¹ = (1 - N₋)(1 - N₊)`). -/
def operatorGaussianPlusInv (P A C : B) : B :=
  amariExpMinus P (-C) * amariExpPlus P (-A)

/-- The exact polynomial inverse of the Backward Operator Gaussian:
`operatorGaussianMinusInv P A C := amariExpPlus P (-A) * amariExpMinus P (-C)`
(`𝒢₋⁻¹ = (1 - N₊)(1 - N₋)`). -/
def operatorGaussianMinusInv (P A C : B) : B :=
  amariExpPlus P (-A) * amariExpMinus P (-C)

/-- The upper Peirce exponential is Mathlib's finite nilpotent exponential in a `ℚ`-algebra.
This connects the polynomial family `1 + N₊` to the native `IsNilpotent.exp`, rather than
using "exponential" as informal notation. -/
theorem amariExpPlus_eq_mathlib_nilpotent_exp
    {B : Type*} [Ring B] [Algebra ℚ B]
    {P : B} (hP : P * P = P) (A : B) :
    amariExpPlus P A = IsNilpotent.exp (conePlus P A) := by
  have hN : (conePlus P A) ^ 2 = 0 := by
    simpa [pow_two] using conePlus_mul_conePlus hP A A
  rw [IsNilpotent.exp_eq_sum (a := conePlus P A) (k := 2) hN]
  simp [amariExpPlus, Finset.sum_range_succ]

/-- The lower Peirce exponential is likewise Mathlib's finite nilpotent exponential. -/
theorem amariExpMinus_eq_mathlib_nilpotent_exp
    {B : Type*} [Ring B] [Algebra ℚ B]
    {P : B} (hP : P * P = P) (C : B) :
    amariExpMinus P C = IsNilpotent.exp (coneMinus P C) := by
  have hN : (coneMinus P C) ^ 2 = 0 := by
    simpa [pow_two] using coneMinus_mul_coneMinus hP C C
  rw [IsNilpotent.exp_eq_sum (a := coneMinus P C) (k := 2) hN]
  simp [amariExpMinus, Finset.sum_range_succ]

/-- In a `ℚ`-algebra, the upper Peirce chart's additive law is exactly Mathlib's
`IsNilpotent.exp_add_of_commute` specialized to the mutually annihilating upper-wing elements. -/
theorem amariExpPlus_mathlib_exp_add
    {B : Type*} [Ring B] [Algebra ℚ B]
    {P : B} (hP : P * P = P) (A₁ A₂ : B) :
    amariExpPlus P (A₁ + A₂) =
      IsNilpotent.exp (conePlus P A₁) * IsNilpotent.exp (conePlus P A₂) := by
  rw [amariExpPlus_eq_mathlib_nilpotent_exp hP, conePlus_add]
  apply IsNilpotent.exp_add_of_commute
  · apply (commute_iff_eq _ _).2
    rw [conePlus_mul_conePlus hP, conePlus_mul_conePlus hP]
  · exact ⟨2, by simpa [pow_two] using conePlus_mul_conePlus hP A₁ A₁⟩
  · exact ⟨2, by simpa [pow_two] using conePlus_mul_conePlus hP A₂ A₂⟩

/-- The lower Peirce chart obeys the matching Mathlib nilpotent-exponential addition law. -/
theorem amariExpMinus_mathlib_exp_add
    {B : Type*} [Ring B] [Algebra ℚ B]
    {P : B} (hP : P * P = P) (C₁ C₂ : B) :
    amariExpMinus P (C₁ + C₂) =
      IsNilpotent.exp (coneMinus P C₁) * IsNilpotent.exp (coneMinus P C₂) := by
  rw [amariExpMinus_eq_mathlib_nilpotent_exp hP, coneMinus_add]
  apply IsNilpotent.exp_add_of_commute
  · apply (commute_iff_eq _ _).2
    rw [coneMinus_mul_coneMinus hP, coneMinus_mul_coneMinus hP]
  · exact ⟨2, by simpa [pow_two] using coneMinus_mul_coneMinus hP C₁ C₁⟩
  · exact ⟨2, by simpa [pow_two] using coneMinus_mul_coneMinus hP C₂ C₂⟩

/-- The ordered forward Gaussian is the product of the two native Mathlib nilpotent
exponentials. The order records the cross-wing noncommutativity. -/
theorem operatorGaussianPlus_eq_mathlib_exp_product
    {B : Type*} [Ring B] [Algebra ℚ B]
    {P : B} (hP : P * P = P) (A C : B) :
    operatorGaussianPlus P A C =
      IsNilpotent.exp (conePlus P A) * IsNilpotent.exp (coneMinus P C) := by
  change amariExpPlus P A * amariExpMinus P C = _
  rw [← amariExpPlus_eq_mathlib_nilpotent_exp hP,
    ← amariExpMinus_eq_mathlib_nilpotent_exp hP]

/-- The backward Gaussian is the reverse-ordered product of the native nilpotent
exponentials. -/
theorem operatorGaussianMinus_eq_mathlib_exp_product
    {B : Type*} [Ring B] [Algebra ℚ B]
    {P : B} (hP : P * P = P) (A C : B) :
    operatorGaussianMinus P A C =
      IsNilpotent.exp (coneMinus P C) * IsNilpotent.exp (conePlus P A) := by
  change amariExpMinus P C * amariExpPlus P A = _
  rw [← amariExpMinus_eq_mathlib_nilpotent_exp hP,
    ← amariExpPlus_eq_mathlib_nilpotent_exp hP]

/-- The exact forward Gaussian inverse is the reverse-ordered product of the negative
Mathlib nilpotent exponentials. -/
theorem operatorGaussianPlusInv_eq_mathlib_exp_product
    {B : Type*} [Ring B] [Algebra ℚ B]
    {P : B} (hP : P * P = P) (A C : B) :
    operatorGaussianPlusInv P A C =
      IsNilpotent.exp (coneMinus P (-C)) * IsNilpotent.exp (conePlus P (-A)) := by
  change amariExpMinus P (-C) * amariExpPlus P (-A) = _
  rw [← amariExpMinus_eq_mathlib_nilpotent_exp hP,
    ← amariExpPlus_eq_mathlib_nilpotent_exp hP]

/-- The exact backward Gaussian inverse is the reverse-ordered product of its negative
Mathlib nilpotent exponentials. -/
theorem operatorGaussianMinusInv_eq_mathlib_exp_product
    {B : Type*} [Ring B] [Algebra ℚ B]
    {P : B} (hP : P * P = P) (A C : B) :
    operatorGaussianMinusInv P A C =
      IsNilpotent.exp (conePlus P (-A)) * IsNilpotent.exp (coneMinus P (-C)) := by
  change amariExpPlus P (-A) * amariExpMinus P (-C) = _
  rw [← amariExpPlus_eq_mathlib_nilpotent_exp hP,
    ← amariExpMinus_eq_mathlib_nilpotent_exp hP]

/-- The commutator of the two native Mathlib nilpotent exponentials is exactly the
Peirce Berry/skewness operator. The cross-wing curvature therefore remains visible
before any trace is taken, while each same-wing exponential family is flat. -/
theorem mathlib_nilpotent_exp_commutator_eq_genSig
    {B : Type*} [Ring B] [Algebra ℚ B]
    {P : B} (hP : P * P = P) (A C : B) :
    comm (IsNilpotent.exp (conePlus P A))
      (IsNilpotent.exp (coneMinus P C)) = genSig P A C := by
  rw [← amariExpPlus_eq_mathlib_nilpotent_exp hP,
    ← amariExpMinus_eq_mathlib_nilpotent_exp hP]
  dsimp [amariExpPlus, amariExpMinus, genSig, qgtPlus, qgtMinus,
    conePlus, coneMinus, OperatorAlgebra.PeirceSpine.comm]
  noncomm_ring

/-- The value of the existing primal `Bˣ` chart is precisely the native Mathlib
nilpotent exponential. This identifies the repository's unit-valued group map with
the standard exponential, rather than merely proving an unrelated invertibility fact. -/
theorem amariExpPlusUnits_val_eq_mathlib_exp
    {B : Type*} [Ring B] [Algebra ℚ B]
    {P : B} (hP : P * P = P) (A : B) :
    ↑(amariExpPlusUnits hP A) = IsNilpotent.exp (conePlus P A) := by
  change amariExpPlus P A = _
  exact amariExpPlus_eq_mathlib_nilpotent_exp hP A

/-- The value of the existing dual `Bˣ` chart is precisely Mathlib's nilpotent
exponential. -/
theorem amariExpMinusUnits_val_eq_mathlib_exp
    {B : Type*} [Ring B] [Algebra ℚ B]
    {P : B} (hP : P * P = P) (C : B) :
    ↑(amariExpMinusUnits hP C) = IsNilpotent.exp (coneMinus P C) := by
  change amariExpMinus P C = _
  exact amariExpMinus_eq_mathlib_nilpotent_exp hP C

/-- Mathlib's exponential unit theorem applies directly to each Peirce chart. -/
theorem conePlus_exp_isUnit
    {B : Type*} [Ring B] [Algebra ℚ B]
    {P : B} (hP : P * P = P) (A : B) :
    IsUnit (IsNilpotent.exp (conePlus P A)) := by
  apply IsNilpotent.isUnit_exp
  exact ⟨2, by simpa [pow_two] using conePlus_mul_conePlus hP A A⟩

/-- The dual Peirce exponential is a unit by Mathlib's nilpotent exponential theorem. -/
theorem coneMinus_exp_isUnit
    {B : Type*} [Ring B] [Algebra ℚ B]
    {P : B} (hP : P * P = P) (C : B) :
    IsUnit (IsNilpotent.exp (coneMinus P C)) := by
  apply IsNilpotent.isUnit_exp
  exact ⟨2, by simpa [pow_two] using coneMinus_mul_coneMinus hP C C⟩

/-- The existing primal unit chart is Mathlib's canonical `IsUnit.unit` of the
nilpotent exponential. Its unit structure and inverse therefore agree with the
standard unit furnished by the nilpotent exponential API. -/
theorem amariExpPlusUnits_eq_mathlib_exp_unit
    {B : Type*} [Ring B] [Algebra ℚ B]
    {P : B} (hP : P * P = P) (A : B) :
    amariExpPlusUnits hP A = (conePlus_exp_isUnit hP A).unit := by
  apply Units.ext
  simpa only [IsUnit.unit_spec] using amariExpPlusUnits_val_eq_mathlib_exp hP A

/-- The existing dual unit chart is Mathlib's canonical unit of its nilpotent
exponential. -/
theorem amariExpMinusUnits_eq_mathlib_exp_unit
    {B : Type*} [Ring B] [Algebra ℚ B]
    {P : B} (hP : P * P = P) (C : B) :
    amariExpMinusUnits hP C = (coneMinus_exp_isUnit hP C).unit := by
  apply Units.ext
  simpa only [IsUnit.unit_spec] using amariExpMinusUnits_val_eq_mathlib_exp hP C

/-- The forward paired Gaussian determines both Peirce off-diagonal coordinates:
its upper-right and lower-left corners recover the primal and dual parameters
after Peirce projection. -/
theorem operatorGaussianPlus_eq_iff_cone_coordinates_eq
    {P A C A' C' : B} (hP : P * P = P) :
    operatorGaussianPlus P A C = operatorGaussianPlus P A' C' ↔
      conePlus P A = conePlus P A' ∧ coneMinus P C = coneMinus P C' := by
  constructor
  · intro h
    have hp := congrArg (fun X : B => conePlus P X) h
    have hm := congrArg (fun X : B => coneMinus P X) h
    have hupper (A C : B) :
        conePlus P (operatorGaussianPlus P A C) = conePlus P A := by
      dsimp [operatorGaussianPlus, amariExpPlus, amariExpMinus,
        conePlus, coneMinus]
      peirce_nf hP
    have hlower (A C : B) :
        coneMinus P (operatorGaussianPlus P A C) = coneMinus P C := by
      dsimp [operatorGaussianPlus, amariExpPlus, amariExpMinus,
        conePlus, coneMinus]
      peirce_nf hP
    rw [hupper, hupper] at hp
    rw [hlower, hlower] at hm
    exact ⟨hp, hm⟩
  · rintro ⟨hp, hm⟩
    have hPhi : genPhi P A C = genPhi P A' C' := by
      dsimp [genPhi]
      rw [hp, hm]
    have hQ : qgtPlus P A C = qgtPlus P A' C' := by
      dsimp [qgtPlus]
      rw [hp, hm]
    have hgp (A C : B) :
        operatorGaussianPlus P A C = 1 + genPhi P A C + qgtPlus P A C := by
      dsimp [operatorGaussianPlus, amariExpPlus, amariExpMinus,
        genPhi, qgtPlus, conePlus, coneMinus]
      peirce_nf hP
    rw [hgp, hgp, hPhi, hQ]

/-- The backward paired Gaussian has the same parameter-identifiability property: the two
Peirce off-diagonal corners recover the primal and dual coordinates. -/
theorem operatorGaussianMinus_eq_iff_cone_coordinates_eq
    {P A C A' C' : B} (hP : P * P = P) :
    operatorGaussianMinus P A C = operatorGaussianMinus P A' C' ↔
      conePlus P A = conePlus P A' ∧ coneMinus P C = coneMinus P C' := by
  constructor
  · intro h
    have hp := congrArg (fun X : B => conePlus P X) h
    have hm := congrArg (fun X : B => coneMinus P X) h
    have hupper (A C : B) :
        conePlus P (operatorGaussianMinus P A C) = conePlus P A := by
      dsimp [operatorGaussianMinus, amariExpPlus, amariExpMinus,
        conePlus, coneMinus]
      peirce_nf hP
    have hlower (A C : B) :
        coneMinus P (operatorGaussianMinus P A C) = coneMinus P C := by
      dsimp [operatorGaussianMinus, amariExpPlus, amariExpMinus,
        conePlus, coneMinus]
      peirce_nf hP
    rw [hupper, hupper] at hp
    rw [hlower, hlower] at hm
    exact ⟨hp, hm⟩
  · rintro ⟨hp, hm⟩
    have hPhi : genPhi P A C = genPhi P A' C' := by
      dsimp [genPhi]
      rw [hp, hm]
    have hQ : qgtMinus P A C = qgtMinus P A' C' := by
      dsimp [qgtMinus]
      rw [hm, hp]
    have hgm (A C : B) :
        operatorGaussianMinus P A C = 1 + genPhi P A C + qgtMinus P A C := by
      dsimp [operatorGaussianMinus, amariExpPlus, amariExpMinus,
        genPhi, qgtMinus, conePlus, coneMinus]
      peirce_nf hP
    rw [hgm, hgm, hPhi, hQ]

/-- Two raw parameter pairs are equivalent when they have the same upper and lower Peirce
coordinates. This setoid is the exact algebraic parameter quotient seen by the ordered Gaussian. -/
def operatorGaussianParameterSetoid (P : B) : Setoid (B × B) where
  r x y := conePlus P x.1 = conePlus P y.1 ∧ coneMinus P x.2 = coneMinus P y.2
  iseqv := ⟨by intro x; exact ⟨rfl, rfl⟩,
    by intro x y h; exact ⟨h.1.symm, h.2.symm⟩,
    by intro x y z hxy hyz; exact ⟨hxy.1.trans hyz.1, hxy.2.trans hyz.2⟩⟩

/-- The quotient of parameter pairs by equality of their Peirce off-diagonal coordinates is
bijective with the range of the forward Gaussian realization. This is an algebraic quotient
construction only; it carries no topology or manifold structure. -/
noncomputable def operatorGaussianParameterQuotientEquiv
    {P : B} (hP : P * P = P) :
    Quotient (operatorGaussianParameterSetoid P) ≃
      Set.range (fun x : B × B => operatorGaussianPlus P x.1 x.2) := by
  let f : Quotient (operatorGaussianParameterSetoid P) →
      Set.range (fun x : B × B => operatorGaussianPlus P x.1 x.2) :=
    Quotient.lift
      (fun x => ⟨operatorGaussianPlus P x.1 x.2, ⟨x, rfl⟩⟩)
      (by
        intro x y hxy
        apply Subtype.ext
        exact (operatorGaussianPlus_eq_iff_cone_coordinates_eq hP).2 hxy)
  apply Equiv.ofBijective f
  constructor
  · intro q r h
    refine Quotient.inductionOn₂
      (motive := fun q r => f q = f r → q = r) q r ?_ h
    intro x y hxy
    apply Quotient.sound
    exact (operatorGaussianPlus_eq_iff_cone_coordinates_eq hP).mp
      (congrArg Subtype.val hxy)
  · intro z
    rcases z with ⟨g, ⟨x, rfl⟩⟩
    exact ⟨Quotient.mk _ x, rfl⟩

-- theorem-class: constructive endpoint
/-- **Stages `𝔇₃, 𝔇₄` & `𝔔₂, 𝔔₃` Theorem (`stage_D3_D4_Q2_Q3_paired_operator_gaussians_and_curvature_birth`)**:
In any noncommutative `[Ring B]` with idempotent `P * P = P`:
1. **Expansion & Bridge to `epistemicCornerShear` (`𝔇₃`)**:
   * `operatorGaussianPlus P A C = epistemicCornerShear P A C`,
   * `operatorGaussianPlus P A C = 1 + genPhi P A C + qgtPlus P A C`,
   * `operatorGaussianMinus P A C = 1 + genPhi P A C + qgtMinus P A C`,
   * `operatorGaussianPlusInv P A C = 1 - genPhi P A C + qgtMinus P A C`,
   * `operatorGaussianMinusInv P A C = 1 - genPhi P A C + qgtPlus P A C`.
2. **Exact Series-Free Two-Sided Inversion (`𝔇₃`)**:
   * `operatorGaussianPlus P A C * operatorGaussianPlusInv P A C = 1`,
   * `operatorGaussianPlusInv P A C * operatorGaussianPlus P A C = 1`,
   * `operatorGaussianMinus P A C * operatorGaussianMinusInv P A C = 1`,
   * `operatorGaussianMinusInv P A C * operatorGaussianMinus P A C = 1`,
   * `(1 + genPhi P A C + qgtPlus P A C) * (1 - genPhi P A C + qgtMinus P A C) = 1`,
   * `(1 + genPhi P A C + qgtMinus P A C) * (1 - genPhi P A C + qgtPlus P A C) = 1`.
3. **Birth of Fisher Metric `V` and Berry/Skewness Tensor `Σ` from Cross-Collision (`𝔇₄`)**:
   * `(operatorGaussianPlus P A C - (1 + genPhi P A C)) + (operatorGaussianMinus P A C - (1 + genPhi P A C)) = genV P A C`,
   * `operatorGaussianPlus P A C + operatorGaussianMinus P A C = (2 : ℤ) • (1 + genPhi P A C) + genV P A C`,
   * `comm (amariExpPlus P A) (amariExpMinus P C) = genSig P A C`,
   * `operatorGaussianPlus P A C - operatorGaussianMinus P A C = genSig P A C`,
   * `operatorGaussianPlusInv P A C - operatorGaussianMinusInv P A C = -genSig P A C`.
4. **Faithful `2 × 2` Peirce Matrix Coordinate Realization (`𝔔₂, 𝔔₃`)**:
   * `peirceCoordinateMatrix P (operatorGaussianPlus P A C) = peirceCoordinateMatrix P (amariExpPlus P A) * peirceCoordinateMatrix P (amariExpMinus P C)`,
   * `peirceCoordinateMatrix P (operatorGaussianPlus P A C) true true = P + qgtPlus P A C`,
   * `peirceCoordinateMatrix P (operatorGaussianPlus P A C) false false = 1 - P`,
   * `peirceCoordinateMatrix P (operatorGaussianMinus P A C) true true = P`,
   * `peirceCoordinateMatrix P (operatorGaussianMinus P A C) false false = (1 - P) + qgtMinus P A C`. -/
theorem stage_D3_D4_Q2_Q3_paired_operator_gaussians_and_curvature_birth
    {P : B} (hP : P * P = P) (A C : B) :
    let Φ := genPhi P A C
    let Qp := qgtPlus P A C
    let Qm := qgtMinus P A C
    let V := genV P A C
    let Sig := genSig P A C
    (operatorGaussianPlus P A C = epistemicCornerShear P A C ∧
      operatorGaussianPlus P A C = 1 + Φ + Qp ∧
      operatorGaussianMinus P A C = 1 + Φ + Qm ∧
      operatorGaussianPlusInv P A C = 1 - Φ + Qm ∧
      operatorGaussianMinusInv P A C = 1 - Φ + Qp) ∧
    (operatorGaussianPlus P A C * operatorGaussianPlusInv P A C = 1 ∧
      operatorGaussianPlusInv P A C * operatorGaussianPlus P A C = 1 ∧
      operatorGaussianMinus P A C * operatorGaussianMinusInv P A C = 1 ∧
      operatorGaussianMinusInv P A C * operatorGaussianMinus P A C = 1 ∧
      (1 + Φ + Qp) * (1 - Φ + Qm) = 1 ∧
      (1 + Φ + Qm) * (1 - Φ + Qp) = 1) ∧
    ((operatorGaussianPlus P A C - (1 + Φ)) +
        (operatorGaussianMinus P A C - (1 + Φ)) = V ∧
      operatorGaussianPlus P A C + operatorGaussianMinus P A C =
        (2 : ℤ) • (1 + Φ) + V ∧
      comm (amariExpPlus P A) (amariExpMinus P C) = Sig ∧
      operatorGaussianPlus P A C - operatorGaussianMinus P A C = Sig ∧
      operatorGaussianPlusInv P A C - operatorGaussianMinusInv P A C = -Sig) ∧
    (peirceCoordinateMatrix P (operatorGaussianPlus P A C) =
        peirceCoordinateMatrix P (amariExpPlus P A) *
          peirceCoordinateMatrix P (amariExpMinus P C) ∧
      peirceCoordinateMatrix P (operatorGaussianPlus P A C) true true = P + Qp ∧
      peirceCoordinateMatrix P (operatorGaussianPlus P A C) false false = 1 - P ∧
      peirceCoordinateMatrix P (operatorGaussianMinus P A C) true true = P ∧
      peirceCoordinateMatrix P (operatorGaussianMinus P A C) false false = (1 - P) + Qm) := by
  intro Φ Qp Qm V Sig
  refine ⟨⟨rfl,
           by dsimp [operatorGaussianPlus, amariExpPlus, amariExpMinus, Φ, Qp, qgtPlus]; peirce_nf hP,
           by dsimp [operatorGaussianMinus, amariExpPlus, amariExpMinus, Φ, Qm, qgtMinus]; peirce_nf hP,
           by dsimp [operatorGaussianPlusInv, amariExpPlus, amariExpMinus, Φ, Qm, qgtMinus]; peirce_nf hP,
           by dsimp [operatorGaussianMinusInv, amariExpPlus, amariExpMinus, Φ, Qp, qgtPlus]; peirce_nf hP⟩,
    ⟨by dsimp [operatorGaussianPlus, operatorGaussianPlusInv, amariExpPlus, amariExpMinus]; peirce_nf hP,
     by dsimp [operatorGaussianPlus, operatorGaussianPlusInv, amariExpPlus, amariExpMinus]; peirce_nf hP,
     by dsimp [operatorGaussianMinus, operatorGaussianMinusInv, amariExpPlus, amariExpMinus]; peirce_nf hP,
     by dsimp [operatorGaussianMinus, operatorGaussianMinusInv, amariExpPlus, amariExpMinus]; peirce_nf hP,
     by dsimp [Φ, Qp, Qm, qgtPlus, qgtMinus]; peirce_nf hP,
     by dsimp [Φ, Qp, Qm, qgtPlus, qgtMinus]; peirce_nf hP⟩,
    ⟨by dsimp [operatorGaussianPlus, operatorGaussianMinus, amariExpPlus, amariExpMinus, Φ, V]; peirce_nf hP,
     by dsimp [operatorGaussianPlus, operatorGaussianMinus, amariExpPlus, amariExpMinus, Φ, V]; peirce_nf hP,
     by dsimp [amariExpPlus, amariExpMinus, Sig]; peirce_nf hP,
     by dsimp [operatorGaussianPlus, operatorGaussianMinus, amariExpPlus, amariExpMinus, Sig]; peirce_nf hP,
     by dsimp [operatorGaussianPlusInv, operatorGaussianMinusInv, amariExpPlus, amariExpMinus, Sig]; peirce_nf hP⟩,
    ⟨peirceCoordinateMatrix_mul hP (amariExpPlus P A) (amariExpMinus P C),
     by dsimp [peirceCoordinateMatrix, peirceCorner, operatorGaussianPlus, amariExpPlus, amariExpMinus, Qp, qgtPlus]; peirce_nf hP,
     by dsimp [peirceCoordinateMatrix, peirceCorner, operatorGaussianPlus, amariExpPlus, amariExpMinus]; peirce_nf hP,
     by dsimp [peirceCoordinateMatrix, peirceCorner, operatorGaussianMinus, amariExpPlus, amariExpMinus]; peirce_nf hP,
     by dsimp [peirceCoordinateMatrix, peirceCorner, operatorGaussianMinus, amariExpPlus, amariExpMinus, Qm, qgtMinus]; peirce_nf hP⟩⟩

end PairedOperatorGaussiansAndCurvatureBirth

/-- The ordered Mathlib exponential products representing the forward/backward Gaussians have
the reversed negative-exponential products as exact two-sided inverses. This transports the
already-proved polynomial Gaussian inverse identities to Mathlib's nilpotent exponential. -/
theorem mathlib_nilpotent_gaussian_products_are_two_sided_inverses
    {B : Type*} [Ring B] [Algebra ℚ B]
    {P : B} (hP : P * P = P) (A C : B) :
    (IsNilpotent.exp (conePlus P A) * IsNilpotent.exp (coneMinus P C)) *
        (IsNilpotent.exp (coneMinus P (-C)) * IsNilpotent.exp (conePlus P (-A))) = 1 ∧
    (IsNilpotent.exp (coneMinus P (-C)) * IsNilpotent.exp (conePlus P (-A))) *
        (IsNilpotent.exp (conePlus P A) * IsNilpotent.exp (coneMinus P C)) = 1 ∧
    (IsNilpotent.exp (coneMinus P C) * IsNilpotent.exp (conePlus P A)) *
        (IsNilpotent.exp (conePlus P (-A)) * IsNilpotent.exp (coneMinus P (-C))) = 1 ∧
    (IsNilpotent.exp (conePlus P (-A)) * IsNilpotent.exp (coneMinus P (-C))) *
        (IsNilpotent.exp (coneMinus P C) * IsNilpotent.exp (conePlus P A)) = 1 := by
  have hD3 := stage_D3_D4_Q2_Q3_paired_operator_gaussians_and_curvature_birth hP A C
  have hGp := operatorGaussianPlus_eq_mathlib_exp_product hP A C
  have hGm := operatorGaussianMinus_eq_mathlib_exp_product hP A C
  have hGpi := operatorGaussianPlusInv_eq_mathlib_exp_product hP A C
  have hGmi := operatorGaussianMinusInv_eq_mathlib_exp_product hP A C
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hGp, ← hGpi]
    exact hD3.2.1.1
  · rw [← hGpi, ← hGp]
    exact hD3.2.1.2.1
  · rw [← hGm, ← hGmi]
    exact hD3.2.1.2.2.1
  · rw [← hGmi, ← hGm]
    exact hD3.2.1.2.2.2.1

/-! ===========================================================================
    Section 5: Stages `𝔇₅, 𝔇₆` & `𝔔₅` — Amari Dual Connections (`∇^(e), ∇^(m)`),
    Midpoint-Skewness Split, Sum–Difference Crossover, & Operator Pythagorean Theorem
    =========================================================================== -/

section AmariDualConnectionsAndOperatorPythagorean

variable {B : Type*} [Ring B]

/-- The Primal (`e`-Flat) Operator Connection `amariEConnection P Ω := sheetPlusConnection P Ω`
(`∇^(e) = ∇₊ = P * Ω * P`). -/
def amariEConnection (P Ω : B) : B :=
  InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection P Ω

/-- The Dual (`m`-Flat) Operator Connection `amariMConnection P Ω := sheetMinusConnection P Ω`
(`∇^(m) = ∇₋ = (1 - P) * Ω * (1 - P)`). -/
def amariMConnection (P Ω : B) : B :=
  InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection P Ω

/-- Twice the Self-Dual Levi-Civita Midpoint Connection
`amariDoubledMidpoint P Ω := sheetConnectionSum P Ω` (`2 ∇^(0) = ∇^(e) + ∇^(m) = Γ_sum`). -/
def amariDoubledMidpoint (P Ω : B) : B :=
  InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnectionSum P Ω

/-- The Amari–Chentsov Skewness / Difference Connection
`amariSkewnessConnection P Ω := sheetConnectionDiff P Ω` (`∇^(e) - ∇^(m) = Γ_diff`). -/
def amariSkewnessConnection (P Ω : B) : B :=
  InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnectionDiff P Ω

-- theorem-class: constructive endpoint
/-- **Stages `𝔇₅, 𝔇₆` & `𝔔₅` Theorem (`stage_D5_D6_Q5_amari_dual_connections_and_operator_pythagorean_theorem`)**:
In any noncommutative `[Ring B]` with idempotent `P * P = P`:
1. **Amari Midpoint–Skewness Decomposition & Orthogonal Sheet Split (`𝔇₅`)**:
   * `amariEConnection P Ω + amariMConnection P Ω = amariDoubledMidpoint P Ω`,
   * `amariEConnection P Ω - amariMConnection P Ω = amariSkewnessConnection P Ω`,
   * `(2 : ℤ) • amariEConnection P Ω = amariDoubledMidpoint P Ω + amariSkewnessConnection P Ω`,
   * `(2 : ℤ) • amariMConnection P Ω = amariDoubledMidpoint P Ω - amariSkewnessConnection P Ω`,
   * `invS P * amariDoubledMidpoint P Ω = amariSkewnessConnection P Ω`,
   * `invS P * amariSkewnessConnection P Ω = amariDoubledMidpoint P Ω`,
   * `amariEConnection P Ω * amariMConnection P Ω = 0` and
     `amariMConnection P Ω * amariEConnection P Ω = 0`,
   * `amariDoubledMidpoint P Ω * amariDoubledMidpoint P Ω =
       amariEConnection P Ω * amariEConnection P Ω + amariMConnection P Ω * amariMConnection P Ω`,
   * `amariSkewnessConnection P Ω * amariSkewnessConnection P Ω =
       amariDoubledMidpoint P Ω * amariDoubledMidpoint P Ω`.
2. **Sum–Difference Parallel Transport Crossover & Endogenous Realization (`Ω = V`, `𝔇₅, 𝔔₅`)**:
   * `comm (amariSkewnessConnection P Ω) (genPhi P A C) = anticomm (amariDoubledMidpoint P Ω) (genJ P A C)`,
   * `anticomm (amariSkewnessConnection P Ω) (genPhi P A C) = comm (amariDoubledMidpoint P Ω) (genJ P A C)`,
   * `amariEConnection P (genV P A C) = qgtPlus P A C`,
   * `amariMConnection P (genV P A C) = qgtMinus P A C`,
   * `amariDoubledMidpoint P (genV P A C) = genV P A C`,
   * `amariSkewnessConnection P (genV P A C) = genSig P A C`,
   * `comm (genV P A C) (genPhi P A C) = 0` and
     `comm (genSig P A C) (genPhi P A C) = anticomm (genV P A C) (genJ P A C)`.
3. **The Operator Pythagorean Theorem (`𝔇₆`)**:
   * `qgtPlus P A C * qgtMinus P A C = 0` and `qgtMinus P A C * qgtPlus P A C = 0`,
   * `genV P A C * genV P A C = qgtPlus P A C * qgtPlus P A C + qgtMinus P A C * qgtMinus P A C`,
   * `genSig P A C * genSig P A C = qgtPlus P A C * qgtPlus P A C + qgtMinus P A C * qgtMinus P A C`,
   * `genV P A C * genV P A C = genSig P A C * genSig P A C`,
   * `genV P A C * genSig P A C = qgtPlus P A C * qgtPlus P A C - qgtMinus P A C * qgtMinus P A C`,
   * `(operatorGaussianPlus P A C - (1 + genPhi P A C)) ^ 2 +
      (operatorGaussianMinus P A C - (1 + genPhi P A C)) ^ 2 = genV P A C * genV P A C`. -/
theorem stage_D5_D6_Q5_amari_dual_connections_and_operator_pythagorean_theorem
    {P : B} (hP : P * P = P) (Ω A C : B) :
    let Φ := genPhi P A C
    let J := genJ P A C
    let Qp := qgtPlus P A C
    let Qm := qgtMinus P A C
    let V := genV P A C
    let Sig := genSig P A C
    (amariEConnection P Ω + amariMConnection P Ω = amariDoubledMidpoint P Ω ∧
      amariEConnection P Ω - amariMConnection P Ω = amariSkewnessConnection P Ω ∧
      (2 : ℤ) • amariEConnection P Ω = amariDoubledMidpoint P Ω + amariSkewnessConnection P Ω ∧
      (2 : ℤ) • amariMConnection P Ω = amariDoubledMidpoint P Ω - amariSkewnessConnection P Ω ∧
      invS P * amariDoubledMidpoint P Ω = amariSkewnessConnection P Ω ∧
      invS P * amariSkewnessConnection P Ω = amariDoubledMidpoint P Ω ∧
      amariEConnection P Ω * amariMConnection P Ω = 0 ∧
      amariMConnection P Ω * amariEConnection P Ω = 0 ∧
      amariDoubledMidpoint P Ω * amariDoubledMidpoint P Ω =
        amariEConnection P Ω * amariEConnection P Ω +
          amariMConnection P Ω * amariMConnection P Ω ∧
      amariSkewnessConnection P Ω * amariSkewnessConnection P Ω =
        amariDoubledMidpoint P Ω * amariDoubledMidpoint P Ω) ∧
    (comm (amariSkewnessConnection P Ω) Φ = anticomm (amariDoubledMidpoint P Ω) J ∧
      anticomm (amariSkewnessConnection P Ω) Φ = comm (amariDoubledMidpoint P Ω) J ∧
      amariEConnection P V = Qp ∧
      amariMConnection P V = Qm ∧
      amariDoubledMidpoint P V = V ∧
      amariSkewnessConnection P V = Sig ∧
      comm V Φ = 0 ∧
      comm Sig Φ = anticomm V J) ∧
    (Qp * Qm = 0 ∧
      Qm * Qp = 0 ∧
      V * V = Qp * Qp + Qm * Qm ∧
      Sig * Sig = Qp * Qp + Qm * Qm ∧
      V * V = Sig * Sig ∧
      V * Sig = Qp * Qp - Qm * Qm ∧
      (operatorGaussianPlus P A C - (1 + Φ)) * (operatorGaussianPlus P A C - (1 + Φ)) +
        (operatorGaussianMinus P A C - (1 + Φ)) * (operatorGaussianMinus P A C - (1 + Φ)) =
        V * V) := by
  intro Φ J Qp Qm V Sig
  have hCross := InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnection_sum_difference_crossover hP Ω A C
  have hOrth := qgt_cycles_orthogonal hP A C
  refine ⟨⟨rfl, rfl,
           by dsimp [amariEConnection, amariDoubledMidpoint, amariSkewnessConnection,
                InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnectionSum,
                InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnectionDiff]; abel,
           by dsimp [amariMConnection, amariDoubledMidpoint, amariSkewnessConnection,
                InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnectionSum,
                InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnectionDiff]; abel,
           by dsimp [amariDoubledMidpoint, amariSkewnessConnection,
                InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnectionSum,
                InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnectionDiff,
                InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection,
                InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection]; peirce_nf hP,
           by dsimp [amariDoubledMidpoint, amariSkewnessConnection,
                InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnectionSum,
                InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnectionDiff,
                InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection,
                InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection]; peirce_nf hP,
           by dsimp [amariEConnection, amariMConnection,
                InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection,
                InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection]; peirce_nf hP,
           by dsimp [amariEConnection, amariMConnection,
                InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection,
                InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection]; peirce_nf hP,
           by dsimp [amariEConnection, amariMConnection, amariDoubledMidpoint,
                InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnectionSum,
                InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection,
                InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection]; peirce_nf hP,
           by dsimp [amariDoubledMidpoint, amariSkewnessConnection,
                InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnectionSum,
                InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnectionDiff,
                InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection,
                InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection]; peirce_nf hP⟩,
    ⟨hCross.1, hCross.2.1,
     by dsimp [amariEConnection, InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection, V, Qp, qgtPlus]; peirce_nf hP,
     by dsimp [amariMConnection, InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection, V, Qm, qgtMinus]; peirce_nf hP,
     by dsimp [amariDoubledMidpoint, InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnectionSum,
          InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection,
          InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection, V]; peirce_nf hP,
     by dsimp [amariSkewnessConnection, InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnectionDiff,
          InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection,
          InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection, V, Sig]; peirce_nf hP,
     by dsimp [V, Φ]; peirce_nf hP,
     by dsimp [Sig, Φ, V, J]; peirce_nf hP⟩,
    ⟨hOrth.1, hOrth.2,
     by dsimp [V, Qp, Qm, qgtPlus, qgtMinus]; peirce_nf hP,
     by dsimp [Sig, Qp, Qm, qgtPlus, qgtMinus]; peirce_nf hP,
     by dsimp [V, Sig]; peirce_nf hP,
     by dsimp [V, Sig, Qp, Qm, qgtPlus, qgtMinus]; peirce_nf hP,
     by dsimp [operatorGaussianPlus, operatorGaussianMinus, amariExpPlus, amariExpMinus, Φ, V]; peirce_nf hP⟩⟩

end AmariDualConnectionsAndOperatorPythagorean

/-! ===========================================================================
    Section 6: Stage `𝔔₄` — The Theorem of Textbook Trace-First Blindness
    vs. Chiral Supertrace Recovery (`tr(Σ) = 0` vs. `Str(Σ) = tr(S_P Σ) = tr(V)`)
    =========================================================================== -/

section TraceFirstBlindnessAndChiralSupertrace

variable {B : Type*} [Ring B]
variable {K : Type*} [AddCommGroup K]

/-- The **Chiral Supertrace** `chiralSupertrace tr P Y := tr (invS P * Y)` associated
to an additive trace `tr : B →+ K` and Peirce grading involution `S_P = invS P`. -/
def chiralSupertrace (tr : B →+ K) (P Y : B) : K :=
  tr (invS P * Y)

-- theorem-class: constructive endpoint
/-- **Stage `𝔔₄` Theorem (`stage_Q4_theorem_trace_first_blindness_and_chiral_supertrace_recovery`)**:
For this Peirce construction, cyclicity of `tr : B →+ K` implies that `tr` annihilates the
operator difference `Σ` and its displayed Gaussian difference; the chiral functional
`Y ↦ tr (invS P * Y)` recovers `tr(V)` from `Σ`. This is an algebraic limitation and recovery
identity for these specified operators, not a historical explanation for textbook practice or a
general classification theorem. Let `tr` satisfy (`∀ X Y : B, tr (X * Y) = tr (Y * X)`). Then for any
idempotent `P * P = P` and any `A, C : B`:
1. **Vanishing of Off-Diagonal Coordinate Traces**:
   * `tr (conePlus P A) = 0` and `tr (coneMinus P C) = 0`,
   * `tr (genPhi P A C) = 0` and `tr (genJ P A C) = 0`.
2. **Cyclic Collapse of the Chiral Gramians & Operator Gaussians**:
   * `tr (qgtPlus P A C) = tr (qgtMinus P A C)`,
   * `tr (operatorGaussianPlus P A C) = tr 1 + tr (qgtPlus P A C)`,
   * `tr (operatorGaussianMinus P A C) = tr 1 + tr (qgtPlus P A C)`,
   * `tr (operatorGaussianPlus P A C) = tr (operatorGaussianMinus P A C)`.
3. **Textbook Trace-First Blindness (Erasure of the Skewness/Berry Tensor `Σ`)**:
   * `tr (genSig P A C) = 0`,
   * `tr (comm (amariExpPlus P A) (amariExpMinus P C)) = 0`,
   * `tr (operatorGaussianPlus P A C - operatorGaussianMinus P A C) = 0`,
   * `tr (genV P A C) = (2 : ℤ) • tr (qgtPlus P A C)`.
4. **Chiral Supertrace Recovery (`Str(Y) = tr(S_P Y)`)**:
   * `chiralSupertrace tr P (genV P A C) = 0`,
   * `chiralSupertrace tr P (genSig P A C) = tr (genV P A C)`,
   * `chiralSupertrace tr P (genSig P A C) = (2 : ℤ) • tr (qgtPlus P A C)`,
   * `chiralSupertrace tr P (operatorGaussianPlus P A C - operatorGaussianMinus P A C) = tr (genV P A C)`,
   * `tr (amariSkewnessConnection P (genV P A C)) = 0` and
     `chiralSupertrace tr P (amariSkewnessConnection P (genV P A C)) = tr (genV P A C)`. -/
theorem stage_Q4_theorem_trace_first_blindness_and_chiral_supertrace_recovery
    {P : B} (hP : P * P = P) (tr : B →+ K)
    (hTr : ∀ X Y : B, tr (X * Y) = tr (Y * X)) (A C : B) :
    let Qp := qgtPlus P A C
    let Qm := qgtMinus P A C
    let V := genV P A C
    let Sig := genSig P A C
    (tr (conePlus P A) = 0 ∧
      tr (coneMinus P C) = 0 ∧
      tr (genPhi P A C) = 0 ∧
      tr (genJ P A C) = 0) ∧
    (tr Qp = tr Qm ∧
      tr (operatorGaussianPlus P A C) = tr 1 + tr Qp ∧
      tr (operatorGaussianMinus P A C) = tr 1 + tr Qp ∧
      tr (operatorGaussianPlus P A C) = tr (operatorGaussianMinus P A C)) ∧
    (tr Sig = 0 ∧
      tr (comm (amariExpPlus P A) (amariExpMinus P C)) = 0 ∧
      tr (operatorGaussianPlus P A C - operatorGaussianMinus P A C) = 0 ∧
      tr V = (2 : ℤ) • tr Qp) ∧
    (chiralSupertrace tr P V = 0 ∧
      chiralSupertrace tr P Sig = tr V ∧
      chiralSupertrace tr P Sig = (2 : ℤ) • tr Qp ∧
      chiralSupertrace tr P (operatorGaussianPlus P A C - operatorGaussianMinus P A C) = tr V ∧
      tr (amariSkewnessConnection P V) = 0 ∧
      chiralSupertrace tr P (amariSkewnessConnection P V) = tr V) := by
  intro Qp Qm V Sig
  have hTrNp : tr (conePlus P A) = 0 := by
    have h1 : conePlus P A = P * conePlus P A := (P_mul_conePlus hP A).symm
    have h2 : conePlus P A * P = 0 := conePlus_mul_P hP A
    calc
      tr (conePlus P A) = tr (P * conePlus P A) := by rw [← h1]
      _ = tr (conePlus P A * P) := hTr P (conePlus P A)
      _ = tr 0 := by rw [h2]
      _ = 0 := map_zero tr
  have hTrNm : tr (coneMinus P C) = 0 := by
    have h1 : coneMinus P C = coneMinus P C * P := (coneMinus_mul_P hP C).symm
    have h2 : P * coneMinus P C = 0 := P_mul_coneMinus hP C
    calc
      tr (coneMinus P C) = tr (coneMinus P C * P) := by rw [← h1]
      _ = tr (P * coneMinus P C) := hTr (coneMinus P C) P
      _ = tr 0 := by rw [h2]
      _ = 0 := map_zero tr
  have hTrPhi : tr (genPhi P A C) = 0 := by
    dsimp [genPhi]
    rw [map_add, hTrNp, hTrNm, add_zero]
  have hTrJ : tr (genJ P A C) = 0 := by
    dsimp [genJ]
    rw [map_sub, hTrNp, hTrNm, sub_zero]
  have hTrQpQm : tr Qp = tr Qm := by
    dsimp [Qp, Qm, qgtPlus, qgtMinus]
    exact hTr (conePlus P A) (coneMinus P C)
  have hGpExp : operatorGaussianPlus P A C = 1 + genPhi P A C + Qp :=
    (stage_D3_D4_Q2_Q3_paired_operator_gaussians_and_curvature_birth hP A C).1.2.1
  have hGmExp : operatorGaussianMinus P A C = 1 + genPhi P A C + Qm :=
    (stage_D3_D4_Q2_Q3_paired_operator_gaussians_and_curvature_birth hP A C).1.2.2.1
  have hTrGp : tr (operatorGaussianPlus P A C) = tr 1 + tr Qp := by
    rw [hGpExp, map_add, map_add, hTrPhi, add_zero]
  have hTrGm : tr (operatorGaussianMinus P A C) = tr 1 + tr Qp := by
    rw [hGmExp, map_add, map_add, hTrPhi, add_zero, hTrQpQm]
  have hTrSig : tr Sig = 0 := by
    have hSigEq : Sig = Qp - Qm := rfl
    rw [hSigEq, map_sub, hTrQpQm, sub_self]
  have hCommExp : comm (amariExpPlus P A) (amariExpMinus P C) = Sig :=
    (stage_D3_D4_Q2_Q3_paired_operator_gaussians_and_curvature_birth hP A C).2.2.1.2.2.1
  have hDiffG : operatorGaussianPlus P A C - operatorGaussianMinus P A C = Sig :=
    (stage_D3_D4_Q2_Q3_paired_operator_gaussians_and_curvature_birth hP A C).2.2.1.2.2.2.1
  have hTrV : tr V = (2 : ℤ) • tr Qp := by
    have hVEq : V = Qp + Qm := rfl
    rw [hVEq, map_add, ← hTrQpQm, two_zsmul]
  have hSV : invS P * V = Sig := by dsimp [V, Sig]; peirce_nf hP
  have hSSig : invS P * Sig = V := by dsimp [V, Sig]; peirce_nf hP
  have hStrV : chiralSupertrace tr P V = 0 := by
    dsimp [chiralSupertrace]
    rw [hSV, hTrSig]
  have hStrSig : chiralSupertrace tr P Sig = tr V := by
    dsimp [chiralSupertrace]
    rw [hSSig]
  have hSkewV : amariSkewnessConnection P V = Sig :=
    (stage_D5_D6_Q5_amari_dual_connections_and_operator_pythagorean_theorem hP V A C).2.1.2.2.2.2.2.1
  refine ⟨⟨hTrNp, hTrNm, hTrPhi, hTrJ⟩,
    ⟨hTrQpQm, hTrGp, hTrGm, by rw [hTrGp, hTrGm]⟩,
    ⟨hTrSig, by rw [hCommExp, hTrSig], by rw [hDiffG, hTrSig], hTrV⟩,
    ⟨hStrV, hStrSig, by rw [hStrSig, hTrV], by rw [hDiffG, hStrSig],
     by rw [hSkewV, hTrSig], by rw [hSkewV, hStrSig]⟩⟩

-- theorem-class: constructive endpoint
/-- **Concrete Matrix Trace-First Blindness vs. Chiral Supertrace Recovery
(`matrix_trace_first_blindness_and_chiral_supertrace_recovery`)**:
Instantiates `stage_Q4_theorem_trace_first_blindness_and_chiral_supertrace_recovery`
for `Matrix.trace : Matrix n n R →+ R` over any finite index type `n` and commutative
ring `R`, proving that `Matrix.trace (genSig P A C) = 0` whereas
`Matrix.trace (invS P * genSig P A C) = Matrix.trace (genV P A C) = (2 : ℤ) • Matrix.trace (qgtPlus P A C)`. -/
theorem matrix_trace_first_blindness_and_chiral_supertrace_recovery
    {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R]
    {P : Matrix n n R} (hP : P * P = P) (A C : Matrix n n R) :
    Matrix.trace (qgtPlus P A C) = Matrix.trace (qgtMinus P A C) ∧
    Matrix.trace (operatorGaussianPlus P A C) = Matrix.trace (operatorGaussianMinus P A C) ∧
    Matrix.trace (genSig P A C) = 0 ∧
    Matrix.trace (genV P A C) = (2 : ℤ) • Matrix.trace (qgtPlus P A C) ∧
    Matrix.trace (invS P * genV P A C) = 0 ∧
    Matrix.trace (invS P * genSig P A C) = Matrix.trace (genV P A C) ∧
    Matrix.trace (invS P * genSig P A C) = (2 : ℤ) • Matrix.trace (qgtPlus P A C) := by
  let trAddHom : Matrix n n R →+ R := (Matrix.traceLinearMap n R R).toAddMonoidHom
  have hCyclic : ∀ X Y : Matrix n n R, trAddHom (X * Y) = trAddHom (Y * X) :=
    fun X Y => Matrix.trace_mul_comm X Y
  have hQ4 := stage_Q4_theorem_trace_first_blindness_and_chiral_supertrace_recovery
    hP trAddHom hCyclic A C
  exact ⟨hQ4.2.1.1, hQ4.2.1.2.2.2, hQ4.2.2.1.1, hQ4.2.2.1.2.2.2,
    hQ4.2.2.2.1, hQ4.2.2.2.2.1, hQ4.2.2.2.2.2.1⟩

/-- A concrete two-dimensional rational matrix witness: the skewness operator is
nonzero although its ordinary trace vanishes, and the chiral supertrace reads the
nonzero metric trace. Thus trace cancellation does not imply operator cancellation.
The example is specifically `Matrix (Fin 2) (Fin 2) ℚ`; it is not an assertion
that every Peirce skewness operator is nonzero. -/
theorem two_by_two_matrix_trace_blindness_has_nonzero_witness :
    let P : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, 0]
    let A : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 0, 0]
    let C : Matrix (Fin 2) (Fin 2) ℚ := !![0, 0; 1, 0]
    Matrix.trace (genSig P A C) = 0 ∧
      Matrix.trace (invS P * genSig P A C) = 2 ∧
      genSig P A C ≠ 0 ∧
      conePlus P A * coneMinus P C - coneMinus P C * conePlus P A ≠ 0 := by
  intro P A C
  have hSig : genSig P A C = !![1, 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [P, A, C, genSig, OperatorAlgebra.PeirceSpine.comm, conePlus, coneMinus,
        Matrix.mul_apply, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail,
        Matrix.one_apply, Fin.sum_univ_two]
  have hSuper : invS P * genSig P A C = !![1, 0; 0, 1] := by
    rw [hSig]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [P, invS, Matrix.mul_apply, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail,
        Matrix.one_apply, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hSig]
    norm_num [Matrix.trace]
  · rw [hSuper]
    norm_num [Matrix.trace]
  · rw [hSig]
    intro hz
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 0 0) hz
    norm_num at h00
  · change genSig P A C ≠ 0
    rw [hSig]
    intro hz
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 0 0) hz
    norm_num at h00

/-- Native Mathlib nilpotent exponentials exhibit the same trace/supertrace split as
their Peirce polynomial representatives: cyclic trace erases the cross-wing commutator,
while the chiral readout recovers the trace of the anticommutator metric. -/
theorem mathlib_nilpotent_exp_commutator_trace_supertrace
    {B : Type*} [Ring B] [Algebra ℚ B]
    {K : Type*} [AddCommGroup K]
    {P : B} (hP : P * P = P) (tr : B →+ K)
    (hTr : ∀ X Y : B, tr (X * Y) = tr (Y * X)) (A C : B) :
    tr (comm (IsNilpotent.exp (conePlus P A))
      (IsNilpotent.exp (coneMinus P C))) = 0 ∧
    chiralSupertrace tr P
      (comm (IsNilpotent.exp (conePlus P A))
        (IsNilpotent.exp (coneMinus P C))) = tr (genV P A C) := by
  rw [mathlib_nilpotent_exp_commutator_eq_genSig hP A C]
  have hQ := stage_Q4_theorem_trace_first_blindness_and_chiral_supertrace_recovery
    hP tr hTr A C
  exact ⟨hQ.2.2.1.1, hQ.2.2.2.2.1⟩

end TraceFirstBlindnessAndChiralSupertrace

/-! ===========================================================================
    Section 7: Stages `𝔇₇` & `𝔔₆` — All-Operator Legendre Resolvent Duality
    (`η_± = W_± Φ`), Operator Bregman Quadratic Remainder, & Fréchet Closure
    =========================================================================== -/

section LegendreResolventAndBregmanClosure

variable {B : Type*} [Ring B]

/-- The All-Operator Legendre Expectation Coordinate Map
`amariLegendreEta W Φ := W * Φ` (`η_± = (1 ± V)⁻¹ Φ`). -/
def amariLegendreEta (W Φ : B) : B :=
  W * Φ

/-- The algebraic rational part `V * W - V` of the Operator Bregman Divergence
`𝒟₋(V) = V(1 - V)⁻¹ + log(1 - V)` at first-order subtraction `log(1 - V) ≈ -V`. -/
def amariOperatorBregmanQuadPart (V W : B) : B :=
  V * W - V

-- theorem-class: constructive endpoint
/-- **Stages `𝔇₇` & `𝔔₆` Theorem (`stage_D7_Q6_legendre_resolvent_duality_and_bregman_closure`)**:
In any noncommutative `[Ring B]` with idempotent `P * P = P`, let `V = genV P A C`
and `Φ = genPhi P A C`, and let `W_plus` and `W_minus` be two-sided inverses of
`1 + V` and `1 - V` respectively:
1. **Resolvent Commutation & Legendre Coordinate Equations**:
   * `(1 + V) * amariLegendreEta W_plus Φ = Φ` and `amariLegendreEta W_plus Φ = Φ * W_plus`,
   * `(1 - V) * amariLegendreEta W_minus Φ = Φ` and `amariLegendreEta W_minus Φ = Φ * W_minus`.
2. **Primal–Dual Legendre Contraction (`Φ * η_±`)**:
   * `Φ * amariLegendreEta W_plus Φ = V * W_plus` and `1 - V * W_plus = W_plus`,
   * `Φ * amariLegendreEta W_minus Φ = V * W_minus` and `W_minus - 1 = V * W_minus`.
3. **Algebraic Operator Bregman Quadratic Remainder Factorization** (this is an identity, not by itself a positivity theorem):
   * `(1 - V) * amariOperatorBregmanQuadPart V W_minus = V * V`,
   * `amariOperatorBregmanQuadPart V W_minus = (V * V) * W_minus`,
   * `amariOperatorBregmanQuadPart V W_minus = (Φ * amariLegendreEta W_minus Φ) * V`.
4. **Chiral Wing Factorization of the Legendre Moment Map**:
   * `P * amariLegendreEta W_plus Φ * (1 - P) = W_plus * conePlus P A`,
   * `(1 - P) * amariLegendreEta W_plus Φ * P = W_plus * coneMinus P C`. -/
theorem stage_D7_Q6_legendre_resolvent_duality_and_bregman_closure
    {P : B} (hP : P * P = P) (A C W_plus W_minus : B)
    (hWp_right : (1 + genV P A C) * W_plus = 1)
    (hWp_left : W_plus * (1 + genV P A C) = 1)
    (hWm_right : (1 - genV P A C) * W_minus = 1)
    (hWm_left : W_minus * (1 - genV P A C) = 1) :
    let Φ := genPhi P A C
    let V := genV P A C
    ((1 + V) * amariLegendreEta W_plus Φ = Φ ∧
      amariLegendreEta W_plus Φ = Φ * W_plus ∧
      (1 - V) * amariLegendreEta W_minus Φ = Φ ∧
      amariLegendreEta W_minus Φ = Φ * W_minus) ∧
    (Φ * amariLegendreEta W_plus Φ = V * W_plus ∧
      1 - V * W_plus = W_plus ∧
      Φ * amariLegendreEta W_minus Φ = V * W_minus ∧
      W_minus - 1 = V * W_minus) ∧
    ((1 - V) * amariOperatorBregmanQuadPart V W_minus = V * V ∧
      amariOperatorBregmanQuadPart V W_minus = (V * V) * W_minus ∧
      amariOperatorBregmanQuadPart V W_minus = (Φ * amariLegendreEta W_minus Φ) * V) ∧
    (P * amariLegendreEta W_plus Φ * (1 - P) = W_plus * conePlus P A ∧
      (1 - P) * amariLegendreEta W_plus Φ * P = W_plus * coneMinus P C) := by
  intro Φ V
  have hVPhi : V * Φ = Φ * V := by
    have h0 : comm V Φ = 0 := by dsimp [V, Φ]; peirce_nf hP
    exact sub_eq_zero.mp h0
  have hPhiSq : Φ * Φ = V := by dsimp [Φ, V]; peirce_nf hP
  have hVV : V * V = V * V := rfl
  have hWpPhi : W_plus * Φ = Φ * W_plus := by
    have hKPhi : (1 + V) * Φ = Φ * (1 + V) := by
      rw [add_mul, one_mul, mul_add, mul_one, hVPhi]
    calc
      W_plus * Φ = W_plus * Φ * 1 := (mul_one _).symm
      _ = W_plus * Φ * ((1 + V) * W_plus) := by rw [hWp_right]
      _ = W_plus * (Φ * (1 + V)) * W_plus := by noncomm_ring
      _ = W_plus * ((1 + V) * Φ) * W_plus := by rw [← hKPhi]
      _ = (W_plus * (1 + V)) * Φ * W_plus := by noncomm_ring
      _ = 1 * Φ * W_plus := by rw [hWp_left]
      _ = Φ * W_plus := by noncomm_ring
  have hWmPhi : W_minus * Φ = Φ * W_minus := by
    have hKPhi : (1 - V) * Φ = Φ * (1 - V) := by
      rw [sub_mul, one_mul, mul_sub, mul_one, hVPhi]
    calc
      W_minus * Φ = W_minus * Φ * 1 := (mul_one _).symm
      _ = W_minus * Φ * ((1 - V) * W_minus) := by rw [hWm_right]
      _ = W_minus * (Φ * (1 - V)) * W_minus := by noncomm_ring
      _ = W_minus * ((1 - V) * Φ) * W_minus := by rw [← hKPhi]
      _ = (W_minus * (1 - V)) * Φ * W_minus := by noncomm_ring
      _ = 1 * Φ * W_minus := by rw [hWm_left]
      _ = Φ * W_minus := by noncomm_ring
  have hWpV : V * W_plus = 1 - W_plus := by
    calc
      V * W_plus = (1 + V) * W_plus - W_plus := by noncomm_ring
      _ = 1 - W_plus := by rw [hWp_right]
  have hWmV : V * W_minus = W_minus - 1 := by
    calc
      V * W_minus = W_minus - (1 - V) * W_minus := by noncomm_ring
      _ = W_minus - 1 := by rw [hWm_right]
  have hWmVComm : W_minus * V = V * W_minus := by
    calc
      W_minus * V = W_minus - W_minus * (1 - V) := by noncomm_ring
      _ = W_minus - 1 := by rw [hWm_left]
      _ = V * W_minus := hWmV.symm
  have hWpP : W_plus * P = P * W_plus := by
    have hVP : V * P = P * V := by dsimp [V]; peirce_nf hP
    have hKP : (1 + V) * P = P * (1 + V) := by
      rw [add_mul, one_mul, mul_add, mul_one, hVP]
    calc
      W_plus * P = W_plus * P * 1 := by noncomm_ring
      _ = W_plus * P * ((1 + V) * W_plus) := by rw [hWp_right]
      _ = W_plus * (P * (1 + V)) * W_plus := by noncomm_ring
      _ = W_plus * ((1 + V) * P) * W_plus := by rw [← hKP]
      _ = (W_plus * (1 + V)) * P * W_plus := by noncomm_ring
      _ = 1 * P * W_plus := by rw [hWp_left]
      _ = P * W_plus := by noncomm_ring
  have hWpP' : W_plus * P = P * W_plus := hWpP
  have hEtaPlusEq : (1 + V) * amariLegendreEta W_plus Φ = Φ := by
    dsimp [amariLegendreEta]
    rw [← mul_assoc, hWp_right, one_mul]
  have hEtaMinusEq : (1 - V) * amariLegendreEta W_minus Φ = Φ := by
    dsimp [amariLegendreEta]
    rw [← mul_assoc, hWm_right, one_mul]
  have hPhiEtaPlus : Φ * amariLegendreEta W_plus Φ = V * W_plus := by
    dsimp [amariLegendreEta]
    rw [hWpPhi, ← mul_assoc, hPhiSq]
  have hPhiEtaMinus : Φ * amariLegendreEta W_minus Φ = V * W_minus := by
    dsimp [amariLegendreEta]
    rw [hWmPhi, ← mul_assoc, hPhiSq]
  have hBreg1 : (1 - V) * amariOperatorBregmanQuadPart V W_minus = V * V := by
    dsimp [amariOperatorBregmanQuadPart]
    calc
      (1 - V) * (V * W_minus - V)
        = V * ((1 - V) * W_minus) - (1 - V) * V := by noncomm_ring
      _ = V * 1 - (1 - V) * V := by rw [hWm_right]
      _ = V * V := by noncomm_ring
  have hBreg2 : amariOperatorBregmanQuadPart V W_minus = (V * V) * W_minus := by
    dsimp [amariOperatorBregmanQuadPart]
    calc
      V * W_minus - V = V * (W_minus - 1) := by noncomm_ring
      _ = V * (V * W_minus) := by rw [← hWmV]
      _ = (V * V) * W_minus := by noncomm_ring
  have hBreg3 :
      amariOperatorBregmanQuadPart V W_minus = (Φ * amariLegendreEta W_minus Φ) * V := by
    rw [hBreg2, hPhiEtaMinus]
    calc
      (V * V) * W_minus = V * (V * W_minus) := by noncomm_ring
      _ = V * (W_minus * V) := by rw [hWmVComm]
      _ = (V * W_minus) * V := by noncomm_ring
  have hWingPlus : P * amariLegendreEta W_plus Φ * (1 - P) = W_plus * conePlus P A := by
    dsimp [amariLegendreEta]
    have hPPhi : P * Φ * (1 - P) = conePlus P A := by dsimp [Φ]; peirce_nf hP
    calc
      P * (W_plus * Φ) * (1 - P) = (P * W_plus) * Φ * (1 - P) := by noncomm_ring
      _ = (W_plus * P) * Φ * (1 - P) := by rw [← hWpP']
      _ = W_plus * (P * Φ * (1 - P)) := by noncomm_ring
      _ = W_plus * conePlus P A := by rw [hPPhi]
  have hWingMinus : (1 - P) * amariLegendreEta W_plus Φ * P = W_plus * coneMinus P C := by
    dsimp [amariLegendreEta]
    have h1mPPhi : (1 - P) * Φ * P = coneMinus P C := by dsimp [Φ]; peirce_nf hP
    have hWp1mP : (1 - P) * W_plus = W_plus * (1 - P) := by
      calc
        (1 - P) * W_plus = W_plus - P * W_plus := by noncomm_ring
        _ = W_plus - W_plus * P := by rw [← hWpP']
        _ = W_plus * (1 - P) := by noncomm_ring
    calc
      (1 - P) * (W_plus * Φ) * P = ((1 - P) * W_plus) * Φ * P := by noncomm_ring
      _ = (W_plus * (1 - P)) * Φ * P := by rw [hWp1mP]
      _ = W_plus * ((1 - P) * Φ * P) := by noncomm_ring
      _ = W_plus * coneMinus P C := by rw [h1mPPhi]
  exact ⟨⟨hEtaPlusEq, hWpPhi, hEtaMinusEq, hWmPhi⟩,
    ⟨hPhiEtaPlus, by rw [hWpV]; abel, hPhiEtaMinus, hWmV.symm⟩,
    ⟨hBreg1, hBreg2, hBreg3⟩,
    ⟨hWingPlus, hWingMinus⟩⟩

/-- If the Peirce metric `V` is nilpotent, Mathlib's finite geometric-resolvent
unit constructs both inverses required by the Legendre theorem. The positive
branch uses the existing `nilpotentResolvent` owner at `-V`, and the negative
branch uses it at `V`; the resulting inverse values then discharge every
two-sided inverse hypothesis of `stage_D7_Q6_legendre_resolvent_duality_and_bregman_closure`.
This is a conditional algebraic construction and does not assert that `V` is
nilpotent for arbitrary Peirce data. -/
theorem exists_legendre_resolvents_of_nilpotent_metric
    {P : B} (A C : B) (n : ℕ)
    (hV : (genV P A C) ^ n = 0) :
    ∃ W_plus W_minus : B,
      (1 + genV P A C) * W_plus = 1 ∧
      W_plus * (1 + genV P A C) = 1 ∧
      (1 - genV P A C) * W_minus = 1 ∧
      W_minus * (1 - genV P A C) = 1 := by
  let V := genV P A C
  have hV' : V ^ n = 0 := by simpa [V] using hV
  have hNegV : (-V) ^ n = 0 := by
    rw [neg_pow, hV', mul_zero]
  let uPlus : Bˣ :=
    InfoGeometry.OperatorAlgebra.OperatorDirichlet.nilpotentResolvent
      (x := -V) hNegV
  let uMinus : Bˣ :=
    InfoGeometry.OperatorAlgebra.OperatorDirichlet.nilpotentResolvent
      (x := V) hV
  let W_plus : B := ↑uPlus.inv
  let W_minus : B := ↑uMinus.inv
  have hWp_right : (1 + V) * W_plus = 1 := by
    simpa [W_plus, uPlus, InfoGeometry.OperatorAlgebra.OperatorDirichlet.nilpotentResolvent,
      sub_neg_eq_add] using uPlus.val_inv
  have hWp_left : W_plus * (1 + V) = 1 := by
    simpa [W_plus, uPlus, InfoGeometry.OperatorAlgebra.OperatorDirichlet.nilpotentResolvent,
      sub_neg_eq_add] using uPlus.inv_val
  have hWm_right : (1 - V) * W_minus = 1 := by
    simpa [W_minus, uMinus, InfoGeometry.OperatorAlgebra.OperatorDirichlet.nilpotentResolvent] using
      uMinus.val_inv
  have hWm_left : W_minus * (1 - V) = 1 := by
    simpa [W_minus, uMinus, InfoGeometry.OperatorAlgebra.OperatorDirichlet.nilpotentResolvent] using
      uMinus.inv_val
  refine ⟨W_plus, W_minus, ?_, ?_, ?_, ?_⟩
  · simpa [V] using hWp_right
  · simpa [V] using hWp_left
  · simpa [V] using hWm_right
  · simpa [V] using hWm_left

end LegendreResolventAndBregmanClosure

/-! ===========================================================================
    Section 8: Master Capstone Theorem Unifying `𝔇₁ ≺ … ≺ 𝔇₇` and `𝔔₁ ≺ … ≺ 𝔔₆`
    =========================================================================== -/

-- theorem-class: capstone consumer theorem
/-- **Master Capstone Theorem (`first_quantized_amari_operator_geometry_master_poset`)**:
Unifies the 7-stage Amari Dually Flat Operator Geometry Poset (`𝔇₁ ≺ … ≺ 𝔇₇`) and the
6-stage First-Quantized Operator Geometry vs. Trace-First Blindness Poset (`𝔔₁ ≺ … ≺ 𝔔₆`):
1. Acyclicity of `AmariDuallyFlatOperatorStage` and `FirstQuantizedAmariStage`,
2. Exact Abelian Flatness of the chiral exponential families `ℰ₊(A) = 1 + N₊(A)` and
   `ℰ₋(C) = 1 + N₋(C)` (`ℰ₊(A₁) ℰ₊(A₂) = ℰ₊(A₁ + A₂)`, `ℰ₋(C₁) ℰ₋(C₂) = ℰ₋(C₁ + C₂)`),
3. Paired Operator Gaussians `𝒢₊ = 1 + Φ + Q₊`, exact series-free inverse
   `𝒢₊⁻¹ = 1 - Φ + Q₋`, and birth of `V` and `Σ` from the cross-collision of `ℰ₊` and `ℰ₋`;
   equality of either ordered Gaussian is equivalent to equality of its two Peirce off-diagonal
   coordinates, with the forward realization's parameter quotient equivalent to its range,
4. Amari Dual Connections `∇^(e), ∇^(m)`, Sum–Difference Crossover
   `[∇^(e) - ∇^(m), Φ] = {∇^(e) + ∇^(m), J}`, and the Operator Pythagorean Theorem
   `V² = Q₊² + Q₋² = Σ²`,
5. The Theorem of Textbook Trace-First Blindness (`tr(Σ) = 0`) and Chiral Supertrace
   Recovery (`Str(Σ) = tr(S_P Σ) = tr(V) = 2 • tr(Q₊)`). -/
theorem first_quantized_amari_operator_geometry_master_poset
    {B : Type*} [Ring B] {K : Type*} [AddCommGroup K]
    {P : B} (hP : P * P = P) (tr : B →+ K)
    (hTr : ∀ X Y : B, tr (X * Y) = tr (Y * X))
    (Ω A₁ A₂ C₁ C₂ A C A' C' : B) :
    let Φ := genPhi P A C
    let J := genJ P A C
    let Qp := qgtPlus P A C
    let Qm := qgtMinus P A C
    let V := genV P A C
    let Sig := genSig P A C
    -- (1) Poset acyclicity
    ((∀ st : AmariDuallyFlatOperatorStage,
        ¬ Relation.TransGen AmariDuallyFlatOperatorStage.causalEdge st st) ∧
      (∀ st : FirstQuantizedAmariStage,
        ¬ Relation.TransGen FirstQuantizedAmariStage.causalEdge st st)) ∧
    -- (2) Dually flat abelian exponential families (𝔇₁, 𝔇₂, 𝔔₁)
    (amariExpPlus P A₁ * amariExpPlus P A₂ = amariExpPlus P (A₁ + A₂) ∧
      amariExpMinus P C₁ * amariExpMinus P C₂ = amariExpMinus P (C₁ + C₂) ∧
      comm (amariExpPlus P A₁) (amariExpPlus P A₂) = 0 ∧
      comm (amariExpMinus P C₁) (amariExpMinus P C₂) = 0) ∧
    -- (3) Paired Operator Gaussians, series-free inversion, & curvature birth (𝔇₃, 𝔇₄, 𝔔₂, 𝔔₃)
    (operatorGaussianPlus P A C = 1 + Φ + Qp ∧
      operatorGaussianPlusInv P A C = 1 - Φ + Qm ∧
      operatorGaussianPlus P A C * operatorGaussianPlusInv P A C = 1 ∧
      (operatorGaussianPlus P A C - (1 + Φ)) +
        (operatorGaussianMinus P A C - (1 + Φ)) = V ∧
      comm (amariExpPlus P A) (amariExpMinus P C) = Sig ∧
      (operatorGaussianPlus P A C = operatorGaussianPlus P A' C' ↔
        conePlus P A = conePlus P A' ∧ coneMinus P C = coneMinus P C') ∧
      (operatorGaussianMinus P A C = operatorGaussianMinus P A' C' ↔
        conePlus P A = conePlus P A' ∧ coneMinus P C = coneMinus P C') ∧
      Nonempty (Quotient (operatorGaussianParameterSetoid P) ≃
        Set.range (fun x : B × B => operatorGaussianPlus P x.1 x.2))) ∧
    -- (4) Amari dual connections, crossover, & Operator Pythagorean Theorem (𝔇₅, 𝔇₆, 𝔔₅)
    (comm (amariSkewnessConnection P Ω) Φ = anticomm (amariDoubledMidpoint P Ω) J ∧
      Qp * Qm = 0 ∧
      V * V = Qp * Qp + Qm * Qm ∧
      V * V = Sig * Sig) ∧
    -- (5) Trace-First Blindness vs. Chiral Supertrace Recovery (𝔔₄)
    (tr Sig = 0 ∧
      tr V = (2 : ℤ) • tr Qp ∧
      chiralSupertrace tr P V = 0 ∧
      chiralSupertrace tr P Sig = tr V) := by
  intro Φ J Qp Qm V Sig
  have hD12 := stage_D1_D2_Q1_dually_flat_chiral_subalgebras_and_abelian_exponentials
    hP A₁ A₂ C₁ C₂ A C
  rcases hD12 with ⟨_, hD12rest⟩
  rcases hD12rest with ⟨_, hExp⟩
  rcases hExp with ⟨_, _, hExpPlus, hExpMinus, _, _, _, _, hCommPlus, hCommMinus⟩
  have hD34 := stage_D3_D4_Q2_Q3_paired_operator_gaussians_and_curvature_birth hP A C
  have hD56 := stage_D5_D6_Q5_amari_dual_connections_and_operator_pythagorean_theorem hP Ω A C
  have hQ4 := stage_Q4_theorem_trace_first_blindness_and_chiral_supertrace_recovery
    hP tr hTr A C
  exact ⟨⟨AmariDuallyFlatOperatorStage.causalEdge_acyclic,
          FirstQuantizedAmariStage.causalEdge_acyclic⟩,
    ⟨hExpPlus, hExpMinus, hCommPlus, hCommMinus⟩,
    ⟨hD34.1.2.1, hD34.1.2.2.2.1, hD34.2.1.1, hD34.2.2.1.1,
      hD34.2.2.1.2.2.1,
      operatorGaussianPlus_eq_iff_cone_coordinates_eq hP,
      operatorGaussianMinus_eq_iff_cone_coordinates_eq hP,
      ⟨operatorGaussianParameterQuotientEquiv hP⟩⟩,
    ⟨hD56.2.1.1, hD56.2.2.1, hD56.2.2.2.2.1, hD56.2.2.2.2.2.2.1⟩,
    ⟨hQ4.2.2.1.1, hQ4.2.2.1.2.2.2, hQ4.2.2.2.1, hQ4.2.2.2.2.1⟩⟩

end InfoGeometry.Canonical.FirstQuantizedAmariOperatorGeometryPoset
