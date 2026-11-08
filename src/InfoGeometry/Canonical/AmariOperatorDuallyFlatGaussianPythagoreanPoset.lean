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
import InfoGeometry.OperatorAlgebra.PeirceSpine.PrimalDual
import InfoGeometry.OperatorAlgebra.PeirceSpine.Bergman
import InfoGeometry.OperatorAlgebra.PeirceSpine.GradedTraceMoments
import InfoGeometry.Canonical.RadonNikodymKahlerParaKahlerBregmanPoset
import InfoGeometry.Canonical.BerryWilsonLoopHyperplaneCausalTransmutationPoset

/-!
# The 7-Stage Amari Operator Geometry Poset: Dually Flat Chiral Subalgebras, Paired Operator Gaussians, Dual Sheet Connections, and the Non-Commutative Operator Pythagorean Theorem (`𝔇₁ ≺ 𝔇₂ ≺ 𝔇₃ ≺ 𝔇₄ ≺ 𝔇₅ ≺ 𝔇₆ ≺ 𝔇₇`)

This module formalizes in Lean 4 (Mathlib) the **7-Stage Amari Operator Geometry Poset**
(`𝔇₁ ≺ 𝔇₂ ≺ 𝔇₃ ≺ 𝔇₄ ≺ 𝔇₅ ≺ 𝔇₆ ≺ 𝔇₇`) over an arbitrary non-commutative associative ring
`[Ring B]` and an idempotent cut `P * P = P`, reusing and unifying the repository's Peirce spine
(`Basic.lean`, `Homogenized.lean`, `Supercharge.lean`, `Unipotent.lean`, `PrimalDual.lean`,
`Bergman.lean`) and the Radon–Nikodym / Legendre / Bregman poset
(`RadonNikodymKahlerParaKahlerBregmanPoset.lean`):

* **Rung 0 (Socratic Aporia of Self-Dual Exponential Curvature)**:
  Attempting to form a single unipotent exponential family `1 + Φ` directly over the combined
  self-dual space `Φ = N₊ + N₋` fails affine flatness because `Φ² = V ≠ 0`:
  `(1 + Φ₁) * (1 + Φ₂) - (1 + Φ₁ + Φ₂) = Φ₁ * Φ₂ = N₊(A₁) * N₋(C₂) + N₋(C₁) * N₊(A₂)`
  and `(1 + Φ) * (1 - Φ) = 1 - V`.
* **Stage `𝔇₁` (`D1_ChiralSplitIntoDuallyFlatAffineSubalgebras`)**:
  The Peirce chiral split `Φ = N₊ + N₋` into the upper `e`-flat nilpotent subalgebra
  `𝔫₊ = P B (1 - P)` (`conePlus P A`) and lower `m`-flat nilpotent subalgebra
  `𝔫₋ = (1 - P) B P` (`coneMinus P C`), where all intra-sheet products vanish identically:
  `N₊(A₁) * N₊(A₂) = 0` and `N₋(C₁) * N₋(C₂) = 0`.
* **Stage `𝔇₂` (`D2_ExactAbelianExponentialFamilies`)**:
  Exact degree-1 truncation of the chiral exponential families `ℰ₊(A) = 1 + N₊(A)`
  (`unipotentExpPlus P A`) and `ℰ₋(C) = 1 + N₋(C)` (`unipotentExpMinus P C`), which satisfy
  exact Abelian group laws with zero Baker–Campbell–Hausdorff (BCH) curvature within each sheet:
  `ℰ₊(A₁) * ℰ₊(A₂) = ℰ₊(A₁ + A₂)`, `ℰ₋(C₁) * ℰ₋(C₂) = ℰ₋(C₁ + C₂)`,
  `ℰ_±(X) * ℰ_±(-X) = 1`, and `[ℰ₊(A₁), ℰ₊(A₂)] = [ℰ₋(C₁), ℰ₋(C₂)] = 0`.
* **Stage `𝔇₃` (`D3_PairedOperatorGaussiansAndPolynomialInversion`)**:
  The forward and backward **Operator Gaussians**
  `𝒢₊(P, A, C) = ℰ₊(A) * ℰ₋(C) = 1 + Φ + Q₊` and
  `𝒢₋(P, A, C) = ℰ₋(C) * ℰ₊(A) = 1 + Φ + Q₋`
  (where `Q₊ = N₊ N₋` and `Q₋ = N₋ N₊`), together with their exact series-free two-sided
  polynomial inverses `𝒢₊⁻¹ = ℰ₋(-C) * ℰ₊(-A) = 1 - Φ + Q₋` and
  `𝒢₋⁻¹ = ℰ₊(-A) * ℰ₋(-C) = 1 - Φ + Q₊` in any associative ring.
* **Stage `𝔇₄` (`D4_BirthOfFisherMetricAndBerrySkewnessFromGaussians`)**:
  The symmetric sum of the quadratic Gaussian excesses over the linear tangent `1 + Φ` gives
  the Fisher–Rao–BKM metric strain `(𝒢₊ - (1 + Φ)) + (𝒢₋ - (1 + Φ)) = Q₊ + Q₋ = V`, while the
  inter-sheet commutator gives the Berry–Amari skewness
  `[ℰ₊(A), ℰ₋(C)] = 𝒢₊ - 𝒢₋ = Q₊ - Q₋ = Σ`.
* **Stage `𝔇₅` (`D5_AmariDualConnectionsMidpointSkewnessAndCrossover`)**:
  Amari's dual sheet connections `∇^(e) = P W P` (`sheetPlusConnection P W`) and
  `∇^(m) = (1 - P) W (1 - P)` (`sheetMinusConnection P W`), the self-dual Levi-Civita sum
  `Γ_sum = ∇^(e) + ∇^(m)`, the Amari–Chentsov skewness difference
  `Γ_diff = ∇^(e) - ∇^(m) = S_P * Γ_sum`, the continuous `α`-connection family
  `∇^(α) = (1/2) • Γ_sum + (α/2) • Γ_diff`, and the **Fourfold Sum–Difference Crossover Law**
  (`sheetConnection_sum_difference_crossover`).
* **Stage `𝔇₆` (`D6_OperatorPythagoreanTheoremAndOrthogonalGramians`)**:
  Exact mutual annihilation `Q₊ * Q₋ = 0` and `Q₋ * Q₊ = 0` of the sheet Gramians, yielding the
  **Non-Commutative Operator Pythagorean Theorem**:
  `V² = (Q₊ + Q₋)² = Q₊² + Q₋² = (Q₊ - Q₋)² = Σ²`,
  `(𝒢₊ - (1 + Φ)) * (𝒢₋ - (1 + Φ)) = 0`, and
  `(𝒢₊ - (1 + Φ))² + (𝒢₋ - (1 + Φ))² = V² = Σ²`.
* **Stage `𝔇₇` (`D7_LegendreResolventDualityBregmanDivergenceAndBKMClosure`)**:
  Legendre–Peirce resolvent moment coordinate recovery `(1 ± V) * η_± = Φ`, Bergman kernel
  determinant identity `B(N₊, N₋)(1) = (1 - Q₊)(1 - Q₋) = 1 - V`, and exact cancellation of the
  linear `n = 1` term in the Operator Bregman divergence series.
-/

namespace InfoGeometry.Canonical.AmariOperatorDuallyFlatGaussianPythagoreanPoset

open InfoGeometry.OperatorAlgebra.OntologyRing
open InfoGeometry.Meta
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.RadonNikodymKahlerParaKahlerBregmanPoset
open InfoGeometry.Canonical.BerryWilsonLoopHyperplaneCausalTransmutationPoset
open scoped BigOperators Matrix

/-!
## 1. The 7-Stage Acyclic Causal Poset (`𝔇₁ ≺ 𝔇₂ ≺ 𝔇₃ ≺ 𝔇₄ ≺ 𝔇₅ ≺ 𝔇₆ ≺ 𝔇₇`)
-/

/-- The 7-stage causal poset of Amari Operator Geometry:
`𝔇₁` (chiral split into dually flat nilpotent subalgebras `𝔫₊` and `𝔫₋`) `≺`
`𝔇₂` (exact Abelian exponential families `ℰ₊` and `ℰ₋`) `≺`
`𝔇₃` (paired Operator Gaussians `𝒢_±` and series-free polynomial inversion) `≺`
`𝔇₄` (birth of the Fisher metric `V` and Berry skewness `Σ` from Gaussian excesses) `≺`
`𝔇₅` (Amari dual sheet connections `∇^(e), ∇^(m)`, `α`-connections, and fourfold crossover) `≺`
`𝔇₆` (orthogonal sheet Gramians `Q₊ Q₋ = 0` and the Operator Pythagorean theorem `V² = Σ²`) `≺`
`𝔇₇` (Legendre–Peirce resolvent duality, Bergman operator, and Bregman divergence closure). -/
inductive AmariOperatorGeometryStage : Type
  | D1_ChiralSplitIntoDuallyFlatAffineSubalgebras
  | D2_ExactAbelianExponentialFamilies
  | D3_PairedOperatorGaussiansAndPolynomialInversion
  | D4_BirthOfFisherMetricAndBerrySkewnessFromGaussians
  | D5_AmariDualConnectionsMidpointSkewnessAndCrossover
  | D6_OperatorPythagoreanTheoremAndOrthogonalGramians
  | D7_LegendreResolventDualityBregmanDivergenceAndBKMClosure
  deriving DecidableEq, Repr, Inhabited

namespace AmariOperatorGeometryStage

/-- Topological rank `0..6` of each stage `𝔇₁..𝔇₇`. -/
def rank : AmariOperatorGeometryStage → ℕ
  | .D1_ChiralSplitIntoDuallyFlatAffineSubalgebras => 0
  | .D2_ExactAbelianExponentialFamilies => 1
  | .D3_PairedOperatorGaussiansAndPolynomialInversion => 2
  | .D4_BirthOfFisherMetricAndBerrySkewnessFromGaussians => 3
  | .D5_AmariDualConnectionsMidpointSkewnessAndCrossover => 4
  | .D6_OperatorPythagoreanTheoremAndOrthogonalGramians => 5
  | .D7_LegendreResolventDualityBregmanDivergenceAndBKMClosure => 6

/-- `rank` is strictly injective on `AmariOperatorGeometryStage`. -/
theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

instance instLinearOrder : LinearOrder AmariOperatorGeometryStage :=
  LinearOrder.lift' rank rank_injective

instance instFintype : Fintype AmariOperatorGeometryStage where
  elems := {
    .D1_ChiralSplitIntoDuallyFlatAffineSubalgebras,
    .D2_ExactAbelianExponentialFamilies,
    .D3_PairedOperatorGaussiansAndPolynomialInversion,
    .D4_BirthOfFisherMetricAndBerrySkewnessFromGaussians,
    .D5_AmariDualConnectionsMidpointSkewnessAndCrossover,
    .D6_OperatorPythagoreanTheoremAndOrthogonalGramians,
    .D7_LegendreResolventDualityBregmanDivergenceAndBKMClosure
  }
  complete := by
    intro x
    cases x <;> simp

/-- Direct covering edges `𝔇₁ → 𝔇₂ → 𝔇₃ → 𝔇₄ → 𝔇₅ → 𝔇₆ → 𝔇₇`. -/
def causalEdge : AmariOperatorGeometryStage → AmariOperatorGeometryStage → Prop
  | .D1_ChiralSplitIntoDuallyFlatAffineSubalgebras,
    .D2_ExactAbelianExponentialFamilies => True
  | .D2_ExactAbelianExponentialFamilies,
    .D3_PairedOperatorGaussiansAndPolynomialInversion => True
  | .D3_PairedOperatorGaussiansAndPolynomialInversion,
    .D4_BirthOfFisherMetricAndBerrySkewnessFromGaussians => True
  | .D4_BirthOfFisherMetricAndBerrySkewnessFromGaussians,
    .D5_AmariDualConnectionsMidpointSkewnessAndCrossover => True
  | .D5_AmariDualConnectionsMidpointSkewnessAndCrossover,
    .D6_OperatorPythagoreanTheoremAndOrthogonalGramians => True
  | .D6_OperatorPythagoreanTheoremAndOrthogonalGramians,
    .D7_LegendreResolventDualityBregmanDivergenceAndBKMClosure => True
  | _, _ => False

instance instDecidableRelCausalEdge : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

/-- Every causal edge strictly increases topological rank. -/
theorem causalEdge_strict_rank_mono {a b : AmariOperatorGeometryStage}
    (h : causalEdge a b) : rank a < rank b := by
  cases a <;> cases b <;> simp [causalEdge, rank] at h ⊢

/-- No stage has a self-loop. -/
theorem causalEdge_irrefl (a : AmariOperatorGeometryStage) : ¬ causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (causalEdge_strict_rank_mono h)

/-- Transitive paths strictly increase topological rank. -/
theorem transGen_causalEdge_strict_rank_mono {a b : AmariOperatorGeometryStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_strict_rank_mono hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_strict_rank_mono hbc)

/-- The 7-stage Amari Operator Geometry poset is strictly acyclic. -/
theorem causalEdge_acyclic (a : AmariOperatorGeometryStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_strict_rank_mono h)

/-- Complete 6-edge causal chain `𝔇₁ ≺ 𝔇₂ ≺ 𝔇₃ ≺ 𝔇₄ ≺ 𝔇₅ ≺ 𝔇₆ ≺ 𝔇₇`. -/
theorem strict_seven_stage_chain :
    causalEdge .D1_ChiralSplitIntoDuallyFlatAffineSubalgebras
      .D2_ExactAbelianExponentialFamilies ∧
    causalEdge .D2_ExactAbelianExponentialFamilies
      .D3_PairedOperatorGaussiansAndPolynomialInversion ∧
    causalEdge .D3_PairedOperatorGaussiansAndPolynomialInversion
      .D4_BirthOfFisherMetricAndBerrySkewnessFromGaussians ∧
    causalEdge .D4_BirthOfFisherMetricAndBerrySkewnessFromGaussians
      .D5_AmariDualConnectionsMidpointSkewnessAndCrossover ∧
    causalEdge .D5_AmariDualConnectionsMidpointSkewnessAndCrossover
      .D6_OperatorPythagoreanTheoremAndOrthogonalGramians ∧
    causalEdge .D6_OperatorPythagoreanTheoremAndOrthogonalGramians
      .D7_LegendreResolventDualityBregmanDivergenceAndBKMClosure ∧
    Fintype.card AmariOperatorGeometryStage = 7 := by
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, ?_⟩
  decide

/-- Monotone embedding into `RepDepth`. -/
def toRepDepth : AmariOperatorGeometryStage → RepDepth
  | .D1_ChiralSplitIntoDuallyFlatAffineSubalgebras => .projective
  | .D2_ExactAbelianExponentialFamilies => .operator
  | .D3_PairedOperatorGaussiansAndPolynomialInversion => .operator
  | .D4_BirthOfFisherMetricAndBerrySkewnessFromGaussians => .krein
  | .D5_AmariDualConnectionsMidpointSkewnessAndCrossover => .transport
  | .D6_OperatorPythagoreanTheoremAndOrthogonalGramians => .transport
  | .D7_LegendreResolventDualityBregmanDivergenceAndBKMClosure => .thermo

/-- Monotone embedding into `OntologyMetaLevel`. -/
def toOntologyMetaLevel : AmariOperatorGeometryStage → OntologyMetaLevel
  | .D1_ChiralSplitIntoDuallyFlatAffineSubalgebras => .M1_ProjectorClabject
  | .D2_ExactAbelianExponentialFamilies => .M1_ProjectorClabject
  | .D3_PairedOperatorGaussiansAndPolynomialInversion => .M2_GrassmannianPowertypeOrbit
  | .D4_BirthOfFisherMetricAndBerrySkewnessFromGaussians => .M2_GrassmannianPowertypeOrbit
  | .D5_AmariDualConnectionsMidpointSkewnessAndCrossover => .M2_GrassmannianPowertypeOrbit
  | .D6_OperatorPythagoreanTheoremAndOrthogonalGramians => .M3_ErlangenCasimirMetaLaw
  | .D7_LegendreResolventDualityBregmanDivergenceAndBKMClosure => .M3_ErlangenCasimirMetaLaw

theorem toRepDepth_rank_monotone {a b : AmariOperatorGeometryStage}
    (h : rank a ≤ rank b) : (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  cases a <;> cases b <;> simp [toRepDepth, RepDepth.toNat, rank] at h ⊢

theorem toOntologyMetaLevel_rank_monotone {a b : AmariOperatorGeometryStage}
    (h : rank a ≤ rank b) : (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  cases a <;> cases b <;> simp [toOntologyMetaLevel, OntologyMetaLevel.rank, rank] at h ⊢

end AmariOperatorGeometryStage

/-- **The 6-Stage First-Quantized Amari Operator Geometry Poset (`FirstQuantizedAmariStage`:
`𝔔₁ ≺ 𝔔₂ ≺ 𝔔₃ ≺ 𝔔₄ ≺ 𝔔₅ ≺ 𝔔₆`)**:
Formalizes the epistemic First-Quantization Binary Cut separating textbook "Trace-First"
`c`-number geometry on `θ ∈ ℝ^m` (where `Tr(N₊ N₋) = Tr(N₋ N₊)` erases `Σ = Q₊ - Q₋`) from
First-Quantized "All-Operator-Map" Amari Geometry in `[Ring B]`:
* `Q1_FirstQuantizationOfCoordinatesToNilpotentMaps`:
  Replacing scalar coordinates `θ, η ∈ ℝ^m` with nilpotent operator maps `N₊(A) ∈ 𝔫₊` and
  `N₋(C) ∈ 𝔫₋` (`N₊(A₁) * N₊(A₂) = 0`, `N₋(C₁) * N₋(C₂) = 0`), eliminating the BCH wall.
* `Q2_OperatorExponentialAndGaussianMaps`:
  Unipotent operator exponential maps `ℰ_±(X) = 1 + N_±(X)` (`ℰ_±(X) * ℰ_±(Y) = ℰ_±(X + Y)`)
  and Paired Operator Gaussians `𝒢_+ = 1 + Φ + Q_+`, `𝒢_- = 1 + Φ + Q_-` with series-free
  polynomial inverses `𝒢_+⁻¹ = 1 - Φ + Q_-`, `𝒢_-⁻¹ = 1 - Φ + Q_+`.
* `Q3_OperatorMetricMapAndOperatorSkewnessMap`:
  Operator Fisher–Rao–BKM metric map `V = Q_+ + Q_- = {N_+, N_-}` and operator Berry–Amari
  skewness map `Σ = Q_+ - Q_- = [ℰ_+, ℰ_-]` satisfying `Q_+ * Q_- = 0` and `V² = Q_+² + Q_-² = Σ²`.
* `Q4_TextbookTraceBlindnessVsChiralSupertraceVisibility`:
  The Theorem of Trace-First Blindness and Chiral Supertrace Recovery: for any cyclic trace
  `Tr(X * Y) = Tr(Y * X)`, `Tr(Q_+) = Tr(Q_-)` forces `Tr(𝒢_+) = Tr(𝒢_-)` and `Tr(Σ) = 0`
  (explaining why standard textbooks missed `Σ`), whereas the chiral supertrace
  `Str(Y) := Tr(S_P * Y)` satisfies `Str(V) = 0` and `Str(Σ) = Tr(V) = 2 • Tr(Q_+)`.
* `Q5_AllOperatorDualConnectionsAndFourfoldCrossover`:
  All-operator sheet bimodule connections `∇^(e) = ∇_+ = P W P`, `∇^(m) = ∇_- = (1 - P) W (1 - P)`
  and the Fourfold Sum–Difference Crossover Law `[∇^(e) - ∇^(m), Φ] = {∇^(e) + ∇^(m), J}`.
* `Q6_AllOperatorLegendreResolventAndBregmanMaps`:
  All-operator Legendre–Peirce resolvent map `η_±(Φ) = W_± * Φ` (`(1 ± V) * η_± = Φ`), Bergman
  kernel factorization `(1 - Q_+) * (1 - Q_-) = 1 - V`, and Operator Bregman divergence series. -/
inductive FirstQuantizedAmariStage : Type
  | Q1_FirstQuantizationOfCoordinatesToNilpotentMaps
  | Q2_OperatorExponentialAndGaussianMaps
  | Q3_OperatorMetricMapAndOperatorSkewnessMap
  | Q4_TextbookTraceBlindnessVsChiralSupertraceVisibility
  | Q5_AllOperatorDualConnectionsAndFourfoldCrossover
  | Q6_AllOperatorLegendreResolventAndBregmanMaps
  deriving DecidableEq, Repr, Inhabited

namespace FirstQuantizedAmariStage

/-- Topological rank `0..5` of each stage `𝔔₁..𝔔₆`. -/
def rank : FirstQuantizedAmariStage → ℕ
  | .Q1_FirstQuantizationOfCoordinatesToNilpotentMaps => 0
  | .Q2_OperatorExponentialAndGaussianMaps => 1
  | .Q3_OperatorMetricMapAndOperatorSkewnessMap => 2
  | .Q4_TextbookTraceBlindnessVsChiralSupertraceVisibility => 3
  | .Q5_AllOperatorDualConnectionsAndFourfoldCrossover => 4
  | .Q6_AllOperatorLegendreResolventAndBregmanMaps => 5

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

instance instLinearOrder : LinearOrder FirstQuantizedAmariStage :=
  LinearOrder.lift' rank rank_injective

instance instFintype : Fintype FirstQuantizedAmariStage where
  elems := {
    .Q1_FirstQuantizationOfCoordinatesToNilpotentMaps,
    .Q2_OperatorExponentialAndGaussianMaps,
    .Q3_OperatorMetricMapAndOperatorSkewnessMap,
    .Q4_TextbookTraceBlindnessVsChiralSupertraceVisibility,
    .Q5_AllOperatorDualConnectionsAndFourfoldCrossover,
    .Q6_AllOperatorLegendreResolventAndBregmanMaps
  }
  complete := by
    intro x
    cases x <;> simp

/-- Direct covering edges `𝔔₁ → 𝔔₂ → 𝔔₃ → 𝔔₄ → 𝔔₅ → 𝔔₆`. -/
def causalEdge : FirstQuantizedAmariStage → FirstQuantizedAmariStage → Prop
  | .Q1_FirstQuantizationOfCoordinatesToNilpotentMaps,
    .Q2_OperatorExponentialAndGaussianMaps => True
  | .Q2_OperatorExponentialAndGaussianMaps,
    .Q3_OperatorMetricMapAndOperatorSkewnessMap => True
  | .Q3_OperatorMetricMapAndOperatorSkewnessMap,
    .Q4_TextbookTraceBlindnessVsChiralSupertraceVisibility => True
  | .Q4_TextbookTraceBlindnessVsChiralSupertraceVisibility,
    .Q5_AllOperatorDualConnectionsAndFourfoldCrossover => True
  | .Q5_AllOperatorDualConnectionsAndFourfoldCrossover,
    .Q6_AllOperatorLegendreResolventAndBregmanMaps => True
  | _, _ => False

instance instDecidableRelCausalEdge : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

theorem causalEdge_strict_rank_mono {a b : FirstQuantizedAmariStage}
    (h : causalEdge a b) : rank a < rank b := by
  cases a <;> cases b <;> simp [causalEdge, rank] at h ⊢

theorem causalEdge_irrefl (a : FirstQuantizedAmariStage) : ¬ causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (causalEdge_strict_rank_mono h)

theorem transGen_causalEdge_strict_rank_mono {a b : FirstQuantizedAmariStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_strict_rank_mono hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_strict_rank_mono hbc)

theorem causalEdge_acyclic (a : FirstQuantizedAmariStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_strict_rank_mono h)

/-- Complete 5-edge causal chain `𝔔₁ ≺ 𝔔₂ ≺ 𝔔₃ ≺ 𝔔₄ ≺ 𝔔₅ ≺ 𝔔₆`. -/
theorem strict_six_stage_chain :
    causalEdge .Q1_FirstQuantizationOfCoordinatesToNilpotentMaps
      .Q2_OperatorExponentialAndGaussianMaps ∧
    causalEdge .Q2_OperatorExponentialAndGaussianMaps
      .Q3_OperatorMetricMapAndOperatorSkewnessMap ∧
    causalEdge .Q3_OperatorMetricMapAndOperatorSkewnessMap
      .Q4_TextbookTraceBlindnessVsChiralSupertraceVisibility ∧
    causalEdge .Q4_TextbookTraceBlindnessVsChiralSupertraceVisibility
      .Q5_AllOperatorDualConnectionsAndFourfoldCrossover ∧
    causalEdge .Q5_AllOperatorDualConnectionsAndFourfoldCrossover
      .Q6_AllOperatorLegendreResolventAndBregmanMaps ∧
    Fintype.card FirstQuantizedAmariStage = 6 := by
  refine ⟨trivial, trivial, trivial, trivial, trivial, ?_⟩
  decide

/-- Order-preserving anchor mapping each `FirstQuantizedAmariStage` (`𝔔₁..𝔔₆`) into
`AmariOperatorGeometryStage` (`𝔇₁..𝔇₇`). -/
def anchorInAmariStage : FirstQuantizedAmariStage → AmariOperatorGeometryStage
  | .Q1_FirstQuantizationOfCoordinatesToNilpotentMaps =>
      .D1_ChiralSplitIntoDuallyFlatAffineSubalgebras
  | .Q2_OperatorExponentialAndGaussianMaps =>
      .D3_PairedOperatorGaussiansAndPolynomialInversion
  | .Q3_OperatorMetricMapAndOperatorSkewnessMap =>
      .D4_BirthOfFisherMetricAndBerrySkewnessFromGaussians
  | .Q4_TextbookTraceBlindnessVsChiralSupertraceVisibility =>
      .D4_BirthOfFisherMetricAndBerrySkewnessFromGaussians
  | .Q5_AllOperatorDualConnectionsAndFourfoldCrossover =>
      .D5_AmariDualConnectionsMidpointSkewnessAndCrossover
  | .Q6_AllOperatorLegendreResolventAndBregmanMaps =>
      .D7_LegendreResolventDualityBregmanDivergenceAndBKMClosure

theorem anchorInAmariStage_monotone {a b : FirstQuantizedAmariStage}
    (h : rank a ≤ rank b) :
    (anchorInAmariStage a).rank ≤ (anchorInAmariStage b).rank := by
  cases a <;> cases b <;>
    simp [anchorInAmariStage, AmariOperatorGeometryStage.rank, rank] at h ⊢

/-- Monotone embedding into `RepDepth`. -/
def toRepDepth : FirstQuantizedAmariStage → RepDepth
  | .Q1_FirstQuantizationOfCoordinatesToNilpotentMaps => .projective
  | .Q2_OperatorExponentialAndGaussianMaps => .operator
  | .Q3_OperatorMetricMapAndOperatorSkewnessMap => .krein
  | .Q4_TextbookTraceBlindnessVsChiralSupertraceVisibility => .krein
  | .Q5_AllOperatorDualConnectionsAndFourfoldCrossover => .transport
  | .Q6_AllOperatorLegendreResolventAndBregmanMaps => .thermo

/-- Monotone embedding into `OntologyMetaLevel`. -/
def toOntologyMetaLevel : FirstQuantizedAmariStage → OntologyMetaLevel
  | .Q1_FirstQuantizationOfCoordinatesToNilpotentMaps => .M1_ProjectorClabject
  | .Q2_OperatorExponentialAndGaussianMaps => .M2_GrassmannianPowertypeOrbit
  | .Q3_OperatorMetricMapAndOperatorSkewnessMap => .M2_GrassmannianPowertypeOrbit
  | .Q4_TextbookTraceBlindnessVsChiralSupertraceVisibility => .M2_GrassmannianPowertypeOrbit
  | .Q5_AllOperatorDualConnectionsAndFourfoldCrossover => .M3_ErlangenCasimirMetaLaw
  | .Q6_AllOperatorLegendreResolventAndBregmanMaps => .M3_ErlangenCasimirMetaLaw

theorem toRepDepth_rank_monotone {a b : FirstQuantizedAmariStage}
    (h : rank a ≤ rank b) : (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  cases a <;> cases b <;> simp [toRepDepth, RepDepth.toNat, rank] at h ⊢

theorem toOntologyMetaLevel_rank_monotone {a b : FirstQuantizedAmariStage}
    (h : rank a ≤ rank b) : (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  cases a <;> cases b <;> simp [toOntologyMetaLevel, OntologyMetaLevel.rank, rank] at h ⊢

end FirstQuantizedAmariStage

/-!
## 2. Rung 0 (Socratic Aporia) & Stages `𝔇₁`–`𝔇₆` over an Arbitrary Ring `[Ring B]`
-/

section AlgebraicAmariSpine

variable {B : Type*} [Ring B]

/-- Forward Operator Gaussian `𝒢₊(P, A, C) := ℰ₊(P, A) * ℰ₋(P, C) = (1 + N₊(A)) * (1 + N₋(C))`. -/
def operatorGaussianPlus (P A C : B) : B :=
  unipotentExpPlus P A * unipotentExpMinus P C

/-- Explicit polynomial inverse of the forward Operator Gaussian:
`𝒢₊⁻¹(P, A, C) := ℰ₋(P, -C) * ℰ₊(P, -A) = (1 - N₋(C)) * (1 - N₊(A))`. -/
def operatorGaussianPlusInv (P A C : B) : B :=
  unipotentExpMinusInv P C * unipotentExpPlusInv P A

/-- Backward Operator Gaussian `𝒢₋(P, A, C) := ℰ₋(P, C) * ℰ₊(P, A) = (1 + N₋(C)) * (1 + N₊(A))`. -/
def operatorGaussianMinus (P A C : B) : B :=
  unipotentExpMinus P C * unipotentExpPlus P A

/-- Explicit polynomial inverse of the backward Operator Gaussian:
`𝒢₋⁻¹(P, A, C) := ℰ₊(P, -A) * ℰ₋(P, -C) = (1 - N₊(A)) * (1 - N₋(C))`. -/
def operatorGaussianMinusInv (P A C : B) : B :=
  unipotentExpPlusInv P A * unipotentExpMinusInv P C

/-- **Rung 0 (The Socratic Aporia of Self-Dual Exponential Curvature)**:
Attempting to define a single unipotent exponential family `1 + Φ` directly over the combined
self-dual tangent space `Φ = N₊ + N₋` fails to be an affine homomorphism because `Φ` is not
nilpotent (`Φ² = V`):
1. The multiplicative defect between `(1 + Φ₁) * (1 + Φ₂)` and the additive target
   `1 + Φ₁ + Φ₂` is the cross-sheet interaction product
   `Φ₁ * Φ₂ = N₊(A₁) * N₋(C₂) + N₋(C₁) * N₊(A₂)`.
2. For `Φ₁ = Φ₂ = Φ`, `(1 + Φ) * (1 + Φ) - (1 + 2 • Φ) = Φ * Φ = V`.
3. Multiplying `1 + Φ` by its sign-flipped partner `1 - Φ` does not invert to `1`, leaving the
   metric strain defect `-V`:
   `(1 + Φ) * (1 - Φ) = 1 - V` and `(1 - Φ) * (1 + Φ) = 1 - V`.
4. Consequently, `1 - Φ` is a right (or left) inverse of `1 + Φ` if and only if the Fisher–BKM
   metric strain `V = genV P A C` vanishes identically (`V = 0`). -/
theorem socratic_aporia_self_dual_exponential_curvature
    {P : B} (hP : P * P = P) (A C A₁ C₁ A₂ C₂ : B) :
    (1 + genPhi P A₁ C₁) * (1 + genPhi P A₂ C₂) -
        (1 + genPhi P A₁ C₁ + genPhi P A₂ C₂) =
      conePlus P A₁ * coneMinus P C₂ + coneMinus P C₁ * conePlus P A₂ ∧
    (1 + genPhi P A C) * (1 + genPhi P A C) -
        (1 + (2 : ℤ) • genPhi P A C) = genV P A C ∧
    (1 + genPhi P A C) * (1 - genPhi P A C) = 1 - genV P A C ∧
    (1 - genPhi P A C) * (1 + genPhi P A C) = 1 - genV P A C ∧
    ((1 + genPhi P A C) * (1 - genPhi P A C) = 1 ↔ genV P A C = 0) := by
  have h1 :
      (1 + genPhi P A₁ C₁) * (1 + genPhi P A₂ C₂) -
          (1 + genPhi P A₁ C₁ + genPhi P A₂ C₂) =
        conePlus P A₁ * coneMinus P C₂ + coneMinus P C₁ * conePlus P A₂ := by
    peirce_nf hP
  have h2 :
      (1 + genPhi P A C) * (1 + genPhi P A C) -
          (1 + (2 : ℤ) • genPhi P A C) = genV P A C := by
    peirce_nf hP
  have h3 : (1 + genPhi P A C) * (1 - genPhi P A C) = 1 - genV P A C := by
    peirce_nf hP
  have h4 : (1 - genPhi P A C) * (1 + genPhi P A C) = 1 - genV P A C := by
    peirce_nf hP
  refine ⟨h1, h2, h3, h4, ?_⟩
  rw [h3]
  constructor
  · intro hEq
    have hSub : (1 : B) - (1 - genV P A C) = 1 - 1 := by rw [hEq]
    calc
      genV P A C = (1 : B) - (1 - genV P A C) := by abel
      _ = 1 - 1 := hSub
      _ = 0 := sub_self 1
  · intro hV
    rw [hV, sub_zero]

/-- **Stage `𝔇₁` (The Chiral Split into Dually Flat Nilpotent Subalgebras `𝔫₊` and `𝔫₋`)**:
For any idempotent `P * P = P`, decomposing the tangent space into the upper `e`-flat corner
`N₊(A) = P A (1 - P) ∈ 𝔫₊` and lower `m`-flat corner `N₋(C) = (1 - P) C P ∈ 𝔫₋` yields:
1. **Universal Intra-Sheet Square-Zero Annihilation**:
   `N₊(A₁) * N₊(A₂) = 0` and `N₋(C₁) * N₋(C₂) = 0` for all `A₁, A₂, C₁, C₂ : B`.
2. **Exact Chiral Grading Eigen-Parities (`T^(1,0)` vs. `T^(0,1)`)**:
   `S_P * N₊(A) = N₊(A)`, `N₊(A) * S_P = -N₊(A)`,
   `S_P * N₋(C) = -N₋(C)`, and `N₋(C) * S_P = N₋(C)`.
3. **Exact Linear Reconstruction of `Φ` and `J` from the Chiral Foliations**:
   `N₊(A) + N₋(C) = Φ`, `N₊(A) - N₋(C) = J`,
   `Φ + J = 2 • N₊(A)`, and `Φ - J = 2 • N₋(C)`. -/
theorem d1_chiral_split_dually_flat_nilpotent_subalgebras
    {P : B} (hP : P * P = P) (A A₁ A₂ C C₁ C₂ : B) :
    conePlus P A₁ * conePlus P A₂ = 0 ∧
    coneMinus P C₁ * coneMinus P C₂ = 0 ∧
    invS P * conePlus P A = conePlus P A ∧
    conePlus P A * invS P = -conePlus P A ∧
    invS P * coneMinus P C = -coneMinus P C ∧
    coneMinus P C * invS P = coneMinus P C ∧
    conePlus P A + coneMinus P C = genPhi P A C ∧
    conePlus P A - coneMinus P C = genJ P A C ∧
    genPhi P A C + genJ P A C = (2 : ℤ) • conePlus P A ∧
    genPhi P A C - genJ P A C = (2 : ℤ) • coneMinus P C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Stage `𝔇₂` (Exact Abelian Exponential Families on `𝔫₊` and `𝔫₋`)**:
Because `N₊(A₁) * N₊(A₂) = 0` and `N₋(C₁) * N₋(C₂) = 0`, the truncated unipotent exponentials
`ℰ₊(A) = 1 + N₊(A)` (`unipotentExpPlus P A`) and `ℰ₋(C) = 1 + N₋(C)` (`unipotentExpMinus P C`)
are exact Abelian exponential families with zero intra-sheet BCH curvature:
1. **Exact Additive-to-Multiplicative Homomorphisms**:
   `ℰ₊(A₁) * ℰ₊(A₂) = ℰ₊(A₁ + A₂)` and `ℰ₋(C₁) * ℰ₋(C₂) = ℰ₋(C₁ + C₂)`.
2. **Exact Two-Sided Unipotent Inversion**:
   `ℰ₊(A) * ℰ₊(-A) = 1`, `ℰ₊(-A) * ℰ₊(A) = 1`,
   `ℰ₋(C) * ℰ₋(-C) = 1`, and `ℰ₋(-C) * ℰ₋(C) = 1`.
3. **Vanishing Intra-Sheet Commutators**:
   `[ℰ₊(A₁), ℰ₊(A₂)] = 0` and `[ℰ₋(C₁), ℰ₋(C₂)] = 0`.
4. **Abelian Adjoint Group Action on the Operator Ring**:
   `conjPlus P A₁ (conjPlus P A₂ X) = conjPlus P (A₁ + A₂) X` and
   `conjMinus P C₁ (conjMinus P C₂ X) = conjMinus P (C₁ + C₂) X`. -/
theorem d2_exact_abelian_exponential_families
    {P : B} (hP : P * P = P) (A A₁ A₂ C C₁ C₂ X : B) :
    unipotentExpPlus P A₁ * unipotentExpPlus P A₂ = unipotentExpPlus P (A₁ + A₂) ∧
    unipotentExpMinus P C₁ * unipotentExpMinus P C₂ = unipotentExpMinus P (C₁ + C₂) ∧
    unipotentExpPlus P A * unipotentExpPlusInv P A = 1 ∧
    unipotentExpPlusInv P A * unipotentExpPlus P A = 1 ∧
    unipotentExpMinus P C * unipotentExpMinusInv P C = 1 ∧
    unipotentExpMinusInv P C * unipotentExpMinus P C = 1 ∧
    comm (unipotentExpPlus P A₁) (unipotentExpPlus P A₂) = 0 ∧
    comm (unipotentExpMinus P C₁) (unipotentExpMinus P C₂) = 0 ∧
    conjPlus P A₁ (conjPlus P A₂ X) = conjPlus P (A₁ + A₂) X ∧
    conjMinus P C₁ (conjMinus P C₂ X) = conjMinus P (C₁ + C₂) X := by
  dsimp only [unipotentExpPlus, unipotentExpPlusInv, unipotentExpMinus, unipotentExpMinusInv,
    conjPlus, conjMinus]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Stage `𝔇₃` / Theorem 1 (Paired Operator Gaussians & Series-Free Polynomial Inversion)**:
Multiplying the primal `e`-exponential `ℰ₊(A) = 1 + N₊(A)` and the dual `m`-exponential
`ℰ₋(C) = 1 + N₋(C)` in either chiral order generates the **Paired Operator Gaussians**
`𝒢₊(P, A, C) = ℰ₊(A) * ℰ₋(C)` and `𝒢₋(P, A, C) = ℰ₋(C) * ℰ₊(A)`:
1. **Exact Quadratic Expansions**:
   `𝒢₊(P, A, C) = 1 + Φ + Q₊` and `𝒢₋(P, A, C) = 1 + Φ + Q₋`,
   where `Φ = N₊ + N₋`, `Q₊ = qgtPlus P A C = N₊ N₋`, and `Q₋ = qgtMinus P A C = N₋ N₊`.
2. **Exact Polynomial Inverse Expansions (Chiral Corner Swap `Q₊ ↔ Q₋`)**:
   `𝒢₊⁻¹(P, A, C) = (1 - N₋) * (1 - N₊) = 1 - Φ + Q₋` and
   `𝒢₋⁻¹(P, A, C) = (1 - N₊) * (1 - N₋) = 1 - Φ + Q₊`.
3. **Exact Series-Free Two-Sided Inversion in Any Associative Ring**:
   `𝒢₊ * 𝒢₊⁻¹ = 1`, `𝒢₊⁻¹ * 𝒢₊ = 1`, `𝒢₋ * 𝒢₋⁻¹ = 1`, and `𝒢₋⁻¹ * 𝒢₋ = 1`
   (holding identically without any spectral-radius or Neumann-series hypothesis).
4. **Möbius–Bruhat Opposite-Sign Specialization**:
   `𝒢₊(P, A, -C) = 1 + J - Q₊` and `𝒢₋(P, -A, C) = 1 - J - Q₋`. -/
theorem d3_paired_operator_gaussians_and_polynomial_inversion
    {P : B} (hP : P * P = P) (A C : B) :
    operatorGaussianPlus P A C = 1 + genPhi P A C + qgtPlus P A C ∧
    operatorGaussianMinus P A C = 1 + genPhi P A C + qgtMinus P A C ∧
    operatorGaussianPlusInv P A C = 1 - genPhi P A C + qgtMinus P A C ∧
    operatorGaussianMinusInv P A C = 1 - genPhi P A C + qgtPlus P A C ∧
    operatorGaussianPlus P A C * operatorGaussianPlusInv P A C = 1 ∧
    operatorGaussianPlusInv P A C * operatorGaussianPlus P A C = 1 ∧
    operatorGaussianMinus P A C * operatorGaussianMinusInv P A C = 1 ∧
    operatorGaussianMinusInv P A C * operatorGaussianMinus P A C = 1 ∧
    operatorGaussianPlus P A (-C) = 1 + genJ P A C - qgtPlus P A C ∧
    operatorGaussianMinus P (-A) C = 1 - genJ P A C - qgtMinus P A C := by
  dsimp only [operatorGaussianPlus, operatorGaussianPlusInv, operatorGaussianMinus,
    operatorGaussianMinusInv, unipotentExpPlus, unipotentExpPlusInv, unipotentExpMinus,
    unipotentExpMinusInv, qgtPlus, qgtMinus]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- The relative product of the two composite Peirce Gaussians.

For `a = conePlus P A` and `b = coneMinus P C`, this is also the conventional
elementary-gate commutator `(1+a)(1+b)(1-a)(1-b)`. Its polynomial form is
`1 + (a*b - b*a) - (a*b + b*a)*(a-b) + (a*b)^2`. This ring identity does
not identify these gates with a categorical braiding. -/
theorem operator_gaussian_relative_product
    {P : B} (hP : P * P = P) (A C : B) :
    operatorGaussianPlus P A C * operatorGaussianMinusInv P A C =
      1 + genSig P A C - genV P A C * genJ P A C +
        qgtPlus P A C * qgtPlus P A C := by
  dsimp only [operatorGaussianPlus, operatorGaussianMinusInv, unipotentExpPlus,
    unipotentExpMinus, unipotentExpPlusInv, unipotentExpMinusInv, genSig,
    genV, genJ, qgtPlus, qgtMinus, genPhi, conePlus, coneMinus]
  peirce_nf hP

/-- The elementary unipotent-gate commutator has the Peirce polynomial readout. -/
theorem unipotent_gate_group_commutator
    {P : B} (hP : P * P = P) (A C : B) :
    unipotentExpPlus P A * unipotentExpMinus P C *
        unipotentExpPlusInv P A * unipotentExpMinusInv P C =
      1 + genSig P A C - genV P A C * genJ P A C +
        qgtPlus P A C * qgtPlus P A C := by
  simpa only [operatorGaussianPlus, operatorGaussianMinusInv, mul_assoc] using
    operator_gaussian_relative_product hP A C

/-- The forward Gaussian is the elementary-gate commutator times the reverse Gaussian. -/
theorem operator_gaussian_forward_eq_commutator_mul_reverse
    {P : B} (hP : P * P = P) (A C : B) :
    (operatorGaussianPlus P A C * operatorGaussianMinusInv P A C) *
        operatorGaussianMinus P A C = operatorGaussianPlus P A C := by
  have hInv := (d3_paired_operator_gaussians_and_polynomial_inversion hP A C).2.2.2.2.2.2.2.1
  calc
    (operatorGaussianPlus P A C * operatorGaussianMinusInv P A C) *
        operatorGaussianMinus P A C =
      operatorGaussianPlus P A C *
        (operatorGaussianMinusInv P A C * operatorGaussianMinus P A C) := by
          rw [mul_assoc]
    _ = operatorGaussianPlus P A C := by rw [hInv, mul_one]

/-- **Stage `𝔇₄` (Birth of the Fisher–Rao–BKM Metric `V` and Berry–Amari Skewness `Σ` from Paired Gaussians)**:
Comparing the forward and backward Operator Gaussians `𝒢₊` and `𝒢₋` against the naive linear
tangent `1 + Φ` and against the unipotently translated Grassmannian chords (`PrimalDual.lean`)
reveals the exact origin of the symmetric metric `V` and antisymmetric curvature `Σ`:
1. **Individual Chiral Excesses over `1 + Φ`**:
   `𝒢₊ - (1 + Φ) = Q₊` and `𝒢₋ - (1 + Φ) = Q₋`.
2. **Symmetric Sum of Gaussian Excesses = Fisher–Rao–BKM Metric `V`**:
   `(𝒢₊ - (1 + Φ)) + (𝒢₋ - (1 + Φ)) = genV P A C`, and
   `𝒢₊ + 𝒢₋ = 2 • (1 + Φ) + genV P A C`.
3. **Inter-Sheet Exponential Commutator = Berry–Amari Skewness `Σ`**:
   `[ℰ₊(A), ℰ₋(C)] = 𝒢₊ - 𝒢₋ = genSig P A C`.
4. **Symmetric and Antisymmetric Inverse-Gaussian Readouts**:
   `(𝒢₊⁻¹ - (1 - Φ)) + (𝒢₋⁻¹ - (1 - Φ)) = genV P A C` and
   `𝒢₋⁻¹ - 𝒢₊⁻¹ = genSig P A C`.
5. **Identity with the Primal–Dual Grassmannian Chord Potentials (`archetype_A42`)**:
   `(P - conjPlus P A P) * (conjMinus P C P - P) = 𝒢₊ - (1 + Φ)` and
   `(conjMinus P C P - P) * (P - conjPlus P A P) = 𝒢₋ - (1 + Φ)`. -/
theorem d4_birth_of_fisher_metric_and_berry_skewness_from_gaussians
    {P : B} (hP : P * P = P) (A C : B) :
    operatorGaussianPlus P A C - (1 + genPhi P A C) = qgtPlus P A C ∧
    operatorGaussianMinus P A C - (1 + genPhi P A C) = qgtMinus P A C ∧
    (operatorGaussianPlus P A C - (1 + genPhi P A C)) +
        (operatorGaussianMinus P A C - (1 + genPhi P A C)) = genV P A C ∧
    operatorGaussianPlus P A C + operatorGaussianMinus P A C =
      (2 : ℤ) • (1 + genPhi P A C) + genV P A C ∧
    comm (unipotentExpPlus P A) (unipotentExpMinus P C) = genSig P A C ∧
    operatorGaussianPlus P A C - operatorGaussianMinus P A C = genSig P A C ∧
    (operatorGaussianPlusInv P A C - (1 - genPhi P A C)) +
        (operatorGaussianMinusInv P A C - (1 - genPhi P A C)) = genV P A C ∧
    operatorGaussianMinusInv P A C - operatorGaussianPlusInv P A C = genSig P A C ∧
    (P - conjPlus P A P) * (conjMinus P C P - P) =
      operatorGaussianPlus P A C - (1 + genPhi P A C) ∧
    (conjMinus P C P - P) * (P - conjPlus P A P) =
      operatorGaussianMinus P A C - (1 + genPhi P A C) := by
  dsimp only [operatorGaussianPlus, operatorGaussianPlusInv, operatorGaussianMinus,
    operatorGaussianMinusInv, unipotentExpPlus, unipotentExpPlusInv, unipotentExpMinus,
    unipotentExpMinusInv, qgtPlus, qgtMinus, conjPlus, conjMinus]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Stage `𝔇₅` / Theorem 3 (Amari's Dual Sheet Connections, Midpoint/Skewness Decomposition, and Fourfold Crossover)**:
Reusing `sheetPlusConnection P W` (`∇^(e) = P W P`), `sheetMinusConnection P W`
(`∇^(m) = (1 - P) W (1 - P)`), `sheetConnectionSum P W` (`Γ_sum = ∇^(e) + ∇^(m)`), and
`sheetConnectionDiff P W` (`Γ_diff = ∇^(e) - ∇^(m)`) from `Homogenized.lean`:
1. **Orthogonal Sheet Disjointness**:
   `∇^(e)(W) * ∇^(m)(W') = 0` and `∇^(m)(W) * ∇^(e)(W') = 0`.
2. **Midpoint & Skewness Reconstruction of Dual Connections (`2 ∇^(e), 2 ∇^(m)`)**:
   `Γ_sum(W) + Γ_diff(W) = 2 • ∇^(e)(W)` and `Γ_sum(W) - Γ_diff(W) = 2 • ∇^(m)(W)`.
3. **Chiral Involution Factorization of the Amari–Chentsov Skewness**:
   `Γ_diff(W) = S_P * Γ_sum(W)` and `Γ_diff(W) = Γ_sum(W) * S_P`.
4. **The Fourfold Sum–Difference Connection Crossover Law**:
   `[Γ_diff(W), Φ] = {Γ_sum(W), J}`,
   `{Γ_diff(W), Φ} = [Γ_sum(W), J]`,
   `[Γ_diff(W), J] = {Γ_sum(W), Φ}`, and
   `{Γ_diff(W), J} = [Γ_sum(W), Φ]`. -/
theorem d5_amari_dual_connections_midpoint_skewness_and_crossover
    {P : B} (hP : P * P = P) (A C W W' : B) :
    sheetPlusConnection P W * sheetMinusConnection P W' = 0 ∧
    sheetMinusConnection P W * sheetPlusConnection P W' = 0 ∧
    sheetConnectionSum P W + sheetConnectionDiff P W =
      (2 : ℤ) • sheetPlusConnection P W ∧
    sheetConnectionSum P W - sheetConnectionDiff P W =
      (2 : ℤ) • sheetMinusConnection P W ∧
    sheetConnectionDiff P W = invS P * sheetConnectionSum P W ∧
    sheetConnectionDiff P W = sheetConnectionSum P W * invS P ∧
    comm (sheetConnectionDiff P W) (genPhi P A C) =
      anticomm (sheetConnectionSum P W) (genJ P A C) ∧
    anticomm (sheetConnectionDiff P W) (genPhi P A C) =
      comm (sheetConnectionSum P W) (genJ P A C) ∧
    comm (sheetConnectionDiff P W) (genJ P A C) =
      anticomm (sheetConnectionSum P W) (genPhi P A C) ∧
    anticomm (sheetConnectionDiff P W) (genJ P A C) =
      comm (sheetConnectionSum P W) (genPhi P A C) := by
  have hCross := sheetConnection_sum_difference_crossover hP W A C
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hCross.1, hCross.2.1, hCross.2.2.1, hCross.2.2.2⟩ <;>
    (simp only [sheetConnectionSum, sheetConnectionDiff, sheetPlusConnection,
      sheetMinusConnection]; peirce_nf hP)

/-- **Stage `𝔇₆` / Theorem 2 (The Non-Commutative Operator Pythagorean Theorem & Orthogonal Sheet Gramians)**:
Because the upper-sheet Gramian `Q₊ = N₊ N₋ ∈ P B P` and the lower-sheet Gramian
`Q₋ = N₋ N₊ ∈ (1 - P) B (1 - P)` live on orthogonal Peirce sheets:
1. **Exact Mutual Gramian Annihilation**:
   `Q₊ * Q₋ = 0` and `Q₋ * Q₊ = 0`.
2. **Orthogonal Sheet Projections of `V` and `Σ`**:
   `P * V * P = Q₊`, `(1 - P) * V * (1 - P) = Q₋`,
   `P * Σ * P = Q₊`, and `(1 - P) * Σ * (1 - P) = -Q₋`.
3. **The Exact Non-Commutative Operator Pythagorean Theorem**:
   `V * V = Q₊ * Q₊ + Q₋ * Q₋`,
   `Σ * Σ = Q₊ * Q₊ + Q₋ * Q₋`, and therefore
   `V * V = Σ * Σ` (`V² - Σ² = 0`), while the mixed product is the sheet-Gramian difference
   `V * Σ = Q₊ * Q₊ - Q₋ * Q₋` and `Σ * V = Q₊ * Q₊ - Q₋ * Q₋`.
4. **Orthogonal Pythagorean Decomposition of the Paired Gaussian Excesses**:
   `(𝒢₊ - (1 + Φ)) * (𝒢₋ - (1 + Φ)) = 0`,
   `(𝒢₋ - (1 + Φ)) * (𝒢₊ - (1 + Φ)) = 0`, and
   `(𝒢₊ - (1 + Φ))² + (𝒢₋ - (1 + Φ))² = V * V`. -/
theorem d6_operator_pythagorean_theorem_and_orthogonal_gramians
    {P : B} (hP : P * P = P) (A C : B) :
    qgtPlus P A C * qgtMinus P A C = 0 ∧
    qgtMinus P A C * qgtPlus P A C = 0 ∧
    peirce11 P (genV P A C) = qgtPlus P A C ∧
    peirce00 P (genV P A C) = qgtMinus P A C ∧
    peirce11 P (genSig P A C) = qgtPlus P A C ∧
    peirce00 P (genSig P A C) = -qgtMinus P A C ∧
    genV P A C * genV P A C =
      qgtPlus P A C * qgtPlus P A C + qgtMinus P A C * qgtMinus P A C ∧
    genSig P A C * genSig P A C =
      qgtPlus P A C * qgtPlus P A C + qgtMinus P A C * qgtMinus P A C ∧
    genV P A C * genV P A C = genSig P A C * genSig P A C ∧
    genV P A C * genSig P A C =
      qgtPlus P A C * qgtPlus P A C - qgtMinus P A C * qgtMinus P A C ∧
    genSig P A C * genV P A C =
      qgtPlus P A C * qgtPlus P A C - qgtMinus P A C * qgtMinus P A C ∧
    (operatorGaussianPlus P A C - (1 + genPhi P A C)) *
        (operatorGaussianMinus P A C - (1 + genPhi P A C)) = 0 ∧
    (operatorGaussianMinus P A C - (1 + genPhi P A C)) *
        (operatorGaussianPlus P A C - (1 + genPhi P A C)) = 0 ∧
    (operatorGaussianPlus P A C - (1 + genPhi P A C)) *
          (operatorGaussianPlus P A C - (1 + genPhi P A C)) +
        (operatorGaussianMinus P A C - (1 + genPhi P A C)) *
          (operatorGaussianMinus P A C - (1 + genPhi P A C)) =
      genV P A C * genV P A C := by
  dsimp only [operatorGaussianPlus, operatorGaussianMinus, unipotentExpPlus, unipotentExpMinus,
    qgtPlus, qgtMinus]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- The **Chiral Supertrace** readout functional `Str(Y) := Tr(S_P * Y)` associated to an
additive trace map `tr : B →+ K` and an idempotent cut `P` (`S_P = invS P = P - (1 - P)`). -/
def chiralSupertrace {K : Type*} [AddCommGroup K] (tr : B →+ K) (P Y : B) : K :=
  tr (invS P * Y)

/-- **Stage `𝔔₄` / Cyclic-Trace Blindness and Chiral Readout**
(`q4_theorem_trace_first_blindness_and_chiral_supertrace_recovery`):
Formalizes an algebraic limitation of cyclic scalar traces: they annihilate the trace of the
operator difference `Σ = Q₊ - Q₋ = [N₊, N₋]`, while the chiral functional
`Str(Y) = Tr(S_P * Y)` recovers `Tr(V)` from `Σ`. This is a statement about these functionals
on the specified Peirce operators; it does not assert a historical explanation for textbook
treatments or establish a general classification of quantum information geometries:
For any idempotent `P * P = P` and any additive trace `tr : B →+ K` satisfying the cyclic trace
identity `hCyclic : ∀ X Y : B, tr (X * Y) = tr (Y * X)`:
1. **Cyclic Trace Equality of Sheet Gramians (`Tr(Q₊) = Tr(Q₋)`)**:
   `tr (qgtPlus P A C) = tr (qgtMinus P A C)`.
2. **Textbook Trace-First Indistinguishability of Forward & Backward Gaussians (`Tr(𝒢₊) = Tr(𝒢₋)`)**:
   `tr (operatorGaussianPlus P A C) = tr (operatorGaussianMinus P A C)` and
   `tr (operatorGaussianPlus P A C - operatorGaussianMinus P A C) = 0`.
3. **Textbook Trace-First Blindness to the Operator Skewness `Σ` (`Tr(Σ) = 0`)**:
   `tr (genSig P A C) = 0` and
   `tr (comm (unipotentExpPlus P A) (unipotentExpMinus P C)) = 0`,
   while `tr (genV P A C) = (2 : ℤ) • tr (qgtPlus P A C)`.
4. **Operator-Level Chiral Inversion (`S_P * V = Σ` and `S_P * Σ = V`)**:
   `invS P * qgtPlus P A C = qgtPlus P A C`,
   `invS P * qgtMinus P A C = -qgtMinus P A C`,
   `invS P * genV P A C = genSig P A C`, and
   `invS P * genSig P A C = genV P A C`.
5. **Complete Chiral Supertrace Visibility Inversion (`Str(V) = 0` and `Str(Σ) = Tr(V) = 2 • Tr(Q₊)`)**:
   `chiralSupertrace tr P (genV P A C) = 0`,
   `chiralSupertrace tr P (genSig P A C) = tr (genV P A C)`,
   `chiralSupertrace tr P (genSig P A C) = (2 : ℤ) • tr (qgtPlus P A C)`, and
   `chiralSupertrace tr P (operatorGaussianPlus P A C - operatorGaussianMinus P A C) = tr (genV P A C)`. -/
theorem q4_theorem_trace_first_blindness_and_chiral_supertrace_recovery
    {K : Type*} [AddCommGroup K] (tr : B →+ K)
    (hCyclic : ∀ X Y : B, tr (X * Y) = tr (Y * X))
    {P : B} (hP : P * P = P) (A C : B) :
    tr (qgtPlus P A C) = tr (qgtMinus P A C) ∧
    tr (operatorGaussianPlus P A C) = tr (operatorGaussianMinus P A C) ∧
    tr (operatorGaussianPlus P A C - operatorGaussianMinus P A C) = 0 ∧
    tr (genSig P A C) = 0 ∧
    tr (comm (unipotentExpPlus P A) (unipotentExpMinus P C)) = 0 ∧
    tr (genV P A C) = (2 : ℤ) • tr (qgtPlus P A C) ∧
    invS P * qgtPlus P A C = qgtPlus P A C ∧
    invS P * qgtMinus P A C = -qgtMinus P A C ∧
    invS P * genV P A C = genSig P A C ∧
    invS P * genSig P A C = genV P A C ∧
    chiralSupertrace tr P (genV P A C) = 0 ∧
    chiralSupertrace tr P (genSig P A C) = tr (genV P A C) ∧
    chiralSupertrace tr P (genSig P A C) = (2 : ℤ) • tr (qgtPlus P A C) ∧
    chiralSupertrace tr P (operatorGaussianPlus P A C - operatorGaussianMinus P A C) =
      tr (genV P A C) := by
  have hQTr : tr (qgtPlus P A C) = tr (qgtMinus P A C) := by
    dsimp only [qgtPlus, qgtMinus]
    exact hCyclic (conePlus P A) (coneMinus P C)
  have hSigDef : genSig P A C = qgtPlus P A C - qgtMinus P A C := rfl
  have hVDef : genV P A C = qgtPlus P A C + qgtMinus P A C := rfl
  have hTrSig : tr (genSig P A C) = 0 := by
    rw [hSigDef, map_sub, hQTr, sub_self]
  have hTrV : tr (genV P A C) = (2 : ℤ) • tr (qgtPlus P A C) := by
    rw [hVDef, map_add, ← hQTr, two_zsmul]
  have hD4 := d4_birth_of_fisher_metric_and_berry_skewness_from_gaussians hP A C
  have hGDiff : operatorGaussianPlus P A C - operatorGaussianMinus P A C = genSig P A C :=
    hD4.2.2.2.2.2.1
  have hExpComm : comm (unipotentExpPlus P A) (unipotentExpMinus P C) = genSig P A C :=
    hD4.2.2.2.2.1
  have hTrGDiff : tr (operatorGaussianPlus P A C - operatorGaussianMinus P A C) = 0 := by
    rw [hGDiff, hTrSig]
  have hTrGEq : tr (operatorGaussianPlus P A C) = tr (operatorGaussianMinus P A C) := by
    rw [← sub_eq_zero, ← map_sub]
    exact hTrGDiff
  have hTrExpComm : tr (comm (unipotentExpPlus P A) (unipotentExpMinus P C)) = 0 := by
    rw [hExpComm, hTrSig]
  have hSQPlus : invS P * qgtPlus P A C = qgtPlus P A C := by
    dsimp only [qgtPlus]; peirce_nf hP
  have hSQMinus : invS P * qgtMinus P A C = -qgtMinus P A C := by
    dsimp only [qgtMinus]; peirce_nf hP
  have hSV : invS P * genV P A C = genSig P A C := by peirce_nf hP
  have hSSig : invS P * genSig P A C = genV P A C := by peirce_nf hP
  have hStrV : chiralSupertrace tr P (genV P A C) = 0 := by
    dsimp only [chiralSupertrace]
    rw [hSV, hTrSig]
  have hStrSig : chiralSupertrace tr P (genSig P A C) = tr (genV P A C) := by
    dsimp only [chiralSupertrace]
    rw [hSSig]
  have hStrSigTwo : chiralSupertrace tr P (genSig P A C) = (2 : ℤ) • tr (qgtPlus P A C) := by
    rw [hStrSig, hTrV]
  have hStrGDiff :
      chiralSupertrace tr P (operatorGaussianPlus P A C - operatorGaussianMinus P A C) =
        tr (genV P A C) := by
    rw [hGDiff, hStrSig]
  exact ⟨hQTr, hTrGEq, hTrGDiff, hTrSig, hTrExpComm, hTrV,
    hSQPlus, hSQMinus, hSV, hSSig, hStrV, hStrSig, hStrSigTwo, hStrGDiff⟩

/-- **Finite-matrix specialization of trace blindness and chiral recovery.**
For matrices over a commutative ring, Mathlib's matrix trace supplies the
additive readout and its cyclicity theorem supplies the trace law; neither is
an extra premise. All Gaussian, Gramian, commutator, and chiral readouts are
the corresponding specialization of `q4_theorem_trace_first_blindness_and_chiral_supertrace_recovery`.
-/
theorem matrix_trace_first_blindness_and_chiral_supertrace_recovery
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R]
    (P A C : Matrix ι ι R) (hP : P * P = P) :
    Matrix.trace (qgtPlus P A C) = Matrix.trace (qgtMinus P A C) ∧
    Matrix.trace (operatorGaussianPlus P A C) =
      Matrix.trace (operatorGaussianMinus P A C) ∧
    Matrix.trace (operatorGaussianPlus P A C - operatorGaussianMinus P A C) = 0 ∧
    Matrix.trace (genSig P A C) = 0 ∧
    Matrix.trace (comm (unipotentExpPlus P A) (unipotentExpMinus P C)) = 0 ∧
    Matrix.trace (genV P A C) = (2 : ℤ) • Matrix.trace (qgtPlus P A C) ∧
    invS P * qgtPlus P A C = qgtPlus P A C ∧
    invS P * qgtMinus P A C = -qgtMinus P A C ∧
    invS P * genV P A C = genSig P A C ∧
    invS P * genSig P A C = genV P A C ∧
    Matrix.trace (invS P * genV P A C) = 0 ∧
    Matrix.trace (invS P * genSig P A C) = Matrix.trace (genV P A C) ∧
    Matrix.trace (invS P * genSig P A C) =
      (2 : ℤ) • Matrix.trace (qgtPlus P A C) ∧
    Matrix.trace (invS P *
      (operatorGaussianPlus P A C - operatorGaussianMinus P A C)) =
        Matrix.trace (genV P A C) := by
  simpa [Matrix.traceAddMonoidHom, chiralSupertrace] using
    (q4_theorem_trace_first_blindness_and_chiral_supertrace_recovery
      (tr := Matrix.traceAddMonoidHom ι R)
      (hCyclic := fun X Y => Matrix.trace_mul_comm X Y) hP A C)

/-- **Stage `𝔔₄` Higher-Moment Extension (`q4_higher_moment_trace_blindness_and_supertrace_recovery`)**:
Reusing `GradedTraceMoments.peirce_sheet_positive_power_trace`,
`GradedTraceMoments.grading_metric_power_eq_commutator`, and
`GradedTraceMoments.cyclic_grading_metric_power_zero`:
For every `k : ℕ` and any additive cyclic trace `tr : B →+ K`:
1. `tr ((qgtPlus P A C) ^ (k + 1)) = tr ((qgtMinus P A C) ^ (k + 1))`
   (all positive-degree sheet Gramian moments have equal cyclic trace).
2. `invS P * (genV P A C) ^ (k + 1) = comm ((genV P A C) ^ k * conePlus P A) (coneMinus P C)`
   (every graded positive power of `V` is an exact commutator).
3. `chiralSupertrace tr P ((genV P A C) ^ (k + 1)) = 0`
   (the chiral supertrace annihilates every positive power `V^{k+1}`). -/
theorem q4_higher_moment_trace_blindness_and_supertrace_recovery
    {K : Type*} [AddCommGroup K] (tr : B →+ K)
    (hCyclic : ∀ X Y : B, tr (X * Y) = tr (Y * X))
    {P : B} (hP : P * P = P) (A C : B) (k : ℕ) :
    tr ((qgtPlus P A C) ^ (k + 1)) = tr ((qgtMinus P A C) ^ (k + 1)) ∧
    invS P * (genV P A C) ^ (k + 1) =
      comm ((genV P A C) ^ k * conePlus P A) (coneMinus P C) ∧
    chiralSupertrace tr P ((genV P A C) ^ (k + 1)) = 0 := by
  refine ⟨GradedTraceMoments.peirce_sheet_positive_power_trace tr hCyclic P A C k,
    GradedTraceMoments.grading_metric_power_eq_commutator hP A C k,
    GradedTraceMoments.cyclic_grading_metric_power_zero tr hCyclic hP A C k⟩

end AlgebraicAmariSpine

/-!
## 3. Continuous Amari `α`-Connection Family & Stage `𝔇₇` (Legendre–Peirce Resolvent, Bergman Kernel, and Bregman Divergence Closure)
-/

section AlphaConnectionsAndLegendreBregman

variable {B : Type*} [Ring B] [Algebra ℝ B]

/-- Continuous one-parameter family of Amari `α`-connections (`α ∈ ℝ`) on the two-sheeted
Peirce spine:
`∇^(α)(P, W) := (1 / 2 : ℝ) • Γ_sum(P, W) + (α / 2 : ℝ) • Γ_diff(P, W)`.
At `α = 0`, this is the self-dual Levi-Civita midpoint `(1/2) • Γ_sum`;
at `α = +1`, the primal `e`-connection `∇^(e) = P W P`;
at `α = -1`, the dual `m`-connection `∇^(m) = (1 - P) W (1 - P)`. -/
noncomputable def amariAlphaConnection (α : ℝ) (P W : B) : B :=
  (1 / 2 : ℝ) • sheetConnectionSum P W + (α / 2 : ℝ) • sheetConnectionDiff P W

/-- **Amari Conjugate `±α`-Connection Duality**:
1. **Self-Dual Midpoint (`α = 0`)**:
   `amariAlphaConnection 0 P W = (1 / 2 : ℝ) • sheetConnectionSum P W`.
2. **Primal `e`-Connection (`α = +1`)**:
   `amariAlphaConnection 1 P W = sheetPlusConnection P W`.
3. **Dual `m`-Connection (`α = -1`)**:
   `amariAlphaConnection (-1) P W = sheetMinusConnection P W`.
4. **Conjugate `±α` Midpoint Law**:
   For every `α : ℝ`, `amariAlphaConnection α P W + amariAlphaConnection (-α) P W = sheetConnectionSum P W`.
5. **Conjugate `±α` Skewness Difference Law**:
   For every `α : ℝ`, `amariAlphaConnection α P W - amariAlphaConnection (-α) P W = α • sheetConnectionDiff P W`. -/
theorem amariAlphaConnection_conjugate_duality (α : ℝ) (P W : B) :
    amariAlphaConnection 0 P W = (1 / 2 : ℝ) • sheetConnectionSum P W ∧
    amariAlphaConnection 1 P W = sheetPlusConnection P W ∧
    amariAlphaConnection (-1) P W = sheetMinusConnection P W ∧
    amariAlphaConnection α P W + amariAlphaConnection (-α) P W =
      sheetConnectionSum P W ∧
    amariAlphaConnection α P W - amariAlphaConnection (-α) P W =
      α • sheetConnectionDiff P W := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [amariAlphaConnection]
    norm_num
  · dsimp [amariAlphaConnection, sheetConnectionSum, sheetConnectionDiff]
    module
  · dsimp [amariAlphaConnection, sheetConnectionSum, sheetConnectionDiff]
    module
  · dsimp [amariAlphaConnection]
    module
  · dsimp [amariAlphaConnection]
    module

/-- **Stage `𝔇₇` (Legendre–Peirce Resolvent Duality, Bergman Kernel Identity, and Operator Bregman Divergence Closure)**:
Unifies the algebraic Gaussian/Pythagorean spine (`𝔇₁`–`𝔇₆`) with the Bergman operator
(`Bergman.lean`) and the Legendre–Peirce resolvent and Operator Bregman divergence series
(`RadonNikodymKahlerParaKahlerBregmanPoset.lean`):
1. **Bergman Operator Identity at `1` (`archetype_A23_bergman_operator`)**:
   `bergmanOp P A C 1 = (1 - Q₊) * (1 - Q₋) = 1 - V`.
2. **Elliptic & Hyperbolic Legendre–Peirce Resolvent Moment Recovery**:
   If `(1 + V) * W_+ = 1` and `W_+ * (1 + V) = 1`, then
   `(1 + V) * legendreDualExpectationPlus W_+ P A C = Φ` and `W_+ * Φ = Φ * W_+`.
   If `(1 - V) * W_- = 1` and `W_- * (1 - V) = 1`, then
   `(1 - V) * legendreDualExpectationMinus W_- P A C = Φ` and `W_- * Φ = Φ * W_-`.
3. **Exact Cancellation of the `n = 1` Linear Term in the Operator Bregman Divergence Series**:
   `geometricSeriesPartialSum N V - paraKahlerPotentialPartialSum N V = bregmanDivergenceMinusPartialSum N V`,
   with quartic expansion
   `bregmanDivergenceMinusPartialSum 4 V = (1/2) • V² + (2/3) • V³ + (3/4) • V⁴`.
4. **Conditional Trace Positivity of the Finite Bregman Series**:
   If `∀ n ∈ Finset.Icc 1 N, 0 ≤ τ (V ^ n)`, then
   `0 ≤ ∑ n ∈ Finset.Icc 1 N, (((n - 1) / n) * τ (V ^ n))`. -/
theorem d7_legendre_resolvent_bregman_divergence_and_bkm_closure
    {P : B} (hP : P * P = P) (A C W_plus W_minus V : B) (N : ℕ) (τ : B → ℝ)
    (hW_plus_r : (1 + genV P A C) * W_plus = 1)
    (hW_plus_l : W_plus * (1 + genV P A C) = 1)
    (hW_minus_r : (1 - genV P A C) * W_minus = 1)
    (hW_minus_l : W_minus * (1 - genV P A C) = 1)
    (hτ : ∀ n ∈ Finset.Icc 1 N, 0 ≤ τ (V ^ n)) :
    bergmanOp P A C 1 = 1 - genV P A C ∧
    (1 - qgtPlus P A C) * (1 - qgtMinus P A C) = 1 - genV P A C ∧
    (1 + genV P A C) * legendreDualExpectationPlus W_plus P A C = genPhi P A C ∧
    W_plus * genPhi P A C = genPhi P A C * W_plus ∧
    (1 - genV P A C) * legendreDualExpectationMinus W_minus P A C = genPhi P A C ∧
    W_minus * genPhi P A C = genPhi P A C * W_minus ∧
    geometricSeriesPartialSum N V - paraKahlerPotentialPartialSum N V =
      bregmanDivergenceMinusPartialSum N V ∧
    bregmanDivergenceMinusPartialSum 4 V =
      (1 / 2 : ℝ) • V ^ 2 + (2 / 3 : ℝ) • V ^ 3 + (3 / 4 : ℝ) • V ^ 4 ∧
    0 ≤ ∑ n ∈ Finset.Icc 1 N, ((((n : ℝ) - 1) / (n : ℝ)) * τ (V ^ n)) := by
  have hBerg : bergmanOp P A C 1 = 1 - genV P A C :=
    (archetype_A23_bergman_operator hP A C).1
  have hFact : (1 - qgtPlus P A C) * (1 - qgtMinus P A C) = 1 - genV P A C := by
    dsimp only [qgtPlus, qgtMinus]
    peirce_nf hP
  have hT3 := theorem3_legendre_resolvent_and_bregman_divergence
    hP A C W_plus W_minus V N hW_plus_r hW_plus_l hW_minus_r hW_minus_l 0
  have hPos := bregmanTracePartialSum_nonneg N V τ hτ
  exact ⟨hBerg, hFact, hT3.1, hT3.2.1, hT3.2.2.1, hT3.2.2.2.1,
    hT3.2.2.2.2.1, hT3.2.2.2.2.2.1, hPos⟩

/-!
## 4. Concrete `M₂(ℝ)` Witness & Master Synthesis (`𝔇₁ ≺ 𝔇₂ ≺ 𝔇₃ ≺ 𝔇₄ ≺ 𝔇₅ ≺ 𝔇₆ ≺ 𝔇₇`)
-/

/-- Concrete `2 × 2` idempotent projector `P₁₁ = !![1, 0; 0, 0]` in `M₂(ℝ)`. -/
def amariMatrixProj : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- The complementary projector `1 - P = E₂₂ = !![0, 0; 0, 1]` in `M₂(ℝ)`. -/
lemma amariMatrixProj_comp :
    (1 : Matrix (Fin 2) (Fin 2) ℝ) - amariMatrixProj = !![0, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [amariMatrixProj, Matrix.sub_apply, Matrix.one_apply]

/-- The concrete rank-one Peirce cut is idempotent. -/
theorem amariMatrixProj_idempotent :
    amariMatrixProj * amariMatrixProj = amariMatrixProj := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [amariMatrixProj]

/-- Upper Gramian for the concrete matrix-unit throat. -/
theorem amariMatrix_qgtPlus :
    qgtPlus amariMatrixProj rnMatrixPlus rnMatrixMinus = amariMatrixProj := by
  unfold qgtPlus conePlus coneMinus
  rw [amariMatrixProj_comp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [amariMatrixProj, rnMatrixPlus, rnMatrixMinus]

/-- Lower Gramian for the concrete matrix-unit throat. -/
theorem amariMatrix_qgtMinus :
    qgtMinus amariMatrixProj rnMatrixPlus rnMatrixMinus =
      1 - amariMatrixProj := by
  unfold qgtMinus conePlus coneMinus
  rw [amariMatrixProj_comp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [amariMatrixProj, rnMatrixPlus, rnMatrixMinus]

/-- **Concrete `2 × 2` Matrix Witness for Paired Operator Gaussians & the Operator Pythagorean Theorem**:
In `M₂(ℝ)` with `P = amariMatrixProj = E₁₁`, `A = rnMatrixPlus = E₁₂`, and
`C = rnMatrixMinus = E₂₁`:
1. `P * P = P`.
2. The forward and backward Operator Gaussians are distinct non-commutative unipotent matrices:
   `operatorGaussianPlus P A C ≠ operatorGaussianMinus P A C`.
3. The upper and lower sheet Gramians `Q₊ = E₁₁` and `Q₋ = E₂₂` are non-zero and mutually
   orthogonal (`Q₊ * Q₋ = 0`).
4. Both `V²` and `Σ²` equal the identity matrix `1 : Matrix (Fin 2) (Fin 2) ℝ ≠ 0`. -/
theorem amari_matrix_two_by_two_gaussian_pythagorean_witness :
    amariMatrixProj * amariMatrixProj = amariMatrixProj ∧
    operatorGaussianPlus amariMatrixProj rnMatrixPlus rnMatrixMinus ≠
      operatorGaussianMinus amariMatrixProj rnMatrixPlus rnMatrixMinus ∧
    qgtPlus amariMatrixProj rnMatrixPlus rnMatrixMinus ≠ 0 ∧
    qgtMinus amariMatrixProj rnMatrixPlus rnMatrixMinus ≠ 0 ∧
    qgtPlus amariMatrixProj rnMatrixPlus rnMatrixMinus *
      qgtMinus amariMatrixProj rnMatrixPlus rnMatrixMinus = 0 ∧
    genV amariMatrixProj rnMatrixPlus rnMatrixMinus *
      genV amariMatrixProj rnMatrixPlus rnMatrixMinus = 1 ∧
    genSig amariMatrixProj rnMatrixPlus rnMatrixMinus *
      genSig amariMatrixProj rnMatrixPlus rnMatrixMinus = 1 := by
  have hP := amariMatrixProj_idempotent
  have hQPlus := amariMatrix_qgtPlus
  have hQMinus := amariMatrix_qgtMinus
  have hV : genV amariMatrixProj rnMatrixPlus rnMatrixMinus = 1 := by
    change qgtPlus amariMatrixProj rnMatrixPlus rnMatrixMinus +
      qgtMinus amariMatrixProj rnMatrixPlus rnMatrixMinus = 1
    rw [hQPlus, hQMinus]
    abel
  have hPyth := d6_operator_pythagorean_theorem_and_orthogonal_gramians
    hP rnMatrixPlus rnMatrixMinus
  have hD4 := d4_birth_of_fisher_metric_and_berry_skewness_from_gaussians
    hP rnMatrixPlus rnMatrixMinus
  have hVSq :
      genV amariMatrixProj rnMatrixPlus rnMatrixMinus *
        genV amariMatrixProj rnMatrixPlus rnMatrixMinus = 1 := by
    rw [hV, mul_one]
  refine ⟨hP, ?_, ?_, ?_, hPyth.1, hVSq, ?_⟩
  · intro hEq
    have hDiffZero :
        operatorGaussianPlus amariMatrixProj rnMatrixPlus rnMatrixMinus -
          operatorGaussianMinus amariMatrixProj rnMatrixPlus rnMatrixMinus = 0 :=
      sub_eq_zero.mpr hEq
    rw [hD4.2.2.2.2.2.1] at hDiffZero
    have hSig : genSig amariMatrixProj rnMatrixPlus rnMatrixMinus =
        amariMatrixProj - (1 - amariMatrixProj) := by
      change qgtPlus amariMatrixProj rnMatrixPlus rnMatrixMinus -
        qgtMinus amariMatrixProj rnMatrixPlus rnMatrixMinus =
        amariMatrixProj - (1 - amariMatrixProj)
      rw [hQPlus, hQMinus]
    rw [hSig] at hDiffZero
    have h00 := congr_arg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hDiffZero
    simp [amariMatrixProj] at h00
  · rw [hQPlus]
    intro hZero
    have h00 := congr_arg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hZero
    simp [amariMatrixProj] at h00
  · rw [hQMinus]
    intro hZero
    have h11 := congr_arg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) hZero
    simp [amariMatrixProj] at h11
  · rw [← hPyth.2.2.2.2.2.2.2.2.1, hVSq]

/-- **Concrete `2 × 2` Matrix Witness for Textbook Trace-First Blindness vs. Chiral Supertrace Visibility**:
In `M₂(ℝ)` with `P = amariMatrixProj = E₁₁`, `A = rnMatrixPlus = E₁₂`, and
`C = rnMatrixMinus = E₂₁`:
1. At the operator level, the skewness/curvature operator `Σ = genSig P A C = diag(1, -1)` is
   **strictly non-zero** (`genSig P A C ≠ 0`).
2. Under the ordinary matrix trace `Matrix.trace`, `Σ` is **identically erased**
   (`Matrix.trace (genSig P A C) = 0`), and the forward and backward Operator Gaussians have
   identical traces (`Matrix.trace (operatorGaussianPlus P A C) = 3` and
   `Matrix.trace (operatorGaussianMinus P A C) = 3`).
3. Under the chiral supertrace `Y ↦ Matrix.trace (invS P * Y)`, visibility is completely inverted:
   `Matrix.trace (invS P * genV P A C) = 0`, whereas
   `Matrix.trace (invS P * genSig P A C) = Matrix.trace (genV P A C) = 2 ≠ 0`! -/
theorem matrix_two_by_two_trace_blindness_vs_supertrace_witness :
    genSig amariMatrixProj rnMatrixPlus rnMatrixMinus ≠ 0 ∧
    Matrix.trace (genSig amariMatrixProj rnMatrixPlus rnMatrixMinus) = 0 ∧
    Matrix.trace (operatorGaussianPlus amariMatrixProj rnMatrixPlus rnMatrixMinus) = 3 ∧
    Matrix.trace (operatorGaussianMinus amariMatrixProj rnMatrixPlus rnMatrixMinus) = 3 ∧
    Matrix.trace (genV amariMatrixProj rnMatrixPlus rnMatrixMinus) = 2 ∧
    Matrix.trace (invS amariMatrixProj * genV amariMatrixProj rnMatrixPlus rnMatrixMinus) = 0 ∧
    Matrix.trace (invS amariMatrixProj * genSig amariMatrixProj rnMatrixPlus rnMatrixMinus) = 2 ∧
    Matrix.trace (invS amariMatrixProj * genSig amariMatrixProj rnMatrixPlus rnMatrixMinus) =
      Matrix.trace (genV amariMatrixProj rnMatrixPlus rnMatrixMinus) := by
  have hP := amariMatrixProj_idempotent
  have hQPlus := amariMatrix_qgtPlus
  have hQMinus := amariMatrix_qgtMinus
  have hV : genV amariMatrixProj rnMatrixPlus rnMatrixMinus = 1 := by
    change qgtPlus amariMatrixProj rnMatrixPlus rnMatrixMinus +
      qgtMinus amariMatrixProj rnMatrixPlus rnMatrixMinus = 1
    rw [hQPlus, hQMinus]
    abel
  have hSig : genSig amariMatrixProj rnMatrixPlus rnMatrixMinus =
      amariMatrixProj - (1 - amariMatrixProj) := by
    change qgtPlus amariMatrixProj rnMatrixPlus rnMatrixMinus -
      qgtMinus amariMatrixProj rnMatrixPlus rnMatrixMinus =
      amariMatrixProj - (1 - amariMatrixProj)
    rw [hQPlus, hQMinus]
  have hTrP : Matrix.trace amariMatrixProj = 1 := by
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two, amariMatrixProj]
  have hTr1 : Matrix.trace (1 : Matrix (Fin 2) (Fin 2) ℝ) = 2 := by
    simp [Matrix.trace, Matrix.diag]
  have hTrPhi : Matrix.trace (genPhi amariMatrixProj rnMatrixPlus rnMatrixMinus) = 0 := by
    unfold genPhi conePlus coneMinus
    rw [amariMatrixProj_comp]
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two, amariMatrixProj, rnMatrixPlus, rnMatrixMinus]
  have hD3 := d3_paired_operator_gaussians_and_polynomial_inversion
    hP rnMatrixPlus rnMatrixMinus
  have hTrSig : Matrix.trace (genSig amariMatrixProj rnMatrixPlus rnMatrixMinus) = 0 := by
    rw [hSig, Matrix.trace_sub, Matrix.trace_sub, hTrP, hTr1]
    norm_num
  have hTrV : Matrix.trace (genV amariMatrixProj rnMatrixPlus rnMatrixMinus) = 2 := by
    rw [hV, hTr1]
  have hSSig :
      invS amariMatrixProj * genSig amariMatrixProj rnMatrixPlus rnMatrixMinus =
        genV amariMatrixProj rnMatrixPlus rnMatrixMinus := by
    peirce_nf hP
  have hSV :
      invS amariMatrixProj * genV amariMatrixProj rnMatrixPlus rnMatrixMinus =
        genSig amariMatrixProj rnMatrixPlus rnMatrixMinus := by
    peirce_nf hP
  refine ⟨?_, hTrSig, ?_, ?_, hTrV, ?_, ?_, ?_⟩
  · rw [hSig]
    intro hZero
    have h00 := congr_arg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hZero
    simp [amariMatrixProj] at h00
  · rw [hD3.1, hQPlus, Matrix.trace_add, Matrix.trace_add, hTr1, hTrPhi, hTrP]
    norm_num
  · rw [hD3.2.1, hQMinus, Matrix.trace_add, Matrix.trace_add, Matrix.trace_sub,
      hTr1, hTrPhi, hTrP]
    norm_num
  · rw [hSV, hTrSig]
  · rw [hSSig, hTrV]
  · rw [hSSig]

/-- **Master Structural Synthesis (`𝔇₁ ≺ ⋯ ≺ 𝔇₇` and `𝔔₁ ≺ ⋯ ≺ 𝔔₆`)**:
Combines in one kernel-checked theorem:
1. Strict acyclicity and cardinalities of `AmariOperatorGeometryStage` (`7` stages) and
   `FirstQuantizedAmariStage` (`6` stages).
2. **Rung 0**: `(1 + Φ) * (1 - Φ) = 1 - V` (self-dual exponential curvature defect).
3. **Stage `𝔇₁` & `𝔇₂` (`𝔔₁` & `𝔔₂`)**: Exact Abelian chiral exponential laws
   `ℰ₊(A₁) * ℰ₊(A₂) = ℰ₊(A₁ + A₂)` and `ℰ₋(C₁) * ℰ₋(C₂) = ℰ₋(C₁ + C₂)`.
4. **Stage `𝔇₃` (`𝔔₂`)**: Paired Operator Gaussian expansions `𝒢₊ = 1 + Φ + Q₊`,
   `𝒢₋ = 1 + Φ + Q₋` and series-free polynomial inversion `𝒢₊ * 𝒢₊⁻¹ = 1`, `𝒢₋ * 𝒢₋⁻¹ = 1`.
5. **Stage `𝔇₄` (`𝔔₃`)**: Birth of the Fisher metric `V` and Berry skewness `Σ` from the paired
   Gaussians: `(𝒢₊ - (1 + Φ)) + (𝒢₋ - (1 + Φ)) = V` and `𝒢₊ - 𝒢₋ = Σ`.
6. **Stage `𝔔₄` (Trace-First Blindness vs. Chiral Supertrace Visibility)**:
   For any cyclic trace `tr : B →+ K`, `tr (genSig P A C) = 0` and
   `chiralSupertrace tr P (genV P A C) = 0`, whereas
   `chiralSupertrace tr P (genSig P A C) = tr (genV P A C)`.
7. **Stage `𝔇₅` (`𝔔₅`)**: Amari conjugate `±α`-connection duality
   `∇^(α) + ∇^(-α) = Γ_sum` and the Fourfold Sum–Difference Crossover Law
   `[Γ_diff, Φ] = {Γ_sum, J}` and `[Γ_diff, J] = {Γ_sum, Φ}`.
8. **Stage `𝔇₆` (`𝔔₃`)**: Orthogonal Gramian annihilation `Q₊ * Q₋ = 0` and the Operator Pythagorean
   Theorem `V * V = Q₊² + Q₋² = Σ * Σ`.
9. **Stage `𝔇₇` (`𝔔₆`)**: Bergman kernel factorization `(1 - Q₊) * (1 - Q₋) = 1 - V`, Legendre–Peirce
   resolvent recovery `(1 ± V) * η_± = Φ`, and Operator Bregman divergence linear-term
   cancellation. -/
theorem amari_operator_dually_flat_gaussian_pythagorean_master_synthesis
    {K : Type*} [AddCommGroup K] (tr : B →+ K)
    (hCyclic : ∀ X Y : B, tr (X * Y) = tr (Y * X))
    {P : B} (hP : P * P = P) (A A₁ A₂ C C₁ C₂ W W_plus W_minus V : B) (α : ℝ) (N : ℕ)
    (hW_plus_r : (1 + genV P A C) * W_plus = 1)
    (hW_plus_l : W_plus * (1 + genV P A C) = 1)
    (hW_minus_r : (1 - genV P A C) * W_minus = 1)
    (hW_minus_l : W_minus * (1 - genV P A C) = 1) :
    (∀ st : AmariOperatorGeometryStage,
      ¬ Relation.TransGen AmariOperatorGeometryStage.causalEdge st st) ∧
    Fintype.card AmariOperatorGeometryStage = 7 ∧
    (∀ qst : FirstQuantizedAmariStage,
      ¬ Relation.TransGen FirstQuantizedAmariStage.causalEdge qst qst) ∧
    Fintype.card FirstQuantizedAmariStage = 6 ∧
    (1 + genPhi P A C) * (1 - genPhi P A C) = 1 - genV P A C ∧
    unipotentExpPlus P A₁ * unipotentExpPlus P A₂ = unipotentExpPlus P (A₁ + A₂) ∧
    unipotentExpMinus P C₁ * unipotentExpMinus P C₂ = unipotentExpMinus P (C₁ + C₂) ∧
    operatorGaussianPlus P A C = 1 + genPhi P A C + qgtPlus P A C ∧
    operatorGaussianMinus P A C = 1 + genPhi P A C + qgtMinus P A C ∧
    operatorGaussianPlus P A C * operatorGaussianPlusInv P A C = 1 ∧
    operatorGaussianMinus P A C * operatorGaussianMinusInv P A C = 1 ∧
    (operatorGaussianPlus P A C - (1 + genPhi P A C)) +
        (operatorGaussianMinus P A C - (1 + genPhi P A C)) = genV P A C ∧
    operatorGaussianPlus P A C - operatorGaussianMinus P A C = genSig P A C ∧
    tr (genSig P A C) = 0 ∧
    chiralSupertrace tr P (genV P A C) = 0 ∧
    chiralSupertrace tr P (genSig P A C) = tr (genV P A C) ∧
    amariAlphaConnection α P W + amariAlphaConnection (-α) P W =
      sheetConnectionSum P W ∧
    comm (sheetConnectionDiff P W) (genPhi P A C) =
      anticomm (sheetConnectionSum P W) (genJ P A C) ∧
    comm (sheetConnectionDiff P W) (genJ P A C) =
      anticomm (sheetConnectionSum P W) (genPhi P A C) ∧
    qgtPlus P A C * qgtMinus P A C = 0 ∧
    genV P A C * genV P A C =
      qgtPlus P A C * qgtPlus P A C + qgtMinus P A C * qgtMinus P A C ∧
    genV P A C * genV P A C = genSig P A C * genSig P A C ∧
    (1 - qgtPlus P A C) * (1 - qgtMinus P A C) = 1 - genV P A C ∧
    (1 + genV P A C) * legendreDualExpectationPlus W_plus P A C = genPhi P A C ∧
    (1 - genV P A C) * legendreDualExpectationMinus W_minus P A C = genPhi P A C ∧
    geometricSeriesPartialSum N V - paraKahlerPotentialPartialSum N V =
      bregmanDivergenceMinusPartialSum N V := by
  have hR0 := socratic_aporia_self_dual_exponential_curvature hP A C A₁ C₁ A₂ C₂
  have hD2 := d2_exact_abelian_exponential_families hP A A₁ A₂ C C₁ C₂ 0
  have hD3 := d3_paired_operator_gaussians_and_polynomial_inversion hP A C
  have hD4 := d4_birth_of_fisher_metric_and_berry_skewness_from_gaussians hP A C
  have hQ4 := q4_theorem_trace_first_blindness_and_chiral_supertrace_recovery tr hCyclic hP A C
  have hD5 := d5_amari_dual_connections_midpoint_skewness_and_crossover hP A C W W
  have hAlpha := amariAlphaConnection_conjugate_duality α P W
  have hD6 := d6_operator_pythagorean_theorem_and_orthogonal_gramians hP A C
  have hD7 := d7_legendre_resolvent_bregman_divergence_and_bkm_closure
    hP A C W_plus W_minus V N (fun _ => 0)
    hW_plus_r hW_plus_l hW_minus_r hW_minus_l (fun _ _ => le_rfl)
  exact ⟨AmariOperatorGeometryStage.causalEdge_acyclic,
    AmariOperatorGeometryStage.strict_seven_stage_chain.2.2.2.2.2.2,
    FirstQuantizedAmariStage.causalEdge_acyclic,
    FirstQuantizedAmariStage.strict_six_stage_chain.2.2.2.2.2,
    hR0.2.2.1,
    hD2.1,
    hD2.2.1,
    hD3.1,
    hD3.2.1,
    hD3.2.2.2.2.1,
    hD3.2.2.2.2.2.2.1,
    hD4.2.2.1,
    hD4.2.2.2.2.2.1,
    hQ4.2.2.2.1,
    hQ4.2.2.2.2.2.2.2.2.2.2.1,
    hQ4.2.2.2.2.2.2.2.2.2.2.2.1,
    hAlpha.2.2.2.1,
    hD5.2.2.2.2.2.2.1,
    hD5.2.2.2.2.2.2.2.2.1,
    hD6.1,
    hD6.2.2.2.2.2.2.1,
    hD6.2.2.2.2.2.2.2.2.1,
    hD7.2.1,
    hD7.2.2.1,
    hD7.2.2.2.2.1,
    hD7.2.2.2.2.2.2.1⟩

end AlphaConnectionsAndLegendreBregman

end InfoGeometry.Canonical.AmariOperatorDuallyFlatGaussianPythagoreanPoset
