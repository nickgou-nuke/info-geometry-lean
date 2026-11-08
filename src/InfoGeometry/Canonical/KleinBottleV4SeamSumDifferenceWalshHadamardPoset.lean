/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.OntologyRing
import InfoGeometry.Meta.Architecture
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.PeirceSpine.Homogenized
import InfoGeometry.OperatorAlgebra.PeirceSpine.Orientation
import InfoGeometry.Canonical.CausalHyperplaneBerryHolonomy
import InfoGeometry.Canonical.SupergradedMoebiusTetraktysKleinQuotientBerezinianWeylPoset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
===============================================================================
HIVE CONSTITUTIONAL HEADER
===============================================================================
Module: InfoGeometry.Canonical.KleinBottleV4SeamSumDifferenceWalshHadamardPoset
Role: Canonical formalization of:
  1. The 7-Stage Berry Wilson Loop & Hyperplane Causal Transmutation Poset
     (`𝔚₁ ≺ 𝔚₂ ≺ ⋯ ≺ 𝔚₇`):
     - `𝔚₁`: Opposite causal squares (`J² = -V`, `Φ² = +V`), `{J, Φ} = 0`, and
       hyperplane Pythagorean difference of squares `(c • J + s • Φ)² = (s² - c²) • V`,
     - `𝔚₂`: Berry curvature `Σ = [N₊, N₋] = J Φ = -Φ J` as hyperplane bivector
       with `{Σ, J} = {Σ, Φ} = 0`,
     - `𝔚₃`: Direct bivector transmutation `Σ * J = V * Φ` (`(Σ * J)² = +V³`) and
       `Σ * Φ = V * J` (`(Σ * Φ)² = -V³`),
     - `𝔚₄`: Infinitesimal holonomy `[Σ, J] = 2 • (V * Φ)` and quadratic flux
       horizon `(J + t • (V * Φ))² = V * (t² • V² - 1)`,
     - `𝔚₅`: Universal polynomial Wilson loop `W(c, s) = c • V + s • Σ` with
       `(W(c, s) * J)² = (s² - c²) • V³`,
     - `𝔚₆`: Critical Berry flux light-cone nilpotent horizon `s = ±c` where
       `W(1, 1) * J = 2 • (V * N₊)`, `W(1, -1) * J = -2 • (V * N₋)`, and
       `(W(1, ±1) * J)² = 0`,
     - `𝔚₇`: Trigonometric Berry rotor `R(θ) = cos θ • 1 + sin θ • S_P`, Rung 0
       anticommuting rotor angle inversion `J * R(θ) = R(-θ) * J`, continuous
       Wick transmutation `J(θ)² = (-cos(2θ)) • V`, and the three causal phases
       (`θ = 0` Timelike `-V`, `θ = π/4` Lightlike `0`, `θ = π/2` Spacelike `+V`).
  2. The 7-Stage Two-Sheeted Peirce–DeWitt Split, Sum–Difference Parallel
     Transport Crossover & `V₄ = ℤ₂ × ℤ₂` Klein Bottle Seam Poset
     (`𝔅₁ ≺ 𝔅₂ ≺ ⋯ ≺ 𝔅₇`):
     - `𝔅₁, 𝔅₂`: Bimodule footing (`N₊ ∇₊ = 0`, `∇₋ N₊ = 0`), Sum connection
       `Γ_sum = ∇₊ + ∇₋`, Difference connection `Γ_diff = ∇₊ - ∇₋ = S_P Γ_sum`,
       and DeWitt quadratic split `Γ_sum² = Γ_diff² = ∇₊² + ∇₋²`,
     - `𝔅₃`: Universal Sum–Difference Parallel Transport Crossover
       `[Γ_diff, Φ] = {Γ_sum, J}`, `{Γ_diff, Φ} = [Γ_sum, J}`,
       `[Γ_diff, J] = {Γ_sum, Φ}`, `{Γ_diff, J} = [Γ_sum, Φ]`,
     - `𝔅₄`: Endogenous Gramian connections (`Γ_sum = V`, `Γ_diff = Σ`), spin
       frame dragging `[Σ, Φ] = {V, J} = 2 • (V * J)`, and Rung 3 combined
       commutator `[V + Φ, Σ + J] = -(2 : ℤ) • Σ - (2 : ℤ) • (V * J)`,
     - `𝔅₅`: `V₄ = ℤ₂ × ℤ₂` Klein Bottle Seam superoperators `α(X) = S_P X S_P`,
       `β(X) = U X U`, `γ(X) = (S_P U) X (U S_P)` with `α ∘ β = β ∘ α = γ` and
       endogenous realization `U = Φ` at unit horizon `V = 1`,
     - `𝔅₆`: Exact Fourfold `V₄` Character Eigen-Classification (`χ₊₊, χ₊₋, χ₋₊, χ₋₋`),
     - `𝔅₇`: `4 × 4` Walsh–Hadamard Projector Resolution (`Π_{++}, Π_{+-}, Π_{-+}, Π_{--}`)
       and exact isolation of `(V, Σ, Φ, J)`.
===============================================================================
-/

noncomputable section

namespace InfoGeometry.Canonical.KleinBottleV4SeamSumDifferenceWalshHadamardPoset

open scoped Matrix
open InfoGeometry.OperatorAlgebra.OntologyRing
open InfoGeometry.Meta
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.CausalHyperplaneBerryHolonomy
open InfoGeometry.Canonical.SupergradedMoebiusTetraktysKleinQuotientBerezinianWeylPoset

/-! ===========================================================================
    Section 1: The Two 7-Stage Posets (`𝔚₁ ≺ ⋯ ≺ 𝔚₇` and `𝔅₁ ≺ ⋯ ≺ 𝔅₇`)
    =========================================================================== -/

/-- The 7 causal stages of the Berry Wilson Loop & Hyperplane Causal
Transmutation Poset (`𝔚₁ ≺ 𝔚₂ ≺ ⋯ ≺ 𝔚₇`). -/
inductive BerryWilsonLoopCausalStage : Type
  | W1_CausalHyperplaneAndOrthogonalOppositeSquares
  | W2_BerryCurvatureHyperplaneBivectorGenerator
  | W3_DirectBerryBivectorSignatureTransmutation
  | W4_InfinitesimalHolonomyCommutatorAndFluxHorizon
  | W5_UniversalPolynomialWilsonLoopHolonomy
  | W6_LightConeNilpotentHorizonAtCriticalFlux
  | W7_TrigonometricBerryRotorAndExactWickTransmutation
  deriving DecidableEq, Repr, Inhabited

namespace BerryWilsonLoopCausalStage

/-- Integer rank `0..6` of the 7 Berry Wilson loop causal transmutation stages. -/
def stageIndex : BerryWilsonLoopCausalStage → ℕ
  | .W1_CausalHyperplaneAndOrthogonalOppositeSquares => 0
  | .W2_BerryCurvatureHyperplaneBivectorGenerator => 1
  | .W3_DirectBerryBivectorSignatureTransmutation => 2
  | .W4_InfinitesimalHolonomyCommutatorAndFluxHorizon => 3
  | .W5_UniversalPolynomialWilsonLoopHolonomy => 4
  | .W6_LightConeNilpotentHorizonAtCriticalFlux => 5
  | .W7_TrigonometricBerryRotorAndExactWickTransmutation => 6

-- theorem-class: transport lemma
theorem stageIndex_injective : Function.Injective stageIndex := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance instLinearOrder : LinearOrder BerryWilsonLoopCausalStage :=
  LinearOrder.lift' stageIndex stageIndex_injective

instance instFintype : Fintype BerryWilsonLoopCausalStage where
  elems := {
    .W1_CausalHyperplaneAndOrthogonalOppositeSquares,
    .W2_BerryCurvatureHyperplaneBivectorGenerator,
    .W3_DirectBerryBivectorSignatureTransmutation,
    .W4_InfinitesimalHolonomyCommutatorAndFluxHorizon,
    .W5_UniversalPolynomialWilsonLoopHolonomy,
    .W6_LightConeNilpotentHorizonAtCriticalFlux,
    .W7_TrigonometricBerryRotorAndExactWickTransmutation
  }
  complete x := by cases x <;> simp

/-- Directed causal edges `𝔚₁ → 𝔚₂ → (𝔚₃, 𝔚₄) → 𝔚₅ → 𝔚₆ → 𝔚₇`. -/
def causalEdge : BerryWilsonLoopCausalStage → BerryWilsonLoopCausalStage → Prop
  | .W1_CausalHyperplaneAndOrthogonalOppositeSquares,
    .W2_BerryCurvatureHyperplaneBivectorGenerator => True
  | .W2_BerryCurvatureHyperplaneBivectorGenerator,
    .W3_DirectBerryBivectorSignatureTransmutation => True
  | .W2_BerryCurvatureHyperplaneBivectorGenerator,
    .W4_InfinitesimalHolonomyCommutatorAndFluxHorizon => True
  | .W3_DirectBerryBivectorSignatureTransmutation,
    .W5_UniversalPolynomialWilsonLoopHolonomy => True
  | .W4_InfinitesimalHolonomyCommutatorAndFluxHorizon,
    .W5_UniversalPolynomialWilsonLoopHolonomy => True
  | .W5_UniversalPolynomialWilsonLoopHolonomy,
    .W6_LightConeNilpotentHorizonAtCriticalFlux => True
  | .W6_LightConeNilpotentHorizonAtCriticalFlux,
    .W7_TrigonometricBerryRotorAndExactWickTransmutation => True
  | _, _ => False

instance instDecidableRelCausalEdge : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

-- theorem-class: transport lemma
theorem causalEdge_lt {s t : BerryWilsonLoopCausalStage} (h : causalEdge s t) : s < t := by
  change stageIndex s < stageIndex t
  cases s <;> cases t <;> revert h <;> decide

-- theorem-class: transport lemma
theorem transGen_causalEdge_lt {s t : BerryWilsonLoopCausalStage}
    (h : Relation.TransGen causalEdge s t) : s < t := by
  induction h with
  | single h1 => exact causalEdge_lt h1
  | tail _ h2 ih => exact lt_trans ih (causalEdge_lt h2)

-- theorem-class: transport lemma
theorem causalEdge_acyclic (s : BerryWilsonLoopCausalStage) :
    ¬ Relation.TransGen causalEdge s s := by
  intro h
  exact lt_irrefl s (transGen_causalEdge_lt h)

/-- Representation-depth projection `toRepDepth : BerryWilsonLoopCausalStage → RepDepth`. -/
def toRepDepth : BerryWilsonLoopCausalStage → RepDepth
  | .W1_CausalHyperplaneAndOrthogonalOppositeSquares => .projective
  | .W2_BerryCurvatureHyperplaneBivectorGenerator => .operator
  | .W3_DirectBerryBivectorSignatureTransmutation => .operator
  | .W4_InfinitesimalHolonomyCommutatorAndFluxHorizon => .krein
  | .W5_UniversalPolynomialWilsonLoopHolonomy => .transport
  | .W6_LightConeNilpotentHorizonAtCriticalFlux => .transport
  | .W7_TrigonometricBerryRotorAndExactWickTransmutation => .thermo

-- theorem-class: transport lemma
theorem toRepDepth_rank_monotone {a b : BerryWilsonLoopCausalStage} (h : a ≤ b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  change stageIndex a ≤ stageIndex b at h
  cases a <;> cases b <;> revert h <;> decide

/-- Meta-level projection `toOntologyMetaLevel : BerryWilsonLoopCausalStage → OntologyMetaLevel`. -/
def toOntologyMetaLevel : BerryWilsonLoopCausalStage → OntologyMetaLevel
  | .W1_CausalHyperplaneAndOrthogonalOppositeSquares => .M1_ProjectorClabject
  | .W2_BerryCurvatureHyperplaneBivectorGenerator => .M1_ProjectorClabject
  | .W3_DirectBerryBivectorSignatureTransmutation => .M2_GrassmannianPowertypeOrbit
  | .W4_InfinitesimalHolonomyCommutatorAndFluxHorizon => .M2_GrassmannianPowertypeOrbit
  | .W5_UniversalPolynomialWilsonLoopHolonomy => .M2_GrassmannianPowertypeOrbit
  | .W6_LightConeNilpotentHorizonAtCriticalFlux => .M3_ErlangenCasimirMetaLaw
  | .W7_TrigonometricBerryRotorAndExactWickTransmutation => .M3_ErlangenCasimirMetaLaw

-- theorem-class: transport lemma
theorem toOntologyMetaLevel_rank_monotone {a b : BerryWilsonLoopCausalStage} (h : a ≤ b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  change stageIndex a ≤ stageIndex b at h
  cases a <;> cases b <;> revert h <;> decide

end BerryWilsonLoopCausalStage

/-- The 7 causal stages of the Two-Sheeted Peirce–DeWitt Split, Sum–Difference
Parallel Transport Crossover, `V₄ = ℤ₂ × ℤ₂` Klein Bottle Seam Closure,
Fourfold Character Eigen-Classification, and Walsh–Hadamard Resolution
(`𝔅₁ ≺ 𝔅₂ ≺ ⋯ ≺ 𝔅₇`). -/
inductive KleinBottleSeamConnectionStage : Type
  | B1_PeirceDeWittTwoSheetSplitAndBimoduleThroat
  | B2_SumAndDifferenceSheetConnections
  | B3_UniversalSumDifferenceTransportCrossover
  | B4_EndogenousGramianConnectionsAndSpinDragging
  | B5_KleinFourSeamClosureAndAdjointCommutativity
  | B6_FourfoldV4CharacterEigenClassification
  | B7_WalshHadamardProjectorResolutionAndMonodromy
  deriving DecidableEq, Repr, Inhabited

namespace KleinBottleSeamConnectionStage

/-- Integer rank `0..6` of the 7 Klein bottle seam & sum–difference stages. -/
def stageIndex : KleinBottleSeamConnectionStage → ℕ
  | .B1_PeirceDeWittTwoSheetSplitAndBimoduleThroat => 0
  | .B2_SumAndDifferenceSheetConnections => 1
  | .B3_UniversalSumDifferenceTransportCrossover => 2
  | .B4_EndogenousGramianConnectionsAndSpinDragging => 3
  | .B5_KleinFourSeamClosureAndAdjointCommutativity => 4
  | .B6_FourfoldV4CharacterEigenClassification => 5
  | .B7_WalshHadamardProjectorResolutionAndMonodromy => 6

-- theorem-class: transport lemma
theorem stageIndex_injective : Function.Injective stageIndex := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance instLinearOrder : LinearOrder KleinBottleSeamConnectionStage :=
  LinearOrder.lift' stageIndex stageIndex_injective

instance instFintype : Fintype KleinBottleSeamConnectionStage where
  elems := {
    .B1_PeirceDeWittTwoSheetSplitAndBimoduleThroat,
    .B2_SumAndDifferenceSheetConnections,
    .B3_UniversalSumDifferenceTransportCrossover,
    .B4_EndogenousGramianConnectionsAndSpinDragging,
    .B5_KleinFourSeamClosureAndAdjointCommutativity,
    .B6_FourfoldV4CharacterEigenClassification,
    .B7_WalshHadamardProjectorResolutionAndMonodromy
  }
  complete x := by cases x <;> simp

/-- Directed cover edges `𝔅₁ → 𝔅₂ → 𝔅₃ → 𝔅₄ → 𝔅₅ → 𝔅₆ → 𝔅₇`. -/
def causalEdge : KleinBottleSeamConnectionStage → KleinBottleSeamConnectionStage → Prop
  | .B1_PeirceDeWittTwoSheetSplitAndBimoduleThroat,
    .B2_SumAndDifferenceSheetConnections => True
  | .B2_SumAndDifferenceSheetConnections,
    .B3_UniversalSumDifferenceTransportCrossover => True
  | .B3_UniversalSumDifferenceTransportCrossover,
    .B4_EndogenousGramianConnectionsAndSpinDragging => True
  | .B4_EndogenousGramianConnectionsAndSpinDragging,
    .B5_KleinFourSeamClosureAndAdjointCommutativity => True
  | .B5_KleinFourSeamClosureAndAdjointCommutativity,
    .B6_FourfoldV4CharacterEigenClassification => True
  | .B6_FourfoldV4CharacterEigenClassification,
    .B7_WalshHadamardProjectorResolutionAndMonodromy => True
  | _, _ => False

instance instDecidableRelCausalEdge : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

-- theorem-class: transport lemma
theorem causalEdge_lt {s t : KleinBottleSeamConnectionStage} (h : causalEdge s t) : s < t := by
  change stageIndex s < stageIndex t
  cases s <;> cases t <;> revert h <;> decide

-- theorem-class: transport lemma
theorem transGen_causalEdge_lt {s t : KleinBottleSeamConnectionStage}
    (h : Relation.TransGen causalEdge s t) : s < t := by
  induction h with
  | single h1 => exact causalEdge_lt h1
  | tail _ h2 ih => exact lt_trans ih (causalEdge_lt h2)

-- theorem-class: transport lemma
theorem causalEdge_acyclic (s : KleinBottleSeamConnectionStage) :
    ¬ Relation.TransGen causalEdge s s := by
  intro h
  exact lt_irrefl s (transGen_causalEdge_lt h)

/-- Representation-depth projection `toRepDepth : KleinBottleSeamConnectionStage → RepDepth`. -/
def toRepDepth : KleinBottleSeamConnectionStage → RepDepth
  | .B1_PeirceDeWittTwoSheetSplitAndBimoduleThroat => .projective
  | .B2_SumAndDifferenceSheetConnections => .operator
  | .B3_UniversalSumDifferenceTransportCrossover => .operator
  | .B4_EndogenousGramianConnectionsAndSpinDragging => .krein
  | .B5_KleinFourSeamClosureAndAdjointCommutativity => .transport
  | .B6_FourfoldV4CharacterEigenClassification => .transport
  | .B7_WalshHadamardProjectorResolutionAndMonodromy => .thermo

-- theorem-class: transport lemma
theorem toRepDepth_rank_monotone {a b : KleinBottleSeamConnectionStage} (h : a ≤ b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  change stageIndex a ≤ stageIndex b at h
  cases a <;> cases b <;> revert h <;> decide

/-- Meta-level projection `toOntologyMetaLevel : KleinBottleSeamConnectionStage → OntologyMetaLevel`. -/
def toOntologyMetaLevel : KleinBottleSeamConnectionStage → OntologyMetaLevel
  | .B1_PeirceDeWittTwoSheetSplitAndBimoduleThroat => .M1_ProjectorClabject
  | .B2_SumAndDifferenceSheetConnections => .M1_ProjectorClabject
  | .B3_UniversalSumDifferenceTransportCrossover => .M2_GrassmannianPowertypeOrbit
  | .B4_EndogenousGramianConnectionsAndSpinDragging => .M2_GrassmannianPowertypeOrbit
  | .B5_KleinFourSeamClosureAndAdjointCommutativity => .M2_GrassmannianPowertypeOrbit
  | .B6_FourfoldV4CharacterEigenClassification => .M3_ErlangenCasimirMetaLaw
  | .B7_WalshHadamardProjectorResolutionAndMonodromy => .M3_ErlangenCasimirMetaLaw

-- theorem-class: transport lemma
theorem toOntologyMetaLevel_rank_monotone {a b : KleinBottleSeamConnectionStage} (h : a ≤ b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  change stageIndex a ≤ stageIndex b at h
  cases a <;> cases b <;> revert h <;> decide

end KleinBottleSeamConnectionStage

/-! ===========================================================================
    Section 2: Part I (`𝔚₁ ≺ 𝔚₂ ≺ ⋯ ≺ 𝔚₇`) — The Causal `(J, Φ)` Hyperplane,
    Berry Curvature Bivector `Σ = J Φ`, Polynomial Wilson Loop `W(c, s)`,
    and Trigonometric Berry Rotor Wick Transmutation
    =========================================================================== -/

section BerryWilsonLoopHyperplaneTransmutation

variable {R : Type*} [CommRing R]
variable {B : Type*} [Ring B] [Algebra R B]

/-- The even polynomial Wilson loop holonomy operator
`wilsonLoopEven P A C c s := c • genV P A C + s • genSig P A C`. -/
def wilsonLoopEven (P A C : B) (c s : R) : B :=
  c • genV P A C + s • genSig P A C

/-- The infinitesimally parallel-transported timelike current
`infinitesimalHolonomyJ P A C t := genJ P A C + t • (genV P A C * genPhi P A C)`. -/
def infinitesimalHolonomyJ (P A C : B) (t : R) : B :=
  genJ P A C + t • (genV P A C * genPhi P A C)

-- theorem-class: constructive endpoint
/-- **Stages `𝔚₁–𝔚₃` Theorem (`stage_W1_W2_W3_hyperplane_pythagorean_and_bivector_transmutation`)**:
In any `R`-algebra `[Ring B] [Algebra R B]` with idempotent `P * P = P`:
1. **Stage `𝔚₁` (Opposite Causal Squares & Hyperplane Pythagorean Cancellation)**:
   * `J² = -V`, `Φ² = +V`, `J² + Φ² = 0`, `{J, Φ} = 0`,
   * `Φ + J = 2 • N₊` and `Φ - J = 2 • N₋`,
   * `(c • J + s • Φ)² = (s² - c²) • V` and `(c • Φ + s • J)² = (c² - s²) • V`.
2. **Stage `𝔚₂` (Berry Curvature as Hyperplane Bivector Generator)**:
   * `Σ = J * Φ = -(Φ * J)`, `{Σ, J} = 0`, `{Σ, Φ} = 0`.
3. **Stage `𝔚₃` (Direct Bivector Signature Transmutation)**:
   * `Σ * J = V * Φ` and `Σ * Φ = V * J`,
   * `(Σ * J)² = +V³` (spacelike!) and `(Σ * Φ)² = -V³` (timelike!). -/
theorem stage_W1_W2_W3_hyperplane_pythagorean_and_bivector_transmutation
    {P : B} (hP : P * P = P) (A C : B) (c s : R) :
    let J := genJ P A C
    let Φ := genPhi P A C
    let V := genV P A C
    let Sig := genSig P A C
    (J * J = -V ∧
      Φ * Φ = V ∧
      J * J + Φ * Φ = 0 ∧
      anticomm J Φ = 0 ∧
      Φ + J = (2 : ℤ) • conePlus P A ∧
      Φ - J = (2 : ℤ) • coneMinus P C ∧
      (c • J + s • Φ) * (c • J + s • Φ) = (s ^ 2 - c ^ 2) • V ∧
      (c • Φ + s • J) * (c • Φ + s • J) = (c ^ 2 - s ^ 2) • V) ∧
    (J * Φ = Sig ∧
      Φ * J = -Sig ∧
      anticomm Sig J = 0 ∧
      anticomm Sig Φ = 0) ∧
    (Sig * J = V * Φ ∧
      Sig * Φ = V * J ∧
      (Sig * J) * (Sig * J) = V * V * V ∧
      (Sig * Φ) * (Sig * Φ) = -(V * V * V)) := by
  intro J Φ V Sig
  have hJ2 : J * J = -V := by dsimp [J, V]; peirce_nf hP
  have hPhi2 : Φ * Φ = V := by dsimp [Φ, V]; peirce_nf hP
  have hAntiJPhi : J * Φ + Φ * J = 0 := by dsimp [J, Φ]; peirce_nf hP
  have hAntiPhiJ : Φ * J + J * Φ = 0 := by dsimp [J, Φ]; peirce_nf hP
  have hPythJ : (c • J + s • Φ) * (c • J + s • Φ) = (s ^ 2 - c ^ 2) • V := by
    calc
      (c • J + s • Φ) * (c • J + s • Φ)
        = (c * c) • (J * J) + (c * s) • (J * Φ + Φ * J) + (s * s) • (Φ * Φ) := by
          simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
            smul_add, smul_smul, mul_comm s c]
          abel
      _ = (c * c) • (-V) + (c * s) • (0 : B) + (s * s) • V := by
          rw [hJ2, hAntiJPhi, hPhi2]
      _ = (s ^ 2 - c ^ 2) • V := by
          rw [smul_neg, smul_zero, add_zero, sub_smul, sq, sq]
          abel
  have hPythPhi : (c • Φ + s • J) * (c • Φ + s • J) = (c ^ 2 - s ^ 2) • V := by
    calc
      (c • Φ + s • J) * (c • Φ + s • J)
        = (c * c) • (Φ * Φ) + (c * s) • (Φ * J + J * Φ) + (s * s) • (J * J) := by
          simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
            smul_add, smul_smul, mul_comm s c]
          abel
      _ = (c * c) • V + (c * s) • (0 : B) + (s * s) • (-V) := by
          rw [hPhi2, hAntiPhiJ, hJ2]
      _ = (c ^ 2 - s ^ 2) • V := by
          rw [smul_neg, smul_zero, add_zero, sub_smul, sq, sq]
          abel
  refine ⟨⟨hJ2, hPhi2, by dsimp [J, Φ]; peirce_nf hP,
           by dsimp [J, Φ]; peirce_nf hP,
           by dsimp [J, Φ]; peirce_nf hP,
           by dsimp [J, Φ]; peirce_nf hP,
           hPythJ, hPythPhi⟩,
    ⟨by dsimp [J, Φ, Sig]; peirce_nf hP,
     by dsimp [J, Φ, Sig]; peirce_nf hP,
     by dsimp [J, Sig]; peirce_nf hP,
     by dsimp [Φ, Sig]; peirce_nf hP⟩,
    ⟨by dsimp [J, Φ, V, Sig]; peirce_nf hP,
     by dsimp [J, Φ, V, Sig]; peirce_nf hP,
     by dsimp [J, V, Sig]; peirce_nf hP,
     by dsimp [Φ, V, Sig]; peirce_nf hP⟩⟩

-- theorem-class: constructive endpoint
/-- **Stages `𝔚₄–𝔚₆` Theorem (`stage_W4_W5_W6_infinitesimal_and_polynomial_wilson_loop_light_cone`)**:
In any `R`-algebra `[Ring B] [Algebra R B]` with idempotent `P * P = P`:
1. **Stage `𝔚₄` (Infinitesimal Berry Holonomy & Flux Horizon)**:
   * `[Σ, J] = 2 • (V * Φ)` and `[Σ, Φ] = 2 • (V * J)`,
   * `infinitesimalHolonomyJ P A C t * infinitesimalHolonomyJ P A C t = V * ((t ^ 2) • (V * V) - 1)`.
2. **Stage `𝔚₅` (Universal Polynomial Wilson Loop Holonomy `W(c, s) = c • V + s • Σ`)**:
   * `wilsonLoopEven P A C c s * J = V * (c • J + s • Φ)`,
   * `wilsonLoopEven P A C c s * Φ = V * (c • Φ + s • J)`,
   * `(wilsonLoopEven P A C c s * J)² = (s² - c²) • (V * V * V)`,
   * `(wilsonLoopEven P A C c s * Φ)² = (c² - s²) • (V * V * V)`.
3. **Stage `𝔚₆` (Light-Cone Nilpotent Horizon at Critical Berry Flux `s = ±c`)**:
   * `wilsonLoopEven P A C (1 : R) (1 : R) * J = (2 : ℤ) • (V * conePlus P A)` and its square is `0`,
   * `wilsonLoopEven P A C (1 : R) (-1 : R) * J = -((2 : ℤ) • (V * coneMinus P C))` and its square is `0`. -/
theorem stage_W4_W5_W6_infinitesimal_and_polynomial_wilson_loop_light_cone
    {P : B} (hP : P * P = P) (A C : B) (c s t : R) :
    let J := genJ P A C
    let Φ := genPhi P A C
    let V := genV P A C
    let Sig := genSig P A C
    (comm Sig J = (2 : ℤ) • (V * Φ) ∧
      comm Sig Φ = (2 : ℤ) • (V * J) ∧
      infinitesimalHolonomyJ P A C t * infinitesimalHolonomyJ P A C t =
        V * ((t ^ 2) • (V * V) - 1)) ∧
    (wilsonLoopEven P A C c s * J = V * (c • J + s • Φ) ∧
      wilsonLoopEven P A C c s * Φ = V * (c • Φ + s • J) ∧
      (wilsonLoopEven P A C c s * J) * (wilsonLoopEven P A C c s * J) =
        (s ^ 2 - c ^ 2) • (V * V * V) ∧
      (wilsonLoopEven P A C c s * Φ) * (wilsonLoopEven P A C c s * Φ) =
        (c ^ 2 - s ^ 2) • (V * V * V)) ∧
    (wilsonLoopEven P A C (1 : R) (1 : R) * J = (2 : ℤ) • (V * conePlus P A) ∧
      (wilsonLoopEven P A C (1 : R) (1 : R) * J) *
        (wilsonLoopEven P A C (1 : R) (1 : R) * J) = 0 ∧
      wilsonLoopEven P A C (1 : R) (-1 : R) * J = -((2 : ℤ) • (V * coneMinus P C)) ∧
      (wilsonLoopEven P A C (1 : R) (-1 : R) * J) *
        (wilsonLoopEven P A C (1 : R) (-1 : R) * J) = 0) := by
  intro J Φ V Sig
  have hSigJ : Sig * J = V * Φ := by dsimp [J, Φ, V, Sig]; peirce_nf hP
  have hSigPhi : Sig * Φ = V * J := by dsimp [J, Φ, V, Sig]; peirce_nf hP
  have hJ2 : J * J = -V := by dsimp [J, V]; peirce_nf hP
  have hJVPhi : J * (V * Φ) + (V * Φ) * J = 0 := by dsimp [J, Φ, V]; peirce_nf hP
  have hVPhi2 : (V * Φ) * (V * Φ) = V * V * V := by dsimp [Φ, V]; peirce_nf hP
  have hVJ2 : (V * J) * (V * J) = -(V * V * V) := by dsimp [J, V]; peirce_nf hP
  have hVJPhiAnti : (V * J) * (V * Φ) + (V * Φ) * (V * J) = 0 := by
    dsimp [J, Φ, V]; peirce_nf hP
  have hVPhiJAnti : (V * Φ) * (V * J) + (V * J) * (V * Φ) = 0 := by
    dsimp [J, Φ, V]; peirce_nf hP
  have hInfSq :
      infinitesimalHolonomyJ P A C t * infinitesimalHolonomyJ P A C t =
        V * ((t ^ 2) • (V * V) - 1) := by
    dsimp [infinitesimalHolonomyJ]
    calc
      (J + t • (V * Φ)) * (J + t • (V * Φ))
        = J * J + t • (J * (V * Φ) + (V * Φ) * J) + (t * t) • ((V * Φ) * (V * Φ)) := by
          simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
          abel
      _ = -V + t • (0 : B) + (t * t) • (V * V * V) := by
          rw [hJ2, hJVPhi, hVPhi2]
      _ = V * ((t ^ 2) • (V * V) - 1) := by
          rw [smul_zero, add_zero, mul_sub, mul_smul_comm, mul_one, ← sq, ← mul_assoc]
          abel
  have hWJ : wilsonLoopEven P A C c s * J = V * (c • J + s • Φ) := by
    dsimp [wilsonLoopEven]
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, hSigJ, mul_add, mul_smul_comm, mul_smul_comm]
  have hWPhi : wilsonLoopEven P A C c s * Φ = V * (c • Φ + s • J) := by
    dsimp [wilsonLoopEven]
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, hSigPhi, mul_add, mul_smul_comm, mul_smul_comm]
  have hWJSq :
      (wilsonLoopEven P A C c s * J) * (wilsonLoopEven P A C c s * J) =
        (s ^ 2 - c ^ 2) • (V * V * V) := by
    have hExp : wilsonLoopEven P A C c s * J = c • (V * J) + s • (V * Φ) := by
      dsimp [wilsonLoopEven]; rw [add_mul, smul_mul_assoc, smul_mul_assoc, hSigJ]
    rw [hExp]
    calc
      (c • (V * J) + s • (V * Φ)) * (c • (V * J) + s • (V * Φ))
        = (c * c) • ((V * J) * (V * J)) +
          (c * s) • ((V * J) * (V * Φ) + (V * Φ) * (V * J)) +
          (s * s) • ((V * Φ) * (V * Φ)) := by
          simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
            smul_add, smul_smul, mul_comm s c]
          abel
      _ = (c * c) • (-(V * V * V)) + (c * s) • (0 : B) + (s * s) • (V * V * V) := by
          rw [hVJ2, hVJPhiAnti, hVPhi2]
      _ = (s ^ 2 - c ^ 2) • (V * V * V) := by
          rw [smul_neg, smul_zero, add_zero, sub_smul, sq, sq]
          abel
  have hWPhiSq :
      (wilsonLoopEven P A C c s * Φ) * (wilsonLoopEven P A C c s * Φ) =
        (c ^ 2 - s ^ 2) • (V * V * V) := by
    have hExp : wilsonLoopEven P A C c s * Φ = c • (V * Φ) + s • (V * J) := by
      dsimp [wilsonLoopEven]; rw [add_mul, smul_mul_assoc, smul_mul_assoc, hSigPhi]
    rw [hExp]
    calc
      (c • (V * Φ) + s • (V * J)) * (c • (V * Φ) + s • (V * J))
        = (c * c) • ((V * Φ) * (V * Φ)) +
          (c * s) • ((V * Φ) * (V * J) + (V * J) * (V * Φ)) +
          (s * s) • ((V * J) * (V * J)) := by
          simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
            smul_add, smul_smul, mul_comm s c]
          abel
      _ = (c * c) • (V * V * V) + (c * s) • (0 : B) + (s * s) • (-(V * V * V)) := by
          rw [hVPhi2, hVPhiJAnti, hVJ2]
      _ = (c ^ 2 - s ^ 2) • (V * V * V) := by
          rw [smul_neg, smul_zero, add_zero, sub_smul, sq, sq]
          abel
  have hW11 : wilsonLoopEven P A C (1 : R) (1 : R) = V + Sig := by
    dsimp [wilsonLoopEven, V, Sig]; simp
  have hW1m1 : wilsonLoopEven P A C (1 : R) (-1 : R) = V - Sig := by
    dsimp [wilsonLoopEven, V, Sig]; simp [sub_eq_add_neg]
  refine ⟨⟨by dsimp [J, Φ, V, Sig]; peirce_nf hP,
           by dsimp [J, Φ, V, Sig]; peirce_nf hP,
           hInfSq⟩,
    ⟨hWJ, hWPhi, hWJSq, hWPhiSq⟩,
    ⟨by rw [hW11]; dsimp [J, V, Sig]; peirce_nf hP,
     by rw [hW11]; dsimp [J, V, Sig]; peirce_nf hP,
     by rw [hW1m1]; dsimp [J, V, Sig]; peirce_nf hP,
     by rw [hW1m1]; dsimp [J, V, Sig]; peirce_nf hP⟩⟩

end BerryWilsonLoopHyperplaneTransmutation

section TrigonometricBerryRotor

variable {B : Type*} [Ring B] [Algebra ℝ B]

/-- The trigonometric Berry rotor `R(θ) = cos θ • 1 + sin θ • S_P` in an `ℝ`-algebra `B`. -/
def berryRotor (P : B) (θ : ℝ) : B :=
  Real.cos θ • (1 : B) + Real.sin θ • invS P

/-- The Berry-rotated current `J(θ) := R(θ) * J`. -/
def rotatedCurrentJ (P A C : B) (θ : ℝ) : B :=
  berryRotor P θ * genJ P A C

/-- The Berry-rotated solder bridge `Φ(θ) := R(θ) * Φ`. -/
def rotatedBridgePhi (P A C : B) (θ : ℝ) : B :=
  berryRotor P θ * genPhi P A C

-- theorem-class: constructive endpoint
/-- **Stage `𝔚₇` Theorem (`stage_W7_trigonometric_berry_rotor_and_wick_transmutation`)**:
In any `ℝ`-algebra `[Ring B] [Algebra ℝ B]` with idempotent `P * P = P`:
1. **Rung 0 Socratic Rotor Angle Inversion & Para-Complex Norm**:
   * `J * berryRotor P θ = berryRotor P (-θ) * J` and `Φ * berryRotor P θ = berryRotor P (-θ) * Φ`,
   * `berryRotor P θ * berryRotor P (-θ) = Real.cos (2 * θ) • (1 : B)`.
2. **Hyperplane Rotation & Continuous Causal Sign Inversion**:
   * `rotatedCurrentJ P A C θ = Real.cos θ • J + Real.sin θ • Φ`,
   * `rotatedCurrentJ P A C θ * rotatedCurrentJ P A C θ = (-Real.cos (2 * θ)) • V`,
   * `rotatedBridgePhi P A C θ * rotatedBridgePhi P A C θ = Real.cos (2 * θ) • V`.
3. **The Three Causal Phases**:
   * `θ = 0`: `rotatedCurrentJ P A C 0 = J` and `rotatedCurrentJ P A C 0 ^ 2 = -V` (Timelike),
   * `θ = π/4`: `rotatedCurrentJ P A C (Real.pi / 4) = Real.sqrt 2 • conePlus P A` and its square is `0` (Lightlike Nilpotent),
   * `θ = π/2`: `rotatedCurrentJ P A C (Real.pi / 2) = Φ` and its square is `+V` (Spacelike). -/
theorem stage_W7_trigonometric_berry_rotor_and_wick_transmutation
    {P : B} (hP : P * P = P) (A C : B) (θ : ℝ) :
    let J := genJ P A C
    let Φ := genPhi P A C
    let V := genV P A C
    (J * berryRotor P θ = berryRotor P (-θ) * J ∧
      Φ * berryRotor P θ = berryRotor P (-θ) * Φ ∧
      berryRotor P θ * berryRotor P (-θ) = Real.cos (2 * θ) • (1 : B)) ∧
    (rotatedCurrentJ P A C θ = Real.cos θ • J + Real.sin θ • Φ ∧
      rotatedCurrentJ P A C θ * rotatedCurrentJ P A C θ = (-Real.cos (2 * θ)) • V ∧
      rotatedBridgePhi P A C θ * rotatedBridgePhi P A C θ = Real.cos (2 * θ) • V) ∧
    (rotatedCurrentJ P A C 0 = J ∧
      rotatedCurrentJ P A C 0 * rotatedCurrentJ P A C 0 = -V ∧
      rotatedCurrentJ P A C (Real.pi / 4) = Real.sqrt 2 • conePlus P A ∧
      rotatedCurrentJ P A C (Real.pi / 4) * rotatedCurrentJ P A C (Real.pi / 4) = 0 ∧
      rotatedCurrentJ P A C (Real.pi / 2) = Φ ∧
      rotatedCurrentJ P A C (Real.pi / 2) * rotatedCurrentJ P A C (Real.pi / 2) = V) := by
  intro J Φ V
  have hJS : J * invS P = -(invS P * J) := by dsimp [J]; peirce_nf hP
  have hPhiS : Φ * invS P = -(invS P * Φ) := by dsimp [Φ]; peirce_nf hP
  have hS2 : invS P * invS P = 1 := by peirce_nf hP
  have hSJ : invS P * J = Φ := by dsimp [J, Φ]; peirce_nf hP
  have hSPhi : invS P * Φ = J := by dsimp [J, Φ]; peirce_nf hP
  have hInvJ : J * berryRotor P θ = berryRotor P (-θ) * J := by
    dsimp [berryRotor]
    rw [Real.cos_neg, Real.sin_neg, mul_add, add_mul,
        mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
        mul_one, one_mul, hJS, smul_neg, neg_smul]
  have hInvPhi : Φ * berryRotor P θ = berryRotor P (-θ) * Φ := by
    dsimp [berryRotor]
    rw [Real.cos_neg, Real.sin_neg, mul_add, add_mul,
        mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
        mul_one, one_mul, hPhiS, smul_neg, neg_smul]
  have hRotorNorm : berryRotor P θ * berryRotor P (-θ) = Real.cos (2 * θ) • (1 : B) := by
    dsimp [berryRotor]
    rw [Real.cos_neg, Real.sin_neg]
    calc
      (Real.cos θ • (1 : B) + Real.sin θ • invS P) *
          (Real.cos θ • (1 : B) + (-Real.sin θ) • invS P)
        = (Real.cos θ * Real.cos θ) • ((1 : B) * 1) +
          (Real.cos θ * (-Real.sin θ)) • ((1 : B) * invS P) +
          (Real.sin θ * Real.cos θ) • (invS P * 1) +
          (Real.sin θ * (-Real.sin θ)) • (invS P * invS P) := by
          simp only [add_mul, mul_add, smul_mul_smul_comm]
          abel
      _ = (Real.cos θ * Real.cos θ) • (1 : B) +
          ((Real.cos θ * (-Real.sin θ) + Real.sin θ * Real.cos θ) • invS P) +
          (Real.sin θ * (-Real.sin θ)) • (1 : B) := by
          rw [mul_one, one_mul, mul_one, hS2, add_smul]
          abel
      _ = (Real.cos θ ^ 2 - Real.sin θ ^ 2) • (1 : B) := by
          have hZero : Real.cos θ * (-Real.sin θ) + Real.sin θ * Real.cos θ = 0 := by ring
          have hDiff : Real.cos θ * Real.cos θ + Real.sin θ * (-Real.sin θ) =
              Real.cos θ ^ 2 - Real.sin θ ^ 2 := by ring
          rw [hZero, zero_smul, add_zero, ← add_smul, hDiff]
      _ = Real.cos (2 * θ) • (1 : B) := by
          rw [← Real.cos_two_mul']
  have hRotJGen : ∀ α : ℝ, rotatedCurrentJ P A C α = Real.cos α • J + Real.sin α • Φ := by
    intro α
    dsimp [rotatedCurrentJ, berryRotor]
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, hSJ]
  have hRotPhiGen : ∀ α : ℝ, rotatedBridgePhi P A C α = Real.cos α • Φ + Real.sin α • J := by
    intro α
    dsimp [rotatedBridgePhi, berryRotor]
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, hSPhi]
  have hW1 := (stage_W1_W2_W3_hyperplane_pythagorean_and_bivector_transmutation
    (R := ℝ) hP A C (Real.cos θ) (Real.sin θ)).1
  have hJSq : rotatedCurrentJ P A C θ * rotatedCurrentJ P A C θ = (-Real.cos (2 * θ)) • V := by
    rw [hRotJGen θ, hW1.2.2.2.2.2.2.1]
    have hTrig : Real.sin θ ^ 2 - Real.cos θ ^ 2 = -Real.cos (2 * θ) := by
      rw [Real.cos_two_mul']; ring
    rw [hTrig]
  have hPhiSq : rotatedBridgePhi P A C θ * rotatedBridgePhi P A C θ = Real.cos (2 * θ) • V := by
    rw [hRotPhiGen θ, hW1.2.2.2.2.2.2.2, ← Real.cos_two_mul']
  have hRotJ0 : rotatedCurrentJ P A C 0 = J := by
    rw [hRotJGen 0, Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero]
  have hJSq0 : rotatedCurrentJ P A C 0 * rotatedCurrentJ P A C 0 = -V := by
    rw [hRotJ0]; dsimp [J, V]; peirce_nf hP
  have hRotJPi4 : rotatedCurrentJ P A C (Real.pi / 4) = Real.sqrt 2 • conePlus P A := by
    have hSumCone : J + Φ = (2 : ℝ) • conePlus P A := by
      rw [two_smul]; dsimp [J, Φ]; peirce_nf hP
    rw [hRotJGen (Real.pi / 4), Real.cos_pi_div_four, Real.sin_pi_div_four,
        ← smul_add, hSumCone, smul_smul]
    have hHalfTwo : Real.sqrt 2 / 2 * 2 = Real.sqrt 2 := by ring
    rw [hHalfTwo]
  have hJSqPi4 : rotatedCurrentJ P A C (Real.pi / 4) * rotatedCurrentJ P A C (Real.pi / 4) = 0 := by
    rw [hRotJPi4, smul_mul_assoc, mul_smul_comm]
    have hNil : conePlus P A * conePlus P A = 0 := by peirce_nf hP
    rw [hNil, smul_zero, smul_zero]
  have hRotJPi2 : rotatedCurrentJ P A C (Real.pi / 2) = Φ := by
    rw [hRotJGen (Real.pi / 2), Real.cos_pi_div_two, Real.sin_pi_div_two,
        zero_smul, one_smul, zero_add]
  have hJSqPi2 : rotatedCurrentJ P A C (Real.pi / 2) * rotatedCurrentJ P A C (Real.pi / 2) = V := by
    rw [hRotJPi2]; dsimp [Φ, V]; peirce_nf hP
  exact ⟨⟨hInvJ, hInvPhi, hRotorNorm⟩,
    ⟨hRotJGen θ, hJSq, hPhiSq⟩,
    ⟨hRotJ0, hJSq0, hRotJPi4, hJSqPi4, hRotJPi2, hJSqPi2⟩⟩

end TrigonometricBerryRotor

/-! ===========================================================================
    Section 3: Stages `𝔅₁–𝔅₄` — Sum–Difference Crossover & The Rung 3
    Combined Connection-Throat Commutator `[Γ_sum + Φ, Γ_diff + J]`
    =========================================================================== -/

section SumDifferenceRung3Commutator

variable {B : Type*} [Ring B]

-- theorem-class: constructive endpoint
/-- **Stages `𝔅₁–𝔅₄` & Rung 3 Combined Connection–Throat Commutator Theorem
(`stage_B1_to_B4_sum_diff_crossover_and_combined_throat_commutator`)**:
In any noncommutative `[Ring B]` with idempotent `P * P = P`, let
`Γ_sum = sheetConnectionSum P W` and `Γ_diff = sheetConnectionDiff P W`:
1. **Chiral Duality & Quadratic DeWitt Split (`𝔅₁, 𝔅₂`)**:
   * `invS P * Γ_sum = Γ_diff = Γ_sum * invS P` and `invS P * Γ_diff = Γ_sum = Γ_diff * invS P`,
   * `Γ_sum * Γ_sum = Γ_diff * Γ_diff = ∇₊² + ∇₋²` and `Γ_sum * Γ_diff = ∇₊² - ∇₋² = invS P * (Γ_sum * Γ_sum)`.
2. **Universal Fourfold Sum–Difference Transport Crossover (`𝔅₃`)**:
   * `[Γ_diff, Φ] = {Γ_sum, J}`, `{Γ_diff, Φ} = [Γ_sum, J}`,
   * `[Γ_diff, J] = {Γ_sum, Φ}`, `{Γ_diff, J} = [Γ_sum, Φ]`.
3. **Rung 3 Combined Connection–Throat Commutator (`[Γ_sum + Φ, Γ_diff + J]`)**:
   `comm (Γ_sum + Φ) (Γ_diff + J) =
     -(2 : ℤ) • genSig P A C + comm Γ_sum J - anticomm Γ_sum J`.
4. **Endogenous Gramian Realization (`W = V = genV P A C`, `𝔅₄`)**:
   `comm (V + Φ) (Σ + J) = -(2 : ℤ) • Σ - (2 : ℤ) • (V * J)`. -/
theorem stage_B1_to_B4_sum_diff_crossover_and_combined_throat_commutator
    {P : B} (hP : P * P = P) (W A C : B) :
    let Γ_sum := InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnectionSum P W
    let Γ_diff := InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnectionDiff P W
    let nablaPlus := InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection P W
    let nablaMinus := InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection P W
    let Φ := genPhi P A C
    let J := genJ P A C
    let V := genV P A C
    let Sig := genSig P A C
    (invS P * Γ_sum = Γ_diff ∧
      Γ_sum * invS P = Γ_diff ∧
      Γ_sum * Γ_sum = nablaPlus * nablaPlus + nablaMinus * nablaMinus ∧
      Γ_diff * Γ_diff = nablaPlus * nablaPlus + nablaMinus * nablaMinus ∧
      Γ_sum * Γ_diff = nablaPlus * nablaPlus - nablaMinus * nablaMinus ∧
      invS P * (Γ_sum * Γ_sum) = nablaPlus * nablaPlus - nablaMinus * nablaMinus) ∧
    (comm Γ_diff Φ = anticomm Γ_sum J ∧
      anticomm Γ_diff Φ = comm Γ_sum J ∧
      comm Γ_diff J = anticomm Γ_sum Φ ∧
      anticomm Γ_diff J = comm Γ_sum Φ) ∧
    (comm (Γ_sum + Φ) (Γ_diff + J) =
      -((2 : ℤ) • Sig) + comm Γ_sum J - anticomm Γ_sum J) ∧
    (comm (V + Φ) (Sig + J) =
      -((2 : ℤ) • Sig) - (2 : ℤ) • (V * J)) := by
  intro Γ_sum Γ_diff nablaPlus nablaMinus Φ J V Sig
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnection_sum_difference_crossover hP W A C,
    ?_, ?_⟩ <;>
    (dsimp [Γ_sum, Γ_diff, nablaPlus, nablaMinus, Φ, J, V, Sig,
      InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnectionSum,
      InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnectionDiff,
      InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection,
      InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection];
     peirce_nf hP)

end SumDifferenceRung3Commutator

/-! ===========================================================================
    Section 4: Stage `𝔅₅` — The `V₄ = ℤ₂ × ℤ₂` Klein Bottle Seam Superoperator
    Group (`α, β, γ`) & Its Endogenous Tetraktys Realization (`U_β = Φ`)
    =========================================================================== -/

section KleinFourSuperoperatorGroup

variable {B : Type*} [Ring B]

/-- The chiral grading superoperator `α(X) := S_P * X * S_P` on `B`. -/
def kleinAlpha (P X : B) : B :=
  invS P * X * invS P

/-- The seam-reflection superoperator `β(X) := U * X * U` on `B`. -/
def kleinBeta (U X : B) : B :=
  U * X * U

/-- The composite Klein seam-twist superoperator `γ(X) := (S_P * U) * X * (U * S_P)` on `B`. -/
def kleinGamma (P U X : B) : B :=
  (invS P * U) * X * (U * invS P)

-- theorem-class: constructive endpoint
/-- **Stage `𝔅₅` Theorem (`stage_B5_klein_four_superoperator_commutativity_and_endogenous_throat_seam`)**:
In any noncommutative `[Ring B]` with idempotent `P * P = P`:
1. **Universal `V₄ = ℤ₂ × ℤ₂` Superoperator Group Table**:
   For any involution `U * U = 1` that anticommutes with `S_P = invS P`
   (`invS P * U = -(U * invS P)`), the three superoperators
   `kleinAlpha P`, `kleinBeta U`, and `kleinGamma P U` satisfy the exact
   Klein four-group multiplication table on every `X : B`:
   * `α(α(X)) = X`, `β(β(X)) = X`, `γ(γ(X)) = X`,
   * `α(β(X)) = γ(X)` and `β(α(X)) = γ(X)` (hence `α ∘ β = β ∘ α`),
   * `α(γ(X)) = β(X)` and `γ(α(X)) = β(X)`,
   * `β(γ(X)) = α(X)` and `γ(β(X)) = α(X)`.
2. **Endogenous Tetraktys Seam Realization (`U = Φ = genPhi P A C` at unit horizon `genV P A C = 1`)**:
   When `genV P A C = 1`, the solder throat `Φ = genPhi P A C` is an involution (`Φ * Φ = 1`)
   that anticommutes with `S_P` (`invS P * Φ = -(Φ * invS P)`), swaps the two Peirce sheets
   (`Φ * P * Φ = 1 - P` and `Φ * (1 - P) * Φ = P`), swaps the nilpotent wings
   (`Φ * conePlus P A * Φ = coneMinus P C` and `Φ * coneMinus P C * Φ = conePlus P A`),
   and identifies `kleinBeta Φ` with `peirceHalfTwist P A C` and `kleinGamma P Φ X`
   with `genJ P A C * X * (-genJ P A C)`. -/
theorem stage_B5_klein_four_superoperator_commutativity_and_endogenous_throat_seam
    {P U : B} (hP : P * P = P) (hU : U * U = 1)
    (hSU : invS P * U = -(U * invS P))
    {A C : B} (hV : genV P A C = 1) (X : B) :
    let S := invS P
    let Φ := genPhi P A C
    let J := genJ P A C
    (kleinAlpha P (kleinAlpha P X) = X ∧
      kleinBeta U (kleinBeta U X) = X ∧
      kleinGamma P U (kleinGamma P U X) = X ∧
      kleinAlpha P (kleinBeta U X) = kleinGamma P U X ∧
      kleinBeta U (kleinAlpha P X) = kleinGamma P U X ∧
      kleinAlpha P (kleinGamma P U X) = kleinBeta U X ∧
      kleinGamma P U (kleinAlpha P X) = kleinBeta U X ∧
      kleinBeta U (kleinGamma P U X) = kleinAlpha P X ∧
      kleinGamma P U (kleinBeta U X) = kleinAlpha P X) ∧
    (Φ * Φ = 1 ∧
      S * Φ = -(Φ * S) ∧
      Φ * P * Φ = 1 - P ∧
      Φ * (1 - P) * Φ = P ∧
      Φ * conePlus P A * Φ = coneMinus P C ∧
      Φ * coneMinus P C * Φ = conePlus P A ∧
      kleinBeta Φ X = peirceHalfTwist P A C X ∧
      kleinGamma P Φ X = J * X * (-J)) := by
  intro S Φ J
  have hS : S * S = 1 := by dsimp [S]; peirce_nf hP
  have hV4 := innerConjugation_v4_relations S U hS hU hSU
  have hAB : kleinAlpha P (kleinBeta U X) = kleinGamma P U X := by
    dsimp [kleinAlpha, kleinBeta, kleinGamma]
    noncomm_ring
  have hBA : kleinBeta U (kleinAlpha P X) = kleinGamma P U X := by
    dsimp [kleinAlpha, kleinBeta]
    rw [← hV4.2.2.1 X]
    exact hAB
  have hAG : kleinAlpha P (kleinGamma P U X) = kleinBeta U X := by
    rw [← hAB]
    exact hV4.1 (kleinBeta U X)
  have hGA : kleinGamma P U (kleinAlpha P X) = kleinBeta U X := by
    calc
      kleinGamma P U (kleinAlpha P X)
        = kleinAlpha P (kleinBeta U (kleinAlpha P X)) := by
          dsimp [kleinAlpha, kleinBeta, kleinGamma]; noncomm_ring
      _ = kleinAlpha P (kleinGamma P U X) := by rw [hBA]
      _ = kleinBeta U X := hAG
  have hBG : kleinBeta U (kleinGamma P U X) = kleinAlpha P X := by
    rw [← hBA]
    exact hV4.2.1 (kleinAlpha P X)
  have hGB : kleinGamma P U (kleinBeta U X) = kleinAlpha P X := by
    calc
      kleinGamma P U (kleinBeta U X)
        = kleinAlpha P (kleinBeta U (kleinBeta U X)) := by
          dsimp [kleinAlpha, kleinBeta, kleinGamma]; noncomm_ring
      _ = kleinAlpha P X := by
          congr 1
          exact hV4.2.1 X
  have hPhiSq : Φ * Φ = 1 := by
    have h1 : Φ * Φ = genV P A C := by dsimp [Φ]; peirce_nf hP
    rw [h1, hV]
  have hSPhi : S * Φ = -(Φ * S) := by dsimp [S, Φ]; peirce_nf hP
  have hPhiP : Φ * P * Φ = 1 - P := by
    have h1 : Φ * P * Φ = genV P A C * (1 - P) := by dsimp [Φ]; peirce_nf hP
    rw [h1, hV, one_mul]
  have hPhi1mP : Φ * (1 - P) * Φ = P := by
    have h1 : Φ * (1 - P) * Φ = genV P A C * P := by dsimp [Φ]; peirce_nf hP
    rw [h1, hV, one_mul]
  have hPhiNp : Φ * conePlus P A * Φ = coneMinus P C := by
    have h1 : Φ * conePlus P A * Φ = genV P A C * coneMinus P C := by
      dsimp [Φ]; peirce_nf hP
    rw [h1, hV, one_mul]
  have hPhiNm : Φ * coneMinus P C * Φ = conePlus P A := by
    have h1 : Φ * coneMinus P C * Φ = conePlus P A * genV P A C := by
      dsimp [Φ]; peirce_nf hP
    rw [h1, hV, mul_one]
  have hGammaPhi : kleinGamma P Φ X = J * X * (-J) := by
    have hSJ : S * Φ = J := by dsimp [S, Φ, J]; peirce_nf hP
    have hPhiS : Φ * S = -J := by dsimp [S, Φ, J]; peirce_nf hP
    dsimp [kleinGamma]
    rw [hSJ, hPhiS]
  exact ⟨⟨hV4.1 X, hV4.2.1 X, hV4.2.2.2 X, hAB, hBA, hAG, hGA, hBG, hGB⟩,
    ⟨hPhiSq, hSPhi, hPhiP, hPhi1mP, hPhiNp, hPhiNm, rfl, hGammaPhi⟩⟩

end KleinFourSuperoperatorGroup

/-! ===========================================================================
    Section 5: Stage `𝔅₆` — Fourfold `V₄ = ℤ₂ × ℤ₂` Character Eigen-Classification
    of the Two-Sheeted Klein Bottle Geometry (`χ₊₊, χ₊₋, χ₋₊, χ₋₋`)
    =========================================================================== -/

section FourfoldV4CharacterClassification

variable {B : Type*} [Ring B]

-- theorem-class: constructive endpoint
/-- **Stage `𝔅₆` Theorem (`stage_B6_fourfold_v4_character_eigen_classification`)**:
In any noncommutative `[Ring B]` with idempotent `P * P = P`, let `U : B` be a
seam-reflection involution (`U * U = 1`) that swaps the nilpotent throat wings
(`U * conePlus P A * U = coneMinus P C` and `U * coneMinus P C * U = conePlus P A`)
and swaps the two sheet connections of `W`
(`U * sheetPlusConnection P W * U = sheetMinusConnection P W` and
`U * sheetMinusConnection P W * U = sheetPlusConnection P W`):
1. **Sector `χ₊₊ = (+1, +1, +1)` (Sum Connection `Γ_sum` & DeWitt Metric `V`)**:
   * `kleinAlpha P Γ_sum = Γ_sum`, `kleinBeta U Γ_sum = Γ_sum`, `kleinGamma P U Γ_sum = Γ_sum`,
   * `kleinAlpha P V = V`, `kleinBeta U V = V`, `kleinGamma P U V = V`.
2. **Sector `χ₊₋ = (+1, -1, -1)` (Difference Connection `Γ_diff` & Spin Curvature `Σ`)**:
   * `kleinAlpha P Γ_diff = Γ_diff`, `kleinBeta U Γ_diff = -Γ_diff`, `kleinGamma P U Γ_diff = -Γ_diff`,
   * `kleinAlpha P Σ = Σ`, `kleinBeta U Σ = -Σ`, `kleinGamma P U Σ = -Σ`.
3. **Sector `χ₋₊ = (-1, +1, -1)` (Untwisted Cylinder Throat `Φ = N₊ + N₋`)**:
   * `kleinAlpha P Φ = -Φ`, `kleinBeta U Φ = Φ`, `kleinGamma P U Φ = -Φ`.
4. **Sector `χ₋₋ = (-1, -1, +1)` (Klein Bottle Seam Twist `J = N₊ - N₋`)**:
   * `kleinAlpha P J = -J`, `kleinBeta U J = -J`, `kleinGamma P U J = J`. -/
theorem stage_B6_fourfold_v4_character_eigen_classification
    {P U W A C : B} (hP : P * P = P) (hU : U * U = 1)
    (hUNp : U * conePlus P A * U = coneMinus P C)
    (hUNm : U * coneMinus P C * U = conePlus P A)
    (hUWp : U * InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection P W * U =
      InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection P W)
    (hUWm : U * InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection P W * U =
      InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection P W) :
    let Γ_sum := InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnectionSum P W
    let Γ_diff := InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnectionDiff P W
    let V := genV P A C
    let Sig := genSig P A C
    let Φ := genPhi P A C
    let J := genJ P A C
    (kleinAlpha P Γ_sum = Γ_sum ∧
      kleinBeta U Γ_sum = Γ_sum ∧
      kleinGamma P U Γ_sum = Γ_sum ∧
      kleinAlpha P V = V ∧
      kleinBeta U V = V ∧
      kleinGamma P U V = V) ∧
    (kleinAlpha P Γ_diff = Γ_diff ∧
      kleinBeta U Γ_diff = -Γ_diff ∧
      kleinGamma P U Γ_diff = -Γ_diff ∧
      kleinAlpha P Sig = Sig ∧
      kleinBeta U Sig = -Sig ∧
      kleinGamma P U Sig = -Sig) ∧
    (kleinAlpha P Φ = -Φ ∧
      kleinBeta U Φ = Φ ∧
      kleinGamma P U Φ = -Φ) ∧
    (kleinAlpha P J = -J ∧
      kleinBeta U J = -J ∧
      kleinGamma P U J = J) := by
  intro Γ_sum Γ_diff V Sig Φ J
  have hGammaEq : ∀ X : B, kleinGamma P U X = kleinAlpha P (kleinBeta U X) := by
    intro X
    dsimp [kleinGamma, kleinAlpha, kleinBeta]
    noncomm_ring
  have hAlphaSum : kleinAlpha P Γ_sum = Γ_sum := by
    dsimp [kleinAlpha, Γ_sum,
      InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnectionSum,
      InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection,
      InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection]
    peirce_nf hP
  have hBetaSum : kleinBeta U Γ_sum = Γ_sum := by
    dsimp [kleinBeta, Γ_sum, InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnectionSum]
    calc
      U * (InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection P W +
          InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection P W) * U
        = U * InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection P W * U +
          U * InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection P W * U := by
          noncomm_ring
      _ = InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection P W +
          InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection P W := by
          rw [hUWp, hUWm]
      _ = InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection P W +
          InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection P W := by
          abel
  have hGammaSum : kleinGamma P U Γ_sum = Γ_sum := by
    rw [hGammaEq, hBetaSum, hAlphaSum]
  have hAlphaDiff : kleinAlpha P Γ_diff = Γ_diff := by
    dsimp [kleinAlpha, Γ_diff,
      InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnectionDiff,
      InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection,
      InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection]
    peirce_nf hP
  have hBetaDiff : kleinBeta U Γ_diff = -Γ_diff := by
    dsimp [kleinBeta, Γ_diff, InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnectionDiff]
    calc
      U * (InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection P W -
          InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection P W) * U
        = U * InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection P W * U -
          U * InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection P W * U := by
          noncomm_ring
      _ = InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection P W -
          InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection P W := by
          rw [hUWp, hUWm]
      _ = -(InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection P W -
          InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection P W) := by
          abel
  have hAlphaNeg : ∀ X : B, kleinAlpha P (-X) = -kleinAlpha P X := by
    intro X; dsimp [kleinAlpha]; noncomm_ring
  have hGammaDiff : kleinGamma P U Γ_diff = -Γ_diff := by
    rw [hGammaEq, hBetaDiff, hAlphaNeg, hAlphaDiff]
  have hUQplus : U * (conePlus P A * coneMinus P C) * U = coneMinus P C * conePlus P A := by
    calc
      U * (conePlus P A * coneMinus P C) * U
        = U * conePlus P A * 1 * coneMinus P C * U := by noncomm_ring
      _ = U * conePlus P A * (U * U) * coneMinus P C * U := by rw [hU]
      _ = (U * conePlus P A * U) * (U * coneMinus P C * U) := by noncomm_ring
      _ = coneMinus P C * conePlus P A := by rw [hUNp, hUNm]
  have hUQminus : U * (coneMinus P C * conePlus P A) * U = conePlus P A * coneMinus P C := by
    calc
      U * (coneMinus P C * conePlus P A) * U
        = U * coneMinus P C * 1 * conePlus P A * U := by noncomm_ring
      _ = U * coneMinus P C * (U * U) * conePlus P A * U := by rw [hU]
      _ = (U * coneMinus P C * U) * (U * conePlus P A * U) := by noncomm_ring
      _ = conePlus P A * coneMinus P C := by rw [hUNm, hUNp]
  have hAlphaV : kleinAlpha P V = V := by dsimp [kleinAlpha, V]; peirce_nf hP
  have hBetaV : kleinBeta U V = V := by
    dsimp [kleinBeta, V, genV, anticomm]
    calc
      U * (conePlus P A * coneMinus P C + coneMinus P C * conePlus P A) * U
        = U * (conePlus P A * coneMinus P C) * U +
          U * (coneMinus P C * conePlus P A) * U := by noncomm_ring
      _ = coneMinus P C * conePlus P A + conePlus P A * coneMinus P C := by
          rw [hUQplus, hUQminus]
      _ = conePlus P A * coneMinus P C + coneMinus P C * conePlus P A := by abel
  have hGammaV : kleinGamma P U V = V := by
    rw [hGammaEq, hBetaV, hAlphaV]
  have hAlphaSig : kleinAlpha P Sig = Sig := by dsimp [kleinAlpha, Sig]; peirce_nf hP
  have hBetaSig : kleinBeta U Sig = -Sig := by
    dsimp [kleinBeta, Sig, genSig, OperatorAlgebra.PeirceSpine.comm]
    calc
      U * (conePlus P A * coneMinus P C - coneMinus P C * conePlus P A) * U
        = U * (conePlus P A * coneMinus P C) * U -
          U * (coneMinus P C * conePlus P A) * U := by noncomm_ring
      _ = coneMinus P C * conePlus P A - conePlus P A * coneMinus P C := by
          rw [hUQplus, hUQminus]
      _ = -(conePlus P A * coneMinus P C - coneMinus P C * conePlus P A) := by abel
  have hGammaSig : kleinGamma P U Sig = -Sig := by
    rw [hGammaEq, hBetaSig, hAlphaNeg, hAlphaSig]
  have hAlphaPhi : kleinAlpha P Φ = -Φ := by dsimp [kleinAlpha, Φ]; peirce_nf hP
  have hBetaPhi : kleinBeta U Φ = Φ := by
    dsimp [kleinBeta, Φ, genPhi]
    calc
      U * (conePlus P A + coneMinus P C) * U
        = U * conePlus P A * U + U * coneMinus P C * U := by noncomm_ring
      _ = coneMinus P C + conePlus P A := by rw [hUNp, hUNm]
      _ = conePlus P A + coneMinus P C := by abel
  have hGammaPhi : kleinGamma P U Φ = -Φ := by
    rw [hGammaEq, hBetaPhi, hAlphaPhi]
  have hAlphaJ : kleinAlpha P J = -J := by dsimp [kleinAlpha, J]; peirce_nf hP
  have hBetaJ : kleinBeta U J = -J := by
    dsimp [kleinBeta, J, genJ]
    calc
      U * (conePlus P A - coneMinus P C) * U
        = U * conePlus P A * U - U * coneMinus P C * U := by noncomm_ring
      _ = coneMinus P C - conePlus P A := by rw [hUNp, hUNm]
      _ = -(conePlus P A - coneMinus P C) := by abel
  have hGammaJ : kleinGamma P U J = J := by
    rw [hGammaEq, hBetaJ, hAlphaNeg, hAlphaJ, neg_neg]
  exact ⟨⟨hAlphaSum, hBetaSum, hGammaSum, hAlphaV, hBetaV, hGammaV⟩,
    ⟨hAlphaDiff, hBetaDiff, hGammaDiff, hAlphaSig, hBetaSig, hGammaSig⟩,
    ⟨hAlphaPhi, hBetaPhi, hGammaPhi⟩,
    ⟨hAlphaJ, hBetaJ, hGammaJ⟩⟩

end FourfoldV4CharacterClassification

/-! ===========================================================================
    Section 6: Stage `𝔅₇` — The `4 × 4` Walsh–Hadamard Projector Resolution
    (`Π_{++}, Π_{+-}, Π_{-+}, Π_{--}`) & Klein Bottle Sector Isolation
    =========================================================================== -/

/-- The `4 × 4` Walsh–Hadamard character table matrix `H₄ = H₂ ⊗ H₂` of `V₄ = ℤ₂ × ℤ₂`. -/
def walshHadamardMatrix4 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![ 1,  1,  1,  1;
      1,  1, -1, -1;
      1, -1,  1, -1;
      1, -1, -1,  1]

/-- A matrix-unit probe showing that the concrete Walsh transform is genuinely
noncommutative with general operators in the same matrix algebra. -/
def walshHadamardProbe : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

-- theorem-class: constructive endpoint
/-- The Walsh matrix does not commute with the rank-one matrix-unit probe. -/
theorem walshHadamardMatrix4_noncommutes_probe :
    walshHadamardMatrix4 * walshHadamardProbe ≠
      walshHadamardProbe * walshHadamardMatrix4 := by
  decide

/-- Concrete `2 × 2` chiral grading involution `S = !![1, 0; 0, -1]` on `Matrix (Fin 2) (Fin 2) ℤ`. -/
def kleinSeamMatS : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 0; 0, -1]

/-- Concrete `2 × 2` seam reflection involution `Φ = !![0, 1; 1, 0]` on `Matrix (Fin 2) (Fin 2) ℤ`. -/
def kleinSeamMatPhi : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, 1; 1, 0]

-- theorem-class: constructive endpoint
/-- Concrete non-commutativity and chiral anticommutation witness for the `2 × 2`
Klein seam generators `kleinSeamMatS` and `kleinSeamMatPhi`. -/
theorem kleinSeamMatS_Phi_noncomm_and_anticomm :
    kleinSeamMatS * kleinSeamMatPhi ≠ kleinSeamMatPhi * kleinSeamMatS ∧
    kleinSeamMatS * kleinSeamMatPhi + kleinSeamMatPhi * kleinSeamMatS = 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    revert h01
    decide
  · ext i j
    fin_cases i <;> fin_cases j <;> decide

section WalshHadamardProjectorResolution

variable {B : Type*} [Ring B]

/-- Unnormalized `V₄` Walsh–Hadamard projector `4 Π_{++}(X) = X + α(X) + β(X) + γ(X)`
onto the doubly-even sector `χ_{++} = (+1, +1)` (housing `Γ_sum` and `V`). -/
def walshHadamardPP (P U X : B) : B :=
  X + kleinAlpha P X + kleinBeta U X + kleinGamma P U X

/-- Unnormalized `V₄` Walsh–Hadamard projector `4 Π_{+-}(X) = X + α(X) - β(X) - γ(X)`
onto the chiral-even, seam-odd sector `χ_{+-} = (+1, -1)` (housing `Γ_diff` and `Σ`). -/
def walshHadamardPM (P U X : B) : B :=
  X + kleinAlpha P X - kleinBeta U X - kleinGamma P U X

/-- Unnormalized `V₄` Walsh–Hadamard projector `4 Π_{-+}(X) = X - α(X) + β(X) - γ(X)`
onto the chiral-odd, seam-even sector `χ_{-+} = (-1, +1)` (housing the throat `Φ`). -/
def walshHadamardMP (P U X : B) : B :=
  X - kleinAlpha P X + kleinBeta U X - kleinGamma P U X

/-- Unnormalized `V₄` Walsh–Hadamard projector `4 Π_{--}(X) = X - α(X) - β(X) + γ(X)`
onto the doubly-odd sector `χ_{--} = (-1, -1)` (housing the Klein seam twist `J`). -/
def walshHadamardMM (P U X : B) : B :=
  X - kleinAlpha P X - kleinBeta U X + kleinGamma P U X

-- theorem-class: constructive endpoint
/-- **Stage `𝔅₇` Theorem (`stage_B7_walsh_hadamard_projector_resolution_and_sector_isolation`)**:
In any noncommutative `[Ring B]` with idempotent `P * P = P` and seam involution
`U * U = 1` anticommuting with `S_P = invS P` (`invS P * U = -(U * invS P)`):
1. **`4 × 4` Walsh–Hadamard Matrix Involution (`H₄² = 4 I₄`)**:
   `walshHadamardMatrix4 * walshHadamardMatrix4 = (4 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)`.
2. **Resolution of the Identity on `B`**:
   For every `X : B`,
   `walshHadamardPP P U X + walshHadamardPM P U X +
     walshHadamardMP P U X + walshHadamardMM P U X = (4 : ℤ) • X`.
3. **Scaled Idempotence & Mutual Orthogonality**:
   * `walshHadamardPP P U (walshHadamardPP P U X) = (4 : ℤ) • walshHadamardPP P U X` (and for `PM`, `MP`, `MM`),
   * All off-diagonal compositions vanish (`walshHadamardPP P U (walshHadamardPM P U X) = 0`, etc.).
4. **Exact Isolation of the 4 Klein Bottle Geometry Sectors**
   (`V, Σ, Φ, J` at unit horizon `genV P A C = 1` with `U = genPhi P A C`):
   * `walshHadamardPP P Φ V = (4 : ℤ) • V`, while `PM, MP, MM` annihilate `V`,
   * `walshHadamardPM P Φ Σ = (4 : ℤ) • Σ`, while `PP, MP, MM` annihilate `Σ`,
   * `walshHadamardMP P Φ Φ = (4 : ℤ) • Φ`, while `PP, PM, MM` annihilate `Φ`,
   * `walshHadamardMM P Φ J = (4 : ℤ) • J`, while `PP, PM, MP` annihilate `J`. -/
theorem stage_B7_walsh_hadamard_projector_resolution_and_sector_isolation
    {P U : B} (hP : P * P = P) (hU : U * U = 1)
    (hSU : invS P * U = -(U * invS P))
    {A C : B} (hV : genV P A C = 1) (X : B) :
    let V := genV P A C
    let Sig := genSig P A C
    let Φ := genPhi P A C
    let J := genJ P A C
    (walshHadamardMatrix4 * walshHadamardMatrix4 =
      (4 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) ∧
    (walshHadamardPP P U X + walshHadamardPM P U X +
      walshHadamardMP P U X + walshHadamardMM P U X = (4 : ℤ) • X) ∧
    (walshHadamardPP P U (walshHadamardPP P U X) = (4 : ℤ) • walshHadamardPP P U X ∧
      walshHadamardPM P U (walshHadamardPM P U X) = (4 : ℤ) • walshHadamardPM P U X ∧
      walshHadamardMP P U (walshHadamardMP P U X) = (4 : ℤ) • walshHadamardMP P U X ∧
      walshHadamardMM P U (walshHadamardMM P U X) = (4 : ℤ) • walshHadamardMM P U X ∧
      walshHadamardPP P U (walshHadamardPM P U X) = 0 ∧
      walshHadamardPP P U (walshHadamardMP P U X) = 0 ∧
      walshHadamardPP P U (walshHadamardMM P U X) = 0 ∧
      walshHadamardPM P U (walshHadamardMP P U X) = 0 ∧
      walshHadamardPM P U (walshHadamardMM P U X) = 0 ∧
      walshHadamardMP P U (walshHadamardMM P U X) = 0) ∧
    (walshHadamardPP P Φ V = (4 : ℤ) • V ∧
      walshHadamardPM P Φ V = 0 ∧
      walshHadamardMP P Φ V = 0 ∧
      walshHadamardMM P Φ V = 0 ∧
      walshHadamardPM P Φ Sig = (4 : ℤ) • Sig ∧
      walshHadamardPP P Φ Sig = 0 ∧
      walshHadamardMP P Φ Sig = 0 ∧
      walshHadamardMM P Φ Sig = 0 ∧
      walshHadamardMP P Φ Φ = (4 : ℤ) • Φ ∧
      walshHadamardPP P Φ Φ = 0 ∧
      walshHadamardPM P Φ Φ = 0 ∧
      walshHadamardMM P Φ Φ = 0 ∧
      walshHadamardMM P Φ J = (4 : ℤ) • J ∧
      walshHadamardPP P Φ J = 0 ∧
      walshHadamardPM P Φ J = 0 ∧
      walshHadamardMP P Φ J = 0) := by
  intro V Sig Φ J
  have hB5 := stage_B5_klein_four_superoperator_commutativity_and_endogenous_throat_seam
    hP hU hSU hV X
  have hAA : ∀ Y : B, kleinAlpha P (kleinAlpha P Y) = Y :=
    fun Y => (stage_B5_klein_four_superoperator_commutativity_and_endogenous_throat_seam hP hU hSU hV Y).1.1
  have hBB : ∀ Y : B, kleinBeta U (kleinBeta U Y) = Y :=
    fun Y => (stage_B5_klein_four_superoperator_commutativity_and_endogenous_throat_seam hP hU hSU hV Y).1.2.1
  have hGG : ∀ Y : B, kleinGamma P U (kleinGamma P U Y) = Y :=
    fun Y => (stage_B5_klein_four_superoperator_commutativity_and_endogenous_throat_seam hP hU hSU hV Y).1.2.2.1
  have hAB : ∀ Y : B, kleinAlpha P (kleinBeta U Y) = kleinGamma P U Y :=
    fun Y => (stage_B5_klein_four_superoperator_commutativity_and_endogenous_throat_seam hP hU hSU hV Y).1.2.2.2.1
  have hBA : ∀ Y : B, kleinBeta U (kleinAlpha P Y) = kleinGamma P U Y :=
    fun Y => (stage_B5_klein_four_superoperator_commutativity_and_endogenous_throat_seam hP hU hSU hV Y).1.2.2.2.2.1
  have hAG : ∀ Y : B, kleinAlpha P (kleinGamma P U Y) = kleinBeta U Y :=
    fun Y => (stage_B5_klein_four_superoperator_commutativity_and_endogenous_throat_seam hP hU hSU hV Y).1.2.2.2.2.2.1
  have hGA : ∀ Y : B, kleinGamma P U (kleinAlpha P Y) = kleinBeta U Y :=
    fun Y => (stage_B5_klein_four_superoperator_commutativity_and_endogenous_throat_seam hP hU hSU hV Y).1.2.2.2.2.2.2.1
  have hBG : ∀ Y : B, kleinBeta U (kleinGamma P U Y) = kleinAlpha P Y :=
    fun Y => (stage_B5_klein_four_superoperator_commutativity_and_endogenous_throat_seam hP hU hSU hV Y).1.2.2.2.2.2.2.2.1
  have hGB : ∀ Y : B, kleinGamma P U (kleinBeta U Y) = kleinAlpha P Y :=
    fun Y => (stage_B5_klein_four_superoperator_commutativity_and_endogenous_throat_seam hP hU hSU hV Y).1.2.2.2.2.2.2.2.2
  have hAlphaAdd : ∀ Y Z : B, kleinAlpha P (Y + Z) = kleinAlpha P Y + kleinAlpha P Z := by
    intro Y Z; dsimp [kleinAlpha]; noncomm_ring
  have hAlphaSub : ∀ Y Z : B, kleinAlpha P (Y - Z) = kleinAlpha P Y - kleinAlpha P Z := by
    intro Y Z; dsimp [kleinAlpha]; noncomm_ring
  have hBetaAdd : ∀ Y Z : B, kleinBeta U (Y + Z) = kleinBeta U Y + kleinBeta U Z := by
    intro Y Z; dsimp [kleinBeta]; noncomm_ring
  have hBetaSub : ∀ Y Z : B, kleinBeta U (Y - Z) = kleinBeta U Y - kleinBeta U Z := by
    intro Y Z; dsimp [kleinBeta]; noncomm_ring
  have hGammaAdd : ∀ Y Z : B, kleinGamma P U (Y + Z) = kleinGamma P U Y + kleinGamma P U Z := by
    intro Y Z; dsimp [kleinGamma]; noncomm_ring
  have hGammaSub : ∀ Y Z : B, kleinGamma P U (Y - Z) = kleinGamma P U Y - kleinGamma P U Z := by
    intro Y Z; dsimp [kleinGamma]; noncomm_ring
  have hMat :
      walshHadamardMatrix4 * walshHadamardMatrix4 =
        (4 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  have hRes :
      walshHadamardPP P U X + walshHadamardPM P U X +
        walshHadamardMP P U X + walshHadamardMM P U X = (4 : ℤ) • X := by
    dsimp [walshHadamardPP, walshHadamardPM, walshHadamardMP, walshHadamardMM]
    abel
  have hV' : V = 1 := hV
  have hPhiSq := hB5.2.1
  have hPhiNp := hB5.2.2.2.2.2.1
  have hPhiNm := hB5.2.2.2.2.2.2.1
  have hPhiWp :
      Φ * InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection P V * Φ =
        InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection P V := by
    have h1 :
        Φ * InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection P V * Φ =
          V * InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection P V := by
      dsimp [Φ, V,
        InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection,
        InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection]
      peirce_nf hP
    rw [h1, hV', one_mul]
  have hPhiWm :
      Φ * InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection P V * Φ =
        InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection P V := by
    have h1 :
        Φ * InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection P V * Φ =
          InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection P V * V := by
      dsimp [Φ, V,
        InfoGeometry.OperatorAlgebra.PeirceSpine.sheetPlusConnection,
        InfoGeometry.OperatorAlgebra.PeirceSpine.sheetMinusConnection]
      peirce_nf hP
    rw [h1, hV', mul_one]
  have hB6 := stage_B6_fourfold_v4_character_eigen_classification
    hP hPhiSq hPhiNp hPhiNm hPhiWp hPhiWm
  refine ⟨hMat, hRes,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · dsimp [walshHadamardPP]
    simp only [hAlphaAdd, hBetaAdd, hGammaAdd, hAA, hBB, hGG, hAB, hBA, hAG, hGA, hBG, hGB]
    abel
  · dsimp [walshHadamardPM]
    simp only [hAlphaAdd, hAlphaSub, hBetaAdd, hBetaSub, hGammaAdd, hGammaSub,
      hAA, hBB, hGG, hAB, hBA, hAG, hGA, hBG, hGB]
    abel
  · dsimp [walshHadamardMP]
    simp only [hAlphaAdd, hAlphaSub, hBetaAdd, hBetaSub, hGammaAdd, hGammaSub,
      hAA, hBB, hGG, hAB, hBA, hAG, hGA, hBG, hGB]
    abel
  · dsimp [walshHadamardMM]
    simp only [hAlphaAdd, hAlphaSub, hBetaAdd, hBetaSub, hGammaAdd, hGammaSub,
      hAA, hBB, hGG, hAB, hBA, hAG, hGA, hBG, hGB]
    abel
  · dsimp [walshHadamardPP, walshHadamardPM]
    simp only [hAlphaAdd, hAlphaSub, hBetaAdd, hBetaSub, hGammaAdd, hGammaSub,
      hAA, hBB, hGG, hAB, hBA, hAG, hGA, hBG, hGB]
    abel
  · dsimp [walshHadamardPP, walshHadamardMP]
    simp only [hAlphaAdd, hAlphaSub, hBetaAdd, hBetaSub, hGammaAdd, hGammaSub,
      hAA, hBB, hGG, hAB, hBA, hAG, hGA, hBG, hGB]
    abel
  · dsimp [walshHadamardPP, walshHadamardMM]
    simp only [hAlphaAdd, hAlphaSub, hBetaAdd, hBetaSub, hGammaAdd, hGammaSub,
      hAA, hBB, hGG, hAB, hBA, hAG, hGA, hBG, hGB]
    abel
  · dsimp [walshHadamardPM, walshHadamardMP]
    simp only [hAlphaAdd, hAlphaSub, hBetaAdd, hBetaSub, hGammaAdd, hGammaSub,
      hAA, hBB, hGG, hAB, hBA, hAG, hGA, hBG, hGB]
    abel
  · dsimp [walshHadamardPM, walshHadamardMM]
    simp only [hAlphaAdd, hAlphaSub, hBetaAdd, hBetaSub, hGammaAdd, hGammaSub,
      hAA, hBB, hGG, hAB, hBA, hAG, hGA, hBG, hGB]
    abel
  · dsimp [walshHadamardMP, walshHadamardMM]
    simp only [hAlphaAdd, hAlphaSub, hBetaAdd, hBetaSub, hGammaAdd, hGammaSub,
      hAA, hBB, hGG, hAB, hBA, hAG, hGA, hBG, hGB]
    abel
  · dsimp [walshHadamardPP]; rw [hB6.1.2.2.2.1, hB6.1.2.2.2.2.1, hB6.1.2.2.2.2.2]; abel
  · dsimp [walshHadamardPM]; rw [hB6.1.2.2.2.1, hB6.1.2.2.2.2.1, hB6.1.2.2.2.2.2]; abel
  · dsimp [walshHadamardMP]; rw [hB6.1.2.2.2.1, hB6.1.2.2.2.2.1, hB6.1.2.2.2.2.2]; abel
  · dsimp [walshHadamardMM]; rw [hB6.1.2.2.2.1, hB6.1.2.2.2.2.1, hB6.1.2.2.2.2.2]; abel
  · dsimp [walshHadamardPM]; rw [hB6.2.1.2.2.2.1, hB6.2.1.2.2.2.2.1, hB6.2.1.2.2.2.2.2]; abel
  · dsimp [walshHadamardPP]; rw [hB6.2.1.2.2.2.1, hB6.2.1.2.2.2.2.1, hB6.2.1.2.2.2.2.2]; abel
  · dsimp [walshHadamardMP]; rw [hB6.2.1.2.2.2.1, hB6.2.1.2.2.2.2.1, hB6.2.1.2.2.2.2.2]; abel
  · dsimp [walshHadamardMM]; rw [hB6.2.1.2.2.2.1, hB6.2.1.2.2.2.2.1, hB6.2.1.2.2.2.2.2]; abel
  · dsimp [walshHadamardMP]; rw [hB6.2.2.1.1, hB6.2.2.1.2.1, hB6.2.2.1.2.2]; abel
  · dsimp [walshHadamardPP]; rw [hB6.2.2.1.1, hB6.2.2.1.2.1, hB6.2.2.1.2.2]; abel
  · dsimp [walshHadamardPM]; rw [hB6.2.2.1.1, hB6.2.2.1.2.1, hB6.2.2.1.2.2]; abel
  · dsimp [walshHadamardMM]; rw [hB6.2.2.1.1, hB6.2.2.1.2.1, hB6.2.2.1.2.2]; abel
  · dsimp [walshHadamardMM]; rw [hB6.2.2.2.1, hB6.2.2.2.2.1, hB6.2.2.2.2.2]; abel
  · dsimp [walshHadamardPP]; rw [hB6.2.2.2.1, hB6.2.2.2.2.1, hB6.2.2.2.2.2]; abel
  · dsimp [walshHadamardPM]; rw [hB6.2.2.2.1, hB6.2.2.2.2.1, hB6.2.2.2.2.2]; abel
  · dsimp [walshHadamardMP]; rw [hB6.2.2.2.1, hB6.2.2.2.2.1, hB6.2.2.2.2.2]; abel

end WalshHadamardProjectorResolution

/-! ===========================================================================
    Section 7: Master Capstone Theorem Unifying `𝔚₁ ≺ … ≺ 𝔚₇`, `𝔅₁ ≺ … ≺ 𝔅₇`,
    and `M1 ≺ … ≺ M6`
    =========================================================================== -/

-- theorem-class: capstone consumer theorem
/-- **Master Capstone Theorem (`klein_bottle_v4_seam_sum_difference_walsh_hadamard_master_poset`)**:
Unifies the 7-stage Berry Wilson Loop & Hyperplane Causal Transmutation Poset (`𝔚₁ ≺ … ≺ 𝔚₇`),
the 7-stage Two-Sheeted Peirce–DeWitt Split, Sum–Difference Crossover & `V₄` Klein Bottle Seam
Poset (`𝔅₁ ≺ … ≺ 𝔅₇`), and the 6-stratum Supergraded Möbius–Tetraktys–Klein–Schur Poset
(`M1 ≺ … ≺ M6`):
1. Acyclicity of `BerryWilsonLoopCausalStage`, `KleinBottleSeamConnectionStage`, and
   `SupergradedMoebiusTetraktysKleinStratum`,
2. Hyperplane causal transmutation `(c • J + s • Φ)² = (s² - c²) • V`, polynomial Wilson loop
   `(W(c, s) * J)² = (s² - c²) • V³`, trigonometric Wick rotation `J(θ)² = (-cos(2θ)) • V`,
   and Rung 0 rotor angle inversion `J * R(θ) = R(-θ) * J`,
3. Universal Sum–Difference parallel transport crossover `[Γ_diff, Φ] = {Γ_sum, J}` and Rung 3
   combined commutator `[V + Φ, Σ + J] = -(2 : ℤ) • Σ - (2 : ℤ) • (V * J)`,
4. `V₄ = ℤ₂ × ℤ₂` superoperator commutativity `α(β(X)) = β(α(X)) = γ(X)`, `4 × 4` Walsh–Hadamard
   resolution `Π_{++} + Π_{+-} + Π_{-+} + Π_{--} = 4 • id`, and exact isolation of `(V, Σ, Φ, J)`. -/
theorem klein_bottle_v4_seam_sum_difference_walsh_hadamard_master_poset
    {B : Type*} [Ring B] [Algebra ℝ B]
    {P : B} (hP : P * P = P) {A C : B} (hV : genV P A C = 1)
    (W X : B) (c s t θ : ℝ) :
    let V := genV P A C
    let Sig := genSig P A C
    let Φ := genPhi P A C
    let J := genJ P A C
    -- (1) Acyclicity across all three posets
    ((∀ st : BerryWilsonLoopCausalStage,
        ¬ Relation.TransGen BerryWilsonLoopCausalStage.causalEdge st st) ∧
      (∀ st : KleinBottleSeamConnectionStage,
        ¬ Relation.TransGen KleinBottleSeamConnectionStage.causalEdge st st) ∧
      (∀ st : SupergradedMoebiusTetraktysKleinStratum,
        ¬ Relation.TransGen SupergradedMoebiusTetraktysKleinStratum.coverEdge st st)) ∧
    -- (2) Berry Wilson Loop & Hyperplane Causal Transmutation (𝔚₁–𝔚₇)
    ((c • J + s • Φ) * (c • J + s • Φ) = (s ^ 2 - c ^ 2) • V ∧
      (wilsonLoopEven P A C c s * J) * (wilsonLoopEven P A C c s * J) =
        (s ^ 2 - c ^ 2) • (V * V * V) ∧
      J * berryRotor P θ = berryRotor P (-θ) * J ∧
      rotatedCurrentJ P A C θ * rotatedCurrentJ P A C θ = (-Real.cos (2 * θ)) • V) ∧
    -- (3) Sum–Difference Transport Crossover & Combined Throat Commutator (𝔅₁–𝔅₄)
    (comm (InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnectionDiff P W) Φ =
        anticomm (InfoGeometry.OperatorAlgebra.PeirceSpine.sheetConnectionSum P W) J ∧
      comm (V + Φ) (Sig + J) = -((2 : ℤ) • Sig) - (2 : ℤ) • (V * J)) ∧
    -- (4) V₄ Superoperator Commutativity & Walsh–Hadamard Sector Isolation (𝔅₅–𝔅₇)
    (kleinAlpha P (kleinBeta Φ X) = kleinBeta Φ (kleinAlpha P X) ∧
      walshHadamardPP P Φ X + walshHadamardPM P Φ X +
        walshHadamardMP P Φ X + walshHadamardMM P Φ X = (4 : ℤ) • X ∧
      walshHadamardPP P Φ V = (4 : ℤ) • V ∧
      walshHadamardPM P Φ Sig = (4 : ℤ) • Sig ∧
      walshHadamardMP P Φ Φ = (4 : ℤ) • Φ ∧
      walshHadamardMM P Φ J = (4 : ℤ) • J) := by
  intro V Sig Φ J
  have hW13 := stage_W1_W2_W3_hyperplane_pythagorean_and_bivector_transmutation
    (R := ℝ) hP A C c s
  have hW46 := stage_W4_W5_W6_infinitesimal_and_polynomial_wilson_loop_light_cone
    (R := ℝ) hP A C c s t
  have hW7 := stage_W7_trigonometric_berry_rotor_and_wick_transmutation hP A C θ
  have hB14 := stage_B1_to_B4_sum_diff_crossover_and_combined_throat_commutator hP W A C
  have hV' : V = 1 := hV
  have hPhiSq : Φ * Φ = 1 := by
    have h1 : Φ * Φ = V := by dsimp [Φ, V]; peirce_nf hP
    rw [h1, hV']
  have hSPhi : invS P * Φ = -(Φ * invS P) := by dsimp [Φ]; peirce_nf hP
  have hB5 := stage_B5_klein_four_superoperator_commutativity_and_endogenous_throat_seam
    hP hPhiSq hSPhi hV X
  have hB7 := stage_B7_walsh_hadamard_projector_resolution_and_sector_isolation
    hP hPhiSq hSPhi hV X
  refine ⟨⟨BerryWilsonLoopCausalStage.causalEdge_acyclic,
    KleinBottleSeamConnectionStage.causalEdge_acyclic,
    SupergradedMoebiusTetraktysKleinStratum.coverEdge_acyclic⟩,
    ⟨hW13.1.2.2.2.2.2.2.1, hW46.2.1.2.2.1, hW7.1.1, hW7.2.1.2.1⟩,
    ⟨hB14.2.1.1, hB14.2.2.2⟩,
    ⟨hB5.1.2.2.2.1.trans hB5.1.2.2.2.2.1.symm,
     hB7.2.1,
     hB7.2.2.2.1,
     hB7.2.2.2.2.2.2.2.1,
     hB7.2.2.2.2.2.2.2.2.2.2.2.1,
     hB7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩⟩

end InfoGeometry.Canonical.KleinBottleV4SeamSumDifferenceWalshHadamardPoset
