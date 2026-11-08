/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.OntologyRing
import InfoGeometry.OperatorAlgebra.PeirceSpine.GravitoElectromagneticBridge
import InfoGeometry.Meta.Architecture
import InfoGeometry.OperatorAlgebra.PeirceSpine.Homogenized
import InfoGeometry.OperatorAlgebra.PeirceSpine.KleinAction
import InfoGeometry.OperatorAlgebra.PeirceSpine.TetraktysKleinActionBridge
import InfoGeometry.Canonical.CausalHyperplaneBerryHolonomy
import InfoGeometry.Canonical.AnalyticOntologyTaxonomyPhylogenesisPoset

/-!
# Two-Sheeted Klein Bottle Seam, `V₄ = ℤ₂ × ℤ₂` Character Decomposition, & Sum–Difference Connection Crossover Poset (`𝔅₁ ≺ 𝔅₂ ≺ ⋯ ≺ 𝔅₇`)

This canonical module formalizes the 7-stage acyclic causal poset
(`KleinBottleSeamConnectionStage`, `𝔅₁ ≺ 𝔅₂ ≺ ⋯ ≺ 𝔅₇`) governing the geometry of
two-sheeted Peirce operator rings (`1 = P + (1 - P)`), the single-sheet blindness
aporia on off-diagonal bimodule throat operators (`N₊, N₋`), the sum and difference
sheet connections (`Γ_sum = ∇₊ + ∇₋`, `Γ_diff = ∇₊ - ∇₋`), the universal fourfold
sum–difference transport crossover on `(Φ, J)`, endogenous DeWitt/Gramian spin-connection
frame dragging (`[Σ, Φ] = {V, J} = 2 V J`), the Klein four-group `V₄ = {id, α, β, γ}`
adjoint superoperator closure from Clifford carrier anticommutation (`U S_P = -S_P U`),
the fourfold `V₄` character classification `(χ₊₊, χ₊₋, χ₋₊, χ₋₋)`, and the scaled
Walsh–Hadamard four-sector projector resolution (`P_{++}, P_{+-}, P_{-+}, P_{--}`).

## Owner Reuse Architecture (`AGENTS.md` Compliant)

This module directly imports and reuses:
- `InfoGeometry.OperatorAlgebra.PeirceSpine` (`Homogenized.lean`):
  `sheetPlusConnection`, `sheetMinusConnection`, `sheetConnectionSum`,
  `sheetConnectionDiff`, `sheetConnection_sum_difference_crossover`,
  `conePlus`, `coneMinus`, `genPhi`, `genJ`, `genV`, `genSig`, `invS`, `comm`, `anticomm`,
- `InfoGeometry.OperatorAlgebra.PeirceSpine` (`UnitSquareAction.lean`, `KleinAction.lean`,
  `TetraktysKleinActionBridge.lean`):
  `squareOneConj`, `phiUnitSquareEquiv`, `kleinHom`, `peirceKleinHom`,
  `tetraktys_sandwich_channels_are_peirce_klein_action`,
- `InfoGeometry.Canonical.CausalHyperplaneBerryHolonomy`:
  `peirce_sum_difference_transport_crossover`, `innerConjugation_v4_relations`,
- `InfoGeometry.Canonical.AnalyticOntologyTaxonomyPhylogenesisPoset`:
  `RepDepth`, `OntologyMetaLevel`.
-/

namespace InfoGeometry.Canonical.KleinBottleSeamSumDifferenceConnectionPoset

open InfoGeometry.OperatorAlgebra.OntologyRing
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Meta
open InfoGeometry.Canonical.AnalyticOntologyTaxonomyPhylogenesisPoset

/-! ===========================================================================
    Section 0: The 7-Stage Klein Bottle Seam & Sum–Difference Connection
    Causal Poset (`𝔅₁ ≺ 𝔅₂ ≺ ⋯ ≺ 𝔅₇`)
    =========================================================================== -/

/-- The 7-stage causal poset `𝔅₁ ≺ 𝔅₂ ≺ ⋯ ≺ 𝔅₇` of two-sheeted Peirce connections,
universal sum–difference transport crossover, Klein four-group seam reflection, and
Walsh–Hadamard character projector resolution. -/
inductive KleinBottleSeamConnectionStage : Type
  | B1_PeirceDeWittTwoSheetSplitAndBimoduleThroat
  | B2_SumAndDifferenceSheetConnections
  | B3_UniversalSumDifferenceTransportCrossover
  | B4_EndogenousGramianConnectionsAndSpinFrameDragging
  | B5_KleinFourSeamReflectionAndAdjointCommutativity
  | B6_FourfoldV4CharacterEigenClassification
  | B7_WalshHadamardProjectorResolutionAndKleinMonodromy
  deriving DecidableEq, Repr, Inhabited

namespace KleinBottleSeamConnectionStage

/-- Numerical rank `0..6` of each stage `𝔅₁ .. 𝔅₇`. -/
def rank : KleinBottleSeamConnectionStage → ℕ
  | .B1_PeirceDeWittTwoSheetSplitAndBimoduleThroat => 0
  | .B2_SumAndDifferenceSheetConnections => 1
  | .B3_UniversalSumDifferenceTransportCrossover => 2
  | .B4_EndogenousGramianConnectionsAndSpinFrameDragging => 3
  | .B5_KleinFourSeamReflectionAndAdjointCommutativity => 4
  | .B6_FourfoldV4CharacterEigenClassification => 5
  | .B7_WalshHadamardProjectorResolutionAndKleinMonodromy => 6

/-- Partial inverse of `rank`. -/
def ofRank? : ℕ → Option KleinBottleSeamConnectionStage
  | 0 => some .B1_PeirceDeWittTwoSheetSplitAndBimoduleThroat
  | 1 => some .B2_SumAndDifferenceSheetConnections
  | 2 => some .B3_UniversalSumDifferenceTransportCrossover
  | 3 => some .B4_EndogenousGramianConnectionsAndSpinFrameDragging
  | 4 => some .B5_KleinFourSeamReflectionAndAdjointCommutativity
  | 5 => some .B6_FourfoldV4CharacterEigenClassification
  | 6 => some .B7_WalshHadamardProjectorResolutionAndKleinMonodromy
  | _ => none

@[simp]
theorem ofRank?_rank (s : KleinBottleSeamConnectionStage) : ofRank? (rank s) = some s := by
  cases s <;> rfl

theorem rank_inj {a b : KleinBottleSeamConnectionStage} (h : rank a = rank b) : a = b := by
  have h' : ofRank? (rank a) = ofRank? (rank b) := congrArg ofRank? h
  simpa using h'

instance : LinearOrder KleinBottleSeamConnectionStage :=
  LinearOrder.lift' rank (fun _ _ => rank_inj)

instance : Fintype KleinBottleSeamConnectionStage where
  elems := {
    .B1_PeirceDeWittTwoSheetSplitAndBimoduleThroat,
    .B2_SumAndDifferenceSheetConnections,
    .B3_UniversalSumDifferenceTransportCrossover,
    .B4_EndogenousGramianConnectionsAndSpinFrameDragging,
    .B5_KleinFourSeamReflectionAndAdjointCommutativity,
    .B6_FourfoldV4CharacterEigenClassification,
    .B7_WalshHadamardProjectorResolutionAndKleinMonodromy
  }
  complete := by
    intro s
    cases s <;> simp

theorem card_eq_seven : Fintype.card KleinBottleSeamConnectionStage = 7 := rfl

/-- Immediate covering edge `𝔅ᵢ ≺ 𝔅ᵢ₊₁` in the 7-stage Klein bottle seam poset. -/
def causalEdge (a b : KleinBottleSeamConnectionStage) : Prop :=
  rank b = rank a + 1

theorem causalEdge_strict {a b : KleinBottleSeamConnectionStage} (h : causalEdge a b) :
    rank a < rank b := by
  unfold causalEdge at h
  omega

theorem transGen_causalEdge_strict {a b : KleinBottleSeamConnectionStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_strict hab
  | tail _ hbc ih =>
      have hlt : rank _ < rank _ := causalEdge_strict hbc
      omega

/-- **Strict DAG Acyclicity (`causalEdge_acyclic`)**:
No stage in `KleinBottleSeamConnectionStage` has a directed cycle under `causalEdge`. -/
theorem causalEdge_acyclic (s : KleinBottleSeamConnectionStage) :
    ¬ Relation.TransGen causalEdge s s := by
  intro h
  have hlt := transGen_causalEdge_strict h
  exact Nat.lt_irrefl (rank s) hlt

/-- Strict 7-stage linear chain `𝔅₁ < 𝔅₂ < 𝔅₃ < 𝔅₄ < 𝔅₅ < 𝔅₆ < 𝔅₇`. -/
theorem strict_seven_stage_chain :
    B1_PeirceDeWittTwoSheetSplitAndBimoduleThroat < B2_SumAndDifferenceSheetConnections ∧
    B2_SumAndDifferenceSheetConnections < B3_UniversalSumDifferenceTransportCrossover ∧
    B3_UniversalSumDifferenceTransportCrossover <
      B4_EndogenousGramianConnectionsAndSpinFrameDragging ∧
    B4_EndogenousGramianConnectionsAndSpinFrameDragging <
      B5_KleinFourSeamReflectionAndAdjointCommutativity ∧
    B5_KleinFourSeamReflectionAndAdjointCommutativity <
      B6_FourfoldV4CharacterEigenClassification ∧
    B6_FourfoldV4CharacterEigenClassification <
      B7_WalshHadamardProjectorResolutionAndKleinMonodromy := by
  decide

/-- Monotone projection to `RepDepth`. -/
def toRepDepth : KleinBottleSeamConnectionStage → RepDepth
  | .B1_PeirceDeWittTwoSheetSplitAndBimoduleThroat => .projective
  | .B2_SumAndDifferenceSheetConnections => .operator
  | .B3_UniversalSumDifferenceTransportCrossover => .operator
  | .B4_EndogenousGramianConnectionsAndSpinFrameDragging => .krein
  | .B5_KleinFourSeamReflectionAndAdjointCommutativity => .transport
  | .B6_FourfoldV4CharacterEigenClassification => .transport
  | .B7_WalshHadamardProjectorResolutionAndKleinMonodromy => .thermo

theorem toRepDepth_rank_monotone {a b : KleinBottleSeamConnectionStage} (hab : a ≤ b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  change rank a ≤ rank b at hab
  cases a <;> cases b <;>
    revert hab <;>
    unfold toRepDepth RepDepth.toNat <;>
    decide

/-- Monotone projection to `OntologyMetaLevel`. -/
def toOntologyMetaLevel : KleinBottleSeamConnectionStage → OntologyMetaLevel
  | .B1_PeirceDeWittTwoSheetSplitAndBimoduleThroat => .M1_ProjectorClabject
  | .B2_SumAndDifferenceSheetConnections => .M1_ProjectorClabject
  | .B3_UniversalSumDifferenceTransportCrossover => .M2_GrassmannianPowertypeOrbit
  | .B4_EndogenousGramianConnectionsAndSpinFrameDragging => .M2_GrassmannianPowertypeOrbit
  | .B5_KleinFourSeamReflectionAndAdjointCommutativity => .M2_GrassmannianPowertypeOrbit
  | .B6_FourfoldV4CharacterEigenClassification => .M3_ErlangenCasimirMetaLaw
  | .B7_WalshHadamardProjectorResolutionAndKleinMonodromy => .M3_ErlangenCasimirMetaLaw

theorem toOntologyMetaLevel_rank_monotone {a b : KleinBottleSeamConnectionStage} (hab : a ≤ b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  change rank a ≤ rank b at hab
  cases a <;> cases b <;>
    revert hab <;>
    unfold toOntologyMetaLevel OntologyMetaLevel.rank <;>
    decide

end KleinBottleSeamConnectionStage

/-! ===========================================================================
    Section 1: Stage `𝔅₁` — Peirce–DeWitt Two-Sheet Split, Bimodule Throat
    (`N₊, N₋`), and Rung 0 Single-Sheet Blindness Aporia
    =========================================================================== -/

section StageB1ToB4

variable {B : Type*} [Ring B]
variable {P : B} (hP : P * P = P)
include hP

/-- **Stage `𝔅₁` Theorem (`single_sheet_blindness_aporia`)**:
In any associative ring `[Ring B]` with idempotent `P * P = P`:
1. **Two-Sheet Orthogonal Split**: `(1 : B) = P + (1 - P)` and the upper/lower sheet
   connections `∇₊ = sheetPlusConnection P W₁ = P W₁ P` and
   `∇₋ = sheetMinusConnection P W₂ = (1 - P) W₂ (1 - P)` are mutually orthogonal:
   `∇₊ * ∇₋ = 0` and `∇₋ * ∇₊ = 0`,
2. **Rung 0 Single-Sheet Blindness on Throat Operators `N₊ = P A (1 - P)` and `N₋ = (1 - P) C P`**:
   * `N₊ * ∇₊ = 0` (`∇₊` is right-blind on `N₊`),
   * `∇₋ * N₊ = 0` (`∇₋` is left-blind on `N₊`),
   * `∇₊ * N₋ = 0` (`∇₊` is left-blind on `N₋`),
   * `N₋ * ∇₋ = 0` (`∇₋` is right-blind on `N₋`),
3. **Failure of Single-Sheet Two-Sided Brackets**:
   * `[∇₊, N₊] = {∇₊, N₊} = ∇₊ * N₊` (cannot sense the right foot of `N₊`),
   * `[∇₋, N₊] = -{∇₋, N₊} = -(N₊ * ∇₋)` (cannot sense the left foot of `N₊`). -/
theorem single_sheet_blindness_aporia (W W₂ A C : B) :
    ((1 : B) = P + (1 - P) ∧
     sheetPlusConnection P W * sheetMinusConnection P W₂ = 0 ∧
     sheetMinusConnection P W₂ * sheetPlusConnection P W = 0) ∧
    (conePlus P A * sheetPlusConnection P W = 0 ∧
     sheetMinusConnection P W * conePlus P A = 0 ∧
     sheetPlusConnection P W * coneMinus P C = 0 ∧
     coneMinus P C * sheetMinusConnection P W = 0) ∧
    (comm (sheetPlusConnection P W) (conePlus P A) =
       sheetPlusConnection P W * conePlus P A ∧
     anticomm (sheetPlusConnection P W) (conePlus P A) =
       sheetPlusConnection P W * conePlus P A ∧
     comm (sheetMinusConnection P W) (conePlus P A) =
       -(conePlus P A * sheetMinusConnection P W) ∧
     anticomm (sheetMinusConnection P W) (conePlus P A) =
       conePlus P A * sheetMinusConnection P W) := by
  refine ⟨⟨by noncomm_ring, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;>
    ((try dsimp only [sheetPlusConnection, sheetMinusConnection]); peirce_nf hP)

/-! ===========================================================================
    Section 2: Stage `𝔅₂` — Sum & Difference Sheet Connections
    (`Γ_sum = ∇₊ + ∇₋`, `Γ_diff = ∇₊ - ∇₋`), Chiral Duality, Bimodule Separation,
    and Squared Curvature Split (`∇₊² ± ∇₋²`)
    =========================================================================== -/

/-- **Stage `𝔅₂` Theorem (`sum_difference_chiral_duality_and_squared_split`)**:
For any connection seed `W : B`, the sum connection `Γ_sum = sheetConnectionSum P W = ∇₊ + ∇₋`
and difference connection `Γ_diff = sheetConnectionDiff P W = ∇₊ - ∇₋` satisfy:
1. **Chiral Duality via `S_P = invS P = 2P - 1`**:
   * `S_P * Γ_sum = Γ_diff` and `Γ_sum * S_P = Γ_diff`,
   * `S_P * Γ_diff = Γ_sum` and `Γ_diff * S_P = Γ_sum`,
2. **Rung 1 Bimodule Left/Right Foot Separation on `N₊`**:
   * `Γ_sum * N₊ = ∇₊ * N₊` and `N₊ * Γ_sum = N₊ * ∇₋`,
   * `Γ_diff * N₊ = ∇₊ * N₊` and `N₊ * Γ_diff = -(N₊ * ∇₋)`,
   * `[Γ_sum, N₊] = {Γ_diff, N₊} = ∇₊ * N₊ - N₊ * ∇₋`,
   * `{Γ_sum, N₊} = [Γ_diff, N₊] = ∇₊ * N₊ + N₊ * ∇₋`,
3. **Rung 3 DeWitt Squared Split & Curvature Asymmetry (`∇₊² ± ∇₋²`)**:
   * `Γ_sum² = ∇₊² + ∇₋²` and `Γ_diff² = ∇₊² + ∇₋²` (`Γ_sum² = Γ_diff²`),
   * `Γ_sum * Γ_diff = ∇₊² - ∇₋²` and `S_P * Γ_sum² = ∇₊² - ∇₋²`. -/
theorem sum_difference_chiral_duality_and_squared_split (W A : B) :
    (invS P * sheetConnectionSum P W = sheetConnectionDiff P W ∧
     sheetConnectionSum P W * invS P = sheetConnectionDiff P W ∧
     invS P * sheetConnectionDiff P W = sheetConnectionSum P W ∧
     sheetConnectionDiff P W * invS P = sheetConnectionSum P W) ∧
    (sheetConnectionSum P W * conePlus P A = sheetPlusConnection P W * conePlus P A ∧
     conePlus P A * sheetConnectionSum P W = conePlus P A * sheetMinusConnection P W ∧
     sheetConnectionDiff P W * conePlus P A = sheetPlusConnection P W * conePlus P A ∧
     conePlus P A * sheetConnectionDiff P W = -(conePlus P A * sheetMinusConnection P W) ∧
     comm (sheetConnectionSum P W) (conePlus P A) =
       anticomm (sheetConnectionDiff P W) (conePlus P A) ∧
     anticomm (sheetConnectionSum P W) (conePlus P A) =
       comm (sheetConnectionDiff P W) (conePlus P A)) ∧
    (sheetConnectionSum P W * sheetConnectionSum P W =
       sheetPlusConnection P W * sheetPlusConnection P W +
         sheetMinusConnection P W * sheetMinusConnection P W ∧
     sheetConnectionDiff P W * sheetConnectionDiff P W =
       sheetPlusConnection P W * sheetPlusConnection P W +
         sheetMinusConnection P W * sheetMinusConnection P W ∧
     sheetConnectionSum P W * sheetConnectionDiff P W =
       sheetPlusConnection P W * sheetPlusConnection P W -
         sheetMinusConnection P W * sheetMinusConnection P W ∧
     invS P * (sheetConnectionSum P W * sheetConnectionSum P W) =
       sheetPlusConnection P W * sheetPlusConnection P W -
         sheetMinusConnection P W * sheetMinusConnection P W) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;>
    ((try dsimp only [sheetConnectionSum, sheetConnectionDiff,
       sheetPlusConnection, sheetMinusConnection]);
     peirce_nf hP)

/-! ===========================================================================
    Section 3: Stage `𝔅₃` — Universal Sum–Difference Transport Crossover Theorem
    (`[Γ_diff, Φ] = {Γ_sum, J}`, `{Γ_diff, Φ} = [Γ_sum, J]`,
     `[Γ_diff, J] = {Γ_sum, Φ}`, `{Γ_diff, J} = [Γ_sum, Φ]`)
    =========================================================================== -/

/-- **Stage `𝔅₃` Theorem (`universal_sum_difference_crossover_theorem`)**:
Reuses `sheetConnection_sum_difference_crossover` from `Homogenized.lean` and proves the
complete fourfold commutator/anticommutator crossover between `(Γ_diff, Γ_sum)` and
the throat pair `(Φ = N₊ + N₋, J = N₊ - N₋)` together with their explicit two-sheet
bimodule expansions:
1. `[Γ_diff, Φ] = {Γ_sum, J} = (∇₊ N₊ + N₊ ∇₋) - (∇₋ N₋ + N₋ ∇₊)`,
2. `{Γ_diff, Φ} = [Γ_sum, J] = (∇₊ N₊ - N₊ ∇₋) - (∇₋ N₋ - N₋ ∇₊)`,
3. `[Γ_diff, J] = {Γ_sum, Φ} = (∇₊ N₊ + N₊ ∇₋) + (∇₋ N₋ + N₋ ∇₊)`,
4. `{Γ_diff, J} = [Γ_sum, Φ] = (∇₊ N₊ - N₊ ∇₋) + (∇₋ N₋ - N₋ ∇₊)`. -/
theorem universal_sum_difference_crossover_theorem (W A C : B) :
    (comm (sheetConnectionDiff P W) (genPhi P A C) =
       anticomm (sheetConnectionSum P W) (genJ P A C) ∧
     comm (sheetConnectionDiff P W) (genPhi P A C) =
       (sheetPlusConnection P W * conePlus P A + conePlus P A * sheetMinusConnection P W) -
         (sheetMinusConnection P W * coneMinus P C + coneMinus P C * sheetPlusConnection P W)) ∧
    (anticomm (sheetConnectionDiff P W) (genPhi P A C) =
       comm (sheetConnectionSum P W) (genJ P A C) ∧
     anticomm (sheetConnectionDiff P W) (genPhi P A C) =
       (sheetPlusConnection P W * conePlus P A - conePlus P A * sheetMinusConnection P W) -
         (sheetMinusConnection P W * coneMinus P C - coneMinus P C * sheetPlusConnection P W)) ∧
    (comm (sheetConnectionDiff P W) (genJ P A C) =
       anticomm (sheetConnectionSum P W) (genPhi P A C) ∧
     comm (sheetConnectionDiff P W) (genJ P A C) =
       (sheetPlusConnection P W * conePlus P A + conePlus P A * sheetMinusConnection P W) +
         (sheetMinusConnection P W * coneMinus P C + coneMinus P C * sheetPlusConnection P W)) ∧
    (anticomm (sheetConnectionDiff P W) (genJ P A C) =
       comm (sheetConnectionSum P W) (genPhi P A C) ∧
     anticomm (sheetConnectionDiff P W) (genJ P A C) =
       (sheetPlusConnection P W * conePlus P A - conePlus P A * sheetMinusConnection P W) +
         (sheetMinusConnection P W * coneMinus P C - coneMinus P C * sheetPlusConnection P W)) := by
  have hCross := sheetConnection_sum_difference_crossover hP W A C
  refine ⟨⟨hCross.1, ?_⟩, ⟨hCross.2.1, ?_⟩, ⟨hCross.2.2.1, ?_⟩, ⟨hCross.2.2.2, ?_⟩⟩ <;>
    ((try dsimp only [sheetConnectionDiff, sheetConnectionSum,
       sheetPlusConnection, sheetMinusConnection]);
     peirce_nf hP)

/-! ===========================================================================
    Section 4: Stage `𝔅₄` — Endogenous Gramian Connections (`Q₊ = N₊ N₋`, `Q₋ = N₋ N₊`)
    and Spin-Connection Frame Dragging (`[Σ, Φ] = {V, J} = 2 V J`)
    =========================================================================== -/

/-- **Stage `𝔅₄` Theorem (`endogenous_dewitt_gramian_spin_frame_dragging`)**:
When the connection seed is the endogenous DeWitt/Casimir metric `W = V = genV P A C`:
1. **Endogenous Sheet Connections**:
   * `sheetPlusConnection P (genV P A C) = conePlus P A * coneMinus P C` (`Q₊ = N₊ N₋`),
   * `sheetMinusConnection P (genV P A C) = coneMinus P C * conePlus P A` (`Q₋ = N₋ N₊`),
   * `sheetConnectionSum P (genV P A C) = genV P A C` (`Γ_sum = V`),
   * `sheetConnectionDiff P (genV P A C) = genSig P A C` (`Γ_diff = Σ`),
2. **Active Spin-Connection Frame Dragging (`Σ`) vs. Passive Metric Commutativity (`V`)**:
   * `[Σ, Φ] = {V, J} = (2 : ℤ) • (V * J)`,
   * `[Σ, J] = {V, Φ} = (2 : ℤ) • (V * Φ)`,
   * `{Σ, Φ} = [V, J] = 0`,
   * `{Σ, J} = [V, Φ] = 0`. -/
theorem endogenous_dewitt_gramian_spin_frame_dragging (A C : B) :
    (sheetPlusConnection P (genV P A C) = conePlus P A * coneMinus P C ∧
     sheetMinusConnection P (genV P A C) = coneMinus P C * conePlus P A ∧
     sheetConnectionSum P (genV P A C) = genV P A C ∧
     sheetConnectionDiff P (genV P A C) = genSig P A C) ∧
    (comm (genSig P A C) (genPhi P A C) = anticomm (genV P A C) (genJ P A C) ∧
     comm (genSig P A C) (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C) ∧
     comm (genSig P A C) (genJ P A C) = anticomm (genV P A C) (genPhi P A C) ∧
     comm (genSig P A C) (genJ P A C) = (2 : ℤ) • (genV P A C * genPhi P A C) ∧
     anticomm (genSig P A C) (genPhi P A C) = comm (genV P A C) (genJ P A C) ∧
     comm (genV P A C) (genJ P A C) = 0 ∧
     anticomm (genSig P A C) (genJ P A C) = comm (genV P A C) (genPhi P A C) ∧
     comm (genV P A C) (genPhi P A C) = 0) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩,
          ⟨?_, gemFirstOrderLenseThirring hP A C,
           ?_, gemDualPrecession hP A C,
           ?_, ?_, ?_, ?_⟩⟩ <;>
    ((try dsimp only [sheetConnectionSum, sheetConnectionDiff,
       sheetPlusConnection, sheetMinusConnection]);
     peirce_nf hP)

end StageB1ToB4

/-! ===========================================================================
    Section 5: Stage `𝔅₅` — Klein Four-Group Seam Reflection (`V₄ = {id, α, β, γ}`)
    and Adjoint Commutativity from Clifford Anticommutation (`U S_P = -S_P U`)
    =========================================================================== -/

section StageB5ToB7

variable {B : Type*} [Ring B]

/-- The chiral parity superoperator `α(X) := S_P X S_P`. -/
def kleinAlpha (P X : B) : B := invS P * X * invS P

/-- The sheet-reflection / seam-exchange superoperator `β(X) := U X U`. -/
def kleinBeta (U X : B) : B := U * X * U

/-- The Klein bottle glide-reflection / diagonal monodromy superoperator
`γ(X) := (S_P U) X (U S_P)`. -/
def kleinGamma (P U X : B) : B := (invS P * U) * X * (U * invS P)

/-- **Stage `𝔅₅` Theorem (`seam_reflection_v4_klein_group_closure`)**:
Let `P : B` be an idempotent (`P * P = P`) and `U : B` be a seam-reflection involution
(`U * U = 1` and `U * P * U = 1 - P`):
1. **Carrier-Level Clifford / Dihedral Anticommutation**:
   * `U * invS P * U = -invS P`,
   * `U * invS P = -(invS P * U)` (`{U, S_P} = 0`),
   * `(invS P * U) * (invS P * U) = -1` and `(U * invS P) * (U * invS P) = -1`
     (at the carrier level, `S_P U` has order 4 and squares to `-1`),
2. **Superoperator-Level Klein Four-Group `V₄ = ℤ₂ × ℤ₂` Closure**:
   Because the minus sign `U S_P = -S_P U` occurs on both sides of `X` in `U (S_P X S_P) U`,
   `(-1) * (-1) = +1` cancels and the adjoint superoperators commute:
   * `kleinAlpha P (kleinAlpha P X) = X`,
   * `kleinBeta U (kleinBeta U X) = X`,
   * `kleinAlpha P (kleinBeta U X) = kleinGamma P U X`,
   * `kleinBeta U (kleinAlpha P X) = kleinGamma P U X`,
   * `kleinAlpha P (kleinBeta U X) = kleinBeta U (kleinAlpha P X)`,
   * `kleinGamma P U (kleinGamma P U X) = X`. -/
theorem seam_reflection_v4_klein_group_closure
    {P U : B} (hP : P * P = P) (hU2 : U * U = 1) (hUP : U * P * U = 1 - P) (X : B) :
    (U * invS P * U = -invS P ∧
     U * invS P = -(invS P * U) ∧
     (invS P * U) * (invS P * U) = -1 ∧
     (U * invS P) * (U * invS P) = -1) ∧
    (kleinAlpha P (kleinAlpha P X) = X ∧
     kleinBeta U (kleinBeta U X) = X ∧
     kleinAlpha P (kleinBeta U X) = kleinGamma P U X ∧
     kleinBeta U (kleinAlpha P X) = kleinGamma P U X ∧
     kleinAlpha P (kleinBeta U X) = kleinBeta U (kleinAlpha P X) ∧
     kleinGamma P U (kleinGamma P U X) = X) := by
  have hS2 : invS P * invS P = 1 := by peirce_nf hP
  have hUS : U * invS P * U = -invS P := by
    unfold invS
    calc
      U * (P - (1 - P)) * U = U * P * U - U * (1 - P) * U := by noncomm_ring
      _ = (1 - P) - P := by
        rw [hUP]
        have hcomp : U * (1 - P) * U = P := by
          calc
            U * (1 - P) * U = U * U - U * P * U := by noncomm_ring
            _ = 1 - (1 - P) := by rw [hU2, hUP]
            _ = P := by abel
        rw [hcomp]
      _ = -(P - (1 - P)) := by abel
  have hAnti : U * invS P = -(invS P * U) := by
    calc
      U * invS P = (U * invS P * U) * U := by
        rw [mul_assoc (U * invS P) U, hU2, mul_one]
      _ = (-invS P) * U := by rw [hUS]
      _ = -(invS P * U) := by noncomm_ring
  have hAnti' : invS P * U = -(U * invS P) := by
    rw [hAnti, neg_neg]
  have hSU2 : (invS P * U) * (invS P * U) = -1 := by
    calc
      (invS P * U) * (invS P * U) = invS P * (U * invS P) * U := by noncomm_ring
      _ = invS P * (-(invS P * U)) * U := by rw [hAnti]
      _ = -((invS P * invS P) * (U * U)) := by noncomm_ring
      _ = -1 := by rw [hS2, hU2, mul_one]
  have hUS2 : (U * invS P) * (U * invS P) = -1 := by
    rw [hAnti, neg_mul, mul_neg, neg_neg, hSU2]
  have hV4 :=
    InfoGeometry.Canonical.CausalHyperplaneBerryHolonomy.innerConjugation_v4_relations
      (invS P) U hS2 hU2 hAnti'
  have hAB : kleinAlpha P (kleinBeta U X) = kleinGamma P U X := by
    unfold kleinAlpha kleinBeta kleinGamma
    noncomm_ring
  have hBA : kleinBeta U (kleinAlpha P X) = kleinGamma P U X := by
    rw [← hAB]
    exact (hV4.2.2.1 X).symm
  refine ⟨⟨hUS, hAnti, hSU2, hUS2⟩,
          ⟨hV4.1 X, hV4.2.1 X, hAB, hBA, hV4.2.2.1 X, hV4.2.2.2 X⟩⟩

/-- **Unit-Horizon Specialization to `peirceKleinHom` and Tetraktys Sandwich Channels
(`unit_horizon_phi_realizes_seam_reflection_and_peirce_klein_action`)**:
When `genV P A C = 1`, the solder bridge `U = genPhi P A C` automatically satisfies all
seam-reflection hypotheses (`Φ² = 1`, `Φ P Φ = 1 - P`, `Φ N₊ Φ = N₋`, `Φ N₋ Φ = N₊`,
and `Φ (sheetPlusConnection P V) Φ = sheetMinusConnection P V`), and `(id, α, β, γ)`
coincide with `tetraktys_sandwich_channels_are_peirce_klein_action` (`grpId, grpSig, grpPhi, grpJ`)
and `peirceKleinHom`. -/
theorem unit_horizon_phi_realizes_seam_reflection_and_peirce_klein_action
    {P : B} (hP : P * P = P) (A C : B) (hV : genV P A C = 1) (X : B) :
    (genPhi P A C * genPhi P A C = 1 ∧
     genPhi P A C * P * genPhi P A C = 1 - P ∧
     genPhi P A C * conePlus P A * genPhi P A C = coneMinus P C ∧
     genPhi P A C * coneMinus P C * genPhi P A C = conePlus P A ∧
     genPhi P A C * sheetPlusConnection P (genV P A C) * genPhi P A C =
       sheetMinusConnection P (genV P A C)) ∧
    (grpId P A C X = X ∧
     grpSig P A C X = kleinAlpha P X ∧
     grpPhi P A C X = kleinBeta (genPhi P A C) X ∧
     grpJ P A C X = kleinGamma P (genPhi P A C) X) := by
  have hPhi2 : genPhi P A C * genPhi P A C = 1 := by
    calc
      genPhi P A C * genPhi P A C = genV P A C := by peirce_nf hP
      _ = 1 := hV
  have hPhiP : genPhi P A C * P * genPhi P A C = 1 - P := by
    calc
      genPhi P A C * P * genPhi P A C = genV P A C * (1 - P) := by peirce_nf hP
      _ = 1 - P := by rw [hV, one_mul]
  have hPhiNp : genPhi P A C * conePlus P A * genPhi P A C = coneMinus P C := by
    calc
      genPhi P A C * conePlus P A * genPhi P A C = genV P A C * coneMinus P C := by peirce_nf hP
      _ = coneMinus P C := by rw [hV, one_mul]
  have hPhiNm : genPhi P A C * coneMinus P C * genPhi P A C = conePlus P A := by
    calc
      genPhi P A C * coneMinus P C * genPhi P A C = genV P A C * conePlus P A := by peirce_nf hP
      _ = conePlus P A := by rw [hV, one_mul]
  have hPhiSheet :
      genPhi P A C * sheetPlusConnection P (genV P A C) * genPhi P A C =
        sheetMinusConnection P (genV P A C) := by
    unfold sheetPlusConnection sheetMinusConnection
    calc
      genPhi P A C * (P * genV P A C * P) * genPhi P A C =
        (genV P A C * genV P A C) * (1 - P) := by peirce_nf hP
      _ = (1 - P) * genV P A C * (1 - P) := by
        rw [hV]
        peirce_nf hP
  have hTet := tetraktys_sandwich_channels_are_peirce_klein_action hP A C hV X
  have hV4 := seam_reflection_v4_klein_group_closure hP hPhi2 hPhiP X
  have hGrpSig : grpSig P A C X = kleinAlpha P X := hTet.2.2.2
  have hGrpPhi : grpPhi P A C X = kleinBeta (genPhi P A C) X := hTet.2.1
  have hGrpJ : grpJ P A C X = kleinGamma P (genPhi P A C) X := by
    rw [hTet.2.2.1]
    exact hV4.2.2.2.2.1
  exact ⟨⟨hPhi2, hPhiP, hPhiNp, hPhiNm, hPhiSheet⟩,
         ⟨hTet.1, hGrpSig, hGrpPhi, hGrpJ⟩⟩

/-! ===========================================================================
    Section 6: Stage `𝔅₆` — Fourfold `V₄ = ℤ₂ × ℤ₂` Character Eigen-Classification
    (`χ₊₊, χ₊₋, χ₋₊, χ₋₋`) of `(Γ_sum, Γ_diff, Φ, J)` and `(V, Σ, Φ, J)`
    =========================================================================== -/

/-- **Stage `𝔅₆` Theorem (`v4_character_eigen_classification`)**:
Under `P * P = P`, `U * U = 1`, `U * P * U = 1 - P`, symmetric sheet seed exchange
`U * sheetPlusConnection P W * U = sheetMinusConnection P W`, and throat wing swap
`U * conePlus P A * U = coneMinus P C` and `U * coneMinus P C * U = conePlus P A`,
the four canonical operator sectors inhabit the four distinct irreducible 1D characters
`(ε₁, ε₂) ∈ {(±1, ±1)}` of `V₄ = ℤ₂ × ℤ₂`:
1. **`χ₊₊ = (+1, +1)` (Even, Seam-Symmetric — `Γ_sum` & `V`)**:
   * `α(Γ_sum) = +Γ_sum`, `β(Γ_sum) = +Γ_sum`, `γ(Γ_sum) = +Γ_sum`,
   * `α(V) = +V`, `β(V) = +V`, `γ(V) = +V`,
2. **`χ₊₋ = (+1, -1)` (Even, Seam-Antisymmetric — `Γ_diff` & `Σ`)**:
   * `α(Γ_diff) = +Γ_diff`, `β(Γ_diff) = -Γ_diff`, `γ(Γ_diff) = -Γ_diff`,
   * `α(Σ) = +Σ`, `β(Σ) = -Σ`, `γ(Σ) = -Σ`,
3. **`χ₋₊ = (-1, +1)` (Odd, Seam-Symmetric — Orientable Solder Bridge `Φ`)**:
   * `α(Φ) = -Φ`, `β(Φ) = +Φ`, `γ(Φ) = -Φ`,
4. **`χ₋₋ = (-1, -1)` (Odd, Seam-Antisymmetric — Non-Orientable Klein Bottle Seam Twist `J`)**:
   * `α(J) = -J`, `β(J) = -J`, `γ(J) = +J` (`J` is strictly invariant under the diagonal
     Klein glide-reflection `γ = α ∘ β`!). -/
theorem v4_character_eigen_classification
    {P U : B} (hP : P * P = P) (hU2 : U * U = 1) (hUP : U * P * U = 1 - P)
    (W A C : B)
    (hUW : U * sheetPlusConnection P W * U = sheetMinusConnection P W)
    (hUNp : U * conePlus P A * U = coneMinus P C)
    (hUNm : U * coneMinus P C * U = conePlus P A) :
    -- (1) χ₊₊ = (+1, +1): Γ_sum and V
    (kleinAlpha P (sheetConnectionSum P W) = sheetConnectionSum P W ∧
     kleinBeta U (sheetConnectionSum P W) = sheetConnectionSum P W ∧
     kleinGamma P U (sheetConnectionSum P W) = sheetConnectionSum P W ∧
     kleinAlpha P (genV P A C) = genV P A C ∧
     kleinBeta U (genV P A C) = genV P A C ∧
     kleinGamma P U (genV P A C) = genV P A C) ∧
    -- (2) χ₊₋ = (+1, -1): Γ_diff and Σ
    (kleinAlpha P (sheetConnectionDiff P W) = sheetConnectionDiff P W ∧
     kleinBeta U (sheetConnectionDiff P W) = -sheetConnectionDiff P W ∧
     kleinGamma P U (sheetConnectionDiff P W) = -sheetConnectionDiff P W ∧
     kleinAlpha P (genSig P A C) = genSig P A C ∧
     kleinBeta U (genSig P A C) = -genSig P A C ∧
     kleinGamma P U (genSig P A C) = -genSig P A C) ∧
    -- (3) χ₋₊ = (-1, +1): Φ
    (kleinAlpha P (genPhi P A C) = -genPhi P A C ∧
     kleinBeta U (genPhi P A C) = genPhi P A C ∧
     kleinGamma P U (genPhi P A C) = -genPhi P A C) ∧
    -- (4) χ₋₋ = (-1, -1): J
    (kleinAlpha P (genJ P A C) = -genJ P A C ∧
     kleinBeta U (genJ P A C) = -genJ P A C ∧
     kleinGamma P U (genJ P A C) = genJ P A C) := by
  have hUW_minus : U * sheetMinusConnection P W * U = sheetPlusConnection P W := by
    calc
      U * sheetMinusConnection P W * U = U * (U * sheetPlusConnection P W * U) * U := by
        rw [← hUW]
      _ = (U * U) * sheetPlusConnection P W * (U * U) := by noncomm_ring
      _ = sheetPlusConnection P W := by rw [hU2]; noncomm_ring
  have hAlphaSum : kleinAlpha P (sheetConnectionSum P W) = sheetConnectionSum P W := by
    unfold kleinAlpha sheetConnectionSum sheetPlusConnection sheetMinusConnection
    peirce_nf hP
  have hBetaSum : kleinBeta U (sheetConnectionSum P W) = sheetConnectionSum P W := by
    unfold kleinBeta sheetConnectionSum
    calc
      U * (sheetPlusConnection P W + sheetMinusConnection P W) * U =
        U * sheetPlusConnection P W * U + U * sheetMinusConnection P W * U := by noncomm_ring
      _ = sheetMinusConnection P W + sheetPlusConnection P W := by rw [hUW, hUW_minus]
      _ = sheetPlusConnection P W + sheetMinusConnection P W := by abel
  have hGammaSum : kleinGamma P U (sheetConnectionSum P W) = sheetConnectionSum P W := by
    have hV4 := seam_reflection_v4_klein_group_closure hP hU2 hUP (sheetConnectionSum P W)
    rw [← hV4.2.2.2.1, hBetaSum, hAlphaSum]
  have hU_NpNm : U * (conePlus P A * coneMinus P C) * U = coneMinus P C * conePlus P A := by
    calc
      U * (conePlus P A * coneMinus P C) * U =
        U * conePlus P A * (U * U) * coneMinus P C * U := by rw [hU2]; noncomm_ring
      _ = (U * conePlus P A * U) * (U * coneMinus P C * U) := by noncomm_ring
      _ = coneMinus P C * conePlus P A := by rw [hUNp, hUNm]
  have hU_NmNp : U * (coneMinus P C * conePlus P A) * U = conePlus P A * coneMinus P C := by
    calc
      U * (coneMinus P C * conePlus P A) * U =
        U * coneMinus P C * (U * U) * conePlus P A * U := by rw [hU2]; noncomm_ring
      _ = (U * coneMinus P C * U) * (U * conePlus P A * U) := by noncomm_ring
      _ = conePlus P A * coneMinus P C := by rw [hUNm, hUNp]
  have hAlphaV : kleinAlpha P (genV P A C) = genV P A C := by
    unfold kleinAlpha; peirce_nf hP
  have hBetaV : kleinBeta U (genV P A C) = genV P A C := by
    unfold kleinBeta genV
    calc
      U * (conePlus P A * coneMinus P C + coneMinus P C * conePlus P A) * U =
        U * (conePlus P A * coneMinus P C) * U + U * (coneMinus P C * conePlus P A) * U := by
        noncomm_ring
      _ = coneMinus P C * conePlus P A + conePlus P A * coneMinus P C := by
        rw [hU_NpNm, hU_NmNp]
      _ = conePlus P A * coneMinus P C + coneMinus P C * conePlus P A := by abel
  have hGammaV : kleinGamma P U (genV P A C) = genV P A C := by
    have hV4 := seam_reflection_v4_klein_group_closure hP hU2 hUP (genV P A C)
    rw [← hV4.2.2.2.1, hBetaV, hAlphaV]
  have hAlphaDiff : kleinAlpha P (sheetConnectionDiff P W) = sheetConnectionDiff P W := by
    unfold kleinAlpha sheetConnectionDiff sheetPlusConnection sheetMinusConnection
    peirce_nf hP
  have hBetaDiff : kleinBeta U (sheetConnectionDiff P W) = -sheetConnectionDiff P W := by
    unfold kleinBeta sheetConnectionDiff
    calc
      U * (sheetPlusConnection P W - sheetMinusConnection P W) * U =
        U * sheetPlusConnection P W * U - U * sheetMinusConnection P W * U := by noncomm_ring
      _ = sheetMinusConnection P W - sheetPlusConnection P W := by rw [hUW, hUW_minus]
      _ = -(sheetPlusConnection P W - sheetMinusConnection P W) := by abel
  have hGammaDiff : kleinGamma P U (sheetConnectionDiff P W) = -sheetConnectionDiff P W := by
    have hV4 := seam_reflection_v4_klein_group_closure hP hU2 hUP (sheetConnectionDiff P W)
    rw [← hV4.2.2.2.2.1, hAlphaDiff, hBetaDiff]
  have hAlphaSig : kleinAlpha P (genSig P A C) = genSig P A C := by
    unfold kleinAlpha; peirce_nf hP
  have hBetaSig : kleinBeta U (genSig P A C) = -genSig P A C := by
    unfold kleinBeta genSig OperatorAlgebra.PeirceSpine.comm
    calc
      U * (conePlus P A * coneMinus P C - coneMinus P C * conePlus P A) * U =
        U * (conePlus P A * coneMinus P C) * U - U * (coneMinus P C * conePlus P A) * U := by
        noncomm_ring
      _ = coneMinus P C * conePlus P A - conePlus P A * coneMinus P C := by
        rw [hU_NpNm, hU_NmNp]
      _ = -(conePlus P A * coneMinus P C - coneMinus P C * conePlus P A) := by abel
  have hGammaSig : kleinGamma P U (genSig P A C) = -genSig P A C := by
    have hV4 := seam_reflection_v4_klein_group_closure hP hU2 hUP (genSig P A C)
    rw [← hV4.2.2.2.2.1, hAlphaSig, hBetaSig]
  have hAlphaPhi : kleinAlpha P (genPhi P A C) = -genPhi P A C := by
    unfold kleinAlpha; peirce_nf hP
  have hBetaPhi : kleinBeta U (genPhi P A C) = genPhi P A C := by
    unfold kleinBeta genPhi
    calc
      U * (conePlus P A + coneMinus P C) * U =
        U * conePlus P A * U + U * coneMinus P C * U := by noncomm_ring
      _ = coneMinus P C + conePlus P A := by rw [hUNp, hUNm]
      _ = conePlus P A + coneMinus P C := by abel
  have hGammaPhi : kleinGamma P U (genPhi P A C) = -genPhi P A C := by
    have hV4 := seam_reflection_v4_klein_group_closure hP hU2 hUP (genPhi P A C)
    rw [← hV4.2.2.2.1, hBetaPhi, hAlphaPhi]
  have hAlphaJ : kleinAlpha P (genJ P A C) = -genJ P A C := by
    unfold kleinAlpha; peirce_nf hP
  have hBetaJ : kleinBeta U (genJ P A C) = -genJ P A C := by
    unfold kleinBeta genJ
    calc
      U * (conePlus P A - coneMinus P C) * U =
        U * conePlus P A * U - U * coneMinus P C * U := by noncomm_ring
      _ = coneMinus P C - conePlus P A := by rw [hUNp, hUNm]
      _ = -(conePlus P A - coneMinus P C) := by abel
  have hGammaJ : kleinGamma P U (genJ P A C) = genJ P A C := by
    have hV4 := seam_reflection_v4_klein_group_closure hP hU2 hUP (genJ P A C)
    rw [← hV4.2.2.2.1, hBetaJ]
    calc
      kleinAlpha P (-genJ P A C) = -kleinAlpha P (genJ P A C) := by
        unfold kleinAlpha; noncomm_ring
      _ = -(-genJ P A C) := by rw [hAlphaJ]
      _ = genJ P A C := by abel
  exact ⟨⟨hAlphaSum, hBetaSum, hGammaSum, hAlphaV, hBetaV, hGammaV⟩,
         ⟨hAlphaDiff, hBetaDiff, hGammaDiff, hAlphaSig, hBetaSig, hGammaSig⟩,
         ⟨hAlphaPhi, hBetaPhi, hGammaPhi⟩,
         ⟨hAlphaJ, hBetaJ, hGammaJ⟩⟩

/-! ===========================================================================
    Section 7: Stage `𝔅₇` — Scaled Walsh–Hadamard Projector Resolution
    (`P_{++}, P_{+-}, P_{-+}, P_{--}`) and Exact Four-Sector Isolation
    =========================================================================== -/

/-- Scaled Walsh–Hadamard character projector onto `χ₊₊ = (+1, +1)`:
`walshProjPP P U X := X + α(X) + β(X) + γ(X)`. -/
def walshProjPP (P U X : B) : B :=
  X + kleinAlpha P X + kleinBeta U X + kleinGamma P U X

/-- Scaled Walsh–Hadamard character projector onto `χ₊₋ = (+1, -1)`:
`walshProjPM P U X := X + α(X) - β(X) - γ(X)`. -/
def walshProjPM (P U X : B) : B :=
  X + kleinAlpha P X - kleinBeta U X - kleinGamma P U X

/-- Scaled Walsh–Hadamard character projector onto `χ₋₊ = (-1, +1)`:
`walshProjMP P U X := X - α(X) + β(X) - γ(X)`. -/
def walshProjMP (P U X : B) : B :=
  X - kleinAlpha P X + kleinBeta U X - kleinGamma P U X

/-- Scaled Walsh–Hadamard character projector onto `χ₋₋ = (-1, -1)`:
`walshProjMM P U X := X - α(X) - β(X) + γ(X)`. -/
def walshProjMM (P U X : B) : B :=
  X - kleinAlpha P X - kleinBeta U X + kleinGamma P U X

/-- **Stage `𝔅₇` Theorem (`walsh_hadamard_four_sector_resolution`)**:
The four scaled Walsh–Hadamard character projectors `walshProjPP`, `walshProjPM`,
`walshProjMP`, `walshProjMM` satisfy:
1. **Unconditional Four-Sector Completeness**:
   `walshProjPP P U X + walshProjPM P U X + walshProjMP P U X + walshProjMM P U X = (4 : ℤ) • X`,
2. **Exact Sector Isolation on `(Γ_sum, Γ_diff, Φ, J)`**:
   Under the hypotheses of `v4_character_eigen_classification`:
   * **`χ₊₊` Sector (`Γ_sum`)**:
     `walshProjPP P U (sheetConnectionSum P W) = (4 : ℤ) • sheetConnectionSum P W`,
     and `walshProjPM`, `walshProjMP`, `walshProjMM` all vanish on `sheetConnectionSum P W`,
   * **`χ₊₋` Sector (`Γ_diff`)**:
     `walshProjPM P U (sheetConnectionDiff P W) = (4 : ℤ) • sheetConnectionDiff P W`,
     and `walshProjPP`, `walshProjMP`, `walshProjMM` all vanish on `sheetConnectionDiff P W`,
   * **`χ₋₊` Sector (`Φ`)**:
     `walshProjMP P U (genPhi P A C) = (4 : ℤ) • genPhi P A C`,
     and `walshProjPP`, `walshProjPM`, `walshProjMM` all vanish on `genPhi P A C`,
   * **`χ₋₋` Sector (`J`, Klein Seam Twist)**:
     `walshProjMM P U (genJ P A C) = (4 : ℤ) • genJ P A C`,
     and `walshProjPP`, `walshProjPM`, `walshProjMP` all vanish on `genJ P A C`. -/
theorem walsh_hadamard_four_sector_resolution
    {P U : B} (hP : P * P = P) (hU2 : U * U = 1) (hUP : U * P * U = 1 - P)
    (W A C X : B)
    (hUW : U * sheetPlusConnection P W * U = sheetMinusConnection P W)
    (hUNp : U * conePlus P A * U = coneMinus P C)
    (hUNm : U * coneMinus P C * U = conePlus P A) :
    -- (1) Four-sector completeness on every ambient operator X
    (walshProjPP P U X + walshProjPM P U X + walshProjMP P U X + walshProjMM P U X =
       (4 : ℤ) • X) ∧
    -- (2) Exact isolation of Γ_sum in χ₊₊
    (walshProjPP P U (sheetConnectionSum P W) = (4 : ℤ) • sheetConnectionSum P W ∧
     walshProjPM P U (sheetConnectionSum P W) = 0 ∧
     walshProjMP P U (sheetConnectionSum P W) = 0 ∧
     walshProjMM P U (sheetConnectionSum P W) = 0) ∧
    -- (3) Exact isolation of Γ_diff in χ₊₋
    (walshProjPM P U (sheetConnectionDiff P W) = (4 : ℤ) • sheetConnectionDiff P W ∧
     walshProjPP P U (sheetConnectionDiff P W) = 0 ∧
     walshProjMP P U (sheetConnectionDiff P W) = 0 ∧
     walshProjMM P U (sheetConnectionDiff P W) = 0) ∧
    -- (4) Exact isolation of Φ in χ₋₊
    (walshProjMP P U (genPhi P A C) = (4 : ℤ) • genPhi P A C ∧
     walshProjPP P U (genPhi P A C) = 0 ∧
     walshProjPM P U (genPhi P A C) = 0 ∧
     walshProjMM P U (genPhi P A C) = 0) ∧
    -- (5) Exact isolation of J in χ₋₋
    (walshProjMM P U (genJ P A C) = (4 : ℤ) • genJ P A C ∧
     walshProjPP P U (genJ P A C) = 0 ∧
     walshProjPM P U (genJ P A C) = 0 ∧
     walshProjMP P U (genJ P A C) = 0) := by
  have hChar := v4_character_eigen_classification hP hU2 hUP W A C hUW hUNp hUNm
  rcases hChar with ⟨⟨hASum, hBSum, hGSum, _, _, _⟩,
                     ⟨hADiff, hBDiff, hGDiff, _, _, _⟩,
                     ⟨hAPhi, hBPhi, hGPhi⟩,
                     ⟨hAJ, hBJ, hGJ⟩⟩
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · unfold walshProjPP walshProjPM walshProjMP walshProjMM
    noncomm_ring
  · unfold walshProjPP
    rw [hASum, hBSum, hGSum]
    abel_nf
  · unfold walshProjPM
    rw [hASum, hBSum, hGSum]
    abel
  · unfold walshProjMP
    rw [hASum, hBSum, hGSum]
    abel
  · unfold walshProjMM
    rw [hASum, hBSum, hGSum]
    abel
  · unfold walshProjPM
    rw [hADiff, hBDiff, hGDiff]
    abel_nf
  · unfold walshProjPP
    rw [hADiff, hBDiff, hGDiff]
    abel
  · unfold walshProjMP
    rw [hADiff, hBDiff, hGDiff]
    abel
  · unfold walshProjMM
    rw [hADiff, hBDiff, hGDiff]
    abel
  · unfold walshProjMP
    rw [hAPhi, hBPhi, hGPhi]
    abel_nf
  · unfold walshProjPP
    rw [hAPhi, hBPhi, hGPhi]
    abel
  · unfold walshProjPM
    rw [hAPhi, hBPhi, hGPhi]
    abel
  · unfold walshProjMM
    rw [hAPhi, hBPhi, hGPhi]
    abel
  · unfold walshProjMM
    rw [hAJ, hBJ, hGJ]
    abel_nf
  · unfold walshProjPP
    rw [hAJ, hBJ, hGJ]
    abel
  · unfold walshProjPM
    rw [hAJ, hBJ, hGJ]
    abel
  · unfold walshProjMP
    rw [hAJ, hBJ, hGJ]
    abel

/-! ===========================================================================
    Section 8: Master 7-Stage Klein Bottle Seam & Sum–Difference Connection
    Synthesis (`𝔅₁ ≺ 𝔅₂ ≺ ⋯ ≺ 𝔅₇`)
    =========================================================================== -/

/-- **Master Theorem (`klein_bottle_seam_sum_difference_connection_master_synthesis`)**:
Unifies the complete 7-stage Klein Bottle Seam & Sum–Difference Connection poset
(`𝔅₁ ≺ 𝔅₂ ≺ ⋯ ≺ 𝔅₇`):
0. Poset acyclicity, strict 7-stage chain, and monotone `RepDepth` / `OntologyMetaLevel`
   embeddings of `KleinBottleSeamConnectionStage`,
1. `𝔅₁`: Rung 0 single-sheet blindness (`N₊ ∇₊ = 0`, `∇₋ N₊ = 0`, `[∇₊, N₊] = {∇₊, N₊}`),
2. `𝔅₂`: Chiral duality (`S_P Γ_sum = Γ_diff`) and DeWitt squared curvature split
   (`Γ_sum² = Γ_diff² = ∇₊² + ∇₋²`, `Γ_sum Γ_diff = ∇₊² - ∇₋²`),
3. `𝔅₃`: Universal fourfold sum–difference transport crossover
   (`[Γ_diff, Φ] = {Γ_sum, J}`, `{Γ_diff, Φ} = [Γ_sum, J]`,
    `[Γ_diff, J] = {Γ_sum, Φ}`, `{Γ_diff, J} = [Γ_sum, Φ]`),
4. `𝔅₄`: Endogenous Gramian connections (`Γ_sum(V) = V`, `Γ_diff(V) = Σ`) and active
   spin-connection frame dragging (`[Σ, Φ] = {V, J} = 2 V J`, `[V, Φ] = 0`),
5. `𝔅₅`: Clifford carrier anticommutation (`U S_P = -S_P U`, `(S_P U)² = -1`) and
   superoperator Klein four-group closure (`α ∘ β = β ∘ α = γ`, `γ ∘ γ = id`),
6. `𝔅₆`: Fourfold `V₄ = ℤ₂ × ℤ₂` character classification (`Γ_sum, V ∈ χ₊₊`,
   `Γ_diff, Σ ∈ χ₊₋`, `Φ ∈ χ₋₊`, `J ∈ χ₋₋`),
7. `𝔅₇`: Scaled Walsh–Hadamard four-sector completeness (`P_{++} + P_{+-} + P_{-+} + P_{--} = 4 • id`)
   and exact sector isolation (`P_{++}(Γ_sum) = 4 Γ_sum`, `P_{+-}(Γ_diff) = 4 Γ_diff`,
   `P_{-+}(Φ) = 4 Φ`, `P_{--}(J) = 4 J`). -/
theorem klein_bottle_seam_sum_difference_connection_master_synthesis
    {P U : B} (hP : P * P = P) (hU2 : U * U = 1) (hUP : U * P * U = 1 - P)
    (W A C X : B)
    (hUW : U * sheetPlusConnection P W * U = sheetMinusConnection P W)
    (hUNp : U * conePlus P A * U = coneMinus P C)
    (hUNm : U * coneMinus P C * U = conePlus P A) :
    -- (0) Poset acyclicity and monotone meta-projections
    ((∀ st : KleinBottleSeamConnectionStage,
        ¬ Relation.TransGen KleinBottleSeamConnectionStage.causalEdge st st) ∧
     (∀ a b : KleinBottleSeamConnectionStage, a ≤ b →
        (KleinBottleSeamConnectionStage.toRepDepth a).toNat ≤
          (KleinBottleSeamConnectionStage.toRepDepth b).toNat) ∧
     (∀ a b : KleinBottleSeamConnectionStage, a ≤ b →
        (KleinBottleSeamConnectionStage.toOntologyMetaLevel a).rank ≤
          (KleinBottleSeamConnectionStage.toOntologyMetaLevel b).rank)) ∧
    -- (1) Stage 𝔅₁: Single-sheet blindness on throat operators
    (conePlus P A * sheetPlusConnection P W = 0 ∧
     sheetMinusConnection P W * conePlus P A = 0 ∧
     comm (sheetPlusConnection P W) (conePlus P A) =
       anticomm (sheetPlusConnection P W) (conePlus P A)) ∧
    -- (2) Stage 𝔅₂: Chiral duality and squared curvature split
    (invS P * sheetConnectionSum P W = sheetConnectionDiff P W ∧
     sheetConnectionSum P W * sheetConnectionSum P W =
       sheetPlusConnection P W * sheetPlusConnection P W +
         sheetMinusConnection P W * sheetMinusConnection P W ∧
     sheetConnectionSum P W * sheetConnectionDiff P W =
       sheetPlusConnection P W * sheetPlusConnection P W -
         sheetMinusConnection P W * sheetMinusConnection P W) ∧
    -- (3) Stage 𝔅₃: Universal fourfold sum-difference transport crossover
    (comm (sheetConnectionDiff P W) (genPhi P A C) =
       anticomm (sheetConnectionSum P W) (genJ P A C) ∧
     anticomm (sheetConnectionDiff P W) (genPhi P A C) =
       comm (sheetConnectionSum P W) (genJ P A C) ∧
     comm (sheetConnectionDiff P W) (genJ P A C) =
       anticomm (sheetConnectionSum P W) (genPhi P A C) ∧
     anticomm (sheetConnectionDiff P W) (genJ P A C) =
       comm (sheetConnectionSum P W) (genPhi P A C)) ∧
    -- (4) Stage 𝔅₄: Endogenous Gramian connections & spin frame dragging
    (sheetConnectionSum P (genV P A C) = genV P A C ∧
     sheetConnectionDiff P (genV P A C) = genSig P A C ∧
     comm (genSig P A C) (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C) ∧
     comm (genV P A C) (genPhi P A C) = 0) ∧
    -- (5) Stage 𝔅₅: Clifford carrier anticommutation & V₄ superoperator closure
    (U * invS P = -(invS P * U) ∧
     (invS P * U) * (invS P * U) = -1 ∧
     kleinAlpha P (kleinBeta U X) = kleinBeta U (kleinAlpha P X) ∧
     kleinGamma P U (kleinGamma P U X) = X) ∧
    -- (6) Stage 𝔅₆: Fourfold V₄ character classification (χ₊₊, χ₊₋, χ₋₊, χ₋₋)
    (kleinBeta U (sheetConnectionSum P W) = sheetConnectionSum P W ∧
     kleinBeta U (sheetConnectionDiff P W) = -sheetConnectionDiff P W ∧
     kleinBeta U (genPhi P A C) = genPhi P A C ∧
     kleinBeta U (genJ P A C) = -genJ P A C ∧
     kleinGamma P U (genJ P A C) = genJ P A C) ∧
    -- (7) Stage 𝔅₇: Walsh–Hadamard four-sector completeness & exact sector isolation
    (walshProjPP P U X + walshProjPM P U X + walshProjMP P U X + walshProjMM P U X =
       (4 : ℤ) • X ∧
     walshProjPP P U (sheetConnectionSum P W) = (4 : ℤ) • sheetConnectionSum P W ∧
     walshProjPM P U (sheetConnectionDiff P W) = (4 : ℤ) • sheetConnectionDiff P W ∧
     walshProjMP P U (genPhi P A C) = (4 : ℤ) • genPhi P A C ∧
     walshProjMM P U (genJ P A C) = (4 : ℤ) • genJ P A C) := by
  have hB1 := single_sheet_blindness_aporia hP W W A C
  have hB2 := sum_difference_chiral_duality_and_squared_split hP W A
  have hB3 := sheetConnection_sum_difference_crossover hP W A C
  have hB4 := endogenous_dewitt_gramian_spin_frame_dragging hP A C
  have hB5 := seam_reflection_v4_klein_group_closure hP hU2 hUP X
  have hB6 := v4_character_eigen_classification hP hU2 hUP W A C hUW hUNp hUNm
  have hB7 := walsh_hadamard_four_sector_resolution hP hU2 hUP W A C X hUW hUNp hUNm
  exact ⟨⟨KleinBottleSeamConnectionStage.causalEdge_acyclic,
          fun a b hab => KleinBottleSeamConnectionStage.toRepDepth_rank_monotone hab,
          fun a b hab => KleinBottleSeamConnectionStage.toOntologyMetaLevel_rank_monotone hab⟩,
         ⟨hB1.2.1.1, hB1.2.1.2.1, hB1.2.2.1.trans hB1.2.2.2.1.symm⟩,
         ⟨hB2.1.1, hB2.2.2.1, hB2.2.2.2.2.1⟩,
         hB3,
         ⟨hB4.1.2.2.1, hB4.1.2.2.2, hB4.2.2.1, hB4.2.2.2.2.2.2.2.2⟩,
         ⟨hB5.1.2.1, hB5.1.2.2.1, hB5.2.2.2.2.2.1, hB5.2.2.2.2.2.2⟩,
         ⟨hB6.1.2.1, hB6.2.1.2.1, hB6.2.2.1.2.1, hB6.2.2.2.2.1, hB6.2.2.2.2.2⟩,
         ⟨hB7.1, hB7.2.1.1, hB7.2.2.1.1, hB7.2.2.2.1.1, hB7.2.2.2.2.1⟩⟩

end StageB5ToB7

end InfoGeometry.Canonical.KleinBottleSeamSumDifferenceConnectionPoset
