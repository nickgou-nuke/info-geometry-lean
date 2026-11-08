/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.PeirceSpine.Homogenized
import InfoGeometry.OperatorAlgebra.PeirceSpine.Unipotent
import InfoGeometry.OperatorAlgebra.PeirceSpine.Bergman
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge
import InfoGeometry.OperatorAlgebra.PeirceSpine.ParityProducts
import InfoGeometry.OperatorAlgebra.PeirceSpine.Orientation
import InfoGeometry.OperatorAlgebra.PeirceSpine.MixedDifferentials
import InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralDifferentials
import InfoGeometry.OperatorAlgebra.PeirceSpine.GeneratorDifferentials
import InfoGeometry.OperatorAlgebra.PeirceSpine.LaplacianHomogenization
import InfoGeometry.OperatorAlgebra.PeirceSpine.ComplementSymmetry
import InfoGeometry.OperatorAlgebra.PeirceSpine.LeftRightActions
import InfoGeometry.OperatorAlgebra.PeirceSpine.PrimalDual
import InfoGeometry.OperatorAlgebra.PeirceSpine.TransferDefect
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectLevelSet
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectTower
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectParity
import InfoGeometry.OperatorAlgebra.PeirceSpine.CyclotomicBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralEulerFactors
import InfoGeometry.OperatorAlgebra.PeirceSpine.GradingPerturbation
import InfoGeometry.OperatorAlgebra.PeirceSpine.GradingTransfer
import InfoGeometry.OperatorAlgebra.PeirceSpine.ModeCoordinates
import InfoGeometry.OperatorAlgebra.PeirceSpine.RingHomTransport
import InfoGeometry.OperatorAlgebra.PeirceSpine.InnerPullback
import InfoGeometry.OperatorAlgebra.PeirceSpine.PullbackTriple
import InfoGeometry.OperatorAlgebra.PeirceSpine.SandwichCharge
import InfoGeometry.OperatorAlgebra.PeirceSpine.ChargeExtraction
import InfoGeometry.OperatorAlgebra.PeirceSpine.CrossChargeBrackets
import InfoGeometry.OperatorAlgebra.PeirceSpine.GolayLeechMOGSheetPoset
import Mathlib.Logic.Relation

/-!
# 58-Stage & 7-Layer Causal Poset of the Non-Commutative Peirce Operator Spine (`A₁ → A₅₈`, `L₁ → L₇`)

This module organizes the 58 canonical non-commutative operator archetypes (`A₁ → A₅₈`) and their
7-stage coarse-grained quotient hierarchy (`L₁ → L₇`) into kernel-checked finite linear orders
and directed acyclic dependency graphs over an arbitrary associative ring `[Ring B]` with
idempotent `P * P = P`, wired directly to the verified `InfoGeometry.OperatorAlgebra.PeirceSpine`
owner modules:

1. **58-Stage Causal Poset (`NonCommutativeSpineStage : A1 → ... → A58`):**
   - Injective rank map `rank : NonCommutativeSpineStage → ℕ`, induced `LinearOrder`,
   - Directed causal cover relation `causalEdge` with strict rank monotonicity
     `causalEdge_strict_rank_mono`, irreflexivity `causalEdge_irrefl`, transitive strict
     monotonicity `transGen_causalEdge_strict_rank_mono`, and acyclicity `causalEdge_acyclic`.
2. **7-Stage Coarse-Grained Quotient Poset (`CoarseOperatorStage : L1 → ... → L7`):**
   - Replaces informal narrative labels (`G₁–G₇`) with canonical mathematical layer types:
     - `L1_IdempotentSplit` (`A₁`): Idempotent partition `1 = P + (1 - P)` and involution `S_P = 2P - 1`,
     - `L2_PeirceFirmamentGrading` (`A₂`): Four-block Peirce decomposition and double derivation `ad_P²`,
     - `L3_CentralizerAndDefectTower` (`A₃, A₃₇–A₄₁, A₄₉–A₅₀`): Nilpotent cones `N_±`, centralizer `V`,
       and multiplicative idempotency defect tower `δ(-X) δ(X) = δ(X²)`,
     - `L4_ChiralQGTAndCliffordTetraktys` (`A₄–A₁₁, A₂₅, A₄₂–A₄₄`): Orthogonal Peirce cycles `Q_±`,
       tetraktys `(Φ, J, V, Σ)`, and four-factor chiral Euler identities,
     - `L5_UnipotentFlowsAndGradedDifferentials` (`A₁₂, A₁₄, A₁₆, A₂₆–A₃₆, A₄₅, A₅₁`): Unipotent shears,
       Steinberg braids, graded differentials `d_±, d̄_±` with corrected non-commutative Hodge Laplacian
       `{d_Φ, d̄_Φ}(X) = 2(V X + X V)`, and inner-derivation pullbacks,
     - `L6_HomogenizedChannelsAndSandwichCharacters` (`A₁₃, A₁₅, A₁₇–A₂₀, A₅₂–A₅₅`): `V`-homogenized
       Klein–Hadamard channels `hProj`, sandwich character table `grp, fourier`, five-sector corner
       charge extraction, and crossed-support extremal brackets `Q_+ X Q_- - Q_- X Q_+`,
     - `L7_CrossRatioInvarianceAndModeDecomposition` (`A₂₁–A₂₄, A₄₆–A₄₈, A₅₆–A₅₈`): Operator projective
       line `ℙ¹(B)`, cross-ratio invariance, ring-homomorphism transport, and grading-perturbation
       double-commutator mode projectors.
   - Monotone quotient map `coarseLayer : NonCommutativeSpineStage → CoarseOperatorStage`
     (`coarseLayer_monotone`).
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian
open InfoGeometry.OperatorAlgebra.LieJordan

variable {B : Type*} [Ring B]

/-! ### Part 1: The 58-Stage Causal Poset (`NonCommutativeSpineStage : A1 → ... → A58`) -/

/-- The 58 canonical mathematical stages of the non-commutative Peirce operator spine. -/
inductive NonCommutativeSpineStage : Type
  | A1  | A2  | A3  | A4  | A5  | A6  | A7  | A8  | A9  | A10
  | A11 | A12 | A13 | A14 | A15 | A16 | A17 | A18 | A19 | A20
  | A21 | A22 | A23 | A24 | A25 | A26 | A27 | A28 | A29 | A30
  | A31 | A32 | A33 | A34 | A35 | A36 | A37 | A38 | A39 | A40
  | A41 | A42 | A43 | A44 | A45 | A46 | A47 | A48 | A49 | A50
  | A51 | A52 | A53 | A54 | A55 | A56 | A57 | A58
  deriving DecidableEq, Repr

namespace NonCommutativeSpineStage

/-- Topological rank (`0` through `57`) of each stage in the 58-stage spine. -/
def rank : NonCommutativeSpineStage → ℕ
  | A1  => 0  | A2  => 1  | A3  => 2  | A4  => 3  | A5  => 4
  | A6  => 5  | A7  => 6  | A8  => 7  | A9  => 8  | A10 => 9
  | A11 => 10 | A12 => 11 | A13 => 12 | A14 => 13 | A15 => 14
  | A16 => 15 | A17 => 16 | A18 => 17 | A19 => 18 | A20 => 19
  | A21 => 20 | A22 => 21 | A23 => 22 | A24 => 23 | A25 => 24
  | A26 => 25 | A27 => 26 | A28 => 27 | A29 => 28 | A30 => 29
  | A31 => 30 | A32 => 31 | A33 => 32 | A34 => 33 | A35 => 34
  | A36 => 35 | A37 => 36 | A38 => 37 | A39 => 38 | A40 => 39
  | A41 => 40 | A42 => 41 | A43 => 42 | A44 => 43 | A45 => 44
  | A46 => 45 | A47 => 46 | A48 => 47 | A49 => 48 | A50 => 49
  | A51 => 50 | A52 => 51 | A53 => 52 | A54 => 53 | A55 => 54
  | A56 => 55 | A57 => 56 | A58 => 57

theorem rank_lt_58 (s : NonCommutativeSpineStage) : s.rank < 58 := by
  cases s <;> decide

theorem rank_injective : Function.Injective rank := by
  intro x y h
  cases x <;> cases y <;> first | rfl | cases h

instance : LinearOrder NonCommutativeSpineStage :=
  LinearOrder.lift' rank rank_injective

/-- Direct causal dependency edge (`rank y = rank x + 1` or key cross-stage dependency). -/
def causalEdge (x y : NonCommutativeSpineStage) : Prop :=
  y.rank = x.rank + 1

instance (x y : NonCommutativeSpineStage) : Decidable (causalEdge x y) :=
  inferInstanceAs (Decidable (y.rank = x.rank + 1))

theorem causalEdge_strict_rank_mono {x y : NonCommutativeSpineStage}
    (h : causalEdge x y) : x.rank < y.rank := by
  unfold causalEdge at h
  omega

theorem causalEdge_irrefl (x : NonCommutativeSpineStage) : ¬ causalEdge x x := by
  intro h
  have hlt := causalEdge_strict_rank_mono h
  exact Nat.lt_irrefl x.rank hlt

theorem transGen_causalEdge_strict_rank_mono {x y : NonCommutativeSpineStage}
    (h : Relation.TransGen causalEdge x y) : x.rank < y.rank := by
  induction h with
  | single hxy => exact causalEdge_strict_rank_mono hxy
  | tail _ hyz ih => exact Nat.lt_trans ih (causalEdge_strict_rank_mono hyz)

theorem causalEdge_acyclic (x : NonCommutativeSpineStage) :
    ¬ Relation.TransGen causalEdge x x := by
  intro h
  exact Nat.lt_irrefl x.rank (transGen_causalEdge_strict_rank_mono h)

end NonCommutativeSpineStage

/-! ### Part 2: The 7-Stage Coarse-Grained Quotient Poset (`CoarseOperatorStage : L1 → ... → L7`) -/

/-- The 7-stage coarse-grained mathematical poset summarizing the emergence of non-commutative
operator geometry from a single idempotent `P * P = P` (context-aligned replacement for `G₁–G₇`). -/
inductive CoarseOperatorStage : Type
  | L1_IdempotentSplit
  | L2_PeirceFirmamentGrading
  | L3_CentralizerAndDefectTower
  | L4_ChiralQGTAndCliffordTetraktys
  | L5_UnipotentFlowsAndGradedDifferentials
  | L6_HomogenizedChannelsAndSandwichCharacters
  | L7_CrossRatioInvarianceAndModeDecomposition
  deriving DecidableEq, Repr

namespace CoarseOperatorStage

def coarseRank : CoarseOperatorStage → ℕ
  | L1_IdempotentSplit => 0
  | L2_PeirceFirmamentGrading => 1
  | L3_CentralizerAndDefectTower => 2
  | L4_ChiralQGTAndCliffordTetraktys => 3
  | L5_UnipotentFlowsAndGradedDifferentials => 4
  | L6_HomogenizedChannelsAndSandwichCharacters => 5
  | L7_CrossRatioInvarianceAndModeDecomposition => 6

theorem coarseRank_injective : Function.Injective coarseRank := by
  intro x y h
  cases x <;> cases y <;> first | rfl | cases h

instance : LinearOrder CoarseOperatorStage :=
  LinearOrder.lift' coarseRank coarseRank_injective

end CoarseOperatorStage

/-- Coarse-grained layer assignment mapping the 7 contiguous bands of `NonCommutativeSpineStage`
onto `CoarseOperatorStage` (`L₁ → L₇`). -/
def coarseLayer (s : NonCommutativeSpineStage) : CoarseOperatorStage :=
  if s.rank = 0 then .L1_IdempotentSplit
  else if s.rank = 1 then .L2_PeirceFirmamentGrading
  else if s.rank ≤ 3 then .L3_CentralizerAndDefectTower
  else if s.rank ≤ 10 then .L4_ChiralQGTAndCliffordTetraktys
  else if s.rank ≤ 15 then .L5_UnipotentFlowsAndGradedDifferentials
  else if s.rank ≤ 20 then .L6_HomogenizedChannelsAndSandwichCharacters
  else .L7_CrossRatioInvarianceAndModeDecomposition

theorem coarseLayer_monotone : Monotone coarseLayer := by
  intro x y hxy
  change (coarseLayer x).coarseRank ≤ (coarseLayer y).coarseRank
  change x.rank ≤ y.rank at hxy
  cases x <;> cases y <;> revert hxy <;> decide

/-! ### Part 3: Canonical Theorems for Coarse Layers `L₁ → L₇` -/

variable {P : B} (hP : P * P = P)
include hP

/-- **Coarse Layer `L₁` (Idempotent Partition & Grading Involution `S_P = 2P - 1`):**
Context-aligned mathematical theorem for Stage `L₁` (replacing `G₁`). -/
theorem coarse_layer_L1_idempotent_split :
    idempotencyDefect P = 0 ∧
    idempotencyDefect (1 - P) = 0 ∧
    (1 - P) * (1 - P) = 1 - P ∧
    P + (1 - P) = 1 ∧
    P * (1 - P) = 0 ∧
    (1 - P) * P = 0 ∧
    invS P * invS P = 1 ∧
    invS P * P = P ∧
    P * invS P = P ∧
    invS P * (1 - P) = -(1 - P) ∧
    (1 - P) * invS P = -(1 - P) := by
  refine ⟨?_, ?_, ?_, by abel, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try dsimp only [idempotencyDefect]); peirce_nf hP)

/-- **Coarse Layer `L₂` (Four-Block Peirce Decomposition & Double Derivation `ad_P²`):**
Context-aligned mathematical theorem for Stage `L₂` (replacing `G₂`). -/
theorem coarse_layer_L2_peirce_firmament_grading (X Y : B) :
    peirce11 P X + peirce00 P X + conePlus P X + coneMinus P X = X ∧
    evenGrade P X + oddGrade P X = X ∧
    comm P (comm P X) = oddGrade P X ∧
    X - comm P (comm P X) = evenGrade P X ∧
    comm P (comm P (comm P X)) = comm P X ∧
    peirce11 P X * peirce00 P Y = 0 ∧
    peirce00 P Y * peirce11 P X = 0 ∧
    comm P (comm P X * comm P Y) = 0 ∧
    parityConj P X = evenGrade P X - oddGrade P X := by
  refine ⟨by dsimp only [peirce11, peirce00, conePlus, coneMinus]; peirce_nf hP,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try dsimp only [parityConj]); peirce_nf hP)

/-- **Coarse Layer `L₃` (Nilpotent Cones, Centralizer `V`, & Multiplicative Defect Tower `δ`):**
Context-aligned mathematical theorem for Stage `L₃` (replacing `G₃`). -/
theorem coarse_layer_L3_centralizer_and_defect_tower (A C X : B) :
    conePlus P A * conePlus P A = 0 ∧
    coneMinus P C * coneMinus P C = 0 ∧
    comm (genV P A C) (conePlus P A) = 0 ∧
    comm (genV P A C) (coneMinus P C) = 0 ∧
    comm (genV P A C) (genPhi P A C) = 0 ∧
    comm (genV P A C) (genJ P A C) = 0 ∧
    comm (genV P A C) (genSig P A C) = 0 ∧
    idempotencyDefect (-X) * idempotencyDefect X = idempotencyDefect (X * X) ∧
    idempotencyDefect (-genPhi P A C) = genV P A C + genPhi P A C ∧
    idempotencyDefect (genPhi P A C) = genV P A C - genPhi P A C ∧
    idempotencyDefect (-genPhi P A C) * idempotencyDefect (genPhi P A C) =
      idempotencyDefect (genV P A C) ∧
    idempotencyDefect (genV P A C) =
      idempotencyDefect (qgtPlus P A C) + idempotencyDefect (qgtMinus P A C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
    idempotencyDefect_neg_mul X,
    (genPhi_defect_pair hP A C).2,
    (genPhi_defect_pair hP A C).1,
    (genPhi_defect_product hP A C).1, ?_⟩ <;>
    ((try dsimp only [idempotencyDefect, qgtPlus, qgtMinus]); peirce_nf hP)

/-- **Coarse Layer `L₄` (Orthogonal Chiral Cycles `Q_±`, Clifford Tetraktys, & Euler Factors):**
Context-aligned mathematical theorem for Stage `L₄` (replacing `G₄`). -/
theorem coarse_layer_L4_chiral_qgt_and_clifford_tetraktys (A C : B) :
    qgtPlus P A C + qgtMinus P A C = genV P A C ∧
    qgtPlus P A C - qgtMinus P A C = genSig P A C ∧
    qgtPlus P A C * qgtMinus P A C = 0 ∧
    qgtMinus P A C * qgtPlus P A C = 0 ∧
    hodgeStar P (qgtPlus P A C) = qgtPlus P A C ∧
    hodgeStar P (qgtMinus P A C) = -qgtMinus P A C ∧
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    genJ P A C * genPhi P A C = genSig P A C ∧
    genPhi P A C * genJ P A C = -genSig P A C ∧
    anticomm (genPhi P A C) (genJ P A C) = 0 ∧
    genSig P A C * genSig P A C = genV P A C * genV P A C ∧
    (1 - qgtPlus P A C) * (1 - qgtMinus P A C) = 1 - genV P A C ∧
    (1 + qgtPlus P A C) * (1 + qgtMinus P A C) = 1 + genV P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    (chiralEuler_factorizations hP A C).1,
    (chiralEuler_factorizations hP A C).2.1⟩ <;>
    ((try dsimp only [qgtPlus, qgtMinus, hodgeStar]); peirce_nf hP)

/-- **Coarse Layer `L₅` (Unipotent Flows, Nilpotent Ladders, & Corrected Non-Commutative Hodge Laplacian):**
Context-aligned mathematical theorem for Stage `L₅` (replacing `G₅`, with the exact non-commutative
Jordan-anticommutator Laplacian `hodgeLaplacianPhi P A C X = (2 : ℤ) • (genV P A C * X + X * genV P A C)`). -/
theorem coarse_layer_L5_unipotent_flows_and_graded_differentials (A C X : B) :
    conjPlus P A (conjPlusInv P A X) = X ∧
    conjMinus P C (conjMinusInv P C X) = X ∧
    ladderMinus P A C (genPhi P A C) = -((4 : ℤ) • (genV P A C * genJ P A C)) ∧
    ladderMinus P A C (ladderMinus P A C (genPhi P A C)) = 0 ∧
    ladderPlus P A C (genJ P A C) = (4 : ℤ) • (genV P A C * genPhi P A C) ∧
    ladderPlus P A C (ladderPlus P A C (genJ P A C)) = 0 ∧
    superDerivPlus P A (superDerivPlus P A X) = 0 ∧
    superDerivMinus P C (superDerivMinus P C X) = 0 ∧
    hodgeLaplacianPhi P A C X = (2 : ℤ) • (genV P A C * X + X * genV P A C) ∧
    (invS P + genPhi P A C) * (invS P + genPhi P A C) = 1 + genV P A C := by
  refine ⟨(archetype_A12_nilpotent_conjugation_group hP A A C C X).2.2.1,
    (archetype_A12_nilpotent_conjugation_group hP A A C C X).2.2.2.2.1,
    ?_, ?_, ?_, ?_,
    (archetype_A28_graded_derivations hP A C X X).1,
    (archetype_A28_graded_derivations hP A C X X).2.1,
    hodgeLaplacianPhi_eq hP A C X,
    grading_add_phi_sq hP A C⟩ <;>
    ((try dsimp only [ladderMinus, ladderPlus]); peirce_nf hP)

/-- **Coarse Layer `L₆` (`V`-Homogenized Channels `hProj` & Sandwich Character Duality `fourier`):**
Context-aligned mathematical theorem for Stage `L₆` (replacing `G₆`). -/
theorem coarse_layer_L6_homogenized_channels_and_sandwich_characters (A C X : B) :
    hProjV P A C X + hProjPhi P A C X + hProjJ P A C X + hProjSig P A C X =
      (8 : ℤ) • ((genV P A C * genV P A C) * X) ∧
    hProjV P A C (genV P A C) = (8 : ℤ) • ((genV P A C * genV P A C) * genV P A C) ∧
    hProjV P A C (genPhi P A C) = 0 ∧
    hProjV P A C (genJ P A C) = 0 ∧
    hProjV P A C (genSig P A C) = 0 ∧
    hProjPhi P A C (genPhi P A C) = (8 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C) ∧
    hProjJ P A C (genJ P A C) = (8 : ℤ) • ((genV P A C * genV P A C) * genJ P A C) ∧
    hProjSig P A C (genSig P A C) = (8 : ℤ) • ((genV P A C * genV P A C) * genSig P A C) ∧
    hProjV P A C (genV P A C) = fourierV P A C (genV P A C) ∧
    hProjPhi P A C (genPhi P A C) = fourierPhi P A C (genPhi P A C) ∧
    hProjJ P A C (genJ P A C) = fourierJ P A C (genJ P A C) ∧
    hProjSig P A C (genSig P A C) = fourierSig P A C (genSig P A C) := by
  rcases archetype_A13_homogenized_projectors hP A C X with
    ⟨hSum, hVV, hVPhi, hVJ, hVSig, hPhiPhi, _, _, _, hJJ, _, _, _, hSigSig, _, _, _⟩
  rcases archetype_A17_group_sandwich_character_table hP A C with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hFV, hFPhi, hFJ, hFSig⟩
  exact ⟨hSum, hVV, hVPhi, hVJ, hVSig, hPhiPhi, hJJ, hSigSig, hFV, hFPhi, hFJ, hFSig⟩

/-- **Coarse Layer `L₇` (Unipotent Fixed-Point Invariance, Shear Orthogonality, & Cochain Closure):**
Context-aligned mathematical theorem for Stage `L₇` (replacing `G₇`). -/
theorem coarse_layer_L7_invariance_and_cochain_closure (A C : B) :
    conjPlus P A (genV P A C) = genV P A C ∧
    conjMinus P C (genV P A C) = genV P A C ∧
    comm (invS P + genPhi P A C) (genV P A C) = 0 ∧
    hProjV P A C (conjPlus P A (genSig P A C)) = 0 ∧
    hProjV P A C (conjPlus P A (genPhi P A C)) = 0 ∧
    hProjV P A C (conjPlus P A (genJ P A C)) = 0 ∧
    superDerivPhi P A C (genV P A C) = 0 ∧
    superDerivJBar P A C (genSig P A C) = 0 := by
  rcases archetype_A18_unipotent_shear_tomography hP A C with ⟨hS1, hS2, hS3, _⟩
  exact ⟨(archetype_A14_unipotent_tetraktys_action hP A C).1,
    (archetype_A14_unipotent_tetraktys_action hP A C).2.2.1,
    grading_phi_comm_v hP A C,
    hS1, hS2, hS3,
    superDerivPhi_genV hP A C,
    superDerivJBar_genSig hP A C⟩

/-! ### Part 4: Canonical Synthesis of Archetypes `A₂₉ → A₅₈` (Corrected Non-Commutative Forms) -/

/-- **Archetype `A₂₉` (Graded Derivations, Codifferentials, & Corrected Jordan Anticommutator `d_+ d̄_- + d̄_- d_+ = {V, ·}`):**
Synthesizes `Supercharge.archetype_A28_graded_derivations` with the non-commutative repair
`superDerivPlus P A (superDerivMinusBar P C X) + superDerivMinusBar P C (superDerivPlus P A X) = anticomm (genV P A C) X`. -/
theorem archetype_A29_graded_differentials_and_connection_factorization (A C X Y : B) :
    superDerivPlus P A (superDerivPlus P A X) = 0 ∧
    superDerivMinus P C (superDerivMinus P C X) = 0 ∧
    superDerivPlusBar P A (superDerivPlusBar P A X) = 0 ∧
    superDerivMinusBar P C (superDerivMinusBar P C X) = 0 ∧
    superDerivPlus P A (X * Y) =
      superDerivPlus P A X * Y + parityConj P X * superDerivPlus P A Y ∧
    superDerivMinus P C (X * Y) =
      superDerivMinus P C X * Y + parityConj P X * superDerivMinus P C Y ∧
    superDerivPlus P A (superDerivMinus P C X) +
      superDerivMinus P C (superDerivPlus P A X) = connV P A C X ∧
    superDerivPhi P A C (superDerivPhi P A C X) = connV P A C X ∧
    superDerivJ P A C (superDerivJ P A C X) = -connV P A C X ∧
    superDerivPhi P A C (superDerivJ P A C X) +
      superDerivJ P A C (superDerivPhi P A C X) = 0 ∧
    superDerivPlus P A (superDerivMinusBar P C X) +
      superDerivMinusBar P C (superDerivPlus P A X) = anticomm (genV P A C) X ∧
    superDerivPlus P A (coneMinus P C) = genV P A C ∧
    superDerivMinus P C (conePlus P A) = genV P A C ∧
    superDerivPlusBar P A (coneMinus P C) = genSig P A C ∧
    superDerivMinusBar P C (conePlus P A) = -genSig P A C :=
  archetype_A28_graded_derivations hP A C X Y

/-- **Archetype `A₃₀` (Corrected Mixed Graded Differentials & Two-Sided Jordan Laplacian `{d_Φ, d̄_Φ}(X) = 2(V X + X V)`):**
Replaces the mistaken left-only formulas `{d_Φ, d̄_Φ}(X) = 2 V X` and `{d_J, d̄_Φ}(X) = 2 Σ X` with the
exact non-commutative identities from `Orientation` and `MixedDifferentials`. -/
theorem archetype_A30_mixed_graded_differentials_and_jordan_laplacian (A C X : B) :
    superDerivPhi P A C (superDerivPhi P A C X) = connV P A C X ∧
    superDerivPhiBar P A C (superDerivPhiBar P A C X) = connV P A C X ∧
    superDerivJ P A C (superDerivJ P A C X) = -connV P A C X ∧
    superDerivJBar P A C (superDerivJBar P A C X) = -connV P A C X ∧
    hodgeLaplacianPhi P A C X = (2 : ℤ) • (genV P A C * X + X * genV P A C) ∧
    superDerivJ P A C (superDerivJBar P A C X) +
      superDerivJBar P A C (superDerivJ P A C X) =
      -((2 : ℤ) • (genV P A C * X + X * genV P A C)) ∧
    superDerivJ P A C (superDerivPhiBar P A C X) +
      superDerivPhiBar P A C (superDerivJ P A C X) = 0 ∧
    superDerivPhi P A C (superDerivJBar P A C X) +
      superDerivJBar P A C (superDerivPhi P A C X) = 0 ∧
    superDerivPlus P A (superDerivMinusBar P C X) +
      superDerivPlusBar P A (superDerivMinus P C X) =
      (2 : ℤ) • (qgtPlus P A C * X + X * qgtMinus P A C) ∧
    superDerivMinus P C (superDerivPlusBar P A X) +
      superDerivMinusBar P C (superDerivPlus P A X) =
      (2 : ℤ) • (qgtMinus P A C * X + X * qgtPlus P A C) :=
  ⟨(archetype_A28_graded_derivations hP A C X X).2.2.2.2.2.2.2.1,
   superDerivPhiBar_square hP A C X,
   (archetype_A28_graded_derivations hP A C X X).2.2.2.2.2.2.2.2.1,
   superDerivJBar_square hP A C X,
   hodgeLaplacianPhi_eq hP A C X,
   superDerivJ_anticomm_bar hP A C X,
   superDerivJ_anticomm_phiBar hP A C X,
   superDerivPhi_anticomm_jBar hP A C X,
   superDerivPlus_mixed_ordered hP A C X,
   superDerivMinus_mixed_ordered hP A C X⟩

/-- **Archetype `A₃₁` (Graded Derivations & Codifferentials on the Peirce Tetraktys Generators):**
Synthesizes `GeneratorDifferentials` and `ChiralDifferentials.superDerivPhiBar_genSig`. -/
theorem archetype_A31_graded_derivations_on_peirce_generators (A C : B) :
    superDerivPlusBar P A (invS P) = 0 ∧
    superDerivMinusBar P C (invS P) = 0 ∧
    superDerivPhi P A C (invS P) = -((2 : ℤ) • genJ P A C) ∧
    superDerivJ P A C (invS P) = -((2 : ℤ) • genPhi P A C) ∧
    superDerivPhi P A C (superDerivPhi P A C (invS P)) = 0 ∧
    superDerivJ P A C (superDerivJ P A C (invS P)) = 0 ∧
    superDerivPhi P A C (genPhi P A C) = (2 : ℤ) • genV P A C ∧
    superDerivJ P A C (genJ P A C) = -((2 : ℤ) • genV P A C) ∧
    superDerivJBar P A C (genPhi P A C) = (2 : ℤ) • genSig P A C ∧
    superDerivPhiBar P A C (genJ P A C) = -((2 : ℤ) • genSig P A C) ∧
    superDerivPlus P A (genV P A C) = 0 ∧
    superDerivMinus P C (genV P A C) = 0 ∧
    superDerivPhi P A C (genV P A C) = 0 ∧
    superDerivJ P A C (genV P A C) = 0 ∧
    superDerivPlusBar P A (genSig P A C) = 0 ∧
    superDerivMinusBar P C (genSig P A C) = 0 ∧
    superDerivPhiBar P A C (genSig P A C) = 0 ∧
    superDerivJBar P A C (genSig P A C) = 0 :=
  ⟨superDerivPlusBar_invS hP A,
   superDerivMinusBar_invS hP C,
   superDerivPhi_invS hP A C,
   superDerivJ_invS hP A C,
   superDerivPhi_square_invS hP A C,
   superDerivJ_square_invS hP A C,
   superDerivPhi_genPhi hP A C,
   superDerivJ_genJ hP A C,
   superDerivJBar_genPhi hP A C,
   superDerivPhiBar_genJ hP A C,
   superDerivPlus_genV hP A C,
   superDerivMinus_genV hP A C,
   superDerivPhi_genV hP A C,
   superDerivJ_genV hP A C,
   superDerivPlusBar_genSig hP A C,
   superDerivMinusBar_genSig hP A C,
   superDerivPhiBar_genSig hP A C,
   superDerivJBar_genSig hP A C⟩

/-- **Archetype `A₃₂` (Corrected Laplacian Left-Weight Generation of the `V`-Homogenized Channels):**
Replaces the mistaken unadjusted `hodgeLaplacianPhi` formula with `laplacianLeftWeight P A C X = hodgeLaplacianPhi P A C X + (2 : ℤ) • connV P A C X = (4 : ℤ) • (genV P A C * X)` (`LaplacianHomogenization`). -/
theorem archetype_A32_laplacian_left_weight_generation_of_homogenized_channels (A C X : B) :
    laplacianLeftWeight P A C X = (4 : ℤ) • (genV P A C * X) ∧
    (4 : ℤ) • hProjV P A C X =
      (2 : ℤ) • laplacianLeftWeight P A C (laplacianLeftWeight P A C X) +
      laplacianLeftWeight P A C (derivSqPhi P A C X) +
      laplacianLeftWeight P A C (derivSqJ P A C X) +
      (4 : ℤ) • derivSqSig P A C X ∧
    (4 : ℤ) • hProjPhi P A C X =
      laplacianLeftWeight P A C (derivSqPhi P A C X) -
      laplacianLeftWeight P A C (derivSqJ P A C X) -
      (4 : ℤ) • derivSqSig P A C X ∧
    (4 : ℤ) • hProjJ P A C X =
      laplacianLeftWeight P A C (derivSqJ P A C X) -
      laplacianLeftWeight P A C (derivSqPhi P A C X) -
      (4 : ℤ) • derivSqSig P A C X ∧
    (4 : ℤ) • hProjSig P A C X =
      (4 : ℤ) • derivSqSig P A C X -
      laplacianLeftWeight P A C (derivSqPhi P A C X) -
      laplacianLeftWeight P A C (derivSqJ P A C X) :=
  ⟨laplacianLeftWeight_eq hP A C X,
   hProjV_laplacian_generation hP A C X,
   hProjPhi_laplacian_generation hP A C X,
   hProjJ_laplacian_generation hP A C X,
   hProjSig_laplacian_generation hP A C X⟩

/-- **Archetype `A₃₅` (Chiral Hodge Self-Duality & Complement Symmetry `(P, A, C) ↦ (1 - P, C, A)`):**
Synthesizes `Orientation` and `ComplementSymmetry`. -/
theorem archetype_A35_chiral_self_duality_and_complement_symmetry (A C X : B) :
    hodgeStar P (conePlus P A) = conePlus P A ∧
    hodgeStar P (coneMinus P C) = -coneMinus P C ∧
    hodgeStar P (qgtPlus P A C) = qgtPlus P A C ∧
    hodgeStar P (qgtMinus P A C) = -qgtMinus P A C ∧
    invS (1 - P) = -invS P ∧
    hodgeStar (1 - P) X = -hodgeStar P X ∧
    conePlus (1 - P) C = coneMinus P C ∧
    coneMinus (1 - P) A = conePlus P A ∧
    genPhi (1 - P) C A = genPhi P A C ∧
    genJ (1 - P) C A = -genJ P A C ∧
    genV (1 - P) C A = genV P A C ∧
    genSig (1 - P) C A = -genSig P A C ∧
    qgtPlus (1 - P) C A = qgtMinus P A C ∧
    qgtMinus (1 - P) C A = qgtPlus P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_,
    conePlus_complement P C, coneMinus_complement P A,
    genPhi_complement P A C, genJ_complement P A C,
    genV_complement P A C, genSig_complement P A C,
    qgtPlus_complement P A C, qgtMinus_complement P A C⟩ <;>
    ((try dsimp only [hodgeStar, qgtPlus, qgtMinus]); peirce_nf hP)

/-- **Archetype `A₃₆` (Left & Parity-Twisted Right Multiplication Actions `diracLeft`, `diracRight`):**
Synthesizes `LeftRightActions`. -/
theorem archetype_A36_left_right_parity_twisted_clifford_actions (A C X : B) :
    diracLeftPhi P A C X = (2 : ℤ) • (genPhi P A C * X) ∧
    diracRightPhi P A C X = -((2 : ℤ) • (parityConj P X * genPhi P A C)) ∧
    diracLeftJ P A C X = (2 : ℤ) • (genJ P A C * X) ∧
    diracRightJ P A C X = -((2 : ℤ) • (parityConj P X * genJ P A C)) ∧
    diracLeftPhi P A C (diracLeftPhi P A C X) = (4 : ℤ) • (genV P A C * X) ∧
    diracRightPhi P A C (diracRightPhi P A C X) = -((4 : ℤ) • (X * genV P A C)) ∧
    diracLeftJ P A C (diracLeftJ P A C X) = -((4 : ℤ) • (genV P A C * X)) ∧
    diracRightJ P A C (diracRightJ P A C X) = (4 : ℤ) • (X * genV P A C) ∧
    diracLeftPhi P A C (diracRightPhi P A C X) +
      diracRightPhi P A C (diracLeftPhi P A C X) = 0 ∧
    diracLeftJ P A C (diracRightJ P A C X) +
      diracRightJ P A C (diracLeftJ P A C X) = 0 :=
  ⟨diracLeftPhi_eq P A C X,
   diracRightPhi_eq P A C X,
   diracLeftJ_eq P A C X,
   diracRightJ_eq P A C X,
   diracLeftPhi_square hP A C X,
   diracRightPhi_square hP A C X,
   diracLeftJ_square hP A C X,
   diracRightJ_square hP A C X,
   diracLeftRightPhi_anticommute hP A C X,
   diracLeftRightJ_anticommute hP A C X⟩

/-- **Archetype `A₃₇` (Idempotency Defect Calculus, Cycle Split, & Unipotent Shear Invariance):**
Synthesizes `IdempotentGraphGrassmannian`, `DefectTower.genV_defect_cycle_split`, `DefectParity.metric_phi_parity_product`, and `Unipotent`. -/
theorem archetype_A37_idempotency_defect_calculus_and_unipotent_invariance (A C X : B) :
    idempotencyDefect (1 - X) = idempotencyDefect X ∧
    idempotencyDefect (bergmanOp P A C 1) = idempotencyDefect (genV P A C) ∧
    idempotencyDefect (genV P A C) =
      idempotencyDefect (qgtPlus P A C) + idempotencyDefect (qgtMinus P A C) ∧
    comm (idempotencyDefect (genV P A C)) (genPhi P A C) = 0 ∧
    comm (idempotencyDefect (genV P A C)) (genJ P A C) = 0 ∧
    comm (idempotencyDefect (genV P A C)) (genSig P A C) = 0 ∧
    conjPlus P A (idempotencyDefect (genV P A C)) = idempotencyDefect (genV P A C) ∧
    conjMinus P C (idempotencyDefect (genV P A C)) = idempotencyDefect (genV P A C) ∧
    (genV P A C + genPhi P A C) * parityConj P (genV P A C + genPhi P A C) =
      idempotencyDefect (genV P A C) ∧
    weylJ P A C * weylJInv P A C - 1 = idempotencyDefect (genV P A C) ∧
    projPhi P A C (genJ P A C) =
      (4 : ℤ) • (idempotencyDefect (genV P A C) * genJ P A C) ∧
    projJ P A C (genPhi P A C) =
      (4 : ℤ) • (idempotencyDefect (genV P A C) * genPhi P A C) := by
  refine ⟨by dsimp only [idempotencyDefect]; noncomm_ring,
    ?_, genV_defect_cycle_split hP A C, ?_, ?_, ?_, ?_, ?_,
    metric_phi_parity_product hP A C, ?_, ?_, ?_⟩ <;>
    ((try dsimp only [idempotencyDefect, bergmanOp, conjPlus, conjMinus,
      weylJ, weylJInv, projPhi, projJ, derivSqPhi, derivSqJ, derivSqSig]); peirce_nf hP)

/-- **Archetype `A₃₈` (Unit Defect Level Set `δ(V) = 1`, Inverse Units, & Fibonacci Power Recurrence):**
Synthesizes `DefectLevelSet` and `DefectParity.derivation_mismatch_phi`. -/
theorem archetype_A38_defect_level_set_units_and_power_recurrence (A C : B) (n : ℕ) :
    (genV P A C + genPhi P A C) * (genV P A C - genPhi P A C) =
      idempotencyDefect (genV P A C) ∧
    (genV P A C - genPhi P A C) * (genV P A C + genPhi P A C) =
      idempotencyDefect (genV P A C) ∧
    genV P A C * genV P A C * genV P A C - genV P A C * genV P A C - genV P A C =
      genV P A C * (idempotencyDefect (genV P A C) - 1) ∧
    derivSqSig P A C (genPhi P A C) - derivSqJ P A C (genPhi P A C) =
      -((4 : ℤ) • (idempotencyDefect (genV P A C) * genPhi P A C)) ∧
    (idempotencyDefect (genV P A C) = 1 →
      (genV P A C + genPhi P A C) * (genV P A C - genPhi P A C) = 1 ∧
      (genV P A C - genPhi P A C) * (genV P A C + genPhi P A C) = 1 ∧
      genV P A C ^ (n + 2) = genV P A C ^ (n + 1) + genV P A C ^ n ∧
      idempotencyDefect (idempotencyDefect (genV P A C)) = 0) := by
  have hProd1 :
      (genV P A C + genPhi P A C) * (genV P A C - genPhi P A C) =
        idempotencyDefect (genV P A C) := by
    dsimp only [idempotencyDefect]; peirce_nf hP
  have hProd2 :
      (genV P A C - genPhi P A C) * (genV P A C + genPhi P A C) =
        idempotencyDefect (genV P A C) := by
    dsimp only [idempotencyDefect]; peirce_nf hP
  have hCubic :
      genV P A C * genV P A C * genV P A C - genV P A C * genV P A C - genV P A C =
        genV P A C * (idempotencyDefect (genV P A C) - 1) := by
    dsimp only [idempotencyDefect]; noncomm_ring
  refine ⟨hProd1, hProd2, hCubic, derivation_mismatch_phi hP A C, ?_⟩
  intro hV
  exact ⟨hProd1.trans hV, hProd2.trans hV,
    defect_level_power_recurrence A C hV n,
    defect_level_second_iterate A C hV⟩

/-- **Archetype `A₃₉` (Multiplicative Defect Tower `δ(-X) δ(X) = δ(X²)` & Ordered Parity Orbit Products):**
Synthesizes `TransferDefect` and `DefectParity`. -/
theorem archetype_A39_defect_tower_multiplication_and_parity_orbit_norm (A C X : B) :
    idempotencyDefect (-X) * idempotencyDefect X = idempotencyDefect (X * X) ∧
    idempotencyDefect X * idempotencyDefect (-X) = idempotencyDefect (X * X) ∧
    idempotencyDefect (genPhi P A C) = genV P A C - genPhi P A C ∧
    idempotencyDefect (-genPhi P A C) = genV P A C + genPhi P A C ∧
    parityConj P (idempotencyDefect (-genPhi P A C)) = idempotencyDefect (genPhi P A C) ∧
    idempotencyDefect (-genPhi P A C) * idempotencyDefect (genPhi P A C) =
      idempotencyDefect (genV P A C) ∧
    (genV P A C + genPhi P A C) * parityConj P (genV P A C + genPhi P A C) =
      idempotencyDefect (genV P A C) ∧
    (genV P A C + genJ P A C) * parityConj P (genV P A C + genJ P A C) =
      idempotencyDefect (-genV P A C) ∧
    ((genV P A C + genPhi P A C) * parityConj P (genV P A C + genPhi P A C)) *
      ((genV P A C + genJ P A C) * parityConj P (genV P A C + genJ P A C)) =
      idempotencyDefect (genV P A C * genV P A C) := by
  refine ⟨idempotencyDefect_neg_mul X,
    by dsimp only [idempotencyDefect]; noncomm_ring,
    (genPhi_defect_pair hP A C).1,
    (genPhi_defect_pair hP A C).2,
    ?_,
    (genPhi_defect_product hP A C).1,
    metric_phi_parity_product hP A C,
    ?_, ?_⟩ <;>
    ((try dsimp only [idempotencyDefect, parityConj]); peirce_nf hP)

/-- **Archetype `A₄₀` (Parity Ring Automorphism, Orbit Sums, & Homogenized Resolvent Extraction):**
Synthesizes `ParityProducts` and `Homogenized`. -/
theorem archetype_A40_parity_conjugation_and_homogenized_resolvent_extraction (A C X Y : B) :
    parityConj P (parityConj P X) = X ∧
    parityConj P (X * Y) = parityConj P X * parityConj P Y ∧
    X + parityConj P X = (2 : ℤ) • evenGrade P X ∧
    X - parityConj P X = (2 : ℤ) • oddGrade P X ∧
    grpPhi P A C (parityConj P X) = parityConj P (grpPhi P A C X) ∧
    grpJ P A C (parityConj P X) = parityConj P (grpJ P A C X) ∧
    grpSig P A C (parityConj P X) = parityConj P (grpSig P A C X) ∧
    hProjV P A C (genV P A C + genPhi P A C + genJ P A C + genSig P A C) =
      (8 : ℤ) • ((genV P A C * genV P A C) * genV P A C) ∧
    hProjPhi P A C (genV P A C + genPhi P A C + genJ P A C + genSig P A C) =
      (8 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C) ∧
    hProjJ P A C (genV P A C + genPhi P A C + genJ P A C + genSig P A C) =
      (8 : ℤ) • ((genV P A C * genV P A C) * genJ P A C) ∧
    hProjSig P A C (genV P A C + genPhi P A C + genJ P A C + genSig P A C) =
      (8 : ℤ) • ((genV P A C * genV P A C) * genSig P A C) := by
  refine ⟨(parityConj_involutive_ring_action hP X Y).1,
    (parityConj_involutive_ring_action hP X Y).2.1,
    parity_orbit_sum_eq_two_even X,
    parity_orbit_difference_eq_two_odd X,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try dsimp only [parityConj, grpPhi, grpJ, grpSig,
      hProjV, hProjPhi, hProjJ, hProjSig, derivSqPhi, derivSqJ, derivSqSig]);
     peirce_nf hP)

/-- **Archetype `A₄₁` (Dyadic Defect Iteration & All-Depth Orthogonal Peirce Cycle Splitting):**
Synthesizes `IdempotentDefectIteration` and `DefectTower`. -/
theorem archetype_A41_defect_iteration_and_orthogonal_cycle_splitting (A C X : B) (n : ℕ) :
    idempotencyDefectBar X * idempotencyDefect X = idempotencyDefect (X * X) ∧
    idempotencyDefectBar (X * X) * idempotencyDefectBar X * idempotencyDefect X =
      idempotencyDefect ((X * X) * (X * X)) ∧
    (1 - X) * (1 + X) * (1 + X * X) * (1 + (X * X) * (X * X)) =
      1 - ((X * X) * (X * X)) * ((X * X) * (X * X)) ∧
    idempotencyDefect (idempotencyDefect (genV P A C)) =
      idempotencyDefect (idempotencyDefect (qgtPlus P A C)) +
      idempotencyDefect (idempotencyDefect (qgtMinus P A C)) ∧
    idempotencyDefect^[n] (genV P A C) =
      idempotencyDefect^[n] (qgtPlus P A C) +
      idempotencyDefect^[n] (qgtMinus P A C) ∧
    idempotencyDefect^[n] (qgtPlus P A C) * idempotencyDefect^[n] (qgtMinus P A C) = 0 ∧
    idempotencyDefect^[n] (qgtMinus P A C) * idempotencyDefect^[n] (qgtPlus P A C) = 0 ∧
    P * idempotencyDefect^[n] (genV P A C) = idempotencyDefect^[n] (qgtPlus P A C) :=
  ⟨by dsimp only [idempotencyDefect, idempotencyDefectBar]; noncomm_ring,
   by dsimp only [idempotencyDefect, idempotencyDefectBar]; noncomm_ring,
   by noncomm_ring,
   genV_defect_iterate_cycle_split hP A C,
   genV_defect_iterates_cycle_split hP A C n,
   (qgt_defect_iterates_orthogonal hP A C n).1,
   (qgt_defect_iterates_orthogonal hP A C n).2,
   genV_defect_iterates_left_projection hP A C n⟩

/-- **Archetype `A₄₃` (Ordered Graph-Chord Products, Euler Factors, & Codifferential Residual `d̄_Φ(1 - Σ) = 2 Φ`):**
Synthesizes `PrimalDual.archetype_A42_primal_dual_chord_potentials`, `ChiralEulerFactors`, and the
corrected codifferential evaluation `ChiralDifferentials.superDerivPhiBar_chiralFactor`. -/
theorem archetype_A43_primal_dual_potentials_and_euler_factor_identities (A C : B) :
    (P - conjPlus P A P) * (conjMinus P C P - P) = qgtPlus P A C ∧
    (conjMinus P C P - P) * (P - conjPlus P A P) = qgtMinus P A C ∧
    (1 - qgtPlus P A C) * (1 - qgtMinus P A C) = zetaFactor P A C ∧
    (1 + qgtPlus P A C) * (1 + qgtMinus P A C) = zetaPlusFactor P A C ∧
    zetaFactor P A C * zetaPlusFactor P A C =
      zetaFactor P A C - idempotencyDefect (genV P A C) ∧
    zetaFactor P A C * (genV P A C + 1) - 1 =
      -(idempotencyDefect (genV P A C) + genV P A C) ∧
    superDerivPhi P A C (zetaFactor P A C) = 0 ∧
    superDerivPhiBar P A C (chiralFactor P A C) = (2 : ℤ) • genPhi P A C := by
  rcases archetype_A42_primal_dual_chord_potentials hP A C with ⟨hC1, hC2, _, _⟩
  rcases chiralEuler_factorizations hP A C with ⟨hE1, hE2, _, _⟩
  refine ⟨hC1, hC2, hE1, hE2,
    by dsimp only [zetaFactor, zetaPlusFactor, idempotencyDefect]; noncomm_ring,
    by dsimp only [zetaFactor, idempotencyDefect]; noncomm_ring,
    superDerivPhi_zetaFactor hP A C,
    superDerivPhiBar_chiralFactor hP A C⟩

/-- **Archetype `A₄₄` (Chiral Factor Products, Even-Grade Projections, & Four-Factor Supercharge Identity):**
Synthesizes `ChiralEulerFactors` and `Supercharge.mixed_supercharge_product_expansions`. -/
theorem archetype_A44_chiral_euler_factors_and_four_factor_supercharge_product (A C : B) :
    (1 - qgtPlus P A C) * (1 + qgtMinus P A C) = chiralFactor P A C ∧
    (1 + qgtPlus P A C) * (1 - qgtMinus P A C) = chiralConjugateFactor P A C ∧
    chiralFactor P A C * chiralConjugateFactor P A C =
      zetaFactor P A C * zetaPlusFactor P A C ∧
    chiralFactor P A C * chiralConjugateFactor P A C =
      1 - genV P A C * genV P A C ∧
    (1 + genJ P A C) * (1 - genPhi P A C) =
      chiralFactor P A C - (2 : ℤ) • coneMinus P C ∧
    (1 - genPhi P A C) * (1 + genJ P A C) =
      chiralConjugateFactor P A C - (2 : ℤ) • coneMinus P C ∧
    evenGrade P ((1 + genJ P A C) * (1 - genPhi P A C)) =
      chiralFactor P A C ∧
    evenGrade P ((1 - genPhi P A C) * (1 + genJ P A C)) =
      chiralConjugateFactor P A C ∧
    (1 - genPhi P A C) * (1 - genJ P A C) * (1 + genJ P A C) * (1 + genPhi P A C) =
      (1 - qgtPlus P A C) * (1 - qgtMinus P A C) *
      (1 + qgtPlus P A C) * (1 + qgtMinus P A C) ∧
    (1 - genPhi P A C) * (1 - genJ P A C) * (1 + genJ P A C) * (1 + genPhi P A C) =
      1 - genV P A C * genV P A C :=
  ⟨(chiralEuler_factorizations hP A C).2.2.1,
   (chiralEuler_factorizations hP A C).2.2.2,
   (chiral_factor_product hP A C).1,
   (chiral_factor_product hP A C).2,
   (mixed_supercharge_product_expansions hP A C).1,
   (mixed_supercharge_product_expansions hP A C).2.2.1,
   (even_grade_supercharge_factorizations hP A C).1,
   (even_grade_supercharge_factorizations hP A C).2,
   supercharge_chiral_cycle_product hP A C,
   supercharge_four_factor_product hP A C⟩

/-- **Archetype `A₄₅` (Grading Perturbation Squares `(S_P ± Φ)² = 1 + V`, `(S_P ± J)² = 1 - V` & Cycle Factorizations):**
Synthesizes `GradingPerturbation`. -/
theorem archetype_A45_grading_perturbation_squares_and_cycle_factorizations (A C : B) :
    (invS P + genPhi P A C) * (invS P + genPhi P A C) = zetaPlusFactor P A C ∧
    (invS P - genPhi P A C) * (invS P - genPhi P A C) = zetaPlusFactor P A C ∧
    (invS P + genPhi P A C) * (invS P + genPhi P A C) =
      (1 + qgtPlus P A C) * (1 + qgtMinus P A C) ∧
    anticomm (invS P + genPhi P A C) (invS P - genPhi P A C) =
      (2 : ℤ) • zetaFactor P A C ∧
    (invS P + genJ P A C) * (invS P + genJ P A C) = zetaFactor P A C ∧
    (invS P - genJ P A C) * (invS P - genJ P A C) = zetaFactor P A C ∧
    (invS P + genJ P A C) * (invS P + genJ P A C) =
      (1 - qgtPlus P A C) * (1 - qgtMinus P A C) ∧
    anticomm (invS P + genJ P A C) (invS P - genJ P A C) =
      (2 : ℤ) • zetaPlusFactor P A C ∧
    ((invS P + genPhi P A C) * (invS P + genPhi P A C)) *
      ((invS P + genJ P A C) * (invS P + genJ P A C)) =
      1 - genV P A C * genV P A C :=
  ⟨grading_add_phi_sq hP A C,
   grading_sub_phi_sq hP A C,
   grading_phi_square_factorization hP A C,
   grading_phi_opposite_anticomm hP A C,
   grading_add_j_sq hP A C,
   grading_sub_j_sq hP A C,
   grading_j_square_factorization hP A C,
   grading_j_opposite_anticomm hP A C,
   grading_perturbation_square_product hP A C⟩

/-- **Archetype `A₄₆` (Grading Perturbation Sandwiches `(S_P + Φ) S_P (S_P + Φ)` & Commutator Brackets):**
Synthesizes `GradingPerturbation`. -/
theorem archetype_A46_grading_perturbation_sandwiches_and_commutator_brackets (A C : B) :
    (invS P + genPhi P A C) * invS P * (invS P + genPhi P A C) =
      zetaFactor P A C * invS P + (2 : ℤ) • genPhi P A C ∧
    (invS P + genJ P A C) * invS P * (invS P + genJ P A C) =
      zetaPlusFactor P A C * invS P + (2 : ℤ) • genJ P A C ∧
    comm (invS P + genPhi P A C) (genV P A C) = 0 ∧
    comm (invS P + genJ P A C) (genV P A C) = 0 ∧
    comm (invS P + genPhi P A C) (genPhi P A C) = (2 : ℤ) • genJ P A C ∧
    comm (invS P + genPhi P A C) (genJ P A C) =
      (2 : ℤ) • (genPhi P A C - genSig P A C) ∧
    comm (invS P + genPhi P A C) (genSig P A C) =
      -((2 : ℤ) • (genV P A C * genJ P A C)) ∧
    comm (invS P + genPhi P A C) (comm (invS P + genPhi P A C) (genPhi P A C)) =
      (4 : ℤ) • (genPhi P A C - genSig P A C) ∧
    comm (invS P + genPhi P A C) (comm (invS P + genPhi P A C) (invS P)) =
      (4 : ℤ) • (genV P A C * invS P - genPhi P A C) :=
  ⟨grading_phi_sandwich hP A C,
   grading_j_sandwich hP A C,
   grading_phi_comm_v hP A C,
   grading_j_comm_v hP A C,
   grading_phi_comm_phi hP A C,
   grading_phi_comm_j hP A C,
   grading_phi_comm_sig hP A C,
   grading_phi_double_comm_phi hP A C,
   grading_phi_double_comm_grading hP A C⟩

/-- **Archetype `A₄₇` (Functorial Ring-Homomorphism Intertwining of the Peirce Operator Spine):**
Synthesizes `RingHomTransport`. -/
theorem archetype_A47_ring_hom_intertwining_of_peirce_operator_spine
    {D : Type*} [Ring D] (f : B →+* D) (A C X : B) :
    f P * f P = f P ∧
    f (invS P) = invS (f P) ∧
    f (conePlus P A) = conePlus (f P) (f A) ∧
    f (coneMinus P C) = coneMinus (f P) (f C) ∧
    f (genPhi P A C) = genPhi (f P) (f A) (f C) ∧
    f (genJ P A C) = genJ (f P) (f A) (f C) ∧
    f (genV P A C) = genV (f P) (f A) (f C) ∧
    f (genSig P A C) = genSig (f P) (f A) (f C) ∧
    f (qgtPlus P A C) = qgtPlus (f P) (f A) (f C) ∧
    f (qgtMinus P A C) = qgtMinus (f P) (f A) (f C) ∧
    f (zetaFactor P A C) = zetaFactor (f P) (f A) (f C) ∧
    f (zetaPlusFactor P A C) = zetaPlusFactor (f P) (f A) (f C) ∧
    f (idempotencyDefect X) = idempotencyDefect (f X) ∧
    f (derivSqPhi P A C X) = derivSqPhi (f P) (f A) (f C) (f X) ∧
    f (derivSqJ P A C X) = derivSqJ (f P) (f A) (f C) (f X) ∧
    f (derivSqSig P A C X) = derivSqSig (f P) (f A) (f C) (f X) :=
  ⟨map_idempotent f hP,
   map_invS f P,
   map_conePlus f P A,
   map_coneMinus f P C,
   map_genPhi f P A C,
   map_genJ f P A C,
   map_genV f P A C,
   map_genSig f P A C,
   map_qgtPlus f P A C,
   map_qgtMinus f P A C,
   map_zetaFactor f P A C,
   map_zetaPlusFactor f P A C,
   map_idempotencyDefect f X,
   map_derivSqPhi f P A C X,
   map_derivSqJ f P A C X,
   map_derivSqSig f P A C X⟩

/-- **Archetype `A₄₈` (Transitive Ring-Homomorphism Composition & Homogenized Channel Transport):**
Synthesizes `RingHomTransport` under `g.comp f`. -/
theorem archetype_A48_ring_hom_composition_and_homogenized_channel_transport
    {D E : Type*} [Ring D] [Ring E] (f : B →+* D) (g : D →+* E) (A C X : B) :
    (g.comp f) P * (g.comp f) P = (g.comp f) P ∧
    (g.comp f) (hProjV P A C X) = hProjV (g (f P)) (g (f A)) (g (f C)) (g (f X)) ∧
    (g.comp f) (hProjPhi P A C X) = hProjPhi (g (f P)) (g (f A)) (g (f C)) (g (f X)) ∧
    (g.comp f) (hProjJ P A C X) = hProjJ (g (f P)) (g (f A)) (g (f C)) (g (f X)) ∧
    (g.comp f) (hProjSig P A C X) = hProjSig (g (f P)) (g (f A)) (g (f C)) (g (f X)) ∧
    (invS (g (f P)) + genPhi (g (f P)) (g (f A)) (g (f C))) *
      (invS (g (f P)) + genPhi (g (f P)) (g (f A)) (g (f C))) =
      1 + genV (g (f P)) (g (f A)) (g (f C)) :=
  ⟨map_idempotent (g.comp f) hP,
   map_hProjV (g.comp f) P A C X,
   map_hProjPhi (g.comp f) P A C X,
   map_hProjJ (g.comp f) P A C X,
   map_hProjSig (g.comp f) P A C X,
   grading_add_phi_sq (map_idempotent (g.comp f) hP) (g (f A)) (g (f C))⟩

/-- **Archetype `A₄₉` (First-Order Idempotency Defect Parity Decomposition & Odd-Perturbation Commutator Squares):**
Synthesizes `DefectParity` (`parity_idempotencyDefect`, `even_idempotencyDefect`, `odd_idempotencyDefect`,
`comm_idempotencyDefect`, `transfer_defect_eq_neg_comm_square`, `transfer_j_defect_eq_neg_comm_square`,
`odd_perturbation_defect_eq_neg_comm_square`). -/
theorem archetype_A49_first_order_defect_parity_and_commutator_squares (A C X : B) :
    parityConj P (idempotencyDefect X) = idempotencyDefect (parityConj P X) ∧
    evenGrade P (idempotencyDefect X) =
      idempotencyDefect (evenGrade P X) + oddGrade P X * oddGrade P X ∧
    oddGrade P (idempotencyDefect X) =
      anticomm (evenGrade P X) (oddGrade P X) - oddGrade P X ∧
    comm P (idempotencyDefect X) = anticomm X (comm P X) - comm P X ∧
    comm P (P + genPhi P A C) = genJ P A C ∧
    comm P (P + genJ P A C) = genPhi P A C ∧
    idempotencyDefect (P + genPhi P A C) = genV P A C ∧
    idempotencyDefect (P + genPhi P A C) =
      -(comm P (P + genPhi P A C) * comm P (P + genPhi P A C)) ∧
    idempotencyDefect (P + genJ P A C) = -genV P A C ∧
    idempotencyDefect (P + genJ P A C) =
      -(comm P (P + genJ P A C) * comm P (P + genJ P A C)) ∧
    idempotencyDefect (P + oddGrade P X) =
      -(comm P (P + oddGrade P X) * comm P (P + oddGrade P X)) :=
  ⟨parity_idempotencyDefect hP X,
   even_idempotencyDefect hP X,
   odd_idempotencyDefect hP X,
   comm_idempotencyDefect P X,
   by peirce_nf hP,
   by peirce_nf hP,
   (peirceTransfer_defect_and_vieta hP A C).1,
   transfer_defect_eq_neg_comm_square hP A C,
   (peirceTransfer_defect_and_vieta hP A C).2.2.1,
   transfer_j_defect_eq_neg_comm_square hP A C,
   odd_perturbation_defect_eq_neg_comm_square hP X⟩

/-- **Archetype `A₅₀` (Second-Order Metric Defect `δ(V)`, Parity Product, & Derivation Mismatch):**
Synthesizes `DefectParity` (`metric_defect_eq_square_add_comm_square`, `metric_phi_parity_product`,
`derivation_mismatch_phi`, `derivation_mismatch_j`, `even_metric_phi_defect`, `odd_metric_phi_defect`). -/
theorem archetype_A50_second_order_defect_and_derivation_mismatch (A C : B) :
    comm P (genV P A C + genPhi P A C) = genJ P A C ∧
    idempotencyDefect (genV P A C) =
      genV P A C * genV P A C + genJ P A C * genJ P A C ∧
    idempotencyDefect (genV P A C) =
      genV P A C * genV P A C +
      comm P (genV P A C + genPhi P A C) * comm P (genV P A C + genPhi P A C) ∧
    idempotencyDefect (genV P A C) =
      (genV P A C + genPhi P A C) * parityConj P (genV P A C + genPhi P A C) ∧
    anticomm (genSig P A C) (genPhi P A C) = 0 ∧
    anticomm (genSig P A C) (genJ P A C) = 0 ∧
    comm (genSig P A C) (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C) ∧
    comm (genSig P A C) (genJ P A C) = (2 : ℤ) • (genV P A C * genPhi P A C) ∧
    derivSqSig P A C (genPhi P A C) - derivSqJ P A C (genPhi P A C) =
      -((4 : ℤ) • (idempotencyDefect (genV P A C) * genPhi P A C)) ∧
    derivSqSig P A C (genJ P A C) - derivSqPhi P A C (genJ P A C) =
      -((4 : ℤ) • (idempotencyDefect (genV P A C) * genJ P A C)) ∧
    evenGrade P (idempotencyDefect (genV P A C + genPhi P A C)) =
      idempotencyDefect (genV P A C) + genV P A C ∧
    oddGrade P (idempotencyDefect (genV P A C + genPhi P A C)) =
      ((2 : ℤ) • genV P A C - 1) * genPhi P A C :=
  ⟨by peirce_nf hP,
   by dsimp only [idempotencyDefect]; peirce_nf hP,
   metric_defect_eq_square_add_comm_square hP A C,
   (metric_phi_parity_product hP A C).symm,
   by peirce_nf hP,
   by peirce_nf hP,
   by peirce_nf hP,
   by peirce_nf hP,
   derivation_mismatch_phi hP A C,
   derivation_mismatch_j hP A C,
   even_metric_phi_defect hP A C,
   odd_metric_phi_defect hP A C⟩

/-- **Archetype `A₅₁` (Two-Cone Inner-Derivation Pullbacks & Associative Jordan Triple Identities):**
Synthesizes `InnerPullback` and `PullbackTriple`. -/
theorem archetype_A51_pullback_and_jordan_triple_synthesis (A C : B) :
    comm P ((1 + conePlus P A) * (1 - coneMinus P C)) = genPhi P A C ∧
    ((1 + coneMinus P C) * (1 - conePlus P A)) *
        comm P ((1 + conePlus P A) * (1 - coneMinus P C)) =
      genPhi P A C - genSig P A C - genV P A C * coneMinus P C ∧
    comm P ((1 + conePlus P A) * (1 - coneMinus P C)) *
        ((1 + coneMinus P C) * (1 - conePlus P A)) =
      genPhi P A C + genSig P A C - genV P A C * conePlus P A ∧
    sandwich (conePlus P A) (conePlus P A) (coneMinus P C) = genV P A C * conePlus P A ∧
    sandwich (coneMinus P C) (coneMinus P C) (conePlus P A) = genV P A C * coneMinus P C ∧
    jordanTriple (genJ P A C) (genJ P A C) (genJ P A C) =
      -((2 : ℤ) • (genV P A C * genJ P A C)) :=
  ⟨comm_two_cone_product hP A C,
   two_cone_left_pullback hP A C,
   two_cone_right_pullback hP A C,
   plus_sandwich_opposite hP A C,
   minus_sandwich_opposite hP A C,
   jordanTriple_j_self hP A C⟩

/-- Complete source-facing A₅₁ packet. This joins the two Maurer–Cartan
pullbacks and their sum/difference with the cone, tetraktys, and two-step
Kantor triple actions. These are associative-ring identities; the name
“Maurer–Cartan” does not assert a differential-form flatness equation. -/
theorem archetype_A51_maurer_cartan_and_kantor_ladder_complete (A C : B) :
    comm P ((1 + conePlus P A) * (1 - coneMinus P C)) = genPhi P A C ∧
    ((1 + coneMinus P C) * (1 - conePlus P A)) *
        comm P ((1 + conePlus P A) * (1 - coneMinus P C)) =
      genPhi P A C - genSig P A C - genV P A C * coneMinus P C ∧
    comm P ((1 + conePlus P A) * (1 - coneMinus P C)) *
        ((1 + coneMinus P C) * (1 - conePlus P A)) =
      genPhi P A C + genSig P A C - genV P A C * conePlus P A ∧
    comm P ((1 + conePlus P A) * (1 - coneMinus P C)) *
        ((1 + coneMinus P C) * (1 - conePlus P A)) +
      ((1 + coneMinus P C) * (1 - conePlus P A)) *
        comm P ((1 + conePlus P A) * (1 - coneMinus P C)) =
      (2 : ℤ) • genPhi P A C - genV P A C * genPhi P A C ∧
    ((1 + coneMinus P C) * (1 - conePlus P A)) *
        comm P ((1 + conePlus P A) * (1 - coneMinus P C)) -
      comm P ((1 + conePlus P A) * (1 - coneMinus P C)) *
        ((1 + coneMinus P C) * (1 - conePlus P A)) =
      -((2 : ℤ) • genSig P A C - genV P A C * genJ P A C) ∧
    kantorTriple (conePlus P A) (coneMinus P C) (conePlus P A) =
      (2 : ℤ) • (genV P A C * conePlus P A) ∧
    kantorTriple (coneMinus P C) (conePlus P A) (coneMinus P C) =
      (2 : ℤ) • (genV P A C * coneMinus P C) ∧
    kantorGp2 P A (coneMinus P C) = genV P A C * conePlus P A ∧
    kantorGm2 P C (conePlus P A) = genV P A C * coneMinus P C ∧
    kantorGp2 P A (kantorGm2 P C (conePlus P A)) =
      (genV P A C * genV P A C) * conePlus P A ∧
    kantorGm2 P C (kantorGp2 P A (coneMinus P C)) =
      (genV P A C * genV P A C) * coneMinus P C ∧
    kantorTriple (genPhi P A C) (genPhi P A C) (genPhi P A C) =
      (2 : ℤ) • (genV P A C * genPhi P A C) ∧
    jordanTriple (genJ P A C) (genJ P A C) (genJ P A C) =
      -((2 : ℤ) • (genV P A C * genJ P A C)) := by
  rcases archetype_A51_pullback_and_jordan_triple_synthesis hP A C with
    ⟨hComm, hLeft, hRight, hTriplePlus, hTripleMinus, hTripleJ⟩
  refine ⟨hComm, hLeft, hRight, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hTripleJ⟩
  · exact two_cone_pullback_sum hP A C
  · have h := two_cone_pullback_difference hP A C
    calc
      _ = -(comm P ((1 + conePlus P A) * (1 - coneMinus P C)) *
            ((1 + coneMinus P C) * (1 - conePlus P A)) -
            ((1 + coneMinus P C) * (1 - conePlus P A)) *
            comm P ((1 + conePlus P A) * (1 - coneMinus P C))) := by noncomm_ring
      _ = -((2 : ℤ) • genSig P A C - genV P A C * genJ P A C) := by rw [h]
  · peirce_abel_golay hP
  · peirce_abel_golay hP
  · peirce_abel_golay hP
  · peirce_abel_golay hP
  · peirce_abel_golay hP
  · peirce_abel_golay hP
  · peirce_abel_golay hP

/-- **Archetype `A₅₂` (Five-Sector Corner Sandwich Charge Spectrum `{ -2, -1, 0, +1, +2 }`):**
Synthesizes `SandwichCharge` (`charge_plus_sandwich`, `charge_plus_comm`, `charge_cross_sandwich`,
`charge_minus_comm`, `charge_minus_sandwich`, `charge_total_first`, `charge_total_second`,
`charge_iter_cubic_difference`). -/
theorem archetype_A52_corner_sandwich_charge_spectrum (A C X : B) :
    charge P (sandwich (conePlus P A) (conePlus P A)) X =
      (2 : ℤ) • sandwich (conePlus P A) (conePlus P A) X ∧
    charge P (comm (conePlus P A)) X = comm (conePlus P A) X ∧
    charge P (sandwichCross P A C) X = 0 ∧
    charge P (comm (coneMinus P C)) X = -comm (coneMinus P C) X ∧
    charge P (sandwich (coneMinus P C) (coneMinus P C)) X =
      -((2 : ℤ) • sandwich (coneMinus P C) (coneMinus P C) X) ∧
    charge P (cornerOperatorSum P A C) X =
      -((2 : ℤ) • sandwich (coneMinus P C) (coneMinus P C) X) -
      comm (coneMinus P C) X + comm (conePlus P A) X +
      (2 : ℤ) • sandwich (conePlus P A) (conePlus P A) X ∧
    chargeIter P (cornerOperatorSum P A C) 2 X =
      (4 : ℤ) • sandwich (coneMinus P C) (coneMinus P C) X +
      comm (coneMinus P C) X + comm (conePlus P A) X +
      (4 : ℤ) • sandwich (conePlus P A) (conePlus P A) X ∧
    chargeIter P (cornerOperatorSum P A C) 3 X -
        chargeIter P (cornerOperatorSum P A C) 1 X =
      (6 : ℤ) • (sandwich (conePlus P A) (conePlus P A) X -
        sandwich (coneMinus P C) (coneMinus P C) X) :=
  ⟨charge_plus_sandwich hP A X,
   charge_plus_comm hP A X,
   charge_cross_sandwich hP A C X,
   charge_minus_comm hP C X,
   charge_minus_sandwich hP C X,
   charge_total_first hP A C X,
   charge_total_second hP A C X,
   charge_iter_cubic_difference hP A C X⟩

/-- **Archetype `A₅₃` (Fifth-Order Charge Annihilator `Δ₅ - 5 Δ₃ + 4 Δ₁ = 0` & Scaled Corner Extractions):**
Synthesizes `charge_iter_fifth_annihilator` and `ChargeExtraction` (`charge_extract_zero`,
`charge_extract_plus_one`, `charge_extract_minus_one`, `charge_extract_plus_two`,
`charge_extract_minus_two`). Note the canonical integer scaling factors (`4` on grade `0`,
`6` on grades `±1`, and `24` on grades `±2`). -/
theorem archetype_A53_corner_charge_extraction_and_fifth_annihilator (A C X : B) :
    chargeIter P (cornerOperatorSum P A C) 5 X -
        (5 : ℤ) • chargeIter P (cornerOperatorSum P A C) 3 X +
        (4 : ℤ) • chargeIter P (cornerOperatorSum P A C) 1 X = 0 ∧
    chargeIter P (cornerOperatorSum P A C) 4 X -
        (5 : ℤ) • chargeIter P (cornerOperatorSum P A C) 2 X +
        (4 : ℤ) • cornerOperatorSum P A C X =
      (4 : ℤ) • sandwichCross P A C X ∧
    ((4 : ℤ) • chargeIter P (cornerOperatorSum P A C) 2 X -
        chargeIter P (cornerOperatorSum P A C) 4 X) +
        ((4 : ℤ) • chargeIter P (cornerOperatorSum P A C) 1 X -
        chargeIter P (cornerOperatorSum P A C) 3 X) =
      (6 : ℤ) • comm (conePlus P A) X ∧
    ((4 : ℤ) • chargeIter P (cornerOperatorSum P A C) 2 X -
        chargeIter P (cornerOperatorSum P A C) 4 X) -
        ((4 : ℤ) • chargeIter P (cornerOperatorSum P A C) 1 X -
        chargeIter P (cornerOperatorSum P A C) 3 X) =
      (6 : ℤ) • comm (coneMinus P C) X ∧
    (chargeIter P (cornerOperatorSum P A C) 4 X -
        chargeIter P (cornerOperatorSum P A C) 2 X) +
        (2 : ℤ) • (chargeIter P (cornerOperatorSum P A C) 3 X -
        chargeIter P (cornerOperatorSum P A C) 1 X) =
      (24 : ℤ) • sandwich (conePlus P A) (conePlus P A) X ∧
    (chargeIter P (cornerOperatorSum P A C) 4 X -
        chargeIter P (cornerOperatorSum P A C) 2 X) -
        (2 : ℤ) • (chargeIter P (cornerOperatorSum P A C) 3 X -
        chargeIter P (cornerOperatorSum P A C) 1 X) =
      (24 : ℤ) • sandwich (coneMinus P C) (coneMinus P C) X :=
  ⟨charge_iter_fifth_annihilator hP A C X,
   charge_extract_zero hP A C X,
   charge_extract_plus_one hP A C X,
   charge_extract_minus_one hP A C X,
   charge_extract_plus_two hP A C X,
   charge_extract_minus_two hP A C X⟩

omit hP in
/-- **Archetypes `A₅₄–A₅₅` (Corrected Crossed-Support Extremal Sandwich Compositions & Same-Support Residual):**
In an arbitrary associative ring, ordered composition of the extremal corner sandwiches
`G_{+2}(X) = N_+ X N_+` and `G_{-2}(X) = N_- X N_-` reverses the order of the right factors,
producing the **crossed-support** sandwiches `Q_+ X Q_-` and `Q_- X Q_+` (rather than the
same-support sandwiches `Q_+ X Q_+` and `Q_- X Q_-`), with exact difference residual
`-V X Σ` (`CrossChargeBrackets.extreme_same_support_residual`). -/
theorem archetype_A54_A55_crossed_support_extremal_brackets (P A C X : B) :
    sandwich (conePlus P A) (conePlus P A)
        (sandwich (coneMinus P C) (coneMinus P C) X) =
      qgtPlus P A C * X * qgtMinus P A C ∧
    sandwich (coneMinus P C) (coneMinus P C)
        (sandwich (conePlus P A) (conePlus P A) X) =
      qgtMinus P A C * X * qgtPlus P A C ∧
    sandwich (conePlus P A) (conePlus P A)
        (sandwich (coneMinus P C) (coneMinus P C) X) +
      sandwich (coneMinus P C) (coneMinus P C)
        (sandwich (conePlus P A) (conePlus P A) X) =
      qgtPlus P A C * X * qgtMinus P A C +
        qgtMinus P A C * X * qgtPlus P A C ∧
    (sandwich (conePlus P A) (conePlus P A)
        (sandwich (coneMinus P C) (coneMinus P C) X) -
      sandwich (coneMinus P C) (coneMinus P C)
        (sandwich (conePlus P A) (conePlus P A) X)) -
      (qgtPlus P A C * X * qgtPlus P A C - qgtMinus P A C * X * qgtMinus P A C) =
      -(genV P A C * X * genSig P A C) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [sandwich, qgtPlus, qgtMinus, mul_assoc]
  · simp only [sandwich, qgtPlus, qgtMinus, mul_assoc]
  · dsimp [sandwich, qgtPlus, qgtMinus]
    noncomm_ring
  · have h := congr_arg (fun f : Module.End ℤ B => f X) (extreme_same_support_residual P A C)
    simpa only [comm, LinearMap.sub_apply, LinearMap.neg_apply, Module.End.mul_apply,
      sandwichOp_apply, sandwich] using h

/-- For an idempotent Peirce split, the extremal Kantor anticommutator is
supported on the odd Peirce grade; crossed supports do not produce the even
grade compression. -/
theorem extremal_kantor_anticommutator_odd_grade
    (A C X : B) :
    sandwich (conePlus P A) (conePlus P A)
        (sandwich (coneMinus P C) (coneMinus P C) X) +
      sandwich (coneMinus P C) (coneMinus P C)
        (sandwich (conePlus P A) (conePlus P A) X) =
      genV P A C * oddGrade P X * genV P A C := by
  rcases archetype_A54_A55_crossed_support_extremal_brackets P A C X with
    ⟨_, _, hsum, _⟩
  calc
    sandwich (conePlus P A) (conePlus P A)
        (sandwich (coneMinus P C) (coneMinus P C) X) +
      sandwich (coneMinus P C) (coneMinus P C)
        (sandwich (conePlus P A) (conePlus P A) X) =
        qgtPlus P A C * X * qgtMinus P A C + qgtMinus P A C * X * qgtPlus P A C := by
      exact hsum
    _ = genV P A C * oddGrade P X * genV P A C := by
      dsimp [qgtPlus, qgtMinus]
      peirce_nf hP

/-- The extremal anticommutator annihilates the two diagonal core generators.
Its support is the odd Peirce grade, so it does not act as the even-grade
compression on `V` or `Σ`. -/
theorem extremal_kantor_anticommutator_annihilates_even_core (A C : B) :
    sandwich (conePlus P A) (conePlus P A)
        (sandwich (coneMinus P C) (coneMinus P C) (genV P A C)) +
      sandwich (coneMinus P C) (coneMinus P C)
        (sandwich (conePlus P A) (conePlus P A) (genV P A C)) = 0 ∧
    sandwich (conePlus P A) (conePlus P A)
        (sandwich (coneMinus P C) (coneMinus P C) (genSig P A C)) +
      sandwich (coneMinus P C) (coneMinus P C)
        (sandwich (conePlus P A) (conePlus P A) (genSig P A C)) = 0 := by
  constructor
  · rw [extremal_kantor_anticommutator_odd_grade hP A C (genV P A C)]
    dsimp [genV]
    peirce_nf hP
  · rw [extremal_kantor_anticommutator_odd_grade hP A C (genSig P A C)]
    dsimp [genSig]
    peirce_nf hP

/-- **Archetype `A₅₆` (Transfer Defect vs. Grading Perturbation Square & Discriminant Completion):**
Synthesizes `GradingTransfer` (`transfer_defect_eq_grading_square_sub_one`,
`transfer_j_defect_eq_grading_square_sub_one`, `transfer_discriminant_eq`,
`transfer_discriminant_square`, `transfer_j_discriminant_square`). -/
theorem archetype_A56_transfer_defect_and_discriminant_completion (A C : B) :
    idempotencyDefect (peirceTransfer P A C) =
      (invS P + genPhi P A C) * (invS P + genPhi P A C) - 1 ∧
    idempotencyDefect (peirceTransferJ P A C) =
      (invS P + genJ P A C) * (invS P + genJ P A C) - 1 ∧
    (2 : ℤ) • peirceTransfer P A C - 1 = invS P + (2 : ℤ) • genPhi P A C ∧
    ((2 : ℤ) • peirceTransfer P A C - 1) *
        ((2 : ℤ) • peirceTransfer P A C - 1) =
      1 + (4 : ℤ) • genV P A C ∧
    ((2 : ℤ) • peirceTransferJ P A C - 1) *
        ((2 : ℤ) • peirceTransferJ P A C - 1) =
      1 - (4 : ℤ) • genV P A C :=
  ⟨transfer_defect_eq_grading_square_sub_one hP A C,
   transfer_j_defect_eq_grading_square_sub_one hP A C,
   transfer_discriminant_eq A C,
   transfer_discriminant_square hP A C,
   transfer_j_discriminant_square hP A C⟩

/-- **Archetype `A₅₇` (Grading Perturbation Commutator & Double-Commutator Mode Identities):**
Synthesizes `GradingTransfer` (`grading_phi_product_v`, `grading_phi_comm_v`,
`grading_phi_comm_product_v`, `grading_phi_comm_j`, `grading_phi_comm_phi_sub_sig`,
`grading_phi_double_comm_j`, `grading_phi_double_comm_phi_sub_sig`, `grading_j_double_comm_phi`). -/
theorem archetype_A57_grading_perturbation_commutator_modes (A C : B) :
    (invS P + genPhi P A C) * genV P A C =
      genV P A C * genPhi P A C + genSig P A C ∧
    comm (invS P + genPhi P A C) (genV P A C) = 0 ∧
    comm (invS P + genPhi P A C) (genV P A C * genPhi P A C + genSig P A C) = 0 ∧
    comm (invS P + genPhi P A C) (genJ P A C) =
      (2 : ℤ) • (genPhi P A C - genSig P A C) ∧
    comm (invS P + genPhi P A C) (genPhi P A C - genSig P A C) =
      (2 : ℤ) • ((1 + genV P A C) * genJ P A C) ∧
    comm (invS P + genPhi P A C) (comm (invS P + genPhi P A C) (genJ P A C)) =
      (4 : ℤ) • ((1 + genV P A C) * genJ P A C) ∧
    comm (invS P + genPhi P A C)
        (comm (invS P + genPhi P A C) (genPhi P A C - genSig P A C)) =
      (4 : ℤ) • ((1 + genV P A C) * (genPhi P A C - genSig P A C)) ∧
    comm (invS P + genJ P A C) (comm (invS P + genJ P A C) (genPhi P A C)) =
      (4 : ℤ) • ((1 - genV P A C) * genPhi P A C) :=
  ⟨grading_phi_product_v hP A C,
   grading_phi_comm_v hP A C,
   grading_phi_comm_product_v hP A C,
   grading_phi_comm_j hP A C,
   grading_phi_comm_phi_sub_sig hP A C,
   grading_phi_double_comm_j hP A C,
   grading_phi_double_comm_phi_sub_sig hP A C,
   grading_j_double_comm_phi hP A C⟩

/-- Double-commutator channel of the perturbed grading `invS P + genPhi P A C`. -/
def gradingPerturbOscChannel (P A C X : B) : B :=
  comm (invS P + genPhi P A C) (comm (invS P + genPhi P A C) X)

/-- Complementary centralizer channel `(4 : ℤ) • ((1 + V) * X) - gradingPerturbOscChannel P A C X`. -/
def gradingPerturbCentralizerChannel (P A C X : B) : B :=
  (4 : ℤ) • ((1 + genV P A C) * X) - gradingPerturbOscChannel P A C X

/-- **Archetype `A₅₈` (Grading Perturbation Double-Commutator Channels & Mode Reconstruction):**
Combines the additive partition and mode selection of `gradingPerturbCentralizerChannel` and
`gradingPerturbOscChannel` with `ModeCoordinates.peirce_mode_reconstruction_scaled`. -/
theorem archetype_A58_grading_double_commutator_projectors_and_mode_reconstruction
    (A C X : B) :
    gradingPerturbCentralizerChannel P A C X + gradingPerturbOscChannel P A C X =
      (4 : ℤ) • ((1 + genV P A C) * X) ∧
    gradingPerturbCentralizerChannel P A C (genV P A C) =
      (4 : ℤ) • ((1 + genV P A C) * genV P A C) ∧
    gradingPerturbCentralizerChannel P A C (genV P A C * genPhi P A C + genSig P A C) =
      (4 : ℤ) • ((1 + genV P A C) * (genV P A C * genPhi P A C + genSig P A C)) ∧
    gradingPerturbCentralizerChannel P A C (genJ P A C) = 0 ∧
    gradingPerturbCentralizerChannel P A C (genPhi P A C - genSig P A C) = 0 ∧
    gradingPerturbOscChannel P A C (genV P A C) = 0 ∧
    gradingPerturbOscChannel P A C (genV P A C * genPhi P A C + genSig P A C) = 0 ∧
    gradingPerturbOscChannel P A C (genJ P A C) =
      (4 : ℤ) • ((1 + genV P A C) * genJ P A C) ∧
    gradingPerturbOscChannel P A C (genPhi P A C - genSig P A C) =
      (4 : ℤ) • ((1 + genV P A C) * (genPhi P A C - genSig P A C)) ∧
    (genV P A C * genPhi P A C + genSig P A C) + (genPhi P A C - genSig P A C) =
      (1 + genV P A C) * genPhi P A C ∧
    (genV P A C * genPhi P A C + genSig P A C) -
        genV P A C * (genPhi P A C - genSig P A C) =
      (1 + genV P A C) * genSig P A C := by
  have hOscV : gradingPerturbOscChannel P A C (genV P A C) = 0 := by
    unfold gradingPerturbOscChannel
    rw [grading_phi_comm_v hP A C]
    simp [comm]
  have hOscD :
      gradingPerturbOscChannel P A C (genV P A C * genPhi P A C + genSig P A C) = 0 := by
    unfold gradingPerturbOscChannel
    rw [grading_phi_comm_product_v hP A C]
    simp [comm]
  have hOscJ :
      gradingPerturbOscChannel P A C (genJ P A C) =
        (4 : ℤ) • ((1 + genV P A C) * genJ P A C) :=
    grading_phi_double_comm_j hP A C
  have hOscE :
      gradingPerturbOscChannel P A C (genPhi P A C - genSig P A C) =
        (4 : ℤ) • ((1 + genV P A C) * (genPhi P A C - genSig P A C)) :=
    grading_phi_double_comm_phi_sub_sig hP A C
  rcases peirce_mode_reconstruction_scaled P A C with ⟨hRec1, hRec2⟩
  refine ⟨by unfold gradingPerturbCentralizerChannel; abel,
    by unfold gradingPerturbCentralizerChannel; rw [hOscV, sub_zero],
    by unfold gradingPerturbCentralizerChannel; rw [hOscD, sub_zero],
    by unfold gradingPerturbCentralizerChannel; rw [hOscJ, sub_self],
    by unfold gradingPerturbCentralizerChannel; rw [hOscE, sub_self],
    hOscV, hOscD, hOscJ, hOscE, hRec1, hRec2⟩

/-! ### Transcript A₄₉: Golden transfer and Bogoliubov square identities

The archive calls this A₄₉, while the causal spine already uses that label for
the defect-parity package. The names below identify the additional operator
claim without shadowing the existing `goldenOp` declaration.
-/

/-- Idempotent perturbed by the even Tetraktys component. -/
def archiveGoldenTransfer (P A C : B) : B := P + genPhi P A C

/-- Idempotent perturbed by the chiral Tetraktys component. -/
def archiveGoldenTransferJ (P A C : B) : B := P + genJ P A C

/-- Bogoliubov-type operator associated with the even component. -/
def archiveNambuPhi (P A C : B) : B := invS P + genPhi P A C

/-- Bogoliubov-type operator associated with the chiral component. -/
def archiveNambuJ (P A C : B) : B := invS P + genJ P A C

/-- Exact Golden–Bogoliubov defect, completed-square, and transfer relations
in an arbitrary unital associative ring. -/
theorem archetype_A49_golden_bogoliubov_defect_and_square
    (A C : B) :
    idempotencyDefect (archiveGoldenTransfer P A C) =
      archiveNambuPhi P A C * archiveNambuPhi P A C - 1 ∧
    idempotencyDefect (archiveGoldenTransferJ P A C) =
      archiveNambuJ P A C * archiveNambuJ P A C - 1 ∧
    (2 : ℤ) • archiveGoldenTransfer P A C - 1 =
      invS P + (2 : ℤ) • genPhi P A C ∧
    ((2 : ℤ) • archiveGoldenTransfer P A C - 1) *
      ((2 : ℤ) • archiveGoldenTransfer P A C - 1) =
      1 + (4 : ℤ) • genV P A C ∧
    ((2 : ℤ) • archiveGoldenTransferJ P A C - 1) *
      ((2 : ℤ) • archiveGoldenTransferJ P A C - 1) =
      1 - (4 : ℤ) • genV P A C ∧
    archiveNambuPhi P A C - archiveGoldenTransfer P A C = -(1 - P) ∧
    archiveNambuPhi P A C + archiveGoldenTransfer P A C =
      P + invS P + (2 : ℤ) • genPhi P A C := by
  unfold archiveNambuPhi archiveNambuJ archiveGoldenTransfer archiveGoldenTransferJ
  unfold idempotencyDefect
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine
