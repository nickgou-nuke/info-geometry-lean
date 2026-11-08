/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.OntologyRing
import InfoGeometry.Meta.Architecture
import InfoGeometry.OperatorAlgebra.OperatorMobiusAction
import InfoGeometry.OperatorAlgebra.OperatorRiccatiRowChart
import InfoGeometry.SuperGrassmannian.GradedGraphTransition
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.PeirceSpine.Orientation
import InfoGeometry.OperatorAlgebra.PeirceSpine.MultiplicatioLogisticTower
import InfoGeometry.Topology.KleinOperatorAlgebraAssociatedQuotient
import InfoGeometry.SuperGrassmannian.BerezinianSheafStiefelWhitney
import InfoGeometry.SuperGrassmannian.WeylBerezinianDeformation
import InfoGeometry.Canonical.BdGSchurBerezinianCompatibility
import InfoGeometry.Algebra.CuntzTensorQuotientPositivityObstruction
import InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity

/-!
# Supergraded Operator Möbius, Peirce Tetraktys Orientation, Klein Quotient Gluing & Schur–Berezinian Positivity Poset (`M1 ≺ ⋯ ≺ M6`)

===============================================================================
HIVE CONSTITUTIONAL HEADER
===============================================================================
Module: InfoGeometry.Canonical.SupergradedMoebiusTetraktysKleinQuotientBerezinianWeylPoset
Role: Genuine noncommutative cross-owner mathematical bridges connecting the
  repository's supergraded operator Möbius/Riccati charts, Peirce Tetraktys
  orientation & double-twist factorization, Klein-bottle operator-algebra
  quotient gluing, Weyl/Cayley operator squashing, and Peirce LDU /
  Schur–Berezinian positivity:
  1. `peirceRiccatiVelocity_eq_tetraktys_and_odd_corner`: Specializing
     `OperatorRiccatiRowChart.rowRiccatiVelocity` to the `ℤ/2ℤ`-supergraded
     Peirce corners (`T = conePlus P A`, `c = coneMinus P C`, `a = P a₀ P`,
     `d = (1 - P) d₀ (1 - P)`, `b = conePlus P B₀`) identifies the quadratic
     Riccati nonlinearity `-T * c * T` with `-genV P A C * T = -T * genV P A C
     = -genSig P A C * T = T * genSig P A C` and proves that the Riccati
     velocity remains strictly inside the odd `(0, 1)`-Peirce corner and
     anticommutes with the supergrading `invS P`.
  2. `peirceHalfTwist_swaps_sheets_and_reflects_logisticStone` &
     `peirceDoubleTwist_restores_sheets_and_logisticStone`: In any
     noncommutative `[Ring B]` with idempotent `P * P = P`, a single Tetraktys
     half-twist `Φ X Φ` swaps the complementary Peirce sheets
     (`Φ P Φ = V * (1 - P)`, `Φ (1 - P) Φ = V * P`), reverses the chiral
     orientation `Σ` and supergrading `S`, and reflects the depth-`0` Peirce
     logistic stone `s₀ = P - Σ` to the complementary stone `V * (1 - s₀)`,
     whereas the double half-twist `J (Φ X Φ) (-J) = Σ X Σ` restores both
     sheets (`Σ P Σ = V² * P`, `Σ (1 - P) Σ = V² * (1 - P)`) and fixes the
     logistic stone `Σ s₀ Σ = V² * s₀`.
  3. `peirceHalfTwistSetoid`, `PeirceMoebiusQuotient`,
     `quotientMk_idempotent_eq_complement`, and `peirceDoubleTwistOnQuotient`:
     At unit horizon `V = genV P A C = 1`, the orientation-reversing half-twist
     `τ_Φ(X) = Φ X Φ` is an involutive ring automorphism of `B` that generates
     an orbit equivalence relation `peirceHalfTwistSetoid` gluing `P` to `1 - P`
     (`quotientMk P = quotientMk (1 - P)`), and the orientation-preserving
     double-twist `τ_Σ(X) = Σ X Σ` commutes with `τ_Φ` and descends to the
     glued quotient `PeirceMoebiusQuotient`.
  4. `peirceWeylReflection_and_cayleySquash_inversion`: In any noncommutative
     `[Ring B]` with `P * P = P`, the supergrading `S = invS P` is the
     intrinsic Weyl reflection (`S² = 1`, `S P S = P`, `S N₊ S = -N₊`,
     `S N₋ S = -N₋`, `S V S = V`, `S Σ S = Σ`) and conjugates the unipotent
     Möbius/Cayley squash `1 + N₊` to its exact multiplicative inverse `1 - N₊`.
  5. `peirceSchurComplement_unipotent_block_diagonalization` &
     `peirceSchurComplement_krein_star_gram_positivity`: For any operator
     `M = P a₀ P + conePlus P A + coneMinus P C + d` with `(1 - P)`-corner
     inverse `d * d_inv = 1 - P = d_inv * d`, the unipotent Möbius shears
     `1 - conePlus P A * d_inv` and `1 - d_inv * coneMinus P C` block-
     diagonalize `M` into `peirceSchurComplement P a₀ A C d_inv + d`; when the
     `(1 - P)`-sheet has opposite Krein/BdG sign `d_inv = -(1 - P)` and `C = A*`
     (`star P = P`), the Schur complement becomes the Hermitian Gram sum
     `P a₀ P + conePlus P A * star (conePlus P A) = P a₀ P + P * genV P A (star A)`,
     explaining why raw determinant positivity is obstructed by the `- (1 - P)`
     sheet sign unless squared (`H_BdG²`, `stageEmbed n`) or restricted to the
     even-parity / double-twist sector.

### Three-Bucket Audit Map

#### BUCKET 1 — Unconditional Kernel Truth
- `SupergradedMoebiusTetraktysKleinStratum`, `rank_injective`, `coverEdge_strictMono`,
  `coverEdge_transGen_strictMono`, `coverEdge_acyclic`.

#### BUCKET 2 — Conditional Kernel Theorems with Explicit Hypotheses
- Bridges `M1 → M6`: `peirceRiccatiVelocity_eq_tetraktys_and_odd_corner`,
  `peirceHalfTwist_swaps_sheets_and_reflects_logisticStone`,
  `peirceDoubleTwist_restores_sheets_and_logisticStone`,
  `peirceMoebiusQuotient_glues_sheets_and_logisticStones`, and
  `peirceSchurComplement_unipotent_block_diagonalization` under explicit idempotent and inverse
  hypotheses.

#### BUCKET 3 — Open / Beyond-Scope Obligations
- Smooth manifold bundle Stiefel–Whitney cohomology classes beyond the algebraic `Setoid` quotient
  `PeirceMoebiusQuotient` remain outside this module's scope.

## i. Overview
Formalizes the 6-stratum supergraded operator Möbius, Peirce Tetraktys orientation, Klein quotient gluing, and Schur–Berezinian positivity poset (`M1 ≺ ⋯ ≺ M6`).

## ii. Key results
- `SupergradedMoebiusTetraktysKleinStratum.coverEdge_acyclic`
- `peirceRiccatiVelocity_eq_tetraktys_and_odd_corner`
- `peirceMoebiusQuotient_glues_sheets_and_logisticStones`

## iii. Table of contents
- Section 1: The 6-Stratum Causal Order (`M1 ≺ ⋯ ≺ M6`)
- Sections 2–6: Bridges `M1 → M6`

## iv. References
- F. A. Berezin, *Introduction to Superanalysis* (1987).
===============================================================================
-/

noncomputable section

namespace InfoGeometry.Canonical.SupergradedMoebiusTetraktysKleinQuotientBerezinianWeylPoset

open scoped ComplexOrder Matrix
open InfoGeometry
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.OntologyRing
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.OperatorRiccatiRowChart
open InfoGeometry.Meta

/-! ===========================================================================
    Section 1: The 6-Stratum Causal Order (`M1 ≺ M2 ≺ M3 ≺ M4 ≺ M5 ≺ M6`)
    =========================================================================== -/

/-- The 6 causal strata of the supergraded operator Möbius, Peirce Tetraktys
orientation, Klein quotient gluing, Weyl/Cayley squashing, Schur–Berezinian
factorization, and downstream orientation-conditioned positivity spine. -/
inductive SupergradedMoebiusTetraktysKleinStratum : Type
  | M1_SupergradedOperatorMoebiusLift
  | M2_TetraktysOrientationAndFactorization
  | M3_KleinQuotientNonOrientedTopologicalGluing
  | M4_MoebiusOperatorSquashingAndFlowClassification
  | M5_PotentialsBerezinianWeylGaugeStiefelWhitney
  | M6_DownstreamOrientationConditionedPositivity
  deriving DecidableEq, Repr

namespace SupergradedMoebiusTetraktysKleinStratum

/-- Numerical rank `0..5` inducing the strict linear order `M1 ≺ ... ≺ M6`. -/
def rank : SupergradedMoebiusTetraktysKleinStratum → ℕ
  | .M1_SupergradedOperatorMoebiusLift => 0
  | .M2_TetraktysOrientationAndFactorization => 1
  | .M3_KleinQuotientNonOrientedTopologicalGluing => 2
  | .M4_MoebiusOperatorSquashingAndFlowClassification => 3
  | .M5_PotentialsBerezinianWeylGaugeStiefelWhitney => 4
  | .M6_DownstreamOrientationConditionedPositivity => 5

/-- The numerical rank map `rank` is injective on `SupergradedMoebiusTetraktysKleinStratum`. -/
theorem rank_injective :
    Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance : LinearOrder SupergradedMoebiusTetraktysKleinStratum :=
  LinearOrder.lift' rank rank_injective

/-- Covering relation along the 6-stratum causal spine `M1 ≺ M2 ≺ M3 ≺ M4 ≺ M5 ≺ M6`. -/
inductive coverEdge :
    SupergradedMoebiusTetraktysKleinStratum → SupergradedMoebiusTetraktysKleinStratum → Prop
  | m1_to_m2 : coverEdge .M1_SupergradedOperatorMoebiusLift .M2_TetraktysOrientationAndFactorization
  | m2_to_m3 :
      coverEdge .M2_TetraktysOrientationAndFactorization .M3_KleinQuotientNonOrientedTopologicalGluing
  | m3_to_m4 :
      coverEdge .M3_KleinQuotientNonOrientedTopologicalGluing
        .M4_MoebiusOperatorSquashingAndFlowClassification
  | m4_to_m5 :
      coverEdge .M4_MoebiusOperatorSquashingAndFlowClassification
        .M5_PotentialsBerezinianWeylGaugeStiefelWhitney
  | m5_to_m6 :
      coverEdge .M5_PotentialsBerezinianWeylGaugeStiefelWhitney
        .M6_DownstreamOrientationConditionedPositivity

/-- Every covering edge strictly increases the stratum order. -/
theorem coverEdge_strictMono {a b : SupergradedMoebiusTetraktysKleinStratum}
    (h : coverEdge a b) : a < b := by
  change rank a < rank b
  cases h <;> decide

/-- Any transitive path of covering edges strictly increases the stratum order. -/
theorem coverEdge_transGen_strictMono {a b : SupergradedMoebiusTetraktysKleinStratum}
    (h : Relation.TransGen coverEdge a b) : a < b := by
  induction h with
  | single hstep => exact coverEdge_strictMono hstep
  | tail _ hstep ih => exact lt_trans ih (coverEdge_strictMono hstep)

-- theorem-class: constructive endpoint
/-- The 6-stratum `SupergradedMoebiusTetraktysKleinStratum` poset is strictly acyclic. -/
theorem coverEdge_acyclic :
    ∀ a : SupergradedMoebiusTetraktysKleinStratum,
      ¬ Relation.TransGen coverEdge a a := by
  intro a ha
  exact lt_irrefl a (coverEdge_transGen_strictMono ha)

/-- Alignment with the 4-stratum operator ontology `OntologyMetaLevel`. -/
def toOntologyMetaLevel : SupergradedMoebiusTetraktysKleinStratum → OntologyMetaLevel
  | .M1_SupergradedOperatorMoebiusLift => OntologyMetaLevel.M1_ProjectorClabject
  | .M2_TetraktysOrientationAndFactorization => OntologyMetaLevel.M1_ProjectorClabject
  | .M3_KleinQuotientNonOrientedTopologicalGluing => OntologyMetaLevel.M2_GrassmannianPowertypeOrbit
  | .M4_MoebiusOperatorSquashingAndFlowClassification => OntologyMetaLevel.M2_GrassmannianPowertypeOrbit
  | .M5_PotentialsBerezinianWeylGaugeStiefelWhitney => OntologyMetaLevel.M3_ErlangenCasimirMetaLaw
  | .M6_DownstreamOrientationConditionedPositivity => OntologyMetaLevel.M3_ErlangenCasimirMetaLaw

/-- Alignment with the 6-layer representation-depth spine `RepDepth`. -/
def toRepDepth : SupergradedMoebiusTetraktysKleinStratum → RepDepth
  | .M1_SupergradedOperatorMoebiusLift => RepDepth.projective
  | .M2_TetraktysOrientationAndFactorization => RepDepth.operator
  | .M3_KleinQuotientNonOrientedTopologicalGluing => RepDepth.krein
  | .M4_MoebiusOperatorSquashingAndFlowClassification => RepDepth.transport
  | .M5_PotentialsBerezinianWeylGaugeStiefelWhitney => RepDepth.thermo
  | .M6_DownstreamOrientationConditionedPositivity => RepDepth.thermo

end SupergradedMoebiusTetraktysKleinStratum

/-! ===========================================================================
    Section 2: Bridge 1 (M1 → M2) — Noncommutative Operator Riccati Velocity on
    Supergraded Peirce Corners Reduces to the Peirce Tetraktys Metric & Dipole
    =========================================================================== -/

section PeirceRiccatiTetraktysBridge

variable {B : Type*} [Ring B]

/-- The noncommutative operator Möbius–Riccati velocity `rowRiccatiVelocity`
specialized to the `ℤ/2ℤ`-supergraded Peirce corners of an idempotent `P`:
* `P * a₀ * P` in the even `(0, 0)`-corner,
* `(1 - P) * d₀ * (1 - P)` in the even `(1, 1)`-corner,
* `conePlus P B₀` in the odd `(0, 1)` translation corner,
* `coneMinus P C` in the odd `(1, 0)` co-translation corner,
* `conePlus P A` as the odd `(0, 1)` graph-chart coordinate. -/
def peirceRiccatiVelocity (P a₀ B₀ C d₀ A : B) : B :=
  rowRiccatiVelocity (P * a₀ * P) (conePlus P B₀) (coneMinus P C)
    ((1 - P) * d₀ * (1 - P)) (conePlus P A)

-- theorem-class: lower bridge identification
/-- **Bridge Theorem 1 (`peirceRiccatiVelocity_eq_tetraktys_and_odd_corner`)**:
In any noncommutative `[Ring B]` with idempotent `P * P = P`:
1. The quadratic Riccati term `conePlus P A * coneMinus P C * conePlus P A`
   equals `genV P A C * conePlus P A`, `conePlus P A * genV P A C`,
   `genSig P A C * conePlus P A`, and `- (conePlus P A * genSig P A C)`.
2. Consequently `peirceRiccatiVelocity P a₀ B₀ C d₀ A` equals
   `conePlus P B₀ + conePlus P A * ((1 - P) * d₀ * (1 - P)) - (P * a₀ * P) * conePlus P A - genV P A C * conePlus P A`.
3. In the pure co-translation flow (`a₀ = 0`, `B₀ = 0`, `d₀ = 0`), the operator
   Riccati velocity is `- (genV P A C * conePlus P A) = - (genSig P A C * conePlus P A)`.
4. The full Riccati velocity stays strictly inside the odd `(0, 1)` Peirce corner
   (`P * v * (1 - P) = v`) and anticommutes with the Peirce supergrading `invS P`
   (`invS P * v = v`, `v * invS P = -v`, `anticomm (invS P) v = 0`). -/
theorem peirceRiccatiVelocity_eq_tetraktys_and_odd_corner
    {P : B} (hP : P * P = P) (a₀ B₀ C d₀ A : B) :
    let Np := conePlus P A
    let Nm := coneMinus P C
    let V := genV P A C
    let Sig := genSig P A C
    let S := invS P
    let vel := peirceRiccatiVelocity P a₀ B₀ C d₀ A
    (Np * Nm * Np = V * Np ∧
      Np * Nm * Np = Np * V ∧
      Np * Nm * Np = Sig * Np ∧
      Np * Nm * Np = -(Np * Sig)) ∧
    vel = conePlus P B₀ + Np * ((1 - P) * d₀ * (1 - P)) -
        (P * a₀ * P) * Np - V * Np ∧
    peirceRiccatiVelocity P 0 0 C 0 A = -(V * Np) ∧
    (P * vel * (1 - P) = vel ∧
      S * vel = vel ∧
      vel * S = -vel ∧
      anticomm S vel = 0) := by
  intro Np Nm V Sig S vel
  have hVNp : Np * Nm * Np = V * Np := by
    dsimp [Np, Nm, V]
    peirce_nf hP
  have hNpV : Np * Nm * Np = Np * V := by
    dsimp [Np, Nm, V]
    peirce_nf hP
  have hSigNp : Np * Nm * Np = Sig * Np := by
    dsimp [Np, Nm, Sig]
    peirce_nf hP
  have hNpSig : Np * Nm * Np = -(Np * Sig) := by
    dsimp [Np, Nm, Sig]
    peirce_nf hP
  have hVel :
      vel = conePlus P B₀ + Np * ((1 - P) * d₀ * (1 - P)) -
        (P * a₀ * P) * Np - V * Np := by
    dsimp [vel, peirceRiccatiVelocity, rowRiccatiVelocity]
    rw [hVNp]
  have hPure : peirceRiccatiVelocity P 0 0 C 0 A = -(V * Np) := by
    dsimp [peirceRiccatiVelocity, rowRiccatiVelocity, Np, V]
    peirce_nf hP
  have hCorner : P * vel * (1 - P) = vel := by
    dsimp [vel, peirceRiccatiVelocity, rowRiccatiVelocity]
    peirce_nf hP
  have hLeftS : S * vel = vel := by
    dsimp [S, vel, peirceRiccatiVelocity, rowRiccatiVelocity]
    peirce_nf hP
  have hRightS : vel * S = -vel := by
    dsimp [S, vel, peirceRiccatiVelocity, rowRiccatiVelocity]
    peirce_nf hP
  have hAntiS : anticomm S vel = 0 := by
    dsimp [anticomm]
    rw [hLeftS, hRightS, add_neg_cancel]
  exact ⟨⟨hVNp, hNpV, hSigNp, hNpSig⟩, hVel, hPure,
    ⟨hCorner, hLeftS, hRightS, hAntiS⟩⟩

end PeirceRiccatiTetraktysBridge

/-! ===========================================================================
    Section 3: Bridge 2 (M2 → M3) — Tetraktys Half-Twist Sheet Swap & Logistic
    Stone Reflection vs. Double-Twist Restoration & Non-Oriented Quotient Gluing
    =========================================================================== -/

section PeirceTetraktysQuotientGluing

variable {B : Type*} [Ring B]

/-- The orientation-reversing Peirce Tetraktys half-twist sandwich
`τ_Φ(X) := Φ * X * Φ`. -/
def peirceHalfTwist (P A C X : B) : B :=
  genPhi P A C * X * genPhi P A C

/-- The orientation-preserving Peirce Tetraktys double-twist sandwich
`τ_Σ(X) := J * (Φ * X * Φ) * (-J) = Σ * X * Σ`. -/
def peirceDoubleTwist (P A C X : B) : B :=
  genSig P A C * X * genSig P A C

-- theorem-class: constructive endpoint
/-- **Bridge Theorem 2a (`peirceHalfTwist_swaps_sheets_and_reflects_logisticStone`)**:
In any noncommutative `[Ring B]` with idempotent `P * P = P`:
1. **Single Half-Twist Sheet Swap**: `peirceHalfTwist P A C P = genV P A C * (1 - P)`
   and `peirceHalfTwist P A C (1 - P) = genV P A C * P`.
2. **Orientation & Supergrading Reversal**:
   `peirceHalfTwist P A C (genSig P A C) = -(genV P A C * genSig P A C)` and
   `peirceHalfTwist P A C (invS P) = -(genV P A C * invS P)`.
3. **Logistic Stone Reflection (`s₀ ↦ 1 - s₀`)**: For the depth-`0` Peirce logistic
   stone `multiplicatioStone 0 P A C = P - genSig P A C`, the single half-twist
   maps `s₀` to `genV P A C * (1 - s₀)` (exchanging the stone with its complement). -/
theorem peirceHalfTwist_swaps_sheets_and_reflects_logisticStone
    {P : B} (hP : P * P = P) (A C : B) :
    let V := genV P A C
    let s₀ := multiplicatioStone 0 P A C
    peirceHalfTwist P A C P = V * (1 - P) ∧
    peirceHalfTwist P A C (1 - P) = V * P ∧
    peirceHalfTwist P A C (genSig P A C) = -(V * genSig P A C) ∧
    peirceHalfTwist P A C (invS P) = -(V * invS P) ∧
    peirceHalfTwist P A C s₀ = V * (1 - s₀) := by
  intro V s₀
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [peirceHalfTwist, V]
    peirce_nf hP
  · dsimp [peirceHalfTwist, V]
    peirce_nf hP
  · dsimp [peirceHalfTwist, V]
    peirce_nf hP
  · dsimp [peirceHalfTwist, V]
    peirce_nf hP
  · dsimp [peirceHalfTwist, V, s₀, multiplicatioStone, multiplicatioCurvature,
      qgtPlus, qgtMinus]
    peirce_nf hP

-- theorem-class: constructive endpoint
/-- **Bridge Theorem 2b (`peirceDoubleTwist_restores_sheets_and_logisticStone`)**:
In any noncommutative `[Ring B]` with idempotent `P * P = P`:
1. Composing the `Φ`-half-twist with the `J`-half-twist equals `peirceDoubleTwist P A C X`:
   `genJ P A C * peirceHalfTwist P A C X * (-genJ P A C) = peirceDoubleTwist P A C X`.
2. **Double-Twist Sheet Restoration**:
   `peirceDoubleTwist P A C P = (genV P A C * genV P A C) * P` and
   `peirceDoubleTwist P A C (1 - P) = (genV P A C * genV P A C) * (1 - P)`.
3. **Double-Twist Logistic Stone Invariance**:
   `peirceDoubleTwist P A C (multiplicatioStone 0 P A C) =
     (genV P A C * genV P A C) * multiplicatioStone 0 P A C`.
4. **Half-Twist / Double-Twist Commutation**: For every `X : B`,
   `peirceHalfTwist P A C (peirceDoubleTwist P A C X) =
     peirceDoubleTwist P A C (peirceHalfTwist P A C X)`. -/
theorem peirceDoubleTwist_restores_sheets_and_logisticStone
    {P : B} (hP : P * P = P) (A C X : B) :
    let V := genV P A C
    let s₀ := multiplicatioStone 0 P A C
    genJ P A C * peirceHalfTwist P A C X * (-genJ P A C) =
      peirceDoubleTwist P A C X ∧
    peirceDoubleTwist P A C P = (V * V) * P ∧
    peirceDoubleTwist P A C (1 - P) = (V * V) * (1 - P) ∧
    peirceDoubleTwist P A C s₀ = (V * V) * s₀ ∧
    peirceHalfTwist P A C (peirceDoubleTwist P A C X) =
      peirceDoubleTwist P A C (peirceHalfTwist P A C X) := by
  intro V s₀
  refine ⟨double_half_twist_eq_spin_sandwich hP A C X, ?_, ?_, ?_, ?_⟩
  · dsimp [peirceDoubleTwist, V]
    peirce_nf hP
  · dsimp [peirceDoubleTwist, V]
    peirce_nf hP
  · dsimp [peirceDoubleTwist, V, s₀, multiplicatioStone, multiplicatioCurvature,
      qgtPlus, qgtMinus]
    peirce_nf hP
  · have hPhiSig : genPhi P A C * genSig P A C = -(genSig P A C * genPhi P A C) := by
      peirce_nf hP
    dsimp [peirceHalfTwist, peirceDoubleTwist]
    calc
      genPhi P A C * (genSig P A C * X * genSig P A C) * genPhi P A C
        = (genPhi P A C * genSig P A C) * X * (genSig P A C * genPhi P A C) := by
          noncomm_ring
      _ = (-(genSig P A C * genPhi P A C)) * X * (genSig P A C * genPhi P A C) := by
          rw [hPhiSig]
      _ = (-(genSig P A C * genPhi P A C)) * X * (-(genPhi P A C * genSig P A C)) := by
          rw [hPhiSig, neg_neg]
      _ = genSig P A C * (genPhi P A C * X * genPhi P A C) * genSig P A C := by
          noncomm_ring

-- theorem-class: transport lemma
/-- At unit horizon `genV P A C = 1`, `peirceHalfTwist P A C` is an involution on `B`
(`peirceHalfTwist P A C (peirceHalfTwist P A C X) = X`) and a ring endomorphism
(`peirceHalfTwist P A C (X * Y) = peirceHalfTwist P A C X * peirceHalfTwist P A C Y`). -/
theorem peirceHalfTwist_involutive_and_mul_of_unit_genV
    {P : B} (hP : P * P = P) {A C : B} (hV : genV P A C = 1) (X Y : B) :
    peirceHalfTwist P A C (peirceHalfTwist P A C X) = X ∧
    peirceHalfTwist P A C (X * Y) =
      peirceHalfTwist P A C X * peirceHalfTwist P A C Y ∧
    peirceHalfTwist P A C 1 = 1 := by
  have hPhiSq : genPhi P A C * genPhi P A C = 1 := by
    rw [(archetype_A3_nilpotent_cones_and_tetraktys_table hP A C).2.2.1, hV]
  refine ⟨?_, ?_, ?_⟩
  · dsimp [peirceHalfTwist]
    calc
      genPhi P A C * (genPhi P A C * X * genPhi P A C) * genPhi P A C
        = (genPhi P A C * genPhi P A C) * X * (genPhi P A C * genPhi P A C) := by
          noncomm_ring
      _ = 1 * X * 1 := by rw [hPhiSq]
      _ = X := by noncomm_ring
  · dsimp [peirceHalfTwist]
    calc
      genPhi P A C * (X * Y) * genPhi P A C
        = genPhi P A C * X * 1 * Y * genPhi P A C := by noncomm_ring
      _ = genPhi P A C * X * (genPhi P A C * genPhi P A C) * Y * genPhi P A C := by
          rw [hPhiSq]
      _ = (genPhi P A C * X * genPhi P A C) * (genPhi P A C * Y * genPhi P A C) := by
          noncomm_ring
  · dsimp [peirceHalfTwist]
    rw [mul_one, hPhiSq]

/-- The native `Setoid B` gluing each operator `X` to its `Φ`-twisted sheet partner
`peirceHalfTwist P A C X` when `P * P = P` and `genV P A C = 1`. -/
def peirceHalfTwistSetoid (P A C : B) (hP : P * P = P) (hV : genV P A C = 1) : Setoid B where
  r X Y := X = Y ∨ X = peirceHalfTwist P A C Y
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact Or.inl rfl
    · intro x y hxy
      rcases hxy with rfl | rfl
      · exact Or.inl rfl
      · right
        exact ((peirceHalfTwist_involutive_and_mul_of_unit_genV hP hV y y).1).symm
    · intro x y z hxy hyz
      rcases hxy with rfl | rfl <;> rcases hyz with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inr rfl
      · left
        exact (peirceHalfTwist_involutive_and_mul_of_unit_genV hP hV z z).1

/-- The non-oriented quotient space `B / τ_Φ` obtained by gluing the two Peirce sheets
via the orientation-reversing Tetraktys half-twist `τ_Φ`. -/
def PeirceMoebiusQuotient (P A C : B) (hP : P * P = P) (hV : genV P A C = 1) : Type _ :=
  Quotient (peirceHalfTwistSetoid P A C hP hV)

/-- Canonical quotient projection `B → PeirceMoebiusQuotient P A C hP hV`. -/
def peirceMoebiusQuotientMk {P A C : B} (hP : P * P = P) (hV : genV P A C = 1) (X : B) :
    PeirceMoebiusQuotient P A C hP hV :=
  Quotient.mk (peirceHalfTwistSetoid P A C hP hV) X

/-- The orientation-preserving double-twist `τ_Σ(X) = Σ * X * Σ` descended to the
glued quotient `PeirceMoebiusQuotient P A C hP hV`. -/
def peirceDoubleTwistOnQuotient {P A C : B} (hP : P * P = P) (hV : genV P A C = 1) :
    PeirceMoebiusQuotient P A C hP hV → PeirceMoebiusQuotient P A C hP hV :=
  Quotient.lift
    (fun X => peirceMoebiusQuotientMk hP hV (peirceDoubleTwist P A C X))
    (by
      intro X Y hXY
      apply Quotient.sound
      rcases hXY with rfl | rfl
      · exact Or.inl rfl
      · right
        exact (peirceDoubleTwist_restores_sheets_and_logisticStone hP A C Y).2.2.2.2.symm)

-- theorem-class: constructive endpoint
/-- **Bridge Theorem 2c (`peirceMoebiusQuotient_glues_sheets_and_logisticStones`)**:
In the glued quotient `PeirceMoebiusQuotient P A C hP hV` (`P * P = P`, `genV P A C = 1`):
1. The two opposite Peirce sheet projectors `P` and `1 - P` are glued into a single
   unoriented class: `peirceMoebiusQuotientMk hP hV P = peirceMoebiusQuotientMk hP hV (1 - P)`.
2. The depth-`0` logistic stone `s₀ = multiplicatioStone 0 P A C` is glued to its
   complement `1 - s₀`:
   `peirceMoebiusQuotientMk hP hV s₀ = peirceMoebiusQuotientMk hP hV (1 - s₀)`.
3. The orientation-preserving double-twist `peirceDoubleTwistOnQuotient hP hV` is an
   involution on `PeirceMoebiusQuotient P A C hP hV` that fixes the glued sheet class
   `peirceMoebiusQuotientMk hP hV P` and the glued logistic-stone class
   `peirceMoebiusQuotientMk hP hV s₀`. -/
theorem peirceMoebiusQuotient_glues_sheets_and_logisticStones
    {P A C : B} (hP : P * P = P) (hV : genV P A C = 1)
    (q : PeirceMoebiusQuotient P A C hP hV) :
    let s₀ := multiplicatioStone 0 P A C
    peirceMoebiusQuotientMk hP hV P = peirceMoebiusQuotientMk hP hV (1 - P) ∧
    peirceMoebiusQuotientMk hP hV s₀ = peirceMoebiusQuotientMk hP hV (1 - s₀) ∧
    peirceDoubleTwistOnQuotient hP hV (peirceDoubleTwistOnQuotient hP hV q) = q ∧
    peirceDoubleTwistOnQuotient hP hV (peirceMoebiusQuotientMk hP hV P) =
      peirceMoebiusQuotientMk hP hV P ∧
    peirceDoubleTwistOnQuotient hP hV (peirceMoebiusQuotientMk hP hV s₀) =
      peirceMoebiusQuotientMk hP hV s₀ := by
  intro s₀
  have hSwap := peirceHalfTwist_swaps_sheets_and_reflects_logisticStone hP A C
  have hRest := peirceDoubleTwist_restores_sheets_and_logisticStone hP A C P
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply Quotient.sound
    right
    have h1 := hSwap.2.1
    rw [hV, one_mul] at h1
    exact h1.symm
  · symm
    apply Quotient.sound
    right
    have h2 := hSwap.2.2.2.2
    rw [hV, one_mul] at h2
    exact h2.symm
  · refine Quotient.inductionOn q (fun X => ?_)
    change peirceMoebiusQuotientMk hP hV
      (peirceDoubleTwist P A C (peirceDoubleTwist P A C X)) =
      peirceMoebiusQuotientMk hP hV X
    have hSigSq : genSig P A C * genSig P A C = 1 := by
      rw [(archetype_A3_nilpotent_cones_and_tetraktys_table hP A C).2.2.2.2.2.2.2.2.2.2.1,
        hV, mul_one]
    have hInv : peirceDoubleTwist P A C (peirceDoubleTwist P A C X) = X := by
      dsimp [peirceDoubleTwist]
      calc
        genSig P A C * (genSig P A C * X * genSig P A C) * genSig P A C
          = (genSig P A C * genSig P A C) * X * (genSig P A C * genSig P A C) := by
            noncomm_ring
        _ = 1 * X * 1 := by rw [hSigSq]
        _ = X := by noncomm_ring
    rw [hInv]
  · change peirceMoebiusQuotientMk hP hV (peirceDoubleTwist P A C P) =
      peirceMoebiusQuotientMk hP hV P
    have hPfix := hRest.2.1
    rw [hV, mul_one, one_mul] at hPfix
    rw [hPfix]
  · change peirceMoebiusQuotientMk hP hV (peirceDoubleTwist P A C s₀) =
      peirceMoebiusQuotientMk hP hV s₀
    have hSfix := hRest.2.2.2.1
    rw [hV, mul_one, one_mul] at hSfix
    rw [hSfix]

end PeirceTetraktysQuotientGluing

/-! ===========================================================================
    Section 4: Bridge 3 (M3 → M4) — Noncommutative Peirce Weyl Reflection &
    Unipotent Cayley/Möbius Squashing Inversion
    =========================================================================== -/

section PeirceWeylCayleySquashing

variable {B : Type*} [Ring B]

/-- The noncommutative upper unipotent Cayley transform of the nilpotent Peirce
cone `N₊ = conePlus P A`:
`peirceCayleyPlus P A := (1 + N₊) * (1 - N₊)⁻¹ = (1 + N₊) * (1 + N₊) = 1 + 2 • N₊`. -/
def peirceCayleyPlus (P A : B) : B :=
  (1 + conePlus P A) * (1 + conePlus P A)

/-- The noncommutative inverse Cayley transform of `N₊ = conePlus P A`:
`peirceCayleyPlusInv P A := (1 - N₊) * (1 - N₊) = 1 - 2 • N₊`. -/
def peirceCayleyPlusInv (P A : B) : B :=
  (1 - conePlus P A) * (1 - conePlus P A)

-- theorem-class: constructive endpoint
/-- **Bridge Theorem 3 (`peirceWeylReflection_and_cayleySquash_inversion`)**:
In any noncommutative `[Ring B]` with idempotent `P * P = P`:
1. **Intrinsic Noncommutative Weyl Reflection**: The supergrading `S = invS P`
   satisfies `S * S = 1`, fixes the Cartan idempotents (`S * P * S = P`,
   `S * (1 - P) * S = 1 - P`), and flips both nilpotent boundary cones
   (`S * conePlus P A * S = -conePlus P A`, `S * coneMinus P C * S = -coneMinus P C`)
   and both odd Tetraktys generators (`S * genPhi P A C * S = -genPhi P A C`,
   `S * genJ P A C * S = -genJ P A C`), while fixing `genV P A C` and `genSig P A C`.
2. **Two-Sided Unipotent Cayley Inverse**:
   `peirceCayleyPlus P A = 1 + (2 : ℤ) • conePlus P A`,
   `peirceCayleyPlusInv P A = 1 - (2 : ℤ) • conePlus P A`, and
   `peirceCayleyPlus P A * peirceCayleyPlusInv P A = 1 =
     peirceCayleyPlusInv P A * peirceCayleyPlus P A`.
3. **Weyl Reflection Inverts the Noncommutative Cayley Squash**:
   Conjugating `peirceCayleyPlus P A` by the Weyl reflection `S = invS P` yields its
   exact multiplicative inverse `peirceCayleyPlusInv P A`:
   `S * peirceCayleyPlus P A * S = peirceCayleyPlusInv P A` and
   `(S * peirceCayleyPlus P A * S) * peirceCayleyPlus P A = 1`. -/
theorem peirceWeylReflection_and_cayleySquash_inversion
    {P : B} (hP : P * P = P) (A C : B) :
    let S := invS P
    let Np := conePlus P A
    let Nm := coneMinus P C
    (S * S = 1 ∧
      S * P * S = P ∧
      S * (1 - P) * S = 1 - P ∧
      S * Np * S = -Np ∧
      S * Nm * S = -Nm ∧
      S * genPhi P A C * S = -genPhi P A C ∧
      S * genJ P A C * S = -genJ P A C ∧
      S * genV P A C * S = genV P A C ∧
      S * genSig P A C * S = genSig P A C) ∧
    (peirceCayleyPlus P A = 1 + (2 : ℤ) • Np ∧
      peirceCayleyPlusInv P A = 1 - (2 : ℤ) • Np ∧
      peirceCayleyPlus P A * peirceCayleyPlusInv P A = 1 ∧
      peirceCayleyPlusInv P A * peirceCayleyPlus P A = 1) ∧
    (S * peirceCayleyPlus P A * S = peirceCayleyPlusInv P A ∧
      (S * peirceCayleyPlus P A * S) * peirceCayleyPlus P A = 1) := by
  intro S Np Nm
  have hCayleyMul : peirceCayleyPlus P A * peirceCayleyPlusInv P A = 1 := by
    dsimp [peirceCayleyPlus, peirceCayleyPlusInv]
    peirce_nf hP
  have hCayleyInvMul : peirceCayleyPlusInv P A * peirceCayleyPlus P A = 1 := by
    dsimp [peirceCayleyPlus, peirceCayleyPlusInv]
    peirce_nf hP
  have hWeylCayley : S * peirceCayleyPlus P A * S = peirceCayleyPlusInv P A := by
    dsimp [S, peirceCayleyPlus, peirceCayleyPlusInv]
    peirce_nf hP
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, hCayleyMul, hCayleyInvMul⟩,
    ⟨hWeylCayley, by rw [hWeylCayley, hCayleyInvMul]⟩⟩
  · dsimp [S]; peirce_nf hP
  · dsimp [S]; peirce_nf hP
  · dsimp [S]; peirce_nf hP
  · dsimp [S, Np]; peirce_nf hP
  · dsimp [S, Nm]; peirce_nf hP
  · dsimp [S]; peirce_nf hP
  · dsimp [S]; peirce_nf hP
  · dsimp [S]; peirce_nf hP
  · dsimp [S]; peirce_nf hP
  · dsimp [peirceCayleyPlus, Np]; peirce_nf hP
  · dsimp [peirceCayleyPlusInv, Np]; peirce_nf hP

end PeirceWeylCayleySquashing

/-! ===========================================================================
    Section 5: Bridge 4 (M4 → M5 → M6) — Noncommutative Peirce LDU /
    Schur–Berezinian Factorization & Orientation-Conditioned Gram Positivity
    =========================================================================== -/

section PeirceSchurBerezinianPositivity

variable {B : Type*} [Ring B]

/-- The noncommutative Peirce Schur complement on the `P * B * P` corner:
`peirceSchurComplement P a₀ A C d_inv := P * a₀ * P - conePlus P A * d_inv * coneMinus P C`,
where `d_inv` is the `(1 - P)`-corner inverse of `d`. -/
def peirceSchurComplement (P a₀ A C d_inv : B) : B :=
  P * a₀ * P - conePlus P A * d_inv * coneMinus P C

/-- Left unipotent Gauss–Möbius elimination shear `1 - conePlus P A * d_inv`. -/
def peirceLeftElimShear (P A d_inv : B) : B :=
  1 - conePlus P A * d_inv

/-- Right unipotent Gauss–Möbius elimination shear `1 - d_inv * coneMinus P C`. -/
def peirceRightElimShear (P C d_inv : B) : B :=
  1 - d_inv * coneMinus P C

-- theorem-class: constructive endpoint
/-- **Bridge Theorem 4a (`peirceSchurComplement_unipotent_block_diagonalization`)**:
In any noncommutative `[Ring B]` with idempotent `P * P = P`, let `d, d_inv : B`
live in the `(1 - P)`-Peirce corner (`(1 - P) * d = d`, `d * (1 - P) = d`,
`(1 - P) * d_inv = d_inv`, `d_inv * (1 - P) = d_inv`) and be mutually inverse
on `1 - P` (`d * d_inv = 1 - P`, `d_inv * d = 1 - P`). Then:
1. The left and right Gauss–Möbius elimination shears `peirceLeftElimShear P A d_inv`
   and `peirceRightElimShear P C d_inv` are two-sided units with explicit inverses
   `1 + conePlus P A * d_inv` and `1 + d_inv * coneMinus P C`.
2. Applying these two unipotent Möbius shears block-diagonalizes the full operator
   `M = P * a₀ * P + conePlus P A + coneMinus P C + d` into the sum of its orthogonal
   Peirce Schur complement and `(1 - P)`-corner block `d`:
   `peirceLeftElimShear P A d_inv *
      (P * a₀ * P + conePlus P A + coneMinus P C + d) *
      peirceRightElimShear P C d_inv =
    peirceSchurComplement P a₀ A C d_inv + d`.
3. The Schur complement lies strictly in the `P * B * P` corner
   (`P * peirceSchurComplement P a₀ A C d_inv * P = peirceSchurComplement P a₀ A C d_inv`)
   and is two-sided orthogonal to `d`
   (`peirceSchurComplement P a₀ A C d_inv * d = 0` and
   `d * peirceSchurComplement P a₀ A C d_inv = 0`). -/
theorem peirceSchurComplement_unipotent_block_diagonalization
    {P d d_inv : B} (hP : P * P = P)
    (hdL : (1 - P) * d = d) (hdR : d * (1 - P) = d)
    (hdiL : (1 - P) * d_inv = d_inv) (hdiR : d_inv * (1 - P) = d_inv)
    (hddi : d * d_inv = 1 - P) (hdid : d_inv * d = 1 - P)
    (a₀ A C : B) :
    let S_schur := peirceSchurComplement P a₀ A C d_inv
    let M := P * a₀ * P + conePlus P A + coneMinus P C + d
    (peirceLeftElimShear P A d_inv * (1 + conePlus P A * d_inv) = 1 ∧
      (1 + conePlus P A * d_inv) * peirceLeftElimShear P A d_inv = 1 ∧
      peirceRightElimShear P C d_inv * (1 + d_inv * coneMinus P C) = 1 ∧
      (1 + d_inv * coneMinus P C) * peirceRightElimShear P C d_inv = 1) ∧
    peirceLeftElimShear P A d_inv * M * peirceRightElimShear P C d_inv =
      S_schur + d ∧
    (P * S_schur * P = S_schur ∧ S_schur * d = 0 ∧ d * S_schur = 0) := by
  intro S_schur M
  let Np := conePlus P A
  let Nm := coneMinus P C
  have hPNp : P * Np = Np := by dsimp [Np]; peirce_nf hP
  have hNpP : Np * P = 0 := by dsimp [Np]; peirce_nf hP
  have hNp1mP : Np * (1 - P) = Np := by dsimp [Np]; peirce_nf hP
  have hNmP : Nm * P = Nm := by dsimp [Nm]; peirce_nf hP
  have hPNm : P * Nm = 0 := by dsimp [Nm]; peirce_nf hP
  have h1mPNm : (1 - P) * Nm = Nm := by dsimp [Nm]; peirce_nf hP
  have hPd : P * d = 0 := by
    calc P * d = P * ((1 - P) * d) := by rw [hdL]
    _ = 0 := by peirce_nf hP
  have hdP : d * P = 0 := by
    calc d * P = (d * (1 - P)) * P := by rw [hdR]
    _ = 0 := by peirce_nf hP
  have hPdi : P * d_inv = 0 := by
    calc P * d_inv = P * ((1 - P) * d_inv) := by rw [hdiL]
    _ = 0 := by peirce_nf hP
  have hdiP : d_inv * P = 0 := by
    calc d_inv * P = (d_inv * (1 - P)) * P := by rw [hdiR]
    _ = 0 := by peirce_nf hP
  have hdiNp : d_inv * Np = 0 := by
    calc d_inv * Np = d_inv * (P * Np) := by rw [hPNp]
    _ = (d_inv * P) * Np := by rw [mul_assoc]
    _ = 0 := by rw [hdiP, zero_mul]
  have hNmdi : Nm * d_inv = 0 := by
    calc Nm * d_inv = (Nm * P) * d_inv := by rw [hNmP]
    _ = Nm * (P * d_inv) := by rw [mul_assoc]
    _ = 0 := by rw [hPdi, mul_zero]
  have hLeftNil : (Np * d_inv) * (Np * d_inv) = 0 := by
    calc (Np * d_inv) * (Np * d_inv) = Np * ((d_inv * Np) * d_inv) := by noncomm_ring
    _ = 0 := by rw [hdiNp, zero_mul, mul_zero]
  have hRightNil : (d_inv * Nm) * (d_inv * Nm) = 0 := by
    calc (d_inv * Nm) * (d_inv * Nm) = d_inv * ((Nm * d_inv) * Nm) := by noncomm_ring
    _ = 0 := by rw [hNmdi, zero_mul, mul_zero]
  have hLeftInv1 : peirceLeftElimShear P A d_inv * (1 + Np * d_inv) = 1 := by
    dsimp [peirceLeftElimShear]
    change (1 - Np * d_inv) * (1 + Np * d_inv) = 1
    noncomm_ring [hLeftNil]
  have hLeftInv2 : (1 + Np * d_inv) * peirceLeftElimShear P A d_inv = 1 := by
    dsimp [peirceLeftElimShear]
    change (1 + Np * d_inv) * (1 - Np * d_inv) = 1
    noncomm_ring [hLeftNil]
  have hRightInv1 : peirceRightElimShear P C d_inv * (1 + d_inv * Nm) = 1 := by
    dsimp [peirceRightElimShear]
    change (1 - d_inv * Nm) * (1 + d_inv * Nm) = 1
    noncomm_ring [hRightNil]
  have hRightInv2 : (1 + d_inv * Nm) * peirceRightElimShear P C d_inv = 1 := by
    dsimp [peirceRightElimShear]
    change (1 + d_inv * Nm) * (1 - d_inv * Nm) = 1
    noncomm_ring [hRightNil]
  have h_u_PaP : (Np * d_inv) * (P * a₀ * P) = 0 := by
    calc (Np * d_inv) * (P * a₀ * P) = Np * ((d_inv * P) * (a₀ * P)) := by noncomm_ring
    _ = 0 := by rw [hdiP, zero_mul, mul_zero]
  have h_u_Np : (Np * d_inv) * Np = 0 := by
    calc (Np * d_inv) * Np = Np * (d_inv * Np) := by rw [mul_assoc]
    _ = 0 := by rw [hdiNp, mul_zero]
  have h_u_d : (Np * d_inv) * d = Np := by
    calc (Np * d_inv) * d = Np * (d_inv * d) := by rw [mul_assoc]
    _ = Np * (1 - P) := by rw [hdid]
    _ = Np := hNp1mP
  have hLeftStep :
      peirceLeftElimShear P A d_inv * M = S_schur + Nm + d := by
    change (1 - Np * d_inv) * (P * a₀ * P + Np + Nm + d) =
      (P * a₀ * P - Np * d_inv * Nm) + Nm + d
    calc
      (1 - Np * d_inv) * (P * a₀ * P + Np + Nm + d)
        = (P * a₀ * P + Np + Nm + d) -
            ((Np * d_inv) * (P * a₀ * P) + (Np * d_inv) * Np +
              (Np * d_inv) * Nm + (Np * d_inv) * d) := by noncomm_ring
      _ = (P * a₀ * P - Np * d_inv * Nm) + Nm + d := by
          rw [h_u_PaP, h_u_Np, h_u_d]
          noncomm_ring
  have hCornerR : S_schur * P = S_schur := by
    change (P * a₀ * P - Np * d_inv * Nm) * P = P * a₀ * P - Np * d_inv * Nm
    calc
      (P * a₀ * P - Np * d_inv * Nm) * P
        = P * a₀ * (P * P) - Np * d_inv * (Nm * P) := by noncomm_ring
      _ = P * a₀ * P - Np * d_inv * Nm := by rw [hP, hNmP]
  have hCornerL : P * S_schur = S_schur := by
    change P * (P * a₀ * P - Np * d_inv * Nm) = P * a₀ * P - Np * d_inv * Nm
    calc
      P * (P * a₀ * P - Np * d_inv * Nm)
        = (P * P) * a₀ * P - (P * Np) * d_inv * Nm := by noncomm_ring
      _ = P * a₀ * P - Np * d_inv * Nm := by rw [hP, hPNp]
  have h_S_v : S_schur * (d_inv * Nm) = 0 := by
    calc S_schur * (d_inv * Nm) = (S_schur * P) * (d_inv * Nm) := by rw [hCornerR]
    _ = S_schur * ((P * d_inv) * Nm) := by noncomm_ring
    _ = 0 := by rw [hPdi, zero_mul, mul_zero]
  have h_Nm_v : Nm * (d_inv * Nm) = 0 := by
    calc Nm * (d_inv * Nm) = (Nm * d_inv) * Nm := by noncomm_ring
    _ = 0 := by rw [hNmdi, zero_mul]
  have h_d_v : d * (d_inv * Nm) = Nm := by
    calc d * (d_inv * Nm) = (d * d_inv) * Nm := by noncomm_ring
    _ = (1 - P) * Nm := by rw [hddi]
    _ = Nm := h1mPNm
  have hDiag :
      peirceLeftElimShear P A d_inv * M * peirceRightElimShear P C d_inv =
        S_schur + d := by
    rw [hLeftStep]
    change (S_schur + Nm + d) * (1 - d_inv * Nm) = S_schur + d
    calc
      (S_schur + Nm + d) * (1 - d_inv * Nm)
        = (S_schur + Nm + d) -
            (S_schur * (d_inv * Nm) + Nm * (d_inv * Nm) + d * (d_inv * Nm)) := by
          noncomm_ring
      _ = S_schur + d := by
          rw [h_S_v, h_Nm_v, h_d_v]
          noncomm_ring
  have hCorner : P * S_schur * P = S_schur := by
    rw [hCornerL, hCornerR]
  have hOrth1 : S_schur * d = 0 := by
    calc S_schur * d = (S_schur * P) * d := by rw [hCornerR]
    _ = S_schur * (P * d) := by rw [mul_assoc]
    _ = 0 := by rw [hPd, mul_zero]
  have hOrth2 : d * S_schur = 0 := by
    calc d * S_schur = d * (P * S_schur) := by rw [hCornerL]
    _ = (d * P) * S_schur := by rw [← mul_assoc]
    _ = 0 := by rw [hdP, zero_mul]
  exact ⟨⟨hLeftInv1, hLeftInv2, hRightInv1, hRightInv2⟩,
    hDiag, ⟨hCorner, hOrth1, hOrth2⟩⟩

-- theorem-class: constructive endpoint
/-- **Bridge Theorem 4b (`peirceSchurComplement_krein_star_gram_positivity`)**:
In any `StarRing B` with self-adjoint idempotent `P * P = P`, `star P = P`:
1. When the `(1 - P)`-corner has **opposite Krein / BdG orientation**
   `d = -(1 - P)` (which is its own `(1 - P)`-inverse `d * d = 1 - P`), the
   noncommutative Peirce Schur complement of `M = P * a₀ * P + conePlus P A +
   coneMinus P (star A) - (1 - P)` flips the `-` sign to `+` and equals the
   Peirce Tetraktys horizon mass `genV P A (star A)` projected onto the `P`-sheet:
   `peirceSchurComplement P a₀ A (star A) (-(1 - P)) =
     P * a₀ * P + P * genV P A (star A) =
     P * a₀ * P + conePlus P A * star (conePlus P A)`.
2. For `a₀ = 1` (the operator lift of `bdgBlock 1 A`), the unipotent Möbius–Gauss
   elimination block-diagonalizes `P + conePlus P A + coneMinus P (star A) - (1 - P)`
   into `(P + conePlus P A * star (conePlus P A)) - (1 - P)`: a **strictly positive**
   Hermitian Gram sum `P * star P + N₊ * star N₊` on the `P`-sheet paired with the
   **negative** orientation `-(1 - P)` on the `(1 - P)`-sheet!
3. Squaring the block-diagonalized operator (`((P + N₊ N₊*) - (1 - P))²`) eliminates
   the negative orientation sign on the `(1 - P)`-sheet and yields the globally
   Hermitian-square sum `(P + N₊ N₊*) * star (P + N₊ N₊*) + (1 - P) * star (1 - P)`. -/
theorem peirceSchurComplement_krein_star_gram_positivity
    [StarRing B] {P : B} (hP : P * P = P) (hPs : star P = P) (a₀ A : B) :
    let Np := conePlus P A
    (peirceSchurComplement P a₀ A (star A) (-(1 - P)) =
        P * a₀ * P + P * genV P A (star A) ∧
      peirceSchurComplement P a₀ A (star A) (-(1 - P)) =
        P * a₀ * P + Np * star Np) ∧
    peirceLeftElimShear P A (-(1 - P)) *
        (P * 1 * P + Np + coneMinus P (star A) + (-(1 - P))) *
        peirceRightElimShear P (star A) (-(1 - P)) =
      (P + Np * star Np) - (1 - P) ∧
    ((P + Np * star Np) - (1 - P)) * ((P + Np * star Np) - (1 - P)) =
      (P + Np * star Np) * star (P + Np * star Np) +
        (1 - P) * star (1 - P) := by
  intro Np
  have hStarNp : star Np = coneMinus P (star A) := star_conePlus hPs A
  have hSchurV :
      peirceSchurComplement P a₀ A (star A) (-(1 - P)) =
        P * a₀ * P + P * genV P A (star A) := by
    dsimp [peirceSchurComplement]
    peirce_nf hP
  have hSchurGramGen : ∀ b₀ : B,
      peirceSchurComplement P b₀ A (star A) (-(1 - P)) =
        P * b₀ * P + Np * star Np := by
    intro b₀
    rw [hStarNp]
    dsimp [peirceSchurComplement, Np]
    peirce_nf hP
  have hdL : (1 - P) * (-(1 - P)) = -(1 - P) := by peirce_nf hP
  have hdR : (-(1 - P)) * (1 - P) = -(1 - P) := by peirce_nf hP
  have hddi : (-(1 - P)) * (-(1 - P)) = 1 - P := by peirce_nf hP
  have hBlock :=
    (peirceSchurComplement_unipotent_block_diagonalization
      hP hdL hdR hdL hdR hddi hddi 1 A (star A)).2.1
  have hS1 : peirceSchurComplement P 1 A (star A) (-(1 - P)) = P + Np * star Np := by
    rw [hSchurGramGen 1]
    have hP1P : P * 1 * P = P := by peirce_nf hP
    rw [hP1P]
  have hElim :
      peirceLeftElimShear P A (-(1 - P)) *
          (P * 1 * P + Np + coneMinus P (star A) + (-(1 - P))) *
          peirceRightElimShear P (star A) (-(1 - P)) =
        (P + Np * star Np) - (1 - P) := by
    rw [hBlock, hS1, ← sub_eq_add_neg]
  have hStarSum : star (P + Np * star Np) = P + Np * star Np := by
    rw [star_add, hPs, star_mul, star_star]
  have hStarComp : star (1 - P) = 1 - P := by
    rw [star_sub, star_one, hPs]
  have hSq :
      ((P + Np * star Np) - (1 - P)) * ((P + Np * star Np) - (1 - P)) =
        (P + Np * star Np) * star (P + Np * star Np) +
          (1 - P) * star (1 - P) := by
    rw [hStarSum, hStarComp]
    dsimp [Np]
    rw [star_conePlus hPs A]
    peirce_nf hP
  exact ⟨⟨hSchurV, hSchurGramGen a₀⟩, hElim, hSq⟩

end PeirceSchurBerezinianPositivity

/-! ===========================================================================
    Section 6: Capstone Coherence Theorem Across the 6 Strata
    =========================================================================== -/

-- theorem-class: capstone consumer theorem
/-- **Capstone Theorem (`supergraded_moebius_tetraktys_klein_quotient_berezinian_weyl_master_poset`)**:
Connects the four new noncommutative Peirce–Möbius–Tetraktys–Schur derivations with
the topological Klein operator-algebra quotient (`KleinOperatorAlgebraAssociatedQuotient`)
and Berezinian Stiefel–Whitney orientation class (`BerezinianSheafStiefelWhitney`):
1. `M1 → M2`: `peirceRiccatiVelocity` reduces `-T c T` to `-genV P A C * conePlus P A`
   and anticommutes with `invS P`,
2. `M2 → M3`: `peirceHalfTwist` swaps `P ↔ 1 - P` and reflects `s₀ ↦ 1 - s₀`, while
   `peirceDoubleTwist` restores `P` and `s₀` and descends to `PeirceMoebiusQuotient`
   at unit horizon `genV P A C = 1`, alongside the topological bundle projection
   `KleinOperatorAlgebraAssociatedQuotient.bundleProjection`,
3. `M3 → M4`: `invS P` is the noncommutative Weyl reflection that inverts
   `peirceCayleyPlus P A`,
4. `M4 → M5 → M6`: Unipotent Möbius shears block-diagonalize
   `P + N₊ + N₋ - (1 - P)` into `(P + N₊ N₊*) - (1 - P)`, where the `-(1 - P)`
   Krein/crosscap sign (classified by `cechCocycleSign n_ber q_ber = ±1`) is eliminated
   upon squaring `((P + N₊ N₊*) - (1 - P))² = (P + N₊ N₊*) * star (P + N₊ N₊*) + (1 - P) * star (1 - P)`. -/
theorem supergraded_moebius_tetraktys_klein_quotient_berezinian_weyl_master_poset
    (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0)
    {B : Type*} [Ring B] [StarRing B] {P : B} (hP : P * P = P) (hPs : star P = P)
    (A : B) (n_ber q_ber : ℕ) :
    let Np := conePlus P A
    let C := star A
    (∀ s : SupergradedMoebiusTetraktysKleinStratum,
      ¬ Relation.TransGen SupergradedMoebiusTetraktysKleinStratum.coverEdge s s) ∧
    (peirceRiccatiVelocity P 0 0 C 0 A = -(genV P A C * Np) ∧
      anticomm (invS P) (peirceRiccatiVelocity P 0 0 C 0 A) = 0) ∧
    (peirceHalfTwist P A C P = genV P A C * (1 - P) ∧
      peirceHalfTwist P A C (multiplicatioStone 0 P A C) =
        genV P A C * (1 - multiplicatioStone 0 P A C) ∧
      peirceDoubleTwist P A C (multiplicatioStone 0 P A C) =
        (genV P A C * genV P A C) * multiplicatioStone 0 P A C) ∧
    (Function.Surjective
        (_root_.KleinOperatorAlgebraAssociatedQuotient.bundleProjection omega homega) ∧
      Continuous
        (_root_.KleinOperatorAlgebraAssociatedQuotient.bundleProjection omega homega)) ∧
    (invS P * peirceCayleyPlus P A * invS P = peirceCayleyPlusInv P A ∧
      (invS P * peirceCayleyPlus P A * invS P) * peirceCayleyPlus P A = 1) ∧
    (peirceLeftElimShear P A (-(1 - P)) *
        (P * 1 * P + Np + coneMinus P C + (-(1 - P))) *
        peirceRightElimShear P C (-(1 - P)) =
      (P + Np * star Np) - (1 - P) ∧
      ((P + Np * star Np) - (1 - P)) * ((P + Np * star Np) - (1 - P)) =
        (P + Np * star Np) * star (P + Np * star Np) + (1 - P) * star (1 - P) ∧
      (InfoGeometry.SuperGrassmannian.BerezinianSheaf.IsOrientableBerezinianSheaf n_ber q_ber ↔
        InfoGeometry.SuperGrassmannian.BerezinianSheaf.cechCocycleSign n_ber q_ber = 1)) := by
  intro Np C
  have hRic := peirceRiccatiVelocity_eq_tetraktys_and_odd_corner hP 0 0 C 0 A
  have hHalf := peirceHalfTwist_swaps_sheets_and_reflects_logisticStone hP A C
  have hDouble := peirceDoubleTwist_restores_sheets_and_logisticStone hP A C P
  have hOp :=
    _root_.KleinOperatorAlgebraAssociatedQuotient.operator_algebra_quotient_packet
      omega homega
  have hWeyl := peirceWeylReflection_and_cayleySquash_inversion hP A C
  have hSchur := peirceSchurComplement_krein_star_gram_positivity hP hPs 1 A
  refine ⟨SupergradedMoebiusTetraktysKleinStratum.coverEdge_acyclic,
    ⟨hRic.2.2.1, hRic.2.2.2.2.2.2⟩,
    ⟨hHalf.1, hHalf.2.2.2.2, hDouble.2.2.2.1⟩,
    ⟨hOp.1, hOp.2.1⟩,
    hWeyl.2.2,
    ⟨hSchur.2.1, hSchur.2.2,
     InfoGeometry.SuperGrassmannian.BerezinianSheaf.orientable_iff_cocycle_one n_ber q_ber⟩⟩

end InfoGeometry.Canonical.SupergradedMoebiusTetraktysKleinQuotientBerezinianWeylPoset
