/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.OntologyRing
import InfoGeometry.Meta.Architecture
import InfoGeometry.OperatorAlgebra.OperatorMobiusAction
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.PeirceSpine.TetraktysKleinActionBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.NonCommutativeKMSStripKleinMonodromyPoset
import InfoGeometry.Topology.KleinBottleOrbitQuotient
import InfoGeometry.Canonical.BerezinianSuperBarrierBridge
import InfoGeometry.Canonical.WeylGaugeOperatorLift
import InfoGeometry.SuperGrassmannian.WeylBerezinianDeformation
import InfoGeometry.SuperGrassmannian.GradedGraphTransition
import InfoGeometry.SuperGrassmannian.MoebiusSuperGrassmannianCPT
import InfoGeometry.SuperGrassmannian.BerezinianSheafStiefelWhitney
import InfoGeometry.Canonical.CorrelationSymmetrization
import InfoGeometry.Canonical.CorrelationAntisymmetrization
import InfoGeometry.Canonical.GLSupermatrixGradedLie
import InfoGeometry.Canonical.BerezinFermionicIntegrationBridge
import InfoGeometry.Canonical.Z3GrassmannDifferentialCalculus
import InfoGeometry.Canonical.Z3TrialityCapstone
import InfoGeometry.Canonical.PrimeParafermionGrandCanonicalClock
import InfoGeometry.Arithmetic.MobiusWittenWeylDenominator
import InfoGeometry.Canonical.PeirceV4GrandCanonicalFourierBridge
import InfoGeometry.Canonical.VandermondeExclusionBridge
import InfoGeometry.Canonical.LaughlinStateQuantumHallBridge
import InfoGeometry.Canonical.WeylCharacterThetaBridge
import InfoGeometry.Canonical.WeylA2AlternatingDeterminantShadow
import InfoGeometry.Canonical.WeylPolynomialDivisibilityShadow
import InfoGeometry.Supergeometry.BerezinianDecomposition
import InfoGeometry.Canonical.RelativeModularBerezinianBridge
import InfoGeometry.Canonical.CattoGurseySplitBasis
import InfoGeometry.Canonical.CattoGurseyBlockGrading
import InfoGeometry.Superalgebra.PeirceDeWittZornQuantization

/-!
===============================================================================
HIVE CONSTITUTIONAL HEADER
===============================================================================
Module: InfoGeometry.Canonical.SupergradedMoebiusTetraktysKleinVandermondeColorPoset
Role: Canonical unification of:
  (A) The 6-stage Supergraded Operator Möbius → Tetraktys Orientation →
      Klein-Bottle Operator-Algebra Quotient → Operator Squashing →
      Berezinian & Stiefel–Whitney Sheaf → Weyl-Gauge Positivity poset
      (`MoebiusKleinBerezinianWeylStage`: `𝔐₁ ≺ 𝔐₂ ≺ 𝔐₃ ≺ 𝔐₄ ≺ 𝔐₅ ≺ 𝔐₆`), and
  (B) The 8-stage Stream VI Vandermonde, Superalgebra, Color Superalgebra &
      Partition-Statistics poset (`VandermondeSuperalgebraColorStage`:
      `𝔙₁ ≺ 𝔙₂ ≺ 𝔙₃ ≺ 𝔙₄ ≺ 𝔙₅ ≺ 𝔙₆ ≺ 𝔙₇ ≺ 𝔙₈`).

Architectural Invariant (Reusing Preexisting Repository Owners):
  1. Supergrading is foundational at every level:
     - Noncommutative operator Möbius graph transitions `(c + d ∘ f) ∘ (a + b ∘ f)⁻¹`
       preserve the direct-sum grading (`GradedGraphTransition.fractional_preservesDegree`),
     - The `2|1` `osp(1|2)` Möbius reflection `τ = J Γ` (`τ² = 1`) intertwines the
       parity-aware `superBracket`, reverses the Cartan generator `τ H τ = -H`, and
       preserves `supertrace` (`MoebiusSuperGrassmannianCPT`),
     - The Peirce Tetraktys `(Φ, J, V, Σ)` characterizes orientation via `1 - 2P = -invS P`,
       half-twist reversal `Φ Σ Φ = -V Σ`, and Klein-four `V₄ = ℤ₂ × ℤ₂` factorization,
     - Topological quotienting and Klein-bottle gluing construct the non-oriented space
       out of the algebra of operators (`KleinBottleOrbitQuotient`, `edgeTransition`),
       with first Stiefel–Whitney class `w₁(Ber) = (n + q : ZMod 2)` and Čech cocycle
       `(-1)^{(n+q)%2}` (`BerezinianSheafStiefelWhitney`),
     - Only downstream of supergrading, Tetraktys orientation, Klein-bottle gluing, and
       operator squashing are potentials, the Berezinian superdeterminant, determinant
       positivity, Weyl gauge invariance, and Vandermonde/color statistics evaluated.
===============================================================================
-/

noncomputable section

namespace InfoGeometry.Canonical.SupergradedMoebiusTetraktysKleinVandermondeColorPoset

open scoped BigOperators Matrix Polynomial
open InfoGeometry.Meta
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.OntologyRing
open InfoGeometry.SuperGrassmannian.GradedGraphChart
open InfoGeometry.SuperGrassmannian.GradedGraphTransition
open InfoGeometry.SuperGrassmannian.MoebiusReflection
open InfoGeometry.SuperGrassmannian.BerezinianSheaf
open InfoGeometry.Canonical.GLSupermatrixGradedLie
open InfoGeometry.Canonical.BerezinFermionicIntegrationBridge
open InfoGeometry.Canonical.Z3GrassmannDifferentialCalculus
open InfoGeometry.Canonical.Z3TrialityCapstone
open InfoGeometry.Canonical.PrimeParafermionGrandCanonicalClock
open InfoGeometry.Arithmetic.MobiusWittenWeylDenominator
open InfoGeometry.Canonical.PeirceV4GrandCanonicalFourierBridge
open InfoGeometry.Canonical.VandermondeExclusionBridge
open InfoGeometry.Canonical.WeylCharacterThetaBridge
open InfoGeometry.Canonical.WeylA2AlternatingDeterminantShadow
open InfoGeometry.Canonical.WeylPolynomialDivisibilityShadow
open InfoGeometry.Supergeometry.Berezinian
open InfoGeometry.Canonical.RelativeModularBerezinianBridge
open InfoGeometry.Canonical.CattoGurseyBlockGrading
open InfoGeometry.Canonical.GunaydinGursey
open InfoGeometry.Superalgebra.PeirceDeWittZornQuantization

/-! ===========================================================================
    Section 1: The 6-Stage Supergraded Operator Möbius → Tetraktys → Klein
    Quotient → Squashing → Berezinian/Stiefel–Whitney → Weyl-Gauge Poset
    (`𝔐₁ ≺ 𝔐₂ ≺ 𝔐₃ ≺ 𝔐₄ ≺ 𝔐₅ ≺ 𝔐₆`) and the 8-Stage Stream VI Poset
    (`𝔙₁ ≺ 𝔙₂ ≺ 𝔙₃ ≺ 𝔙₄ ≺ 𝔙₅ ≺ 𝔙₆ ≺ 𝔙₇ ≺ 𝔙₈`)
    =========================================================================== -/

/-- **The 6-Stage Supergraded Operator Möbius–Tetraktys–Klein–Berezinian–Weyl Poset
(`MoebiusKleinBerezinianWeylStage`)**:
Encodes the strict 6-stage causal dependency order `𝔐₁ ≺ 𝔐₂ ≺ 𝔐₃ ≺ 𝔐₄ ≺ 𝔐₅ ≺ 𝔐₆`. -/
inductive MoebiusKleinBerezinianWeylStage : Type
  | M1_PlanarToOperatorRingMoebiusLift
  | M2_TetraktysOrientationCharacterization
  | M3_KleinBottleOperatorAlgebraQuotientGluing
  | M4_GroupMoebiusSquashingAndCayleyWeylTransform
  | M5_BerezinianSuperdeterminantAndGradedPotential
  | M6_WeylGaugeTwoSheetVolumeAndIntensiveOperatorClosure
  deriving DecidableEq, Repr

namespace MoebiusKleinBerezinianWeylStage

/-- Integer rank `0..5` of the 6 causal stages. -/
def stageIndex : MoebiusKleinBerezinianWeylStage → ℕ
  | .M1_PlanarToOperatorRingMoebiusLift => 0
  | .M2_TetraktysOrientationCharacterization => 1
  | .M3_KleinBottleOperatorAlgebraQuotientGluing => 2
  | .M4_GroupMoebiusSquashingAndCayleyWeylTransform => 3
  | .M5_BerezinianSuperdeterminantAndGradedPotential => 4
  | .M6_WeylGaugeTwoSheetVolumeAndIntensiveOperatorClosure => 5

theorem stageIndex_injective : Function.Injective stageIndex := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance instLinearOrder : LinearOrder MoebiusKleinBerezinianWeylStage :=
  LinearOrder.lift' stageIndex stageIndex_injective

instance instFintype : Fintype MoebiusKleinBerezinianWeylStage where
  elems := {
    .M1_PlanarToOperatorRingMoebiusLift,
    .M2_TetraktysOrientationCharacterization,
    .M3_KleinBottleOperatorAlgebraQuotientGluing,
    .M4_GroupMoebiusSquashingAndCayleyWeylTransform,
    .M5_BerezinianSuperdeterminantAndGradedPotential,
    .M6_WeylGaugeTwoSheetVolumeAndIntensiveOperatorClosure
  }
  complete x := by cases x <;> simp

/-- Direct covering edge `s ≺ t` iff `stageIndex t = stageIndex s + 1`. -/
def causalEdge (s t : MoebiusKleinBerezinianWeylStage) : Prop :=
  stageIndex t = stageIndex s + 1

theorem causalEdge_lt {s t : MoebiusKleinBerezinianWeylStage} (h : causalEdge s t) : s < t := by
  change stageIndex s < stageIndex t
  unfold causalEdge at h
  omega

theorem transGen_causalEdge_lt {s t : MoebiusKleinBerezinianWeylStage}
    (h : Relation.TransGen causalEdge s t) : s < t := by
  induction h with
  | single h1 => exact causalEdge_lt h1
  | tail _ h2 ih => exact lt_trans ih (causalEdge_lt h2)

theorem causalEdge_acyclic (s : MoebiusKleinBerezinianWeylStage) :
    ¬ Relation.TransGen causalEdge s s := by
  intro h
  exact lt_irrefl s (transGen_causalEdge_lt h)

/-- Strict 6-stage chain `𝔐₁ < 𝔐₂ < 𝔐₃ < 𝔐₄ < 𝔐₅ < 𝔐₆`. -/
theorem strict_six_stage_chain :
    MoebiusKleinBerezinianWeylStage.M1_PlanarToOperatorRingMoebiusLift <
      .M2_TetraktysOrientationCharacterization ∧
    MoebiusKleinBerezinianWeylStage.M2_TetraktysOrientationCharacterization <
      .M3_KleinBottleOperatorAlgebraQuotientGluing ∧
    MoebiusKleinBerezinianWeylStage.M3_KleinBottleOperatorAlgebraQuotientGluing <
      .M4_GroupMoebiusSquashingAndCayleyWeylTransform ∧
    MoebiusKleinBerezinianWeylStage.M4_GroupMoebiusSquashingAndCayleyWeylTransform <
      .M5_BerezinianSuperdeterminantAndGradedPotential ∧
    MoebiusKleinBerezinianWeylStage.M5_BerezinianSuperdeterminantAndGradedPotential <
      .M6_WeylGaugeTwoSheetVolumeAndIntensiveOperatorClosure := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

end MoebiusKleinBerezinianWeylStage

/-- **The 8-Stage Vandermonde, Superalgebra, Color & Partition-Statistics Poset
(`VandermondeSuperalgebraColorStage`)**:
Encodes the strict 8-stage progression `𝔙₁ ≺ 𝔙₂ ≺ 𝔙₃ ≺ 𝔙₄ ≺ 𝔙₅ ≺ 𝔙₆ ≺ 𝔙₇ ≺ 𝔙₈`:
* `V1_TwoStateExchangeAndPhaseLinearCorrelationSplit`:
  Two-state exchange and `K = J ε` phase-linear correlation splitting (`CorrelationSymmetrization`,
  `CorrelationAntisymmetrization`).
* `V2_Z2KoszulGLSupermatrixLieAndBerezinContraction`:
  `ℤ₂` Koszul sign `(-1)^{|X||Y|}`, `gl(m|n)` super-Jacobi identity, vanishing supertrace of
  supercommutators, and one-mode Berezin exterior contraction (`GLSupermatrixGradedLie`,
  `BerezinFermionicIntegrationBridge`).
* `V3_Z3TernaryQuantumPlaneAndTripotentProjectors`:
  `ℤ₃` ternary quantum plane (`ω³ = 1`, `θ₁ θ₂ = ω θ₂ θ₁`, `θᵢ³ = 0`, `d³ = 0`) and tripotent
  `O³ = O` vacuum/up/down projectors (`Z3GrassmannDifferentialCalculus`, `Z3TrialityCapstone`).
* `V4_CyclotomicParafermionMobiusWittenAndV4Fourier`:
  Truncated geometric partition quotients `Q_κ(x) = ∑_{j<κ} x^j = (1 - x^κ)/(1 - x)` for fermions
  (`κ = 2`), `ℤ₃` parafermions (`κ = 3`), and bosonic limit (`κ → ∞`), finite Möbius–Witten–Weyl
  supertrace cancellation `Z_B · STr_F = 1`, and `V₄ = ℤ₂ × ℤ₂` Walsh–Fourier sector inversion.
* `V5_VandermondePauliExclusionAndLaughlinBraid`:
  Pauli exclusion collision locus `det(Matrix.vandermonde W) = ∏_{i<j}(W_j - W_i) = 0 ↔ ∃ i ≠ j, W_i = W_j`
  and Laughlin fractional quantum Hall braid statistics (`VandermondeExclusionBridge`,
  `LaughlinStateQuantumHallBridge`).
* `V6_WeylCharacterDenominatorAndPolynomialDivisibility`:
  Weyl character denominator for `A₁ = 𝔰𝔲(2)`, `A₂ = 𝔰𝔩₃` alternating 3-color Vandermonde
  `(y - x)(z - x)(z - y)`, and polynomial collision-pole divisibility `(X - a) ∣ (X^n - a^n)`.
* `V7_SuperLUBerezinianAndRelativeModularSupervolume`:
  Super-LU trifactor decomposition `L · H · R = M`, balanced Berezinian scaling invariance, and
  relative modular Berezinian supervolume potential (`BerezinianDecomposition`,
  `RelativeModularBerezinianBridge`).
* `V8_CattoGurseyColorSuperalgebraAndMomentCurveVandermonde`:
  Catto–Gürsey split-octonion hadronic color superalgebra (`SuperMatrix 6 21 R`,
  `STr(I_{6|21}) = -15`, quark cross-product fusion, 3-quark baryon singlet `-det(x, y, z) u₀`),
  and its specialization on the quadratic moment curve `(1, t_c, t_c²)` to the 3-color
  Vandermonde determinant `(t₂ - t₁)(t₃ - t₁)(t₃ - t₂)`. -/
inductive VandermondeSuperalgebraColorStage : Type
  | V1_TwoStateExchangeAndPhaseLinearCorrelationSplit
  | V2_Z2KoszulGLSupermatrixLieAndBerezinContraction
  | V3_Z3TernaryQuantumPlaneAndTripotentProjectors
  | V4_CyclotomicParafermionMobiusWittenAndV4Fourier
  | V5_VandermondePauliExclusionAndLaughlinBraid
  | V6_WeylCharacterDenominatorAndPolynomialDivisibility
  | V7_SuperLUBerezinianAndRelativeModularSupervolume
  | V8_CattoGurseyColorSuperalgebraAndMomentCurveVandermonde
  deriving DecidableEq, Repr

namespace VandermondeSuperalgebraColorStage

/-- Integer rank `0..7` of the 8 Stream VI stages. -/
def stageIndex : VandermondeSuperalgebraColorStage → ℕ
  | .V1_TwoStateExchangeAndPhaseLinearCorrelationSplit => 0
  | .V2_Z2KoszulGLSupermatrixLieAndBerezinContraction => 1
  | .V3_Z3TernaryQuantumPlaneAndTripotentProjectors => 2
  | .V4_CyclotomicParafermionMobiusWittenAndV4Fourier => 3
  | .V5_VandermondePauliExclusionAndLaughlinBraid => 4
  | .V6_WeylCharacterDenominatorAndPolynomialDivisibility => 5
  | .V7_SuperLUBerezinianAndRelativeModularSupervolume => 6
  | .V8_CattoGurseyColorSuperalgebraAndMomentCurveVandermonde => 7

theorem stageIndex_injective : Function.Injective stageIndex := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance instLinearOrder : LinearOrder VandermondeSuperalgebraColorStage :=
  LinearOrder.lift' stageIndex stageIndex_injective

instance instFintype : Fintype VandermondeSuperalgebraColorStage where
  elems := {
    .V1_TwoStateExchangeAndPhaseLinearCorrelationSplit,
    .V2_Z2KoszulGLSupermatrixLieAndBerezinContraction,
    .V3_Z3TernaryQuantumPlaneAndTripotentProjectors,
    .V4_CyclotomicParafermionMobiusWittenAndV4Fourier,
    .V5_VandermondePauliExclusionAndLaughlinBraid,
    .V6_WeylCharacterDenominatorAndPolynomialDivisibility,
    .V7_SuperLUBerezinianAndRelativeModularSupervolume,
    .V8_CattoGurseyColorSuperalgebraAndMomentCurveVandermonde
  }
  complete x := by cases x <;> simp

/-- Direct covering edge `s ≺ t` iff `stageIndex t = stageIndex s + 1`. -/
def causalEdge (s t : VandermondeSuperalgebraColorStage) : Prop :=
  stageIndex t = stageIndex s + 1

theorem causalEdge_lt {s t : VandermondeSuperalgebraColorStage} (h : causalEdge s t) : s < t := by
  change stageIndex s < stageIndex t
  unfold causalEdge at h
  omega

theorem transGen_causalEdge_lt {s t : VandermondeSuperalgebraColorStage}
    (h : Relation.TransGen causalEdge s t) : s < t := by
  induction h with
  | single h1 => exact causalEdge_lt h1
  | tail _ h2 ih => exact lt_trans ih (causalEdge_lt h2)

theorem causalEdge_acyclic (s : VandermondeSuperalgebraColorStage) :
    ¬ Relation.TransGen causalEdge s s := by
  intro h
  exact lt_irrefl s (transGen_causalEdge_lt h)

/-- Strict 8-stage chain `𝔙₁ < 𝔙₂ < 𝔙₃ < 𝔙₄ < 𝔙₅ < 𝔙₆ < 𝔙₇ < 𝔙₈`. -/
theorem strict_eight_stage_chain :
    VandermondeSuperalgebraColorStage.V1_TwoStateExchangeAndPhaseLinearCorrelationSplit <
      .V2_Z2KoszulGLSupermatrixLieAndBerezinContraction ∧
    VandermondeSuperalgebraColorStage.V2_Z2KoszulGLSupermatrixLieAndBerezinContraction <
      .V3_Z3TernaryQuantumPlaneAndTripotentProjectors ∧
    VandermondeSuperalgebraColorStage.V3_Z3TernaryQuantumPlaneAndTripotentProjectors <
      .V4_CyclotomicParafermionMobiusWittenAndV4Fourier ∧
    VandermondeSuperalgebraColorStage.V4_CyclotomicParafermionMobiusWittenAndV4Fourier <
      .V5_VandermondePauliExclusionAndLaughlinBraid ∧
    VandermondeSuperalgebraColorStage.V5_VandermondePauliExclusionAndLaughlinBraid <
      .V6_WeylCharacterDenominatorAndPolynomialDivisibility ∧
    VandermondeSuperalgebraColorStage.V6_WeylCharacterDenominatorAndPolynomialDivisibility <
      .V7_SuperLUBerezinianAndRelativeModularSupervolume ∧
    VandermondeSuperalgebraColorStage.V7_SuperLUBerezinianAndRelativeModularSupervolume <
      .V8_CattoGurseyColorSuperalgebraAndMomentCurveVandermonde := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Order-preserving anchor mapping each Stream VI stage `𝔙₁..𝔙₈` to its structural foundation
in the 6-stage `MoebiusKleinBerezinianWeylStage` (`𝔐₁..𝔐₆`) poset. -/
def anchorInMoebiusKleinPoset :
    VandermondeSuperalgebraColorStage → MoebiusKleinBerezinianWeylStage
  | .V1_TwoStateExchangeAndPhaseLinearCorrelationSplit =>
      .M2_TetraktysOrientationCharacterization
  | .V2_Z2KoszulGLSupermatrixLieAndBerezinContraction =>
      .M2_TetraktysOrientationCharacterization
  | .V3_Z3TernaryQuantumPlaneAndTripotentProjectors =>
      .M3_KleinBottleOperatorAlgebraQuotientGluing
  | .V4_CyclotomicParafermionMobiusWittenAndV4Fourier =>
      .M4_GroupMoebiusSquashingAndCayleyWeylTransform
  | .V5_VandermondePauliExclusionAndLaughlinBraid =>
      .M5_BerezinianSuperdeterminantAndGradedPotential
  | .V6_WeylCharacterDenominatorAndPolynomialDivisibility =>
      .M5_BerezinianSuperdeterminantAndGradedPotential
  | .V7_SuperLUBerezinianAndRelativeModularSupervolume =>
      .M5_BerezinianSuperdeterminantAndGradedPotential
  | .V8_CattoGurseyColorSuperalgebraAndMomentCurveVandermonde =>
      .M6_WeylGaugeTwoSheetVolumeAndIntensiveOperatorClosure

theorem anchorInMoebiusKleinPoset_monotone :
    Monotone anchorInMoebiusKleinPoset := by
  intro a b hab
  change MoebiusKleinBerezinianWeylStage.stageIndex (anchorInMoebiusKleinPoset a) ≤
    MoebiusKleinBerezinianWeylStage.stageIndex (anchorInMoebiusKleinPoset b)
  change stageIndex a ≤ stageIndex b at hab
  cases a <;> cases b <;>
    simp [anchorInMoebiusKleinPoset, MoebiusKleinBerezinianWeylStage.stageIndex, stageIndex] at hab ⊢

/-- Monotone projection onto the 6-layer representation-depth spine `RepDepth`. -/
def toRepDepth : VandermondeSuperalgebraColorStage → RepDepth
  | .V1_TwoStateExchangeAndPhaseLinearCorrelationSplit => .krein
  | .V2_Z2KoszulGLSupermatrixLieAndBerezinContraction => .krein
  | .V3_Z3TernaryQuantumPlaneAndTripotentProjectors => .krein
  | .V4_CyclotomicParafermionMobiusWittenAndV4Fourier => .transport
  | .V5_VandermondePauliExclusionAndLaughlinBraid => .thermo
  | .V6_WeylCharacterDenominatorAndPolynomialDivisibility => .thermo
  | .V7_SuperLUBerezinianAndRelativeModularSupervolume => .thermo
  | .V8_CattoGurseyColorSuperalgebraAndMomentCurveVandermonde => .thermo

theorem toRepDepth_rank_monotone :
    ∀ a b, a ≤ b → (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  intro a b hab
  change stageIndex a ≤ stageIndex b at hab
  cases a <;> cases b <;> simp [toRepDepth, RepDepth.toNat, stageIndex] at hab ⊢

/-- Monotone projection onto the 4-stratum operator ontology `OntologyMetaLevel`. -/
def toOntologyMetaLevel : VandermondeSuperalgebraColorStage → OntologyMetaLevel
  | .V1_TwoStateExchangeAndPhaseLinearCorrelationSplit => .M1_ProjectorClabject
  | .V2_Z2KoszulGLSupermatrixLieAndBerezinContraction => .M1_ProjectorClabject
  | .V3_Z3TernaryQuantumPlaneAndTripotentProjectors => .M2_GrassmannianPowertypeOrbit
  | .V4_CyclotomicParafermionMobiusWittenAndV4Fourier => .M2_GrassmannianPowertypeOrbit
  | .V5_VandermondePauliExclusionAndLaughlinBraid => .M3_ErlangenCasimirMetaLaw
  | .V6_WeylCharacterDenominatorAndPolynomialDivisibility => .M3_ErlangenCasimirMetaLaw
  | .V7_SuperLUBerezinianAndRelativeModularSupervolume => .M3_ErlangenCasimirMetaLaw
  | .V8_CattoGurseyColorSuperalgebraAndMomentCurveVandermonde => .M3_ErlangenCasimirMetaLaw

theorem toOntologyMetaLevel_rank_monotone :
    ∀ a b, a ≤ b → (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  intro a b hab
  change stageIndex a ≤ stageIndex b at hab
  cases a <;> cases b <;>
    simp [toOntologyMetaLevel, OntologyMetaLevel.rank, stageIndex] at hab ⊢

end VandermondeSuperalgebraColorStage

/-! ===========================================================================
    Section 2: Supergraded Operator Möbius Transitions, `2|1` `osp(1|2)`
    Reflection `τ = J Γ`, & Stiefel–Whitney Orientation Sheaf `w₁(Ber)`
    =========================================================================== -/

/-- **Supergraded Operator Möbius & Stiefel–Whitney Orientation Bridge
(`supergraded_operator_moebius_and_stiefel_whitney_orientation_bridge`)**:
Reuses `GradedGraphTransition.lean`, `MoebiusSuperGrassmannianCPT.lean`, and
`BerezinianSheafStiefelWhitney.lean` alongside `MoebiusTetraktysKleinBerezinianWeylPoset.lean`:
1. Over any (possibly noncommutative) `[Ring A]` and graded module decompositions `Decomposition GU`,
   `Decomposition GW`, the ordered fractional operator Möbius transition
   `((c + d.comp f).comp u.symm.toLinearMap)` preserves the direct-sum grading (`PreservesDegree GU GW`),
2. On the ordered `2|1` supermatrix carrier `M₃ R`, the Möbius reflection `τ = J Γ` squares to `1`,
   intertwines the parity-aware `superBracket p q`, reverses the Cartan generator `τ H τ = -H`,
   and preserves `supertrace`,
3. Under the Möbius inversion `Φ_M(T) = T⁻¹` on the super-Grassmannian crosscap quotient
   `Gr(n|q; 2n|2q)/ℤ₂`, the Berezinian Jacobian parity satisfies `(-1)^{(gradedParity n q)²} =
   cechCocycleSign n q`, and the Berezinian sheaf is orientable (`w₁(Ber) = 0`) iff `(n + q) % 2 = 0`
   and a non-orientable crosscap (`w₁(Ber) = 1`) iff `(n + q) % 2 = 1`. -/
theorem supergraded_operator_moebius_and_stiefel_whitney_orientation_bridge
    {A k ι U W : Type*} [Ring A] [CommRing k] [DecidableEq ι]
    [AddCommGroup U] [Module A U] [Module k U]
    [AddCommGroup W] [Module A W] [Module k W]
    (GU : ι → Submodule k U) (GW : ι → Submodule k W)
    [DirectSum.Decomposition GU] [DirectSum.Decomposition GW]
    (a_op : Module.End A U) (b_op : W →ₗ[A] U)
    (c_op : U →ₗ[A] W) (d_op : Module.End A W) (f_op : U →ₗ[A] W)
    (ha : PreservesDegree GU GU a_op) (hb : PreservesDegree GW GU b_op)
    (hc : PreservesDegree GU GW c_op) (hd : PreservesDegree GW GW d_op)
    (hf : PreservesDegree GU GW f_op)
    (u_inv : U ≃ₗ[A] U) (hu : u_inv.toLinearMap = a_op + b_op.comp f_op)
    {R : Type*} [CommRing R] (p_par q_par : Bool) (X_m3 Y_m3 : M₃ R)
    (n_dim q_dim : ℕ) :
    (PreservesDegree GU GW ((c_op + d_op.comp f_op).comp u_inv.symm.toLinearMap)) ∧
    (tau (R := R) * tau = 1 ∧
     tau (R := R) *
       InfoGeometry.Algebra.SupergradedBracket.superBracket p_par q_par X_m3 Y_m3 * tau =
       InfoGeometry.Algebra.SupergradedBracket.superBracket p_par q_par
         (tau * X_m3 * tau) (tau * Y_m3 * tau) ∧
     tau (R := R) *
       InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen R * tau =
       -InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.H_gen R ∧
     InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.supertrace
       (tau (R := R) * X_m3 * tau) =
       InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.supertrace X_m3) ∧
    ((-1 : ℤ) ^ ((gradedParity n_dim q_dim) ^ 2) = cechCocycleSign n_dim q_dim ∧
     (IsOrientableBerezinianSheaf n_dim q_dim ↔ (n_dim + q_dim) % 2 = 0) ∧
     (IsCrosscapNonOrientable n_dim q_dim ↔ (n_dim + q_dim) % 2 = 1) ∧
     (IsOrientableBerezinianSheaf n_dim q_dim ∨ IsCrosscapNonOrientable n_dim q_dim)) :=
  ⟨fractional_preservesDegree GU GW a_op b_op c_op d_op f_op ha hb hc hd hf u_inv hu,
   ⟨tau_sq (R := R),
    tau_conj_superBracket p_par q_par X_m3 Y_m3,
    tau_conj_H (R := R),
    supertrace_tau_invariant X_m3⟩,
   ⟨berezinian_parity_square_law n_dim q_dim,
    orientable_iff_even_mismatch n_dim q_dim,
    non_orientable_iff_odd_mismatch n_dim q_dim,
    orientable_or_crosscap n_dim q_dim⟩⟩

/-! ===========================================================================
    Section 3: Stream VI Stages `𝔙₁–𝔙₄` (Symmetry → Supergrading → Cyclotomic
    & Möbius–Witten Partition Statistics)
    =========================================================================== -/

/-- **Stage `𝔙₁` Theorem (`stage_V1_two_state_exchange_and_phase_linear_correlation_split`)**:
Reuses `CorrelationSymmetrization.lean` and `CorrelationAntisymmetrization.lean`:
1. Every two-state channel correlation on `DoubledSpace E` splits into its symmetric (bosonic)
   and antisymmetric (fermionic) exchange components,
2. Under the Bogoliubov phase-shift operator `K = J ε`, phase-linear perturbation channels have
   identically vanishing symmetric self-correlation, isolating the antisymmetric symplectic channel. -/
theorem stage_V1_two_state_exchange_and_phase_linear_correlation_split
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (reference comparison : InfoGeometry.Krein.DoubledSpace E)
    (X Y : InfoGeometry.Canonical.RelationalInformationCore.PerturbationChannel E)
    (hX : InfoGeometry.Canonical.BogoliubovTransport.IsPhaseLinear (E := E) X)
    (hY : InfoGeometry.Canonical.BogoliubovTransport.IsPhaseLinear (E := E) Y) :
    (InfoGeometry.Canonical.ModularTwoStateCorrelation.twoStateChannelCorrelation
        (E := E) reference comparison X Y =
      InfoGeometry.Canonical.CorrelationSymmetrization.symmetricTwoStateChannelCorrelation
        (E := E) reference comparison X Y +
      InfoGeometry.Canonical.CorrelationSymmetrization.antisymmetricTwoStateChannelCorrelation
        (E := E) reference comparison X Y) ∧
    (InfoGeometry.Canonical.CorrelationAntisymmetrization.symmetricPhaseShiftedTwoStateChannelCorrelation
        (E := E) comparison comparison X Y = 0) :=
  ⟨InfoGeometry.Canonical.CorrelationSymmetrization.twoStateChannelCorrelation_eq_symmetric_add_antisymmetric
     reference comparison X Y,
   InfoGeometry.Canonical.CorrelationAntisymmetrization.symmetricPhaseShiftedTwoStateChannelCorrelation_self_eq_zero_of_IsPhaseLinear
     comparison X Y hX hY⟩

/-- **Stage `𝔙₂` Theorem (`stage_V2_z2_koszul_gl_supermatrix_lie_and_berezin_contraction`)**:
Reuses `GLSupermatrixGradedLie.lean` and `BerezinFermionicIntegrationBridge.lean`:
1. On the native `gl(m|n)` supermatrix carrier `SuperMatrix m n R = Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) R`,
   the homogeneous supercommutator `superbracket p q X Y` preserves the `ℤ₂` grading `p + q`,
   the supertrace `supertrace M = Tr(A) - Tr(D)` obeys Koszul-graded cyclicity
   `supertrace (X * Y) = Parity.sign R p q * supertrace (Y * X)` and vanishes on all homogeneous
   supercommutators (`supertrace (superbracket p q X Y) = 0`), and the universal Koszul-signed
   super-Jacobi identity holds across all 8 parity triples `(pX, pY, pZ)`,
2. On the exterior Fock algebra `ExteriorAlgebra R (U →ₗ[R] R)`, the one-mode Berezin contraction
   `berezinIntegralOp u` annihilates the vacuum (`berezinIntegralOp u (vacuumState R U) = 0`)
   and integrates any normalized single-particle state (`alpha u = 1`) to the unit `1`. -/
theorem stage_V2_z2_koszul_gl_supermatrix_lie_and_berezin_contraction
    {m n : ℕ} {R : Type*} [CommRing R]
    (p q pX pY pZ : Parity) (X Y Z : SuperMatrix m n R)
    (hX : IsHomogeneous p X) (hY : IsHomogeneous q Y)
    {U : Type*} [AddCommGroup U] [Module R U]
    (u : U) (alpha : U →ₗ[R] R) (hpair : alpha u = 1) :
    (IsHomogeneous (p + q) (superbracket p q X Y) ∧
     supertrace (X * Y) = Parity.sign R p q * supertrace (Y * X) ∧
     supertrace (superbracket p q X Y) = 0 ∧
     Parity.sign (SuperMatrix m n R) pX pZ *
         ringSuperbracket pX (pY + pZ) X (ringSuperbracket pY pZ Y Z) +
       Parity.sign (SuperMatrix m n R) pY pX *
         ringSuperbracket pY (pZ + pX) Y (ringSuperbracket pZ pX Z X) +
       Parity.sign (SuperMatrix m n R) pZ pY *
         ringSuperbracket pZ (pX + pY) Z (ringSuperbracket pX pY X Y) = 0) ∧
    (berezinIntegralOp u (InfoGeometry.Canonical.FockVacuumAnnihilationBridge.vacuumState R U) = 0 ∧
     berezinIntegralOp u (InfoGeometry.Canonical.SingleParticleFockStateBridge.singleParticleState alpha) = 1) :=
  ⟨⟨superbracket_preserves_grading p q X Y hX hY,
    supertrace_mul_graded p q X Y hX hY,
    supertrace_superbracket_eq_zero p q X Y hX hY,
    gl_graded_super_jacobi pX pY pZ X Y Z⟩,
   ⟨berezin_integral_scalar_zero u,
    berezin_integral_single_particle_one u alpha hpair⟩⟩

/-- **Stage `𝔙₃` Theorem (`stage_V3_z3_ternary_quantum_plane_and_tripotent_projectors`)**:
Reuses `Z3GrassmannDifferentialCalculus.lean` and `Z3TrialityCapstone.lean`:
1. Any `Z3QuantumPlane A` satisfies `ω³ = 1`, cubic Grassmann nilpotence `θ₁³ = 0`, `θ₂³ = 0`,
   and ternary `q`-commutation `θ₁ * θ₂ = ω * (θ₂ * θ₁)`,
2. Any `Z3DifferentialCalculus B` satisfies the cubic differential identity `d (d (d x)) = 0`
   and the `ℤ₃`-graded Leibniz rule `d (x * y) = d x * y + ω^{deg x} * (x * d y)`,
3. Any tripotent operator `O³ = O` (`OSp12.Op Vspace`) decomposes the carrier into mutually
   orthogonal idempotent vacuum, up, and down projectors summing to `1`. -/
theorem stage_V3_z3_ternary_quantum_plane_and_tripotent_projectors
    {A : Type*} [MonoidWithZero A] (P_z3 : Z3QuantumPlane A)
    {B : Type*} [Zero B] [Add B] [Mul B] (D_z3 : Z3DifferentialCalculus B) (x_b y_b : B)
    {Vspace : Type*} [AddCommGroup Vspace] [Module ℝ Vspace]
    (O : InfoGeometry.Algebra.OSp12.Op Vspace) (hO3 : O ^ 3 = O) :
    (P_z3.omega ^ 3 = 1 ∧ P_z3.theta1 ^ 3 = 0 ∧ P_z3.theta2 ^ 3 = 0 ∧
     P_z3.theta1 * P_z3.theta2 = P_z3.omega * (P_z3.theta2 * P_z3.theta1)) ∧
    (D_z3.d (D_z3.d (D_z3.d x_b)) = 0 ∧
     D_z3.d (x_b * y_b) = D_z3.d x_b * y_b + D_z3.omegaPow (D_z3.degree x_b) * (x_b * D_z3.d y_b)) ∧
    (InfoGeometry.Algebra.OSp12.projVac O * InfoGeometry.Algebra.OSp12.projVac O =
       InfoGeometry.Algebra.OSp12.projVac O ∧
     InfoGeometry.Algebra.OSp12.projUp O * InfoGeometry.Algebra.OSp12.projUp O =
       InfoGeometry.Algebra.OSp12.projUp O ∧
     InfoGeometry.Algebra.OSp12.projDown O * InfoGeometry.Algebra.OSp12.projDown O =
       InfoGeometry.Algebra.OSp12.projDown O ∧
     InfoGeometry.Algebra.OSp12.projVac O + InfoGeometry.Algebra.OSp12.projUp O +
       InfoGeometry.Algebra.OSp12.projDown O = 1 ∧
     InfoGeometry.Algebra.OSp12.projUp O * InfoGeometry.Algebra.OSp12.projDown O = 0) := by
  have hTrip := hadjiivanov_tripotent_projector_packet O hO3
  exact ⟨z3_quantum_plane_packet P_z3,
         z3_differential_calculus_packet D_z3 x_b y_b,
         ⟨hTrip.1, hTrip.2.1, hTrip.2.2.1, hTrip.2.2.2.1, hTrip.2.2.2.2.2⟩⟩

/-- **Stage `𝔙₄` Theorem (`stage_V4_cyclotomic_parafermion_mobius_witten_and_v4_fourier`)**:
Reuses `PrimeParafermionGrandCanonicalClock.lean`, `MobiusWittenWeylDenominator.lean`, and
`PeirceV4GrandCanonicalFourierBridge.lean`:
1. The `κ`-truncated local partition factor `parafermionLocalFactor κ x = ∑_{j < κ} x^j` equals
   `(1 - x^κ) / (1 - x)` for `x ≠ 1`, specializes to the fermionic cyclotomic factor `Φ₂(x) = 1 + x`
   at `κ = 2` and the `ℤ₃` color parafermion factor `Φ₃(x) = 1 + x + x²` at `κ = 3`, and converges
   as `κ → ∞` (`|x| < 1`) to the bosonic geometric factor `(1 - x)⁻¹`,
2. Over any finite prime register `P`, the Möbius Dirichlet polynomial equals both the finite Weyl
   denominator `∏_{p ∈ P} (1 - q(p))` and the Witten fermionic supertrace `STrF`, and cancels the
   bosonic inverse denominator (`Z_B · STr_F = 1`),
3. On any finite state space graded by the Klein 4-group `V4Group`, the 4-character Walsh–Fourier
   transform inverts the twisted partition sums back to each individual `V₄`-sector partition. -/
theorem stage_V4_cyclotomic_parafermion_mobius_witten_and_v4_fourier
    (κ : ℕ) (x : ℝ) (hx_ne : x ≠ 1) (hx_lt : |x| < 1)
    (P_reg : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) (q_w : ℕ → ℂ)
    (hq : ∀ p ∈ P_reg.primes, (1 : ℂ) - q_w p ≠ 0)
    {α : Type*} [Fintype α] [Nonempty α]
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α)
    (grade : α → InfoGeometry.Topology.V4RootSystem.V4Group)
    (β μ : ℝ) (g_v4 : InfoGeometry.Topology.V4RootSystem.V4Group) :
    (parafermionLocalFactor κ x = (1 - x ^ κ) / (1 - x) ∧
     parafermionLocalFactor 2 x = 1 + x ∧
     parafermionLocalFactor 3 x = 1 + x + x ^ 2 ∧
     Filter.Tendsto (fun k : ℕ => parafermionLocalFactor k x) Filter.atTop (nhds ((1 - x)⁻¹))) ∧
    (InfoGeometry.Arithmetic.MobiusDirichletInverseBridge.finiteMobiusDirichletPolynomial P_reg q_w =
       InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge.finitePrimeWeylDenominator P_reg.primes q_w ∧
     InfoGeometry.Arithmetic.MobiusDirichletInverseBridge.finiteMobiusDirichletPolynomial P_reg q_w =
       InfoGeometry.Arithmetic.PrimonFinite.STrF P_reg.primes q_w ∧
     InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge.finitePrimeBosonicInverseDenominator P_reg.primes q_w *
       InfoGeometry.Arithmetic.MobiusDirichletInverseBridge.finiteMobiusDirichletPolynomial P_reg q_w = 1) ∧
    (InfoGeometry.GrandCanonical.partitionGC params β μ =
       ∑ g : InfoGeometry.Topology.V4RootSystem.V4Group, v4SectorPartition params grade β μ g ∧
     (1 / 4 : ℝ) *
       ∑ k : Fin 4,
         InfoGeometry.Canonical.V4GroupFourierTransform.v4Character k g_v4 *
           v4TwistedPartition params grade β μ k =
       v4SectorPartition params grade β μ g_v4) :=
  ⟨⟨parafermionLocalFactor_eq_div κ x hx_ne,
    parafermionLocalFactor_two x,
    parafermionLocalFactor_three x,
    tendsto_parafermionLocalFactor_atTop x hx_lt⟩,
   finite_mobius_witten_weyl_packet P_reg q_w hq,
   ⟨v4SectorPartition_total params grade β μ,
    v4Fourier_sector_inversion params grade β μ g_v4⟩⟩

/-! ===========================================================================
    Section 4: Stream VI Stages `𝔙₅–𝔙₈` (Vandermonde Exclusion, Weyl
    Denominators, Super-LU Berezinian, & Catto–Gürsey Color Superalgebra)
    =========================================================================== -/

/-- **Stage `𝔙₅` Theorem (`stage_V5_vandermonde_pauli_exclusion_and_laughlin_braid`)**:
Reuses `VandermondeExclusionBridge.lean` and `LaughlinStateQuantumHallBridge.lean`:
1. For any `n`-particle spectral node tuple `W : Fin n → R` over an integral domain `R`, the
   Vandermonde determinant equals the pairwise root separation product
   `∏ i, ∏ j ∈ Ioi i, (W j - W i)`, vanishes iff two nodes collide (`∃ i j, W i = W j ∧ i ≠ j`),
   and is nonzero iff `W` is injective (Pauli exclusion),
2. For any Laughlin state `L : QuantumHall.LaughlinState` (`0 < L.m`), the filling factor
   `ν = 1 / m` and anyon exchange braid phase `θ = π / m` are strictly positive, and `m`
   quasi-holes of charge `q = e / m` reconstruct the fundamental charge `q * m = e`. -/
theorem stage_V5_vandermonde_pauli_exclusion_and_laughlin_braid
    {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} (W : Fin n → R)
    (L : QuantumHall.LaughlinState) (e_charge : ℝ) :
    (FiniteVandermondeExclusionWitness.determinant W =
       ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (W j - W i) ∧
     (FiniteVandermondeExclusionWitness.determinant W ≠ 0 ↔ Function.Injective W) ∧
     (FiniteVandermondeExclusionWitness.determinant W = 0 ↔
       ∃ i j : Fin n, W i = W j ∧ i ≠ j)) ∧
    (0 < L.fillingFactor ∧
     L.quasiHoleCharge e_charge * (L.m : ℝ) = e_charge ∧
     0 < L.anyonBraidPhase) :=
  ⟨⟨FiniteVandermondeExclusionWitness.determinant_eq_pairwise_separation W,
    (FiniteVandermondeExclusionWitness.exclusion_packet W).1,
    (FiniteVandermondeExclusionWitness.exclusion_packet W).2⟩,
   ⟨L.filling_factor_pos,
    L.quasi_hole_charge_mult e_charge,
    L.anyon_braid_phase_pos⟩⟩

/-- **Stage `𝔙₆` Theorem (`stage_V6_weyl_character_denominator_and_polynomial_divisibility`)**:
Reuses `WeylCharacterThetaBridge.lean`, `WeylA2AlternatingDeterminantShadow.lean`, and
`WeylPolynomialDivisibilityShadow.lean`:
1. The `A₁ = 𝔰𝔲(2)` Weyl denominator satisfies `e^{iθ} - e^{-iθ} = 2i sin θ` and the Weyl
   character–denominator product identity `χ_m(e^{iθ}) (e^{iθ} - e^{-iθ}) = e^{i(m+1)θ} - e^{-i(m+1)θ}`,
2. On the 3-node `A₂ = 𝔰𝔩₃` color chart `C : Chart`, both the scalar Vandermonde denominator
   `(y - x)(z - x)(z - y)` and the exponential numerator `(e^y - e^x)(e^z - e^x)(e^z - e^y)`
   are alternating under the root transposition `x ↔ y`,
3. In the polynomial ring `R[X]`, the linear collision factor `X - C a` divides `X^n - C (a^n)`. -/
theorem stage_V6_weyl_character_denominator_and_polynomial_divisibility
    (θ : ℝ) (m_wt : ℕ)
    (C_a2 : Chart)
    {R : Type*} [CommRing R] (P_div : TwoNodePolynomialShadow R) :
    (Complex.exp (Complex.I * (θ : ℂ)) - Complex.exp (-Complex.I * (θ : ℂ)) =
       2 * Complex.I * (Real.sin θ : ℂ) ∧
     InfoGeometry.Canonical.WeylA1Character.su2Character (Complex.exp (Complex.I * (θ : ℂ))) m_wt *
       (Complex.exp (Complex.I * (θ : ℂ)) - Complex.exp (-Complex.I * (θ : ℂ))) =
       Complex.exp ((m_wt + 1) • (Complex.I * (θ : ℂ))) -
         Complex.exp (-((m_wt + 1) • (Complex.I * (θ : ℂ))))) ∧
    (C_a2.swap01.alternatingDenominatorFactor = -C_a2.alternatingDenominatorFactor ∧
     C_a2.swap01.alternatingNumeratorFactor = -C_a2.alternatingNumeratorFactor) ∧
    (P_div.denominator ∣ P_div.numerator ∧
     ∃ q : R[X], P_div.denominator * q = P_div.numerator) :=
  ⟨⟨weyl_denominator_su2 θ,
    character_denominator_product θ m_wt⟩,
   C_a2.alternating_determinant_packet,
   P_div.polynomial_divisibility_packet⟩

/-- **Stage `𝔙₇` Theorem (`stage_V7_super_lu_berezinian_and_relative_modular_supervolume`)**:
Reuses `BerezinianDecomposition.lean` and `RelativeModularBerezinianBridge.lean`:
1. For any `2 × 2` supermatrix `M` with invertible fermionic block `M 1 1 * invD = 1`, the
   Super-LU trifactor decomposition `factorL M invD * factorH M invD * factorR M invD = M` holds,
   unipotent factors have unit Berezinian (`berezinian !![1, x; 0, 1] 1 = 1`), and balanced
   `(1|1)` scaling leaves the Berezinian invariant (`berezinian (c • M) (inv_c * invD) = berezinian M invD`),
2. For finite positive rays `qPlus, q0Plus, qMinus, q0Minus : PositiveRay (Fin n)`, the doubled-sheet
   restricted volume scale equals `relativeModularBerezinianShadow`, its negative logarithm is
   `relativeModularSupervolumePotential`, and its Krein quadratic lift has exact first and second
   Fréchet derivatives equal to the Krein gradient and Krein Hessian. -/
theorem stage_V7_super_lu_berezinian_and_relative_modular_supervolume
    {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) (invD x_uni c inv_c : R)
    (hD : M 1 1 * invD = 1) (hc : c * inv_c = 1)
    {n : ℕ} [Nonempty (Fin n)]
    (qPlus q0Plus qMinus q0Minus : InfoGeometry.Canonical.PositiveRayCore.PositiveRay (Fin n))
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (u_kr v_kr : InfoGeometry.Krein.DoubledSpace E) :
    (factorL M invD * factorH M invD * factorR M invD = M ∧
     berezinian (!![1, x_uni; 0, 1]) 1 = 1 ∧
     berezinian (c • M) (inv_c * invD) = berezinian M invD) ∧
    (InfoGeometry.Canonical.RestrictedVolumeCharacter.RestrictedSheetEquiv.restrictedVolumeScale
       (E := (Fin n → ℝ))
       (relativeModularRestrictedSheetEquiv (n := n) qPlus q0Plus qMinus q0Minus) =
       InfoGeometry.Canonical.RelativeModularOperator.relativeModularBerezinianShadow
         (n := n) qPlus q0Plus qMinus q0Minus ∧
     -Real.log
       (InfoGeometry.Canonical.RestrictedVolumeCharacter.RestrictedSheetEquiv.restrictedVolumeScale
         (E := (Fin n → ℝ))
         (relativeModularRestrictedSheetEquiv (n := n) qPlus q0Plus qMinus q0Minus)) =
       InfoGeometry.Canonical.RelativeModularOperator.relativeModularSupervolumePotential
         (n := n) qPlus q0Plus qMinus q0Minus ∧
     inner ℝ
       (relativeModularSupervolumeKreinHessian (n := n) (E := E) qPlus q0Plus qMinus q0Minus u_kr)
       v_kr =
       InfoGeometry.Geometry.krein_form (E := E) u_kr v_kr) :=
  ⟨⟨super_lu_factorization M invD hD,
    unipotent_L_berezinian x_uni,
    berezinian_scaling_balanced M invD c inv_c hc⟩,
   ⟨relativeModularRestrictedSheetEquiv_restrictedVolumeScale_eq_berezinianShadow
      qPlus q0Plus qMinus q0Minus,
    neg_log_relativeModularRestrictedSheetEquiv_restrictedVolumeScale_eq_supervolumePotential
      qPlus q0Plus qMinus q0Minus,
    relativeModularSupervolumeKreinHessian_bilin_eq_krein_form
      qPlus q0Plus qMinus q0Minus u_kr v_kr⟩⟩

/-- Three-color point `(1, t, t²)` on the quadratic spectral moment curve. -/
def colorMomentCurve {R : Type*} [CommRing R] (t : R) : ColorVec3 R :=
  ⟨1, t, t ^ 2⟩

/-- Node map `Fin 3 → R` for the `3 × 3` Vandermonde matrix. -/
def momentNodes {R : Type*} (t₁ t₂ t₃ : R) : Fin 3 → R
  | 0 => t₁
  | 1 => t₂
  | 2 => t₃

/-- On the quadratic moment curve `(1, t_c, t_c²)`, the 3-quark baryon singlet `ColorVec3.baryonDet`
equals the 3-node Vandermonde product `(t₂ - t₁)(t₃ - t₁)(t₃ - t₂)`. -/
theorem baryonDet_colorMomentCurve_eq_vandermonde_product
    {R : Type*} [CommRing R] (t₁ t₂ t₃ : R) :
    ColorVec3.baryonDet (colorMomentCurve t₁) (colorMomentCurve t₂) (colorMomentCurve t₃) =
      (t₂ - t₁) * (t₃ - t₁) * (t₃ - t₂) := by
  simp [ColorVec3.baryonDet, ColorVec3.dot, ColorVec3.cross, colorMomentCurve]
  ring

/-- On the quadratic moment curve, the 3-quark baryon singlet equals the native Mathlib `3 × 3`
Vandermonde determinant `FiniteVandermondeExclusionWitness.determinant (momentNodes t₁ t₂ t₃)`. -/
theorem baryonDet_colorMomentCurve_eq_vandermonde_determinant
    {R : Type*} [CommRing R] (t₁ t₂ t₃ : R) :
    ColorVec3.baryonDet (colorMomentCurve t₁) (colorMomentCurve t₂) (colorMomentCurve t₃) =
      FiniteVandermondeExclusionWitness.determinant (momentNodes t₁ t₂ t₃) := by
  rw [baryonDet_colorMomentCurve_eq_vandermonde_product]
  simp only [FiniteVandermondeExclusionWitness.determinant,
    FiniteVandermondeExclusionWitness.matrix, Matrix.det_fin_three,
    Matrix.vandermonde_apply, momentNodes]
  norm_num
  ring

/-- Over an integral domain, the 3-quark baryon singlet on the moment curve vanishes iff two of the
three color spectral nodes collide. -/
theorem baryonDet_colorMomentCurve_eq_zero_iff_collision
    {R : Type*} [CommRing R] [IsDomain R] (t₁ t₂ t₃ : R) :
    ColorVec3.baryonDet (colorMomentCurve t₁) (colorMomentCurve t₂) (colorMomentCurve t₃) = 0 ↔
      ∃ i j : Fin 3, momentNodes t₁ t₂ t₃ i = momentNodes t₁ t₂ t₃ j ∧ i ≠ j := by
  rw [baryonDet_colorMomentCurve_eq_vandermonde_determinant]
  exact FiniteVandermondeExclusionWitness.determinant_eq_zero_iff_collision (momentNodes t₁ t₂ t₃)

/-- **Stage `𝔙₈` Theorem (`stage_V8_catto_gursey_color_superalgebra_and_moment_curve_vandermonde`)**:
Reuses `CattoGurseyBlockGrading.lean`, `CattoGurseySplitBasis.lean`, and
`PeirceDeWittZornQuantization.lean`:
1. On `SuperMatrix m n R`, the Peirce projections `even firstSupport` and `odd firstSupport`
   recover the native even/odd block decomposition, and on the hadronic `6|21` carrier the identity
   has supertrace `supertrace (1 : SuperMatrix 6 21 R) = -15`,
2. In the signed split-octonion basis (`CattoGurseySplitBasis`), the singlets resolve the unit
   (`uZero + uStarZero = one`), two triplet quarks fuse into an antitriplet diquark via the cross
   product (`mul (u i) (u j) = ∑ k, (e_i × e_j)_k • uStar k`), and three triplet quarks contract
   to the scalar triple-product baryon singlet `-dot x (cross y z)` along `uStarZero` / `uZero`,
3. Evaluated on the quadratic spectral moment curve `(1, t_c, t_c²)`, the 3-quark baryon singlet
   `ColorVec3.baryonDet` equals the `3 × 3` Vandermonde determinant `(t₂ - t₁)(t₃ - t₁)(t₃ - t₂)`
   and vanishes iff two color spectral nodes collide. -/
theorem stage_V8_catto_gursey_color_superalgebra_and_moment_curve_vandermonde
    {R : Type*} [CommRing R] [IsDomain R]
    {m n : ℕ} (H : SuperMatrix m n R)
    (i_c j_c : Fin 3) (x_z y_z z_z : InfoGeometry.Algebra.ZornVec3 R)
    (t₁ t₂ t₃ : R) :
    ((InfoGeometry.Core.PeirceGrading.even (firstSupport (R := R)) H =
        evenMatrix (blockA H) (blockD H) ∧
      InfoGeometry.Core.PeirceGrading.odd (firstSupport (R := R)) H =
        oddMatrix (blockB H) (blockC H)) ∧
     supertrace (1 : SuperMatrix 6 21 R) = -15) ∧
    ((InfoGeometry.Canonical.GunaydinGursey.uZero (R := R) :
       InfoGeometry.Algebra.ZornVectorMatrix R) +
       InfoGeometry.Canonical.GunaydinGursey.uStarZero (R := R) =
       InfoGeometry.Algebra.ZornVectorMatrix.one ∧
     InfoGeometry.Algebra.ZornVectorMatrix.mul
       (InfoGeometry.Canonical.GunaydinGursey.u i_c : InfoGeometry.Algebra.ZornVectorMatrix R)
       (InfoGeometry.Canonical.GunaydinGursey.u j_c) =
       ∑ k : Fin 3,
         InfoGeometry.Algebra.ZornVec3.cross
           (InfoGeometry.Algebra.ZornVec3.basis i_c : InfoGeometry.Algebra.ZornVec3 R)
           (InfoGeometry.Algebra.ZornVec3.basis j_c) k •
         InfoGeometry.Canonical.GunaydinGursey.uStar k ∧
     InfoGeometry.Algebra.ZornVectorMatrix.mul
       (InfoGeometry.Algebra.ZornVectorMatrix.mul
         (InfoGeometry.Algebra.ZornVectorMatrix.offDiagonal (R := R) (0 : InfoGeometry.Algebra.ZornVec3 R) x_z)
         (InfoGeometry.Algebra.ZornVectorMatrix.offDiagonal (R := R) (0 : InfoGeometry.Algebra.ZornVec3 R) y_z))
       (InfoGeometry.Algebra.ZornVectorMatrix.offDiagonal (R := R) (0 : InfoGeometry.Algebra.ZornVec3 R) z_z) =
       InfoGeometry.Algebra.ZornVectorMatrix.smul
         (-InfoGeometry.Algebra.ZornVec3.dot x_z (InfoGeometry.Algebra.ZornVec3.cross y_z z_z))
         InfoGeometry.Canonical.GunaydinGursey.uStarZero) ∧
    (ColorVec3.baryonDet (colorMomentCurve t₁) (colorMomentCurve t₂) (colorMomentCurve t₃) =
       (t₂ - t₁) * (t₃ - t₁) * (t₃ - t₂) ∧
     ColorVec3.baryonDet (colorMomentCurve t₁) (colorMomentCurve t₂) (colorMomentCurve t₃) =
       FiniteVandermondeExclusionWitness.determinant (momentNodes t₁ t₂ t₃) ∧
     (ColorVec3.baryonDet (colorMomentCurve t₁) (colorMomentCurve t₂) (colorMomentCurve t₃) = 0 ↔
       ∃ i j : Fin 3, momentNodes t₁ t₂ t₃ i = momentNodes t₁ t₂ t₃ j ∧ i ≠ j)) :=
  ⟨⟨peirce_components H, supertrace_identity_6_21⟩,
   ⟨singlet_sum,
    (fusion_table i_c j_c).1,
    (baryon_parenthesizations x_z y_z z_z).1⟩,
   ⟨baryonDet_colorMomentCurve_eq_vandermonde_product t₁ t₂ t₃,
    baryonDet_colorMomentCurve_eq_vandermonde_determinant t₁ t₂ t₃,
    baryonDet_colorMomentCurve_eq_zero_iff_collision t₁ t₂ t₃⟩⟩

/-! ===========================================================================
    Section 5: Master Cross-Poset Synthesis Uniting Supergraded Operator
    Möbius / Tetraktys / Klein-Bottle Gluing / Berezinian / Weyl Gauge
    (`𝔐₁ ≺ … ≺ 𝔐₆`) with Stream VI (`𝔙₁ ≺ … ≺ 𝔙₈`)
    =========================================================================== -/

/-- **Master Cross-Poset Synthesis Theorem
(`supergraded_moebius_tetraktys_klein_to_vandermonde_color_master_synthesis`)**:
Unites the 6-stage Supergraded Operator Möbius / Tetraktys Orientation / Klein-Bottle Quotient /
Squashing / Berezinian / Weyl-Gauge poset (`𝔐₁ ≺ … ≺ 𝔐₆`) with the 8-stage Stream VI
Vandermonde / Superalgebra / Color / Partition-Statistics poset (`𝔙₁ ≺ … ≺ 𝔙₈`):
1. Acyclicity of both causal posets and monotonicity of the cross-poset anchor
   `anchorInMoebiusKleinPoset : VandermondeSuperalgebraColorStage → MoebiusKleinBerezinianWeylStage`,
2. Supergraded `2|1` `osp(1|2)` Möbius reflection `τ² = 1` intertwining `superBracket` and
   preserving `supertrace`, together with the Stiefel–Whitney orientation dichotomy
   `IsOrientableBerezinianSheaf n q ∨ IsCrosscapNonOrientable n q`,
3. Peirce Tetraktys orientation involution `1 - 2P = -invS P`, Klein-bottle orbit quotient
   surjectivity, and period-2 unipotent edge-transition gluing,
4. Cyclotomic fermion (`κ = 2`) and `ℤ₃` parafermion (`κ = 3`) partition factors, finite
   Möbius–Witten–Weyl supertrace cancellation `Z_B · STr_F = 1`, and `V₄` Walsh–Fourier
   sector inversion,
5. Super-LU Berezinian factorization `L · H · R = M`, `gl(6|21)` supertrace `-15`, and the
   3-color moment-curve baryon singlet identity `baryonDet = det(Vandermonde)` with its exact
   node-collision vanishing locus. -/
theorem supergraded_moebius_tetraktys_klein_to_vandermonde_color_master_synthesis
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A_b X_b : B)
    {R : Type*} [CommRing R] [IsDomain R]
    (p_par q_par : Bool) (X_m3 Y_m3 : M₃ R)
    (n_dim q_dim : ℕ)
    (x_part : ℝ)
    (P_reg : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) (q_w : ℕ → ℂ)
    (hq : ∀ p ∈ P_reg.primes, (1 : ℂ) - q_w p ≠ 0)
    {α : Type*} [Fintype α] [Nonempty α]
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α)
    (grade : α → InfoGeometry.Topology.V4RootSystem.V4Group)
    (β μ : ℝ) (g_v4 : InfoGeometry.Topology.V4RootSystem.V4Group)
    (M_ber : Matrix (Fin 2) (Fin 2) R) (invD : R) (hD : M_ber 1 1 * invD = 1)
    (t₁ t₂ t₃ : R) :
    -- (1) Acyclicity of both posets & monotone cross-poset anchor
    ((∀ s : MoebiusKleinBerezinianWeylStage,
        ¬ Relation.TransGen MoebiusKleinBerezinianWeylStage.causalEdge s s) ∧
     (∀ v : VandermondeSuperalgebraColorStage,
        ¬ Relation.TransGen VandermondeSuperalgebraColorStage.causalEdge v v) ∧
     Monotone VandermondeSuperalgebraColorStage.anchorInMoebiusKleinPoset) ∧
    -- (2) Supergraded Möbius reflection `τ = J Γ` & Stiefel–Whitney crosscap dichotomy
    (tau (R := R) * tau = 1 ∧
     tau (R := R) *
       InfoGeometry.Algebra.SupergradedBracket.superBracket p_par q_par X_m3 Y_m3 * tau =
       InfoGeometry.Algebra.SupergradedBracket.superBracket p_par q_par
         (tau * X_m3 * tau) (tau * Y_m3 * tau) ∧
     InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.supertrace
       (tau (R := R) * X_m3 * tau) =
       InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.supertrace X_m3 ∧
     (IsOrientableBerezinianSheaf n_dim q_dim ∨ IsCrosscapNonOrientable n_dim q_dim)) ∧
    -- (3) Peirce Tetraktys orientation involution, Klein-bottle quotient, & period-2 edge gluing
    ((1 : B) - (2 : ℤ) • P = -PeirceSpine.invS P ∧
     Function.Surjective KleinBottleOrbitQuotient.quotientMap ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.NonCommutativeKMSStripKleinMonodromyPoset.edgeTransition
       P (1 + PeirceSpine.conePlus P A_b) (1 - PeirceSpine.conePlus P A_b)
       (InfoGeometry.OperatorAlgebra.PeirceSpine.NonCommutativeKMSStripKleinMonodromyPoset.edgeTransition
         P (1 + PeirceSpine.conePlus P A_b) (1 - PeirceSpine.conePlus P A_b) X_b) =
       X_b) ∧
    -- (4) Cyclotomic partition factors, Möbius–Witten–Weyl cancellation, & V₄ Walsh–Fourier inversion
    (parafermionLocalFactor 2 x_part = 1 + x_part ∧
     parafermionLocalFactor 3 x_part = 1 + x_part + x_part ^ 2 ∧
     InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge.finitePrimeBosonicInverseDenominator P_reg.primes q_w *
       InfoGeometry.Arithmetic.MobiusDirichletInverseBridge.finiteMobiusDirichletPolynomial P_reg q_w = 1 ∧
     (1 / 4 : ℝ) *
       ∑ k : Fin 4,
         InfoGeometry.Canonical.V4GroupFourierTransform.v4Character k g_v4 *
           v4TwistedPartition params grade β μ k =
       v4SectorPartition params grade β μ g_v4) ∧
    -- (5) Super-LU Berezinian, gl(6|21) supertrace -15, & 3-color moment-curve Vandermonde exclusion
    (factorL M_ber invD * factorH M_ber invD * factorR M_ber invD = M_ber ∧
     supertrace (1 : SuperMatrix 6 21 R) = -15 ∧
     ColorVec3.baryonDet (colorMomentCurve t₁) (colorMomentCurve t₂) (colorMomentCurve t₃) =
       FiniteVandermondeExclusionWitness.determinant (momentNodes t₁ t₂ t₃) ∧
     (ColorVec3.baryonDet (colorMomentCurve t₁) (colorMomentCurve t₂) (colorMomentCurve t₃) = 0 ↔
       ∃ i j : Fin 3, momentNodes t₁ t₂ t₃ i = momentNodes t₁ t₂ t₃ j ∧ i ≠ j)) := by
  have hInvNeg : (1 : B) - (2 : ℤ) • P = -PeirceSpine.invS P := by peirce_nf hP
  have hEdge :=
    (InfoGeometry.OperatorAlgebra.PeirceSpine.NonCommutativeKMSStripKleinMonodromyPoset.twisted_edge_transition_cocycle_and_klein_quotient_bridge
      hP (1 + PeirceSpine.conePlus P A_b) (1 - PeirceSpine.conePlus P A_b)
      (1 + PeirceSpine.conePlus P A_b) (1 - PeirceSpine.conePlus P A_b) A_b X_b).2.2.2
  exact ⟨⟨MoebiusKleinBerezinianWeylStage.causalEdge_acyclic,
          VandermondeSuperalgebraColorStage.causalEdge_acyclic,
          VandermondeSuperalgebraColorStage.anchorInMoebiusKleinPoset_monotone⟩,
         ⟨tau_sq (R := R),
          tau_conj_superBracket p_par q_par X_m3 Y_m3,
          supertrace_tau_invariant X_m3,
          orientable_or_crosscap n_dim q_dim⟩,
         ⟨hInvNeg,
          KleinBottleOrbitQuotient.quotientMap_surjective,
          hEdge⟩,
         ⟨parafermionLocalFactor_two x_part,
          parafermionLocalFactor_three x_part,
          finiteBoson_mul_mobiusPolynomial_cancel P_reg q_w hq,
          v4Fourier_sector_inversion params grade β μ g_v4⟩,
         ⟨super_lu_factorization M_ber invD hD,
          supertrace_identity_6_21,
          baryonDet_colorMomentCurve_eq_vandermonde_determinant t₁ t₂ t₃,
          baryonDet_colorMomentCurve_eq_zero_iff_collision t₁ t₂ t₃⟩⟩

end InfoGeometry.Canonical.SupergradedMoebiusTetraktysKleinVandermondeColorPoset
