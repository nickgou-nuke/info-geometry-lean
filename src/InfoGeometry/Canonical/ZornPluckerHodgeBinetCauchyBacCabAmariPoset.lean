/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.OntologyRing
import InfoGeometry.Meta.Architecture
import InfoGeometry.Superalgebra.PeirceDeWittZornQuantization
import InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset
import InfoGeometry.Projective.KleinQuadricPlucker
import InfoGeometry.Canonical.SplitOctonionIsotropicCircularAmariBaryonNambuPoset

/-!
# The 6-Stage Zorn Plücker–Hodge, Binet–Cauchy / Lagrange Volume Repair, BAC–CAB Alternativity & Amari Closure Poset (`ℨ₁ ≺ ⋯ ≺ ℨ₆`)

===============================================================================
HIVE CONSTITUTIONAL HEADER
===============================================================================
Module: InfoGeometry.Canonical.ZornPluckerHodgeBinetCauchyBacCabAmariPoset
Role: Canonical formalization of Stream XIII — The Zorn Plücker–Hodge,
  Binet–Cauchy / Lagrange Volume Repair, BAC–CAB Alternativity Cancellation,
  & Amari Dual-Isotropic Closure Poset (`ℨ₁ ≺ ℨ₂ ≺ ℨ₃ ≺ ℨ₄ ≺ ℨ₅ ≺ ℨ₆`):

1. **Stage `ℨ₁` (`Z1_TwoSheetedPeirceCarrierAndIsotropicAffineSpaces`)**:
   - Reuses `InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset`
     (`Vec3`, `ZornMatrix`, `eL`, `eR`, `psiPlus`, `psiMinus`, `psiOffDiag`) over any
     noncommutative `[Ring R]` and
     `InfoGeometry.Superalgebra.PeirceDeWittZornQuantization`
     (`ColorVec3`, `ZornAlgebra`, `norm`, `e₁`, `e₂`, `quarkU`, `antiquarkV`) over
     any `[CommRing K]`.
   - Reuses the imported Peirce carrier, isotropic wings, and multiplication tables;
     its own Stage `ℨ₁`–`ℨ₂` theorem proves the Zorn-versus-naive product decomposition
     and the orthogonal-reflection collapse witness. The separate `zornParamMul α β`
     family is defined over `[CommRing K]` for the later sign-lock results.

2. **Stage `ℨ₂` & Rung 0 (`Z2_OrthogonalCollapseAporiaOfNaiveBlockMultiplication`)**:
   - Defines naive associative-style block multiplication `naiveZornMatrixMul` (over
     `[Ring R]`) and `naiveZornAlgebraMul = zornParamMul 0 0` (over `[CommRing K]`)
     omitting the off-diagonal cross products.
   - Proves the **Orthogonal Collapse Aporia**: whenever `u₁ · v₂ = 0` and
     `v₁ · u₂ = 0`, naive block multiplication of off-diagonal matrices collapses to
     zero (`naiveZornAlgebraMul X Y = 0`).
   - Proves the concrete reflection aporia for `W_x = [[0, e₁], [e₁, 0]]` and
     `W_y = [[0, e₂], [e₂, 0]]`: both are invertible reflections (`W_x² = I₂`,
     `W_y² = I₂`, `norm(W_x) = norm(W_y) = -1`), yet their naive product is the zero
     matrix (`norm = 0 ≠ (-1)(-1)`), whereas Zorn's cross products rescue the product
     as `[[0, -e₃], [+e₃, 0]]` with `norm = +1 = (-1)(-1)`.

3. **Stage `ℨ₃` & Rung 1 (`Z3_DimensionalSelectionLawAndAlternatingWedgeClosure`)**:
   - Proves the **dimension-counting identity**: `D = 3` is the unique positive
     natural number satisfying `Nat.choose D 2 = D` (and over `ℤ`,
     `D(D - 1) = 2 D ↔ D = 0 ∨ D = 3`). This is a numerical dimension match only;
     this theorem does not construct an exterior-square map or prove an isomorphism
     `Λ²(𝔫₊) ≃ 𝔫₋`.

4. **Stage `ℨ₄` & Rung 2 (`Z4_BinetCauchyLagrangeDeterminantRepair`)**:
   - Proves the off-diagonal norm-defect formula for `X = [[0, u₁], [v₁, 0]]` and
     `Y = [[0, u₂], [v₂, 0]]`, the parameterized determinant defect is
     `norm(X) * norm(Y) - norm(zornParamMul α β X Y) =
      (1 + α * β) * ((u₁ × u₂) · (v₁ × v₂))`.
   - Proves that norm multiplicativity holds for all off-diagonal matrices if and
     only if `α * β = -1`, establishes the Binet–Cauchy / Lagrange identity for
     the off-diagonal defect, and separately reuses arbitrary-input norm
     multiplicativity of the fixed Zorn product `ZornAlgebra.mul`.

5. **Stage `ℨ₅` & Rung 3 (`Z5_BacCabVectorTripleProductAlternativityCancellation`)**:
   - Proves the universal 3D **BAC–CAB Vector Triple Product Identities**
     `v × (u × w) = (v · w) u - (v · u) w` and
     `(u × w) × v = (u · v) w - (w · v) u` on `ColorVec3 K`.
   - Proves that under `zornParamMul α β`, the `(1,2)` entry of
     `X · (X · Y) - (X · X) · Y` for `X = [[0, u], [v, 0]]` and `Y = [[0, u₂], [0, 0]]`
     is `(1 + α * β) • ((v · u₂) u - (u · v) u₂)`, which vanishes for all `u, v, u₂`
     if and only if `α * β = -1`.
   - Proves that for `α = 1, β = -1` (`ZornAlgebra.mul`), full left alternativity
     `X · (X · Y) = (X · X) · Y`, right alternativity `(Y · X) · X = Y · (X · X)`,
     and flexibility `(X · Y) · X = X · (Y · X)` hold identically for all
     `X, Y : ZornAlgebra K`.

6. **Stage `ℨ₆` & Rung 4 (`Z6_UniqueZornTableTwistorPluckerAndAmariCubicSynthesis`)**:
   - Proves the **Theorem 1 Uniqueness Synthesis**: fixing the canonical orientation
     `N_+(e_r) N_+(e_g) = N_-(e_b)` (`α = 1`) together with `α * β = -1` forces
     `β = -1` and uniquely selects `ZornAlgebra.mul = zornParamMul 1 (-1)`.
   - Proves the **Fourfold Relational Anatomy Decomposition** of `X * Y`, the
     **Affine Twistor Plücker Bridge** (`pluckerLine (1, u₁) (1, u₂)` has electric
     part `u₂ - u₁`, magnetic part `u₁ × u₂` equal to `N_+(u₁) N_+(u₂)`, and zero
     Klein quadric norm), and the **Amari–Chentsov Cubic Baryon Tensor**
     `{N_+(u₁) N_+(u₂), N_+(u₃)} = ((u₁ × u₂) · u₃) I₂`.

### Three-Bucket Audit Map

#### BUCKET 1 — Unconditional Kernel Truth
- `ZornPluckerHodgeBinetCauchyAmariStage`, `stageIndex_injective`, `causalEdge_lt`,
  `transGen_causalEdge_lt`, `causalEdge_acyclic`, `strict_six_stage_chain`,
  `toRepDepth_rank_monotone`, `toOntologyMetaLevel_rank_monotone`.
- Exact Zorn vector-matrix identities, Binet–Cauchy determinant defect, BAC–CAB vector triple
  products, and alternativity/flexibility over `[CommRing K]`.

#### BUCKET 2 — Conditional Kernel Theorems with Explicit Hypotheses
- Parameterized sign-lock `α * β = -1` uniqueness theorems under explicit orientation and
  vanishing-defect hypotheses.

#### BUCKET 3 — Open / Beyond-Scope Obligations
- Full exterior-algebra module isomorphism $\Lambda^2(\mathfrak{n}_+) \simeq \mathfrak{n}_-$
  beyond the dimension-counting and 3D cross-product realization remains outside this module.

## i. Overview
Formalizes the 6-stage Zorn Plücker–Hodge, Binet–Cauchy determinant repair, BAC–CAB alternativity cancellation, and Amari dual-isotropic closure poset (`ℨ₁ ≺ ⋯ ≺ ℨ₆`).

## ii. Key results
- `ZornPluckerHodgeBinetCauchyAmariStage.causalEdge_acyclic`
- `ZornPluckerHodgeBinetCauchyAmariStage.strict_six_stage_chain`

## iii. Table of contents
- Section 1: The 6-Stage Acyclic Causal Poset (`ℨ₁ ≺ ⋯ ≺ ℨ₆`)
- Sections 2–6: Stages `ℨ₁`–`ℨ₆`

## iv. References
- M. Zorn, *Alternativkörper und quadratische Systeme* (1933).
===============================================================================
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornPluckerHodgeBinetCauchyBacCabAmariPoset

open InfoGeometry.OperatorAlgebra.OntologyRing
open InfoGeometry.Meta
open InfoGeometry.Superalgebra.PeirceDeWittZornQuantization
open InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset
open InfoGeometry.Projective.KleinQuadricPlucker
open InfoGeometry.Canonical.SplitOctonionIsotropicCircularAmariBaryonNambuPoset

/-! ===========================================================================
    Section 1: The 6-Stage Acyclic Causal Poset (`ℨ₁ ≺ ℨ₂ ≺ ℨ₃ ≺ ℨ₄ ≺ ℨ₅ ≺ ℨ₆`)
    =========================================================================== -/

/-- The 6 causal stages of the Zorn Plücker–Hodge, Binet–Cauchy / Lagrange
Volume Repair, BAC–CAB Alternativity Cancellation, and Amari Dual-Isotropic
Closure Poset (`ℨ₁ ≺ ℨ₂ ≺ ℨ₃ ≺ ℨ₄ ≺ ℨ₅ ≺ ℨ₆`). -/
inductive ZornPluckerHodgeBinetCauchyAmariStage : Type
  | Z1_TwoSheetedPeirceCarrierAndIsotropicAffineSpaces
  | Z2_OrthogonalCollapseAporiaOfNaiveBlockMultiplication
  | Z3_DimensionalSelectionLawAndAlternatingWedgeClosure
  | Z4_BinetCauchyLagrangeDeterminantRepair
  | Z5_BacCabVectorTripleProductAlternativityCancellation
  | Z6_UniqueZornTableTwistorPluckerAndAmariCubicSynthesis
  deriving DecidableEq, Repr, Inhabited

namespace ZornPluckerHodgeBinetCauchyAmariStage

/-- Integer index `0..5` of the 6 Zorn–Amari closure stages. -/
def stageIndex : ZornPluckerHodgeBinetCauchyAmariStage → ℕ
  | .Z1_TwoSheetedPeirceCarrierAndIsotropicAffineSpaces => 0
  | .Z2_OrthogonalCollapseAporiaOfNaiveBlockMultiplication => 1
  | .Z3_DimensionalSelectionLawAndAlternatingWedgeClosure => 2
  | .Z4_BinetCauchyLagrangeDeterminantRepair => 3
  | .Z5_BacCabVectorTripleProductAlternativityCancellation => 4
  | .Z6_UniqueZornTableTwistorPluckerAndAmariCubicSynthesis => 5

-- theorem-class: transport lemma
/-- The integer index map `stageIndex` is injective on `ZornPluckerHodgeBinetCauchyAmariStage`. -/
theorem stageIndex_injective : Function.Injective stageIndex := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance instLinearOrder : LinearOrder ZornPluckerHodgeBinetCauchyAmariStage :=
  LinearOrder.lift' stageIndex stageIndex_injective

instance instFintype : Fintype ZornPluckerHodgeBinetCauchyAmariStage where
  elems := {
    .Z1_TwoSheetedPeirceCarrierAndIsotropicAffineSpaces,
    .Z2_OrthogonalCollapseAporiaOfNaiveBlockMultiplication,
    .Z3_DimensionalSelectionLawAndAlternatingWedgeClosure,
    .Z4_BinetCauchyLagrangeDeterminantRepair,
    .Z5_BacCabVectorTripleProductAlternativityCancellation,
    .Z6_UniqueZornTableTwistorPluckerAndAmariCubicSynthesis
  }
  complete x := by cases x <;> simp

/-- Directed cover edges `ℨ₁ → ℨ₂ → ℨ₃ → ℨ₄ → ℨ₅ → ℨ₆`. -/
def causalEdge :
    ZornPluckerHodgeBinetCauchyAmariStage →
    ZornPluckerHodgeBinetCauchyAmariStage → Prop
  | .Z1_TwoSheetedPeirceCarrierAndIsotropicAffineSpaces,
    .Z2_OrthogonalCollapseAporiaOfNaiveBlockMultiplication => True
  | .Z2_OrthogonalCollapseAporiaOfNaiveBlockMultiplication,
    .Z3_DimensionalSelectionLawAndAlternatingWedgeClosure => True
  | .Z3_DimensionalSelectionLawAndAlternatingWedgeClosure,
    .Z4_BinetCauchyLagrangeDeterminantRepair => True
  | .Z4_BinetCauchyLagrangeDeterminantRepair,
    .Z5_BacCabVectorTripleProductAlternativityCancellation => True
  | .Z5_BacCabVectorTripleProductAlternativityCancellation,
    .Z6_UniqueZornTableTwistorPluckerAndAmariCubicSynthesis => True
  | _, _ => False

instance instDecidableRelCausalEdge : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

-- theorem-class: transport lemma
/-- Every directed cover edge strictly increases the stage order. -/
theorem causalEdge_lt {s t : ZornPluckerHodgeBinetCauchyAmariStage}
    (h : causalEdge s t) : s < t := by
  change stageIndex s < stageIndex t
  cases s <;> cases t <;> revert h <;> decide

-- theorem-class: transport lemma
/-- Any transitive path of cover edges strictly increases the stage order. -/
theorem transGen_causalEdge_lt {s t : ZornPluckerHodgeBinetCauchyAmariStage}
    (h : Relation.TransGen causalEdge s t) : s < t := by
  induction h with
  | single h1 => exact causalEdge_lt h1
  | tail _ h2 ih => exact lt_trans ih (causalEdge_lt h2)

-- theorem-class: transport lemma
/-- The 6-stage `ZornPluckerHodgeBinetCauchyAmariStage` poset is strictly acyclic. -/
theorem causalEdge_acyclic (s : ZornPluckerHodgeBinetCauchyAmariStage) :
    ¬ Relation.TransGen causalEdge s s := by
  intro h
  exact lt_irrefl s (transGen_causalEdge_lt h)

-- theorem-class: transport lemma
/-- Complete 6-stage cover chain and cardinality `6` witness. -/
theorem strict_six_stage_chain :
    causalEdge .Z1_TwoSheetedPeirceCarrierAndIsotropicAffineSpaces
      .Z2_OrthogonalCollapseAporiaOfNaiveBlockMultiplication ∧
    causalEdge .Z2_OrthogonalCollapseAporiaOfNaiveBlockMultiplication
      .Z3_DimensionalSelectionLawAndAlternatingWedgeClosure ∧
    causalEdge .Z3_DimensionalSelectionLawAndAlternatingWedgeClosure
      .Z4_BinetCauchyLagrangeDeterminantRepair ∧
    causalEdge .Z4_BinetCauchyLagrangeDeterminantRepair
      .Z5_BacCabVectorTripleProductAlternativityCancellation ∧
    causalEdge .Z5_BacCabVectorTripleProductAlternativityCancellation
      .Z6_UniqueZornTableTwistorPluckerAndAmariCubicSynthesis ∧
    Fintype.card ZornPluckerHodgeBinetCauchyAmariStage = 6 := by
  decide

/-- Representation-depth projection `toRepDepth`. -/
def toRepDepth : ZornPluckerHodgeBinetCauchyAmariStage → RepDepth
  | .Z1_TwoSheetedPeirceCarrierAndIsotropicAffineSpaces => .projective
  | .Z2_OrthogonalCollapseAporiaOfNaiveBlockMultiplication => .operator
  | .Z3_DimensionalSelectionLawAndAlternatingWedgeClosure => .operator
  | .Z4_BinetCauchyLagrangeDeterminantRepair => .krein
  | .Z5_BacCabVectorTripleProductAlternativityCancellation => .transport
  | .Z6_UniqueZornTableTwistorPluckerAndAmariCubicSynthesis => .thermo

-- theorem-class: transport lemma
/-- The representation-depth projection `toRepDepth` is monotone with respect to stage order. -/
theorem toRepDepth_rank_monotone {a b : ZornPluckerHodgeBinetCauchyAmariStage}
    (h : a ≤ b) : (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  change stageIndex a ≤ stageIndex b at h
  cases a <;> cases b <;> revert h <;> decide

/-- Meta-level projection `toOntologyMetaLevel`. -/
def toOntologyMetaLevel : ZornPluckerHodgeBinetCauchyAmariStage → OntologyMetaLevel
  | .Z1_TwoSheetedPeirceCarrierAndIsotropicAffineSpaces => .M1_ProjectorClabject
  | .Z2_OrthogonalCollapseAporiaOfNaiveBlockMultiplication => .M1_ProjectorClabject
  | .Z3_DimensionalSelectionLawAndAlternatingWedgeClosure => .M2_GrassmannianPowertypeOrbit
  | .Z4_BinetCauchyLagrangeDeterminantRepair => .M2_GrassmannianPowertypeOrbit
  | .Z5_BacCabVectorTripleProductAlternativityCancellation => .M3_ErlangenCasimirMetaLaw
  | .Z6_UniqueZornTableTwistorPluckerAndAmariCubicSynthesis => .M3_ErlangenCasimirMetaLaw

-- theorem-class: transport lemma
/-- The ontology meta-level projection `toOntologyMetaLevel` is monotone with respect to stage order. -/
theorem toOntologyMetaLevel_rank_monotone {a b : ZornPluckerHodgeBinetCauchyAmariStage}
    (h : a ≤ b) : (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  change stageIndex a ≤ stageIndex b at h
  cases a <;> cases b <;> revert h <;> decide

end ZornPluckerHodgeBinetCauchyAmariStage

/-! ===========================================================================
    Section 2: Stages `ℨ₁, ℨ₂` & Rung 0 — Two-Sheeted Peirce Carrier,
    Two-Parameter Cross-Product Family `zornParamMul α β`, Naive Block
    Multiplication (`α = β = 0`), & The Orthogonal Reflection Collapse Aporia
    =========================================================================== -/

section StageZ1Z2CarrierAndAporia

variable {R : Type*} [Ring R]
variable {K : Type*} [CommRing K]

/-- Naive associative-style `2 × 2` block multiplication on `ZornMatrix R` over
any noncommutative `[Ring R]`, omitting the off-diagonal Hodge cross products
`-v₁ × v₂` and `+u₁ × u₂`. -/
@[simp] def naiveZornMatrixMul (X Y : ZornMatrix R) : ZornMatrix R where
  a := X.a * Y.a + Vec3.dot X.u Y.v
  u := Vec3.smulLeft X.a Y.u + Vec3.smulRight X.u Y.d
  v := Vec3.smulRight X.v Y.a + Vec3.smulLeft X.d Y.v
  d := Vec3.dot X.v Y.u + X.d * Y.d

/-- The pure Plücker–Hodge cross-product correction matrix
`⟨0, -v₁ × v₂, +u₁ × u₂, 0⟩` separating Zorn multiplication from naive block
multiplication over `[Ring R]`. -/
@[simp] def zornHodgeCrossMatrix (X Y : ZornMatrix R) : ZornMatrix R :=
  ⟨0, -Vec3.cross X.v Y.v, Vec3.cross X.u Y.u, 0⟩

/-- Two-parameter bilinear multiplication `zornParamMul α β X Y` on
`ZornAlgebra K` over `[CommRing K]` with lower-left primal cross term
`α • (u₁ × u₂)` and upper-right dual cross term `β • (v₁ × v₂)`:
- `zornParamMul 0 0` is naive associative-style block multiplication,
- `zornParamMul 1 (-1)` is Zorn's split-octonion multiplication `ZornAlgebra.mul`. -/
def zornParamMul (α β : K) (X Y : ZornAlgebra K) : ZornAlgebra K where
  a := X.a * Y.a + ColorVec3.dot X.u Y.v
  u := ColorVec3.add (ColorVec3.smul Y.b X.u)
         (ColorVec3.add (ColorVec3.smul X.a Y.u)
           (ColorVec3.smul β (ColorVec3.cross X.v Y.v)))
  v := ColorVec3.add (ColorVec3.smul X.b Y.v)
         (ColorVec3.add (ColorVec3.smul Y.a X.v)
           (ColorVec3.smul α (ColorVec3.cross X.u Y.u)))
  b := ColorVec3.dot X.v Y.u + X.b * Y.b

/-- Naive `2 × 2` block multiplication on `ZornAlgebra K`, defined as
`zornParamMul 0 0`. -/
def naiveZornAlgebraMul (X Y : ZornAlgebra K) : ZornAlgebra K :=
  zornParamMul 0 0 X Y

/-- Pure off-diagonal element `[[0, u], [v, 0]]` in `ZornAlgebra K`. -/
def zornOffDiag (u v : ColorVec3 K) : ZornAlgebra K :=
  ⟨0, u, v, 0⟩

/-- First coordinate reflection `W_r = [[0, e_r], [e_r, 0]]` in `ZornAlgebra K`. -/
def zornReflectionR : ZornAlgebra K :=
  zornOffDiag ColorVec3.e_r ColorVec3.e_r

/-- Second coordinate reflection `W_g = [[0, e_g], [e_g, 0]]` in `ZornAlgebra K`. -/
def zornReflectionG : ZornAlgebra K :=
  zornOffDiag ColorVec3.e_g ColorVec3.e_g

-- theorem-class: algebra/bridge law
/-- Parameter specialization laws for `zornParamMul`:
1. `zornParamMul 1 (-1) X Y = ZornAlgebra.mul X Y` (Zorn split-octonion product).
2. `naiveZornAlgebraMul X Y = zornParamMul 0 0 X Y` has zero cross-product terms. -/
theorem zornParamMul_one_neg_one_eq_mul (X Y : ZornAlgebra K) :
    zornParamMul (1 : K) (-1 : K) X Y = ZornAlgebra.mul X Y := by
  ext <;> dsimp [zornParamMul, ZornAlgebra.mul, ColorVec3.add, ColorVec3.sub,
    ColorVec3.smul, ColorVec3.cross] <;> ring

open ZornMatrix in
-- theorem-class: constructive endpoint
/-- **Stage `ℨ₁` & `ℨ₂` / Rung 0 Theorem
(`stage_Z1_Z2_peirce_grading_and_orthogonal_reflection_collapse_aporia`)**:
1. **Noncommutative `[Ring R]` Decomposition (`ZornMatrix R`)**:
   * `X * Y = naiveZornMatrixMul X Y + zornHodgeCrossMatrix X Y`,
   * For any off-diagonal `X = psiOffDiag u₁ v₁` and `Y = psiOffDiag u₂ v₂` with
     `u₁ · v₂ = 0` and `v₁ · u₂ = 0`, `naiveZornMatrixMul X Y = 0`.
2. **Noncommutative Reflection Collapse Aporia (`Wx`, `Wy` in `ZornMatrix R`)**:
   * `(Wx : ZornMatrix R) * Wx = 1` and `(Wy : ZornMatrix R) * Wy = 1`,
   * `naiveZornMatrixMul (Wx : ZornMatrix R) Wy = 0`,
   * `(Wx : ZornMatrix R) * Wy = ⟨0, -Vec3.eZ, Vec3.eZ, 0⟩`.
3. **Commutative `[CommRing K]` Norm & Reflection Collapse Aporia (`ZornAlgebra K`)**:
   * For `X = zornOffDiag u₁ v₁` and `Y = zornOffDiag u₂ v₂`,
     `ZornAlgebra.norm (naiveZornAlgebraMul X Y) = (u₁ · v₂) * (v₁ · u₂)`,
   * If `u₁ · v₂ = 0`, then `ZornAlgebra.norm (naiveZornAlgebraMul X Y) = 0`,
   * For the invertible reflections `zornReflectionR` and `zornReflectionG`:
     - `ZornAlgebra.mul zornReflectionR zornReflectionR = ZornAlgebra.one` and
       `ZornAlgebra.norm zornReflectionR = -1`,
     - `ZornAlgebra.mul zornReflectionG zornReflectionG = ZornAlgebra.one` and
       `ZornAlgebra.norm zornReflectionG = -1`,
     - `naiveZornAlgebraMul zornReflectionR zornReflectionG = ZornAlgebra.zero` and
       `ZornAlgebra.norm (naiveZornAlgebraMul zornReflectionR zornReflectionG) = 0`,
     - `ZornAlgebra.mul zornReflectionR zornReflectionG =
        ⟨0, ColorVec3.neg ColorVec3.e_b, ColorVec3.e_b, 0⟩` and
       `ZornAlgebra.norm (ZornAlgebra.mul zornReflectionR zornReflectionG) = 1 =
        ZornAlgebra.norm zornReflectionR * ZornAlgebra.norm zornReflectionG`. -/
theorem stage_Z1_Z2_peirce_grading_and_orthogonal_reflection_collapse_aporia
    (X Y : ZornMatrix R) (u₁ v₁ u₂ v₂ : ColorVec3 K) :
    (X * Y = naiveZornMatrixMul X Y + zornHodgeCrossMatrix X Y ∧
      (∀ x₁ y₁ x₂ y₂ : Vec3 R,
        Vec3.dot x₁ y₂ = 0 → Vec3.dot y₁ x₂ = 0 →
        naiveZornMatrixMul (ZornMatrix.psiOffDiag x₁ y₁) (ZornMatrix.psiOffDiag x₂ y₂) = 0)) ∧
    ((ZornMatrix.Wx : ZornMatrix R) * ZornMatrix.Wx = 1 ∧
      (ZornMatrix.Wy : ZornMatrix R) * ZornMatrix.Wy = 1 ∧
      naiveZornMatrixMul (ZornMatrix.Wx : ZornMatrix R) ZornMatrix.Wy = 0 ∧
      (ZornMatrix.Wx : ZornMatrix R) * ZornMatrix.Wy = ⟨0, -Vec3.eZ, Vec3.eZ, 0⟩) ∧
    (ZornAlgebra.norm (naiveZornAlgebraMul (zornOffDiag u₁ v₁) (zornOffDiag u₂ v₂)) =
        ColorVec3.dot u₁ v₂ * ColorVec3.dot v₁ u₂ ∧
      (ColorVec3.dot u₁ v₂ = 0 →
        ZornAlgebra.norm (naiveZornAlgebraMul (zornOffDiag u₁ v₁) (zornOffDiag u₂ v₂)) = 0)) ∧
    (ZornAlgebra.mul (zornReflectionR : ZornAlgebra K) zornReflectionR = ZornAlgebra.one ∧
      ZornAlgebra.mul (zornReflectionG : ZornAlgebra K) zornReflectionG = ZornAlgebra.one ∧
      ZornAlgebra.norm (zornReflectionR : ZornAlgebra K) = -1 ∧
      ZornAlgebra.norm (zornReflectionG : ZornAlgebra K) = -1 ∧
      naiveZornAlgebraMul (zornReflectionR : ZornAlgebra K) zornReflectionG = ZornAlgebra.zero ∧
      ZornAlgebra.norm (naiveZornAlgebraMul (zornReflectionR : ZornAlgebra K) zornReflectionG) = 0 ∧
      ZornAlgebra.mul (zornReflectionR : ZornAlgebra K) zornReflectionG =
        ⟨0, ColorVec3.neg ColorVec3.e_b, ColorVec3.e_b, 0⟩ ∧
      ZornAlgebra.norm (ZornAlgebra.mul (zornReflectionR : ZornAlgebra K) zornReflectionG) = 1 ∧
      ZornAlgebra.norm (ZornAlgebra.mul (zornReflectionR : ZornAlgebra K) zornReflectionG) =
        ZornAlgebra.norm (zornReflectionR : ZornAlgebra K) *
          ZornAlgebra.norm (zornReflectionG : ZornAlgebra K)) := by
  have hNaiveNorm :
      ZornAlgebra.norm (naiveZornAlgebraMul (zornOffDiag u₁ v₁) (zornOffDiag u₂ v₂)) =
        ColorVec3.dot u₁ v₂ * ColorVec3.dot v₁ u₂ := by
    dsimp [naiveZornAlgebraMul, zornParamMul, zornOffDiag, ZornAlgebra.norm,
      ColorVec3.dot, ColorVec3.add, ColorVec3.smul, ColorVec3.cross]
    ring
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨hNaiveNorm, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · dsimp [naiveZornMatrixMul, zornHodgeCrossMatrix]; zorn_ring
  · intro x₁ y₁ x₂ y₂ h12 h21
    dsimp only [naiveZornMatrixMul, ZornMatrix.psiOffDiag]
    rw [h12, h21]
    zorn_ring
  · zorn_ring
  · zorn_ring
  · dsimp [naiveZornMatrixMul]; zorn_ring
  · zorn_ring
  · intro h12
    rw [hNaiveNorm, h12, zero_mul]
  · ext <;> dsimp [zornReflectionR, zornOffDiag, ZornAlgebra.mul, ZornAlgebra.one,
      ColorVec3.e_r, ColorVec3.zero, ColorVec3.dot, ColorVec3.add, ColorVec3.sub,
      ColorVec3.smul, ColorVec3.cross] <;> ring
  · ext <;> dsimp [zornReflectionG, zornOffDiag, ZornAlgebra.mul, ZornAlgebra.one,
      ColorVec3.e_g, ColorVec3.zero, ColorVec3.dot, ColorVec3.add, ColorVec3.sub,
      ColorVec3.smul, ColorVec3.cross] <;> ring
  · dsimp [zornReflectionR, zornOffDiag, ZornAlgebra.norm, ColorVec3.e_r, ColorVec3.dot]
    ring
  · dsimp [zornReflectionG, zornOffDiag, ZornAlgebra.norm, ColorVec3.e_g, ColorVec3.dot]
    ring
  · ext <;> dsimp [naiveZornAlgebraMul, zornParamMul, zornReflectionR, zornReflectionG,
      zornOffDiag, ZornAlgebra.zero, ColorVec3.e_r, ColorVec3.e_g, ColorVec3.zero,
      ColorVec3.dot, ColorVec3.add, ColorVec3.smul, ColorVec3.cross] <;> ring
  · dsimp [naiveZornAlgebraMul, zornParamMul, zornReflectionR, zornReflectionG,
      zornOffDiag, ZornAlgebra.norm, ColorVec3.e_r, ColorVec3.e_g,
      ColorVec3.dot, ColorVec3.add, ColorVec3.smul, ColorVec3.cross]
    ring
  · ext <;> dsimp [zornReflectionR, zornReflectionG, zornOffDiag, ZornAlgebra.mul,
      ColorVec3.e_r, ColorVec3.e_g, ColorVec3.e_b, ColorVec3.neg, ColorVec3.dot,
      ColorVec3.add, ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring
  · dsimp [zornReflectionR, zornReflectionG, zornOffDiag, ZornAlgebra.mul,
      ZornAlgebra.norm, ColorVec3.e_r, ColorVec3.e_g, ColorVec3.dot,
      ColorVec3.add, ColorVec3.sub, ColorVec3.smul, ColorVec3.cross]
    ring
  · dsimp [zornReflectionR, zornReflectionG, zornOffDiag, ZornAlgebra.mul,
      ZornAlgebra.norm, ColorVec3.e_r, ColorVec3.e_g, ColorVec3.dot,
      ColorVec3.add, ColorVec3.sub, ColorVec3.smul, ColorVec3.cross]
    ring

end StageZ1Z2CarrierAndAporia

/-! ===========================================================================
    Section 3: Stage `ℨ₃` & Rung 1 — Dimensional Selection Law
    (`Nat.choose D 2 = D ↔ D = 3` for `D > 0`) & Self-Dual Exterior Wedge
    =========================================================================== -/

-- theorem-class: constructive endpoint
/-- **Stage `ℨ₃` / Rung 1 Theorem
(`stage_Z3_dimensional_selection_law_for_self_dual_isotropic_wedge`)**:
Numerical dimension-counting identities only (no exterior-power map is defined):
1. Over `ℕ`, for any positive dimension `D > 0`, `Nat.choose D 2 = D ↔ D = 3`.
2. Over `ℤ`, `D * (D - 1) = 2 * D ↔ D = 0 ∨ D = 3`.
3. In dimension `D = 3`, the total Zorn carrier dimension is `1 + 3 + 3 + 1 = 8`,
   with `Nat.choose 3 2 = 3`. -/
theorem stage_Z3_dimensional_selection_law_for_self_dual_isotropic_wedge :
    (∀ D : ℕ, 0 < D → (Nat.choose D 2 = D ↔ D = 3)) ∧
    (∀ D : ℤ, D * (D - 1) = 2 * D ↔ D = 0 ∨ D = 3) ∧
    Nat.choose 3 2 = 3 ∧
    1 + 3 + 3 + 1 = 8 := by
  refine ⟨?_, ?_, by decide, by decide⟩
  · intro D hD
    constructor
    · intro hChoose
      rcases D with _ | _ | _ | _ | n
      · omega
      · revert hChoose; decide
      · revert hChoose; decide
      · rfl
      · exfalso
        have hChoose' : (n + 4).choose 2 = n + 4 := hChoose
        rw [Nat.choose_two_right] at hChoose'
        change (n + 4) * (n + 3) / 2 = n + 4 at hChoose'
        have hMul : (n + 4) * (n + 3) ≥ 2 * (n + 4) + 2 := by
          nlinarith
        omega
    · intro h3
      subst h3
      decide
  · intro D
    constructor
    · intro hEq
      have hFact : D * (D - 3) = 0 := by
        linarith
      rcases mul_eq_zero.mp hFact with h0 | h3
      · exact Or.inl h0
      · exact Or.inr (sub_eq_zero.mp h3)
    · rintro (rfl | rfl) <;> ring

/-! ===========================================================================
    Section 4: Stage `ℨ₄` & Rung 2 — The Binet–Cauchy / Lagrange Determinant
    Repair (`(u₁·v₂)(v₁·u₂) + (u₁×u₂)·(v₁×v₂) = (u₁·v₁)(u₂·v₂)`)
    =========================================================================== -/

section StageZ4BinetCauchyLagrange

variable {K : Type*} [CommRing K]

-- theorem-class: constructive endpoint
/-- **Stage `ℨ₄` / Rung 2 Theorem
(`stage_Z4_binet_cauchy_lagrange_determinant_repair`)**:
Over any `[CommRing K]`:
1. **3D Binet–Cauchy / Lagrange Identity**:
   `(u₁ · v₂) * (v₁ · u₂) + (u₁ × u₂) · (v₁ × v₂) = (u₁ · v₁) * (u₂ · v₂)`.
2. **Parameterized Off-Diagonal Norm Defect**:
   For `X = zornOffDiag u₁ v₁` and `Y = zornOffDiag u₂ v₂` (`norm(X) = -u₁ · v₁`,
   `norm(Y) = -u₂ · v₂`):
   `ZornAlgebra.norm X * ZornAlgebra.norm Y -
     ZornAlgebra.norm (zornParamMul α β X Y) =
       (1 + α * β) * ColorVec3.dot (ColorVec3.cross u₁ u₂) (ColorVec3.cross v₁ v₂)`.
3. **Opposite-Sign Equivalence (`α * β = -1`)**:
   `(∀ u₁ v₁ u₂ v₂ : ColorVec3 K,
      ZornAlgebra.norm (zornParamMul α β (zornOffDiag u₁ v₁) (zornOffDiag u₂ v₂)) =
        ZornAlgebra.norm (zornOffDiag u₁ v₁) * ZornAlgebra.norm (zornOffDiag u₂ v₂))
    ↔ α * β = -1`.
4. **Full `2 × 2` Naive vs. Zorn Determinant Discrepancy**:
   For arbitrary `X, Y : ZornAlgebra K`,
   `ZornAlgebra.norm (ZornAlgebra.mul X Y) = ZornAlgebra.norm X * ZornAlgebra.norm Y`,
   and when `X = zornOffDiag u₁ v₁`, `Y = zornOffDiag u₂ v₂`,
   `ZornAlgebra.norm (ZornAlgebra.mul X Y) - ZornAlgebra.norm (naiveZornAlgebraMul X Y) =
     ColorVec3.dot (ColorVec3.cross u₁ u₂) (ColorVec3.cross v₁ v₂)`. -/
theorem stage_Z4_binet_cauchy_lagrange_determinant_repair
    (α β : K) (u₁ v₁ u₂ v₂ : ColorVec3 K) (X Y : ZornAlgebra K) :
    (ColorVec3.dot u₁ v₂ * ColorVec3.dot v₁ u₂ +
        ColorVec3.dot (ColorVec3.cross u₁ u₂) (ColorVec3.cross v₁ v₂) =
      ColorVec3.dot u₁ v₁ * ColorVec3.dot u₂ v₂) ∧
    (ZornAlgebra.norm (zornOffDiag u₁ v₁) * ZornAlgebra.norm (zornOffDiag u₂ v₂) -
        ZornAlgebra.norm (zornParamMul α β (zornOffDiag u₁ v₁) (zornOffDiag u₂ v₂)) =
      (1 + α * β) * ColorVec3.dot (ColorVec3.cross u₁ u₂) (ColorVec3.cross v₁ v₂)) ∧
    ((∀ x₁ y₁ x₂ y₂ : ColorVec3 K,
        ZornAlgebra.norm (zornParamMul α β (zornOffDiag x₁ y₁) (zornOffDiag x₂ y₂)) =
          ZornAlgebra.norm (zornOffDiag x₁ y₁) * ZornAlgebra.norm (zornOffDiag x₂ y₂)) ↔
      α * β = -1) ∧
    (ZornAlgebra.norm (ZornAlgebra.mul X Y) = ZornAlgebra.norm X * ZornAlgebra.norm Y ∧
      ZornAlgebra.norm (ZornAlgebra.mul (zornOffDiag u₁ v₁) (zornOffDiag u₂ v₂)) -
        ZornAlgebra.norm (naiveZornAlgebraMul (zornOffDiag u₁ v₁) (zornOffDiag u₂ v₂)) =
      ColorVec3.dot (ColorVec3.cross u₁ u₂) (ColorVec3.cross v₁ v₂)) := by
  have hDefect :
      ∀ x₁ y₁ x₂ y₂ : ColorVec3 K,
        ZornAlgebra.norm (zornOffDiag x₁ y₁) * ZornAlgebra.norm (zornOffDiag x₂ y₂) -
          ZornAlgebra.norm (zornParamMul α β (zornOffDiag x₁ y₁) (zornOffDiag x₂ y₂)) =
        (1 + α * β) * ColorVec3.dot (ColorVec3.cross x₁ x₂) (ColorVec3.cross y₁ y₂) := by
    intro x₁ y₁ x₂ y₂
    dsimp [zornParamMul, zornOffDiag, ZornAlgebra.norm,
      ColorVec3.dot, ColorVec3.add, ColorVec3.smul, ColorVec3.cross]
    ring
  refine ⟨?_, hDefect u₁ v₁ u₂ v₂, ?_, ⟨ZornAlgebra.norm_mul X Y, ?_⟩⟩
  · dsimp [ColorVec3.dot, ColorVec3.cross]
    ring
  · constructor
    · intro hAll
      have hSpec := hAll ColorVec3.e_r ColorVec3.e_r ColorVec3.e_g ColorVec3.e_g
      have hDefSpec := hDefect ColorVec3.e_r ColorVec3.e_r ColorVec3.e_g ColorVec3.e_g
      rw [hSpec, sub_self] at hDefSpec
      have hCross :
          ColorVec3.dot (ColorVec3.cross (ColorVec3.e_r : ColorVec3 K) ColorVec3.e_g)
            (ColorVec3.cross ColorVec3.e_r ColorVec3.e_g) = 1 := by
        dsimp [ColorVec3.e_r, ColorVec3.e_g, ColorVec3.cross, ColorVec3.dot]
        ring
      rw [hCross, mul_one] at hDefSpec
      linear_combination -hDefSpec
    · intro hαβ x₁ y₁ x₂ y₂
      have hDef := hDefect x₁ y₁ x₂ y₂
      have hZero : 1 + α * β = 0 := by linear_combination hαβ
      rw [hZero, zero_mul, sub_eq_zero] at hDef
      exact hDef.symm
  · dsimp [ZornAlgebra.mul, naiveZornAlgebraMul, zornParamMul, zornOffDiag,
      ZornAlgebra.norm, ColorVec3.dot, ColorVec3.add, ColorVec3.sub,
      ColorVec3.smul, ColorVec3.cross]
    ring

end StageZ4BinetCauchyLagrange

/-! ===========================================================================
    Section 5: Stage `ℨ₅` & Rung 3 — The BAC–CAB Vector Triple Product
    Identity & Opposite-Sign Alternativity Lock (`X(X Y) = X² Y`)
    =========================================================================== -/

section StageZ5BacCabAlternativity

variable {K : Type*} [CommRing K]

-- theorem-class: algebra/bridge law
/-- **3D BAC–CAB Vector Triple Product Identities (`cross_cross_bac_cab`)**:
For all `u, v, w : ColorVec3 K`:
1. Left BAC–CAB: `v × (u × w) = (v · w) • u - (v · u) • w`.
2. Right BAC–CAB: `(u × w) × v = (u · v) • w - (w · v) • u`. -/
theorem cross_cross_bac_cab (u v w : ColorVec3 K) :
    ColorVec3.cross v (ColorVec3.cross u w) =
      ColorVec3.sub (ColorVec3.smul (ColorVec3.dot v w) u)
        (ColorVec3.smul (ColorVec3.dot v u) w) ∧
    ColorVec3.cross (ColorVec3.cross u w) v =
      ColorVec3.sub (ColorVec3.smul (ColorVec3.dot u v) w)
        (ColorVec3.smul (ColorVec3.dot w v) u) := by
  refine ⟨?_, ?_⟩
  · ext <;> dsimp [ColorVec3.cross, ColorVec3.sub, ColorVec3.smul, ColorVec3.dot] <;> ring
  · ext <;> dsimp [ColorVec3.cross, ColorVec3.sub, ColorVec3.smul, ColorVec3.dot] <;> ring

-- theorem-class: constructive endpoint
/-- **Stage `ℨ₅` / Rung 3 Theorem
(`stage_Z5_bac_cab_vector_triple_product_enforces_alternativity`)**:
1. **Parameterized `(α, β)` Left Alternativity Defect on `(X, X, Y)`**:
   For `X = zornOffDiag u v` and `Y = quarkU u₂ = [[0, u₂], [0, 0]]`, under
   `zornParamMul α β`:
   * `zornParamMul α β X X = ColorVec3.dot u v • ZornAlgebra.one`,
   * `(zornParamMul α β (zornParamMul α β X X) Y).u = (u · v) • u₂`,
   * `(zornParamMul α β X (zornParamMul α β X Y)).u =
      (1 + α * β) • ((v · u₂) • u) - (α * β) • ((u · v) • u₂)`,
   * Thus the `(1,2)` left-alternativity defect is
     `(zornParamMul α β X (zornParamMul α β X Y)).u -
      (zornParamMul α β (zornParamMul α β X X) Y).u =
        (1 + α * β) • ((v · u₂) • u - (u · v) • u₂)`.
2. **Necessary and Sufficient Sign Lock (`α * β = -1`)**:
   `(∀ u v u₂ : ColorVec3 K,
      zornParamMul α β (zornOffDiag u v)
        (zornParamMul α β (zornOffDiag u v) (ZornAlgebra.quarkU u₂)) =
      zornParamMul α β (zornParamMul α β (zornOffDiag u v) (zornOffDiag u v))
        (ZornAlgebra.quarkU u₂)) ↔ α * β = -1`.
3. **Full Left Alternativity, Right Alternativity, & Flexibility of `ZornAlgebra.mul`**:
   For ALL `A, B : ZornAlgebra K`:
   * `ZornAlgebra.associator A A B = ZornAlgebra.zero` (`(A · A) · B = A · (A · B)`),
   * `ZornAlgebra.associator B A A = ZornAlgebra.zero` (`(B · A) · A = B · (A · A)`),
   * `ZornAlgebra.associator A B A = ZornAlgebra.zero` (`(A · B) · A = A · (B · A)`). -/
theorem stage_Z5_bac_cab_vector_triple_product_enforces_alternativity
    (α β : K) (u v u₂ : ColorVec3 K) (A B : ZornAlgebra K) :
    let X := zornOffDiag u v
    let Y := ZornAlgebra.quarkU u₂
    (zornParamMul α β X X = ZornAlgebra.smul (ColorVec3.dot u v) ZornAlgebra.one ∧
      (zornParamMul α β (zornParamMul α β X X) Y).u =
        ColorVec3.smul (ColorVec3.dot u v) u₂ ∧
      ColorVec3.sub (zornParamMul α β X (zornParamMul α β X Y)).u
        (zornParamMul α β (zornParamMul α β X X) Y).u =
        ColorVec3.smul (1 + α * β)
          (ColorVec3.sub (ColorVec3.smul (ColorVec3.dot v u₂) u)
            (ColorVec3.smul (ColorVec3.dot u v) u₂))) ∧
    ((∀ x y x₂ : ColorVec3 K,
        zornParamMul α β (zornOffDiag x y)
          (zornParamMul α β (zornOffDiag x y) (ZornAlgebra.quarkU x₂)) =
        zornParamMul α β (zornParamMul α β (zornOffDiag x y) (zornOffDiag x y))
          (ZornAlgebra.quarkU x₂)) ↔
      α * β = -1) ∧
    (ZornAlgebra.associator A A B = ZornAlgebra.zero ∧
      ZornAlgebra.associator B A A = ZornAlgebra.zero ∧
      ZornAlgebra.associator A B A = ZornAlgebra.zero) := by
  intro X Y
  have hAltDefect :
      ∀ x y x₂ : ColorVec3 K,
        ColorVec3.sub
          (zornParamMul α β (zornOffDiag x y)
            (zornParamMul α β (zornOffDiag x y) (ZornAlgebra.quarkU x₂))).u
          (zornParamMul α β (zornParamMul α β (zornOffDiag x y) (zornOffDiag x y))
            (ZornAlgebra.quarkU x₂)).u =
        ColorVec3.smul (1 + α * β)
          (ColorVec3.sub (ColorVec3.smul (ColorVec3.dot y x₂) x)
            (ColorVec3.smul (ColorVec3.dot x y) x₂)) := by
    intro x y x₂
    ext <;> dsimp [zornParamMul, zornOffDiag, ZornAlgebra.quarkU, ColorVec3.zero,
      ColorVec3.dot, ColorVec3.add, ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring
  refine ⟨⟨?_, ?_, hAltDefect u v u₂⟩, ?_, ⟨?_, ?_, ?_⟩⟩
  · ext <;> dsimp [X, zornParamMul, zornOffDiag, ZornAlgebra.smul, ZornAlgebra.one,
      ColorVec3.zero, ColorVec3.dot, ColorVec3.add, ColorVec3.smul, ColorVec3.cross] <;> ring
  · ext <;> dsimp [X, Y, zornParamMul, zornOffDiag, ZornAlgebra.quarkU,
      ColorVec3.zero, ColorVec3.dot, ColorVec3.add, ColorVec3.smul, ColorVec3.cross] <;> ring
  · constructor
    · intro hAll
      have hSpec := congrArg (fun M : ZornAlgebra K => M.u.c₁)
        (hAll ColorVec3.e_r ColorVec3.e_g ColorVec3.e_g)
      dsimp [zornParamMul, zornOffDiag, ZornAlgebra.quarkU,
        ColorVec3.e_r, ColorVec3.e_g, ColorVec3.zero,
        ColorVec3.dot, ColorVec3.add, ColorVec3.smul, ColorVec3.cross] at hSpec
      linear_combination hSpec
    · intro hαβ x y x₂
      have hZero : 1 + α * β = 0 := by linear_combination hαβ
      have hSub : α * β = -1 := hαβ
      ext
      · dsimp [zornParamMul, zornOffDiag, ZornAlgebra.quarkU, ColorVec3.zero,
          ColorVec3.dot, ColorVec3.add, ColorVec3.smul, ColorVec3.cross]
        ring
      · have h1 := congrArg ColorVec3.c₁ (hAltDefect x y x₂)
        rw [hZero] at h1
        dsimp [ColorVec3.sub, ColorVec3.smul] at h1
        linear_combination h1
      · have h2 := congrArg ColorVec3.c₂ (hAltDefect x y x₂)
        rw [hZero] at h2
        dsimp [ColorVec3.sub, ColorVec3.smul] at h2
        linear_combination h2
      · have h3 := congrArg ColorVec3.c₃ (hAltDefect x y x₂)
        rw [hZero] at h3
        dsimp [ColorVec3.sub, ColorVec3.smul] at h3
        linear_combination h3
      · dsimp [zornParamMul, zornOffDiag, ZornAlgebra.quarkU, ColorVec3.zero,
          ColorVec3.dot, ColorVec3.add, ColorVec3.smul, ColorVec3.cross]
        ring
      · dsimp [zornParamMul, zornOffDiag, ZornAlgebra.quarkU, ColorVec3.zero,
          ColorVec3.dot, ColorVec3.add, ColorVec3.smul, ColorVec3.cross]
        ring
      · dsimp [zornParamMul, zornOffDiag, ZornAlgebra.quarkU, ColorVec3.zero,
          ColorVec3.dot, ColorVec3.add, ColorVec3.smul, ColorVec3.cross]
        ring
      · dsimp [zornParamMul, zornOffDiag, ZornAlgebra.quarkU, ColorVec3.zero,
          ColorVec3.dot, ColorVec3.add, ColorVec3.smul, ColorVec3.cross]
        ring
  · ext <;> dsimp [ZornAlgebra.associator, ZornAlgebra.sub, ZornAlgebra.mul,
      ZornAlgebra.zero, ColorVec3.zero, ColorVec3.dot, ColorVec3.add,
      ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring
  · ext <;> dsimp [ZornAlgebra.associator, ZornAlgebra.sub, ZornAlgebra.mul,
      ZornAlgebra.zero, ColorVec3.zero, ColorVec3.dot, ColorVec3.add,
      ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring
  · ext <;> dsimp [ZornAlgebra.associator, ZornAlgebra.sub, ZornAlgebra.mul,
      ZornAlgebra.zero, ColorVec3.zero, ColorVec3.dot, ColorVec3.add,
      ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring

-- theorem-class: algebra/bridge law
/-- **Universal Cayley–Hamilton Quadratic Law & Moufang Identities on `ZornAlgebra K`
(`zornAlgebra_cayley_hamilton_and_moufang_identities`)**:
For all `X, Y, Z : ZornAlgebra K` over `[CommRing K]`:
1. **Adjugate / Conjugation Inversion Law**:
   `X · X̄ = norm(X) • I = X̄ · X`.
2. **Universal Cayley–Hamilton Quadratic Identity**:
   `X · X - trace(X) • X + norm(X) • I = 0`.
3. **Left, Right, & Middle Moufang Identities**:
   * `(X · (Y · X)) · Z = X · (Y · (X · Z))`,
   * `Z · (X · (Y · X)) = ((Z · X) · Y) · X`,
   * `(X · Y) · (Z · X) = X · ((Y · Z) · X)`. -/
theorem zornAlgebra_cayley_hamilton_and_moufang_identities
    (X Y Z : ZornAlgebra K) :
    (ZornAlgebra.mul X (ZornAlgebra.conj X) =
        ZornAlgebra.smul (ZornAlgebra.norm X) ZornAlgebra.one ∧
      ZornAlgebra.mul (ZornAlgebra.conj X) X =
        ZornAlgebra.smul (ZornAlgebra.norm X) ZornAlgebra.one) ∧
    ZornAlgebra.add
      (ZornAlgebra.sub (ZornAlgebra.mul X X)
        (ZornAlgebra.smul (ZornAlgebra.trace X) X))
      (ZornAlgebra.smul (ZornAlgebra.norm X) ZornAlgebra.one) =
      ZornAlgebra.zero ∧
    (ZornAlgebra.mul (ZornAlgebra.mul X (ZornAlgebra.mul Y X)) Z =
        ZornAlgebra.mul X (ZornAlgebra.mul Y (ZornAlgebra.mul X Z)) ∧
      ZornAlgebra.mul Z (ZornAlgebra.mul X (ZornAlgebra.mul Y X)) =
        ZornAlgebra.mul (ZornAlgebra.mul (ZornAlgebra.mul Z X) Y) X ∧
      ZornAlgebra.mul (ZornAlgebra.mul X Y) (ZornAlgebra.mul Z X) =
        ZornAlgebra.mul X (ZornAlgebra.mul (ZornAlgebra.mul Y Z) X)) := by
  refine ⟨⟨ZornAlgebra.mul_conj X, ZornAlgebra.conj_mul X⟩, ?_, ⟨?_, ?_, ?_⟩⟩
  · ext <;> (dsimp [ZornAlgebra.add, ZornAlgebra.sub, ZornAlgebra.mul,
      ZornAlgebra.smul, ZornAlgebra.trace, ZornAlgebra.norm, ZornAlgebra.one,
      ZornAlgebra.zero, ColorVec3.zero, ColorVec3.dot, ColorVec3.add,
      ColorVec3.sub, ColorVec3.smul, ColorVec3.cross]; ring)
  · ext <;> (dsimp [ZornAlgebra.mul, ColorVec3.dot, ColorVec3.add,
      ColorVec3.sub, ColorVec3.smul, ColorVec3.cross]; ring)
  · ext <;> (dsimp [ZornAlgebra.mul, ColorVec3.dot, ColorVec3.add,
      ColorVec3.sub, ColorVec3.smul, ColorVec3.cross]; ring)
  · ext <;> (dsimp [ZornAlgebra.mul, ColorVec3.dot, ColorVec3.add,
      ColorVec3.sub, ColorVec3.smul, ColorVec3.cross]; ring)

end StageZ5BacCabAlternativity

/-! ===========================================================================
    Section 6: Stage `ℨ₆` & Rung 4 — Unique Emergence of the Complete Zorn
    Multiplication Table, Fourfold Relational Anatomy, Affine Twistor Plücker
    Bridge (`pluckerLine`), & Amari–Chentsov Cubic Baryon Tensor
    =========================================================================== -/

section StageZ6SynthesisAndTwistorPlucker

variable {R : Type*} [Ring R]
variable {K : Type*} [CommRing K]

/-- Embed a 3-vector `u : ColorVec3 K` as an affine twistor `Z(u) = (1, u₁, u₂, u₃)`
in `KleinQuadricPlucker.Vec4 K`. -/
def affineTwistorVec4 (u : ColorVec3 K) : Vec4 K where
  x0 := 1
  x1 := u.c₁
  x2 := u.c₂
  x3 := u.c₃

/-- Extract the electric (primal `𝔫₊`) Plücker 3-vector `(p₀₁, p₀₂, p₀₃)` from
`Plucker6 K`. -/
def pluckerElectricVec3 (P : Plucker6 K) : ColorVec3 K :=
  ⟨P.p01, P.p02, P.p03⟩

/-- Extract the magnetic (dual `𝔫₋` Hodge-star) Plücker 3-vector
`(p₂₃, -p₁₃, p₁₂)` from `Plucker6 K`. -/
def pluckerMagneticVec3 (P : Plucker6 K) : ColorVec3 K :=
  ⟨P.p23, -P.p13, P.p12⟩

/-- Organ 1 of Zorn multiplication: Diagonal scalar core + Amari cross-metric
`[[a₁ a₂ + u₁ · v₂, 0], [0, v₁ · u₂ + d₁ d₂]]`. -/
@[simp] def zornOrgan1DiagonalCore (X Y : ZornMatrix R) : ZornMatrix R :=
  ⟨X.a * Y.a + Vec3.dot X.u Y.v, 0, 0, Vec3.dot X.v Y.u + X.d * Y.d⟩

/-- Organ 2 of Zorn multiplication: Primal `e`-isotropic `(1,2)` bimodule drift
`[[0, a₁ u₂ + u₁ d₂], [0, 0]]`. -/
@[simp] def zornOrgan2PrimalBimoduleDrift (X Y : ZornMatrix R) : ZornMatrix R :=
  ⟨0, Vec3.smulLeft X.a Y.u + Vec3.smulRight X.u Y.d, 0, 0⟩

/-- Organ 3 of Zorn multiplication: Dual `m`-isotropic `(2,1)` bimodule drift
`[[0, 0], [v₁ a₂ + d₁ v₂, 0]]`. -/
@[simp] def zornOrgan3DualBimoduleDrift (X Y : ZornMatrix R) : ZornMatrix R :=
  ⟨0, 0, Vec3.smulRight X.v Y.a + Vec3.smulLeft X.d Y.v, 0⟩

/-- Organ 4 of Zorn multiplication: Paired Plücker–Hodge cross-product jump
`[[0, -v₁ × v₂], [+u₁ × u₂, 0]]`. -/
@[simp] def zornOrgan4PluckerHodgeCross (X Y : ZornMatrix R) : ZornMatrix R :=
  zornHodgeCrossMatrix X Y

open ZornMatrix in
-- theorem-class: constructive endpoint
/-- **Stage `ℨ₆` / Rung 4 Theorem
(`stage_Z6_unique_zorn_table_fourfold_anatomy_twistor_plucker_and_cubic_baryon`)**:
1. **Uniqueness of the Zorn Parameter Pair `(α, β) = (1, -1)`**:
   If `zornParamMul α β` satisfies the canonical diquark orientation
   `zornParamMul α β (quarkU e_r) (quarkU e_g) = antiquarkV e_b` (`α = 1`) and the
   Lagrange / BAC–CAB lock `α * β = -1`, then `α = 1`, `β = -1`, and
   `zornParamMul α β X Y = ZornAlgebra.mul X Y` for all `X, Y : ZornAlgebra K`.
2. **Fourfold Relational Anatomy of Zorn Multiplication (`ZornMatrix R`)**:
   For any `X, Y : ZornMatrix R` over any noncommutative `[Ring R]`,
   `X * Y = zornOrgan1DiagonalCore X Y + zornOrgan2PrimalBimoduleDrift X Y +
            zornOrgan3DualBimoduleDrift X Y + zornOrgan4PluckerHodgeCross X Y`.
3. **Affine Twistor Plücker Line Bridge (`affineTwistorVec4`, `Plucker6.pluckerLine`)**:
   For any two primal vectors `u₁, u₂ : ColorVec3 K` embedded as affine twistors
   `Z₁ = (1, u₁)` and `Z₂ = (1, u₂)`:
   * `pluckerElectricVec3 (Plucker6.pluckerLine Z₁ Z₂) = u₂ - u₁`,
   * `pluckerMagneticVec3 (Plucker6.pluckerLine Z₁ Z₂) = u₁ × u₂`,
   * `ZornAlgebra.mul (ZornAlgebra.quarkU u₁) (ZornAlgebra.quarkU u₂) =
      ZornAlgebra.antiquarkV (pluckerMagneticVec3 (Plucker6.pluckerLine Z₁ Z₂))`,
   * `Plucker6.kleinQ (Plucker6.pluckerLine Z₁ Z₂) =
      ColorVec3.dot (pluckerElectricVec3 (Plucker6.pluckerLine Z₁ Z₂))
        (pluckerMagneticVec3 (Plucker6.pluckerLine Z₁ Z₂)) = 0`.
4. **Amari–Chentsov Cubic Baryon Singlet Tensor**:
   `ZornAlgebra.anticommutator
      (ZornAlgebra.mul (ZornAlgebra.quarkU u₁) (ZornAlgebra.quarkU u₂))
      (ZornAlgebra.quarkU u₃) =
    ZornAlgebra.smul (ColorVec3.dot (ColorVec3.cross u₁ u₂) u₃) ZornAlgebra.one`. -/
theorem stage_Z6_unique_zorn_table_fourfold_anatomy_twistor_plucker_and_cubic_baryon
    (α β : K) (X Y : ZornMatrix R) (A B : ZornAlgebra K) (u₁ u₂ u₃ : ColorVec3 K) :
    let L := Plucker6.pluckerLine (affineTwistorVec4 u₁) (affineTwistorVec4 u₂)
    ((zornParamMul α β (ZornAlgebra.quarkU ColorVec3.e_r) (ZornAlgebra.quarkU ColorVec3.e_g) =
        ZornAlgebra.antiquarkV ColorVec3.e_b ∧ α * β = -1) →
      α = 1 ∧ β = -1 ∧ zornParamMul α β A B = ZornAlgebra.mul A B) ∧
    (X * Y = zornOrgan1DiagonalCore X Y + zornOrgan2PrimalBimoduleDrift X Y +
        zornOrgan3DualBimoduleDrift X Y + zornOrgan4PluckerHodgeCross X Y) ∧
    (pluckerElectricVec3 L = ColorVec3.sub u₂ u₁ ∧
      pluckerMagneticVec3 L = ColorVec3.cross u₁ u₂ ∧
      ZornAlgebra.mul (ZornAlgebra.quarkU u₁) (ZornAlgebra.quarkU u₂) =
        ZornAlgebra.antiquarkV (pluckerMagneticVec3 L) ∧
      Plucker6.kleinQ L =
        ColorVec3.dot (pluckerElectricVec3 L) (pluckerMagneticVec3 L) ∧
      Plucker6.kleinQ L = 0) ∧
    (ZornAlgebra.anticommutator
        (ZornAlgebra.mul (ZornAlgebra.quarkU u₁) (ZornAlgebra.quarkU u₂))
        (ZornAlgebra.quarkU u₃) =
      ZornAlgebra.smul (ColorVec3.dot (ColorVec3.cross u₁ u₂) u₃) ZornAlgebra.one) := by
  intro L
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨hOrient, hProd⟩
    have hα : α = 1 := by
      have h3 := congrArg (fun M : ZornAlgebra K => M.v.c₃) hOrient
      dsimp [zornParamMul, ZornAlgebra.quarkU, ZornAlgebra.antiquarkV,
        ColorVec3.e_r, ColorVec3.e_g, ColorVec3.e_b, ColorVec3.zero,
        ColorVec3.add, ColorVec3.smul, ColorVec3.cross] at h3
      linear_combination h3
    have hβ : β = -1 := by
      rw [hα, one_mul] at hProd
      exact hProd
    refine ⟨hα, hβ, ?_⟩
    rw [hα, hβ]
    exact zornParamMul_one_neg_one_eq_mul A B
  · dsimp [zornOrgan1DiagonalCore, zornOrgan2PrimalBimoduleDrift,
      zornOrgan3DualBimoduleDrift, zornOrgan4PluckerHodgeCross, zornHodgeCrossMatrix]
    zorn_ring
  · dsimp only [L]
    refine ⟨?_, ?_, ?_, ?_, Plucker6.kleinQ_pluckerLine _ _⟩
    · ext <;> dsimp [pluckerElectricVec3, Plucker6.pluckerLine, affineTwistorVec4,
        ColorVec3.sub] <;> ring
    · ext <;> dsimp [pluckerMagneticVec3, Plucker6.pluckerLine, affineTwistorVec4,
        ColorVec3.cross] <;> ring
    · ext <;> dsimp [ZornAlgebra.mul, ZornAlgebra.quarkU, ZornAlgebra.antiquarkV,
        pluckerMagneticVec3, Plucker6.pluckerLine, affineTwistorVec4,
        ColorVec3.zero, ColorVec3.dot, ColorVec3.add, ColorVec3.sub,
        ColorVec3.smul, ColorVec3.cross] <;> ring
    · dsimp [Plucker6.kleinQ, pluckerElectricVec3, pluckerMagneticVec3, ColorVec3.dot]
      ring
  · change ZornAlgebra.add
      (ZornAlgebra.mul (ZornAlgebra.mul (ZornAlgebra.quarkU u₁)
        (ZornAlgebra.quarkU u₂)) (ZornAlgebra.quarkU u₃))
      (ZornAlgebra.mul (ZornAlgebra.quarkU u₃)
        (ZornAlgebra.mul (ZornAlgebra.quarkU u₁) (ZornAlgebra.quarkU u₂))) = _
    ext <;> dsimp [ZornAlgebra.add, ZornAlgebra.mul,
      ZornAlgebra.quarkU, ZornAlgebra.smul, ZornAlgebra.one, ColorVec3.zero,
      ColorVec3.dot, ColorVec3.add, ColorVec3.sub, ColorVec3.smul,
      ColorVec3.cross] <;> ring

end StageZ6SynthesisAndTwistorPlucker

/-! ===========================================================================
    Section 7: Master Poset Synthesis (`ℨ₁ ≺ ℨ₂ ≺ ℨ₃ ≺ ℨ₄ ≺ ℨ₅ ≺ ℨ₆`)
    =========================================================================== -/

-- theorem-class: synthesis/master theorem
/-- **Master Synthesis Theorem
   (`zorn_plucker_hodge_binet_cauchy_bac_cab_amari_master_poset`)**:
Packages selected results from the 6-stage Zorn Plücker–Hodge, Binet–Cauchy / Lagrange
Volume Repair, BAC–CAB Alternativity Cancellation, and Amari Dual-Isotropic Closure Poset
(`ℨ₁ ≺ ℨ₂ ≺ ℨ₃ ≺ ℨ₄ ≺ ℨ₅ ≺ ℨ₆`):
1. Strict 6-stage causal chain and acyclicity of `ZornPluckerHodgeBinetCauchyAmariStage`.
2. Stages `ℨ₁, ℨ₂` & Rung 0: Naive `2 × 2` block multiplication vs. Zorn cross-product
   multiplication and the orthogonal reflection collapse aporia (`W_x W_y`).
3. Stage `ℨ₃` & Rung 1: Unique dimensional fixed point `Nat.choose D 2 = D ↔ D = 3`
   for `D > 0`.
4. Stage `ℨ₄` & Rung 2: the off-diagonal norm defect, the Binet–Cauchy identity,
   the conditional `α * β = -1` sign lock, and the imported arbitrary-input norm
   multiplicativity theorem for the fixed Zorn product.
5. Stage `ℨ₅` & Rung 3: 3D BAC–CAB vector triple product cancellation and
   equivalence of left alternativity with `α * β = -1`.
6. Stage `ℨ₆` & Rung 4: the stated orientation-conditional parameter uniqueness,
   fourfold product decomposition, and Amari–Chentsov cubic identity. The Stage 6
   twistor Plücker result and the Stage 4/5 sign equivalences remain available in
   their dedicated theorems and are not fields of this master theorem. -/
theorem zorn_plucker_hodge_binet_cauchy_bac_cab_amari_master_poset
    {R : Type*} [Ring R] {K : Type*} [CommRing K]
    (α β : K) (X Y : ZornMatrix R) (A B : ZornAlgebra K)
    (u₁ v₁ u₂ v₂ u₃ : ColorVec3 K) :
    (∀ s : ZornPluckerHodgeBinetCauchyAmariStage,
      ¬ Relation.TransGen ZornPluckerHodgeBinetCauchyAmariStage.causalEdge s s) ∧
    Fintype.card ZornPluckerHodgeBinetCauchyAmariStage = 6 ∧
    (X * Y = naiveZornMatrixMul X Y + zornHodgeCrossMatrix X Y ∧
      naiveZornMatrixMul (ZornMatrix.Wx : ZornMatrix R) ZornMatrix.Wy = 0 ∧
      (ZornMatrix.Wx : ZornMatrix R) * ZornMatrix.Wy = ⟨0, -Vec3.eZ, Vec3.eZ, 0⟩) ∧
    (∀ D : ℕ, 0 < D → (Nat.choose D 2 = D ↔ D = 3)) ∧
    (ZornAlgebra.norm (zornOffDiag u₁ v₁) * ZornAlgebra.norm (zornOffDiag u₂ v₂) -
        ZornAlgebra.norm (zornParamMul α β (zornOffDiag u₁ v₁) (zornOffDiag u₂ v₂)) =
      (1 + α * β) * ColorVec3.dot (ColorVec3.cross u₁ u₂) (ColorVec3.cross v₁ v₂)) ∧
    (ZornAlgebra.associator A A B = ZornAlgebra.zero ∧
      ZornAlgebra.associator B A A = ZornAlgebra.zero) ∧
    (X * Y = zornOrgan1DiagonalCore X Y + zornOrgan2PrimalBimoduleDrift X Y +
        zornOrgan3DualBimoduleDrift X Y + zornOrgan4PluckerHodgeCross X Y ∧
      ZornAlgebra.anticommutator
        (ZornAlgebra.mul (ZornAlgebra.quarkU u₁) (ZornAlgebra.quarkU u₂))
        (ZornAlgebra.quarkU u₃) =
      ZornAlgebra.smul (ColorVec3.dot (ColorVec3.cross u₁ u₂) u₃) ZornAlgebra.one) := by
  have hZ12 :=
    stage_Z1_Z2_peirce_grading_and_orthogonal_reflection_collapse_aporia
      X Y u₁ v₁ u₂ v₂
  have hZ3 := stage_Z3_dimensional_selection_law_for_self_dual_isotropic_wedge
  have hZ4 :=
    stage_Z4_binet_cauchy_lagrange_determinant_repair α β u₁ v₁ u₂ v₂ A B
  have hZ5 :=
    stage_Z5_bac_cab_vector_triple_product_enforces_alternativity α β u₁ v₁ u₂ A B
  have hZ6 :=
    stage_Z6_unique_zorn_table_fourfold_anatomy_twistor_plucker_and_cubic_baryon
      α β X Y A B u₁ u₂ u₃
  exact ⟨ZornPluckerHodgeBinetCauchyAmariStage.causalEdge_acyclic,
    ZornPluckerHodgeBinetCauchyAmariStage.strict_six_stage_chain.2.2.2.2.2,
    ⟨hZ12.1.1, hZ12.2.1.2.2.1, hZ12.2.1.2.2.2⟩,
    hZ3.1,
    hZ4.2.1,
    ⟨hZ5.2.2.1, hZ5.2.2.2.1⟩,
    ⟨hZ6.2.1, hZ6.2.2.2⟩⟩

end InfoGeometry.Canonical.ZornPluckerHodgeBinetCauchyBacCabAmariPoset
