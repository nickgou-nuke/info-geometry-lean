/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon
import InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset
import InfoGeometry.Canonical.SuperGrassmannianParaKahlerInfoGeometryPoset
import Mathlib.Data.Nat.Choose.Basic

/-!
===============================================================================
HIVE CONSTITUTIONAL HEADER
===============================================================================
Module: InfoGeometry.Canonical.ZornPluckerHodgeAmariVolumePoset
Role: Canonical formalization of the 6-Stage Zorn Plücker–Hodge & Amari Dual-
  Isotropic Volume Closure Poset (`ℨ₁ ≺ ℨ₂ ≺ ⋯ ≺ ℨ₆`), resolving why Max Zorn's
  vector-matrices (`ZornMatrix R`, `ZornVectorMatrix R`) possess their exact
  multiplication law from Amari ray isotropy, dimensional self-duality `D = 3`,
  Binet–Cauchy / Lagrange volume repair, and BAC–CAB alternativity cancellation:

1. **Stage `ℨ₁` (`Z1_TwoSheetedPeirceCarrierAndIsotropicAffineSpaces`)**:
   - Reuses `InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon` (`Vec3`,
     `ZornMatrix`, `zornConePlus`, `zornConeMinus`, `zornPhi`) and
     `InfoGeometry.Algebra.ZornVectorMatrix` (`ZornVectorMatrix`, `norm`, `trace`,
     `conj`, `E11`, `E22`, `U`, `V`).
   - Establishes the **Fourfold Relational Anatomy** of Zorn multiplication over
     any associative ring `[Ring R]`:
     (i) Diagonal scalar core (`a₁ a₂ + u₁ · v₂`, `v₁ · u₂ + d₁ d₂`) from the
         Amari cross-metric on the DeWitt vacuum projectors `u₀, u₀*`;
     (ii) Linear off-diagonal bimodule parallel transport (`a₁ u₂ + u₁ d₂`,
          `v₁ a₂ + d₁ v₂`);
     (iii) Lower-left Plücker/diquark Hodge jump `+u₁ × u₂ ∈ 𝔫_-` from
           `zornConePlus u₁ * zornConePlus u₂ = zornConeMinus (u₁ × u₂)`;
     (iv) Upper-right dual-to-primal Hodge return `-v₁ × v₂ ∈ 𝔫_+` from
          `zornConeMinus v₁ * zornConeMinus v₂ = zornConePlus (-(v₁ × v₂))`.

2. **Rung 0 & Stage `ℨ₂` (`Z2_OrthogonalCollapseAporiaOfNaiveBlockMultiplication`)**:
   - Defines the **Naive Associative Block-Matrix Product** `naiveBlockMul X Y`
     obtained by omitting the cross products `-v₁ × v₂` and `+u₁ × u₂`.
   - Proves that on off-diagonal matrices `X = zornPhi u₁ v₁`, `Y = zornPhi u₂ v₂`,
     `naiveBlockMul X Y` has determinant `(u₁ · v₂)(v₁ · u₂)`, missing the true
     product of norms `(u₁ · v₁)(u₂ · v₂)` by the exact Binet–Cauchy `2 × 2` minor
     `(u₁ × u₂) · (v₁ × v₂)`.
   - Proves the **Rung 0 Orthogonal Reflection Collapse Aporia**: for the two
     orthogonal reflections `R₁ = zornPhi e₁ e₁` and `R₂ = zornPhi e₂ e₂`
     (`R₁² = 1`, `R₂² = 1`, `zornNorm R₁ = zornNorm R₂ = -1`), naive multiplication
     collapses to the zero matrix (`naiveBlockMul R₁ R₂ = 0`, `zornNorm = 0`),
     whereas Zorn multiplication yields `R₁ * R₂ = ⟨0, -e₃, e₃, 0⟩` with
     `zornNorm (R₁ * R₂) = +1 = (-1)(-1)`.

3. **Rung 1 & Stage `ℨ₃` (`Z3_DimensionalSelectionLawForSelfDualIsotropicWedge`)**:
   - Proves the **Unique Dimensional Fixed-Point Theorem** for a self-dual
     exterior wedge map `Λ²(K^D) ≅ K^D`:
     $$\binom{D}{2} = D \iff D = 0 \vee D = 3, \qquad D > 0 \wedge \binom{D}{2} = D \iff D = 3.$$
   - Proves that for any `(α, β)`-scaled cross-product bilinear law `paramZornMul α β`,
     every primal ray `zornConePlus u` and dual ray `zornConeMinus v` is square-zero
     (`u × u = 0`), preserving exact Amari ray exponential flatness
     `(1 + N_+(u))(1 - N_+(u)) = 1`.

4. **Rung 2, Rung 3, & Stages `ℨ₄ ≺ ℨ₅` (`Z4_BinetCauchyLagrangeDeterminantRepair`,
   `Z5_BacCabTripleProductCancellationAndAlternativity`)**:
   - For the general `(α, β)`-parameterized multiplication `paramZornMul α β`
     (with `+α(u₁ × u₂)` in `(2,1)` and `+β(v₁ × v₂)` in `(1,2)`), proves:
     - **Lagrange / Binet–Cauchy Defect Formula (`ℨ₄`)**: on the off-diagonal
       sector `X = zornPhi u₁ v₁`, `Y = zornPhi u₂ v₂`,
       $$N(\text{paramZornMul } \alpha \, \beta \, X \, Y) - N(X) N(Y)
         = -(1 + \alpha\beta)\big((u_1 \times u_2) \cdot (v_1 \times v_2)\big).$$
     - **BAC–CAB Alternativity Cancellation (`ℨ₅`)**: proves the 3D vector triple
       product identity `v × (u × u₂) = (v · u₂) u - (u · v) u₂` and shows that the
       `(1,2)` left-alternativity defect of `paramZornMul α β` on
       `X = zornPhi u v` and `Y = zornConePlus u₂` equals
       $$(1 + \alpha\beta)\big(v \times (u \times u₂)\big).$$
     - **Uniqueness of Opposite Signs (`α β = -1`)**: proves that either norm
       multiplicativity or left alternativity of `paramZornMul α β` forces the
       exact opposite-sign lock `α * β = -1`, uniquely selecting the Zorn sign
       convention `(α, β) = (1, -1)` up to orientation rescaling.

5. **Rung 4 & Stage `ℨ₆` (`Z6_UniqueEmergenceOfCompleteZornMultiplicationAndTwistorBridge`)**:
   - Synthesizes the complete Zorn multiplication law, Hurwitz–Zorn norm
     multiplicativity `norm (mul X Y) = norm X * norm Y`, left/right/flexible
     alternativity, and the Plücker twistor / Amplituhedron 4-bracket bridge.
===============================================================================
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornPluckerHodgeAmariVolumePoset

open InfoGeometry.OperatorAlgebra.OntologyRing
open InfoGeometry.Meta
open InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon
open InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix
open InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.Twistor4
open InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset
open InfoGeometry.Canonical.SuperGrassmannianParaKahlerInfoGeometryPoset hiding zornPhi
alias ZornVectorMatrix := InfoGeometry.Algebra.ZornVectorMatrix

/-!
## 1. The 6-Stage Zorn Plücker–Hodge & Amari Dual-Isotropic Volume Poset (`ℨ₁ ≺ ℨ₂ ≺ ⋯ ≺ ℨ₆`)
-/

/-- The 6 causal stages of the **Zorn Plücker–Hodge & Amari Dual-Isotropic Volume
Closure Poset** (`ℨ₁ ≺ ℨ₂ ≺ ℨ₃ ≺ ℨ₄ ≺ ℨ₅ ≺ ℨ₆`). -/
inductive ZornPluckerHodgeAmariStage : Type
  /-- `ℨ₁`: Two-sheeted Peirce carrier `[[a, u], [v, d]]`, fourfold Zorn anatomy, and Bergman norm `ad - u · v`. -/
  | Z1_TwoSheetedPeirceCarrierAndIsotropicAffineSpaces
  /-- `ℨ₂`: Rung 0 orthogonal reflection collapse aporia of naive block multiplication (`naiveBlockMul R₁ R₂ = 0`). -/
  | Z2_OrthogonalCollapseAporiaOfNaiveBlockMultiplication
  /-- `ℨ₃`: Dimensional selection law `D(D - 1)/2 = D ⟺ D = 3` for self-dual isotropic wedge closure `Λ²(𝔫_+) ≅ 𝔫_-`. -/
  | Z3_DimensionalSelectionLawForSelfDualIsotropicWedge
  /-- `ℨ₄`: Binet–Cauchy / Lagrange determinant repair `(u₁·v₂)(v₁·u₂) + (u₁×u₂)·(v₁×v₂) = (u₁·v₁)(u₂·v₂)`. -/
  | Z4_BinetCauchyLagrangeDeterminantRepair
  /-- `ℨ₅`: BAC–CAB vector triple product cancellation `u(v·u₂) - v×(u×u₂) = (u·v)u₂` & opposite-sign lock `α β = -1`. -/
  | Z5_BacCabTripleProductCancellationAndAlternativity
  /-- `ℨ₆`: Unique emergence of the complete Zorn multiplication table, Hurwitz–Zorn norm composition, and twistor bridge. -/
  | Z6_UniqueEmergenceOfCompleteZornMultiplicationAndTwistorBridge
  deriving DecidableEq, Repr, Inhabited

namespace ZornPluckerHodgeAmariStage

/-- Integer rank `0..5` of each stage `ℨ₁..ℨ₆`. -/
def rank : ZornPluckerHodgeAmariStage → ℕ
  | .Z1_TwoSheetedPeirceCarrierAndIsotropicAffineSpaces => 0
  | .Z2_OrthogonalCollapseAporiaOfNaiveBlockMultiplication => 1
  | .Z3_DimensionalSelectionLawForSelfDualIsotropicWedge => 2
  | .Z4_BinetCauchyLagrangeDeterminantRepair => 3
  | .Z5_BacCabTripleProductCancellationAndAlternativity => 4
  | .Z6_UniqueEmergenceOfCompleteZornMultiplicationAndTwistorBridge => 5

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance : LinearOrder ZornPluckerHodgeAmariStage where
  le a b := rank a ≤ rank b
  lt a b := rank a < rank b
  le_refl _ := le_rfl
  le_trans _ _ _ := Nat.le_trans
  lt_iff_le_not_ge a b := @lt_iff_le_not_ge Nat _ (rank a) (rank b)
  le_antisymm _ _ hab hba := rank_injective (Nat.le_antisymm hab hba)
  le_total a b := Nat.le_total (rank a) (rank b)
  toDecidableLE a b := Nat.decLe (rank a) (rank b)
  toDecidableEq := inferInstance
  toDecidableLT a b := Nat.decLt (rank a) (rank b)

instance : Fintype ZornPluckerHodgeAmariStage where
  elems := {
    .Z1_TwoSheetedPeirceCarrierAndIsotropicAffineSpaces,
    .Z2_OrthogonalCollapseAporiaOfNaiveBlockMultiplication,
    .Z3_DimensionalSelectionLawForSelfDualIsotropicWedge,
    .Z4_BinetCauchyLagrangeDeterminantRepair,
    .Z5_BacCabTripleProductCancellationAndAlternativity,
    .Z6_UniqueEmergenceOfCompleteZornMultiplicationAndTwistorBridge
  }
  complete x := by cases x <;> simp

theorem card_eq_six : Fintype.card ZornPluckerHodgeAmariStage = 6 := rfl

/-- Directed covering edges `ℨ_k ≺ ℨ_{k+1}`. -/
def causalEdge (a b : ZornPluckerHodgeAmariStage) : Prop :=
  rank b = rank a + 1

theorem causalEdge_lt {a b : ZornPluckerHodgeAmariStage}
    (h : causalEdge a b) : rank a < rank b := by
  dsimp [causalEdge] at h
  omega

theorem transGen_causalEdge_lt {a b : ZornPluckerHodgeAmariStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_lt hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_lt hbc)

/-- Strict DAG acyclicity of `ℨ₁ ≺ ℨ₂ ≺ ⋯ ≺ ℨ₆`. -/
theorem causalEdge_acyclic (a : ZornPluckerHodgeAmariStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_lt h)

/-- Monotone representation-depth projection across `ℨ₁..ℨ₆`. -/
def toRepDepth : ZornPluckerHodgeAmariStage → RepDepth
  | .Z1_TwoSheetedPeirceCarrierAndIsotropicAffineSpaces => .operator
  | .Z2_OrthogonalCollapseAporiaOfNaiveBlockMultiplication => .operator
  | .Z3_DimensionalSelectionLawForSelfDualIsotropicWedge => .operator
  | .Z4_BinetCauchyLagrangeDeterminantRepair => .transport
  | .Z5_BacCabTripleProductCancellationAndAlternativity => .transport
  | .Z6_UniqueEmergenceOfCompleteZornMultiplicationAndTwistorBridge => .thermo

/-- Monotone ontology meta-level projection across `ℨ₁..ℨ₆`. -/
def toOntologyMetaLevel : ZornPluckerHodgeAmariStage → OntologyMetaLevel
  | .Z1_TwoSheetedPeirceCarrierAndIsotropicAffineSpaces => .M1_ProjectorClabject
  | .Z2_OrthogonalCollapseAporiaOfNaiveBlockMultiplication => .M1_ProjectorClabject
  | .Z3_DimensionalSelectionLawForSelfDualIsotropicWedge => .M2_GrassmannianPowertypeOrbit
  | .Z4_BinetCauchyLagrangeDeterminantRepair => .M2_GrassmannianPowertypeOrbit
  | .Z5_BacCabTripleProductCancellationAndAlternativity => .M3_ErlangenCasimirMetaLaw
  | .Z6_UniqueEmergenceOfCompleteZornMultiplicationAndTwistorBridge => .M3_ErlangenCasimirMetaLaw

theorem toRepDepth_mono {a b : ZornPluckerHodgeAmariStage} (h : a ≤ b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  change rank a ≤ rank b at h
  cases a <;> cases b <;>
    revert h <;>
    unfold toRepDepth RepDepth.toNat <;>
    decide

theorem toOntologyMetaLevel_mono {a b : ZornPluckerHodgeAmariStage} (h : a ≤ b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  change rank a ≤ rank b at h
  cases a <;> cases b <;>
    revert h <;>
    unfold toOntologyMetaLevel OntologyMetaLevel.rank <;>
    decide

end ZornPluckerHodgeAmariStage

/-!
## 2. Stage `ℨ₁`: The Fourfold Relational Anatomy of Zorn Multiplication
-/

section StageZ1_FourfoldZornAnatomy

variable {R : Type*} [Ring R]

/-- Quadratic Bergman / Peirce–Zorn determinant `det_Zorn(X) = a d - u · v` on `ZornMat R`. -/
@[simp] def zornMatNorm (X : ZornMat R) : R :=
  X.a * X.d - Vec3.dot X.u X.v

/-- Pure diagonal Zorn matrix `[[a, 0], [0, d]] = a u₀ + d u₀*`. -/
@[simp] def zornDiag (a d : R) : ZornMat R :=
  ⟨a, 0, 0, d⟩

/-- Standard coordinate basis vectors `e₁, e₂, e₃ ∈ Vec3 R`. -/
@[simp] def vec3E1 : Vec3 R := ⟨1, 0, 0⟩
@[simp] def vec3E2 : Vec3 R := ⟨0, 1, 0⟩
@[simp] def vec3E3 : Vec3 R := ⟨0, 0, 1⟩

/-- **Stage `ℨ₁` (`z1_two_sheeted_peirce_carrier_and_fourfold_zorn_anatomy`)**:
Every term in Zorn's vector-matrix product `X * Y` is uniquely determined by one of the four
relational organs of the DeWitt-split Peirce carrier `[[a, u], [v, d]]`:
1. **Diagonal Core (Amari Cross-Metric)**:
   `zornConePlus u₁ * zornConeMinus v₂ = zornDiag (u₁ · v₂) 0` (Sheet `+` Gramian `Q_+`) and
   `zornConeMinus v₁ * zornConePlus u₂ = zornDiag 0 (v₁ · u₂)` (Sheet `-` Gramian `Q_-`).
2. **Linear Off-Diagonal Terms (Bimodule Parallel Transport)**:
   `zornDiag a₁ d₁ * zornPhi u₂ v₂ = ⟨0, a₁ u₂, d₁ v₂, 0⟩` and
   `zornPhi u₁ v₁ * zornDiag a₂ d₂ = ⟨0, u₁ d₂, v₁ a₂, 0⟩`.
3. **Lower-Left Cross Product (`+u₁ × u₂`, Primal-to-Dual Plücker / Diquark Hodge Jump)**:
   `zornConePlus u₁ * zornConePlus u₂ = zornConeMinus (u₁ × u₂)`.
4. **Upper-Right Cross Product (`-v₁ × v₂`, Dual-to-Primal Hodge Return)**:
   `zornConeMinus v₁ * zornConeMinus v₂ = zornConePlus (-(v₁ × v₂))`.
5. **Fourfold Additive Synthesis**:
   For any `X, Y : ZornMat R`, `X * Y` is the exact sum of the diagonal scalar core, the
   bimodule drift, the lower-left diquark Hodge jump, and the upper-right Hodge return. -/
theorem z1_two_sheeted_peirce_carrier_and_fourfold_zorn_anatomy
    (a₁ d₁ a₂ d₂ : R) (u₁ v₁ u₂ v₂ : Vec3 R) (X Y : ZornMat R) :
    -- 1. Amari Cross-Metric on the DeWitt vacuum sheets:
    zornConePlus u₁ * zornConeMinus v₂ = zornDiag (Vec3.dot u₁ v₂) 0 ∧
    zornConeMinus v₁ * zornConePlus u₂ = zornDiag 0 (Vec3.dot v₁ u₂) ∧
    -- 2. Bimodule parallel transport from diagonal sheets to off-diagonal vectors:
    zornDiag a₁ d₁ * zornPhi u₂ v₂ =
      zornPhi (Vec3.smulLeft a₁ u₂) (Vec3.smulLeft d₁ v₂) ∧
    zornPhi u₁ v₁ * zornDiag a₂ d₂ =
      zornPhi (Vec3.smulRight u₁ d₂) (Vec3.smulRight v₁ a₂) ∧
    -- 3. Lower-left Plücker / diquark Hodge jump (+u₁ × u₂ ∈ 𝔫_-):
    zornConePlus u₁ * zornConePlus u₂ = zornConeMinus (Vec3.cross u₁ u₂) ∧
    -- 4. Upper-right dual-to-primal Hodge return (-v₁ × v₂ ∈ 𝔫_+):
    zornConeMinus v₁ * zornConeMinus v₂ = zornConePlus (-Vec3.cross v₁ v₂) ∧
    -- 5. Complete fourfold additive decomposition of X * Y:
    X * Y =
      zornDiag (X.a * Y.a + Vec3.dot X.u Y.v) (Vec3.dot X.v Y.u + X.d * Y.d) +
      zornPhi (Vec3.smulLeft X.a Y.u + Vec3.smulRight X.u Y.d)
              (Vec3.smulRight X.v Y.a + Vec3.smulLeft X.d Y.v) +
      zornConeMinus (Vec3.cross X.u Y.u) +
      zornConePlus (-Vec3.cross X.v Y.v) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> simp [zornConePlus, zornConeMinus, zornDiag, Vec3.dot, Vec3.cross,
      Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [zornConePlus, zornConeMinus, zornDiag, Vec3.dot, Vec3.cross,
      Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [zornDiag, zornPhi, Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [zornDiag, zornPhi, Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [zornConePlus, zornConeMinus, Vec3.dot, Vec3.cross,
      Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [zornConePlus, zornConeMinus, Vec3.dot, Vec3.cross,
      Vec3.smulLeft, Vec3.smulRight]
  · ext <;>
    · simp only [zornDiag, zornPhi, zornConeMinus, zornConePlus,
        mul_a, mul_u, mul_v, mul_d,
        add_a, add_u, add_v, add_d,
        Vec3.zero_x, Vec3.zero_y, Vec3.zero_z,
        Vec3.add_x, Vec3.add_y, Vec3.add_z,
        Vec3.sub_x, Vec3.sub_y, Vec3.sub_z,
        Vec3.neg_x, Vec3.neg_y, Vec3.neg_z]
      abel

end StageZ1_FourfoldZornAnatomy

/-!
## 3. Rung 0 & Stage `ℨ₂`: Naive Block-Matrix Multiplication & The Orthogonal Reflection Collapse Aporia
-/

section StageZ2_NaiveBlockCollapseAporia

variable {R : Type*} [Ring R]

/-- **The Conscious Thesis `𝐓` (`naiveBlockMul`)**:
Naive `2 × 2` block-matrix multiplication on `ZornMat R`, keeping the diagonal dot products
`u₁ · v₂`, `v₁ · u₂` and linear bimodule drift `a₁ u₂ + u₁ d₂`, `v₁ a₂ + d₁ v₂`, but omitting
the Hodge cross products `-v₁ × v₂` and `+u₁ × u₂` (setting same-sheet products to zero). -/
@[simp] def naiveBlockMul (X Y : ZornMat R) : ZornMat R :=
  ⟨ X.a * Y.a + Vec3.dot X.u Y.v,
    Vec3.smulLeft X.a Y.u + Vec3.smulRight X.u Y.d,
    Vec3.smulRight X.v Y.a + Vec3.smulLeft X.d Y.v,
    Vec3.dot X.v Y.u + X.d * Y.d ⟩

/-- Orthogonal unit reflections `R₁ = [[0, e₁], [e₁, 0]]` and `R₂ = [[0, e₂], [e₂, 0]]`. -/
@[simp] def zornReflectE1 : ZornMat R := zornPhi vec3E1 vec3E1
@[simp] def zornReflectE2 : ZornMat R := zornPhi vec3E2 vec3E2

/-- **Rung 0 & Stage `ℨ₂` (`z2_naive_block_multiplication_aporia_and_orthogonal_reflection_collapse`)**:
1. **Same-Sheet Vanishing & Diagonal-Only Collapse of Naive Multiplication**:
   Under `naiveBlockMul`, two pure off-diagonal matrices `X = zornPhi u₁ v₁` and `Y = zornPhi u₂ v₂`
   multiply to the purely diagonal matrix `zornDiag (u₁ · v₂) (v₁ · u₂)` with determinant
   `zornMatNorm (naiveBlockMul X Y) = (u₁ · v₂) * (v₁ · v₂)`.
2. **Orthogonal Reflection Collapse Aporia**:
   The reflections `R₁ = zornReflectE1` and `R₂ = zornReflectE2` both square to the identity
   (`R₁ * R₁ = 1`, `R₂ * R₂ = 1`, `naiveBlockMul R₁ R₁ = 1`, `naiveBlockMul R₂ R₂ = 1`) and have
   unit negative norm `zornMatNorm R₁ = -1`, `zornMatNorm R₂ = -1`.
   Yet because `e₁ · e₂ = 0`, **naive block multiplication annihilates their product**:
   $$\text{naiveBlockMul } R_1 \, R_2 = 0, \qquad \text{zornMatNorm}(\text{naiveBlockMul } R_1 \, R_2) = 0,$$
   violating norm multiplicativity (`0 ≠ (-1) * (-1)` in any `[Nontrivial R]`).
3. **Zorn Cross-Product Rescue**:
   With Zorn's cross products `-e₁ × e₂ = -e₃` and `+e₁ × e₂ = +e₃`, the product is rescued from
   zero:
   $$R_1 * R_2 = \begin{pmatrix} 0 & -e_3 \\ +e_3 & 0 \end{pmatrix}, \qquad
     \text{zornMatNorm}(R_1 * R_2) = 1 = \text{zornMatNorm}(R_1) \cdot \text{zornMatNorm}(R_2).$$ -/
theorem z2_naive_block_multiplication_aporia_and_orthogonal_reflection_collapse
    [Nontrivial R] (u₁ v₁ u₂ v₂ : Vec3 R) :
    -- 1. Naive product of off-diagonal matrices collapses to the diagonal:
    naiveBlockMul (zornPhi u₁ v₁) (zornPhi u₂ v₂) =
      zornDiag (Vec3.dot u₁ v₂) (Vec3.dot v₁ u₂) ∧
    zornMatNorm (naiveBlockMul (zornPhi u₁ v₁) (zornPhi u₂ v₂)) =
      Vec3.dot u₁ v₂ * Vec3.dot v₁ u₂ ∧
    -- 2. Both R₁ and R₂ are invertible reflections (R_i² = 1, norm = -1):
    (zornReflectE1 : ZornMat R) * zornReflectE1 = 1 ∧
    (zornReflectE2 : ZornMat R) * zornReflectE2 = 1 ∧
    naiveBlockMul (zornReflectE1 : ZornMat R) zornReflectE1 = 1 ∧
    naiveBlockMul (zornReflectE2 : ZornMat R) zornReflectE2 = 1 ∧
    zornMatNorm (zornReflectE1 : ZornMat R) = -1 ∧
    zornMatNorm (zornReflectE2 : ZornMat R) = -1 ∧
    -- 3. Rung 0 Aporia: Naive multiplication collapses R₁ · R₂ to zero!
    naiveBlockMul (zornReflectE1 : ZornMat R) zornReflectE2 = 0 ∧
    zornMatNorm (naiveBlockMul (zornReflectE1 : ZornMat R) zornReflectE2) = 0 ∧
    zornMatNorm (naiveBlockMul (zornReflectE1 : ZornMat R) zornReflectE2) ≠
      zornMatNorm (zornReflectE1 : ZornMat R) * zornMatNorm (zornReflectE2 : ZornMat R) ∧
    -- 4. Zorn cross-product rescue onto the transverse e₃ = e₁ × e₂ plane:
    (zornReflectE1 : ZornMat R) * zornReflectE2 = zornPhi (-vec3E3) vec3E3 ∧
    zornMatNorm ((zornReflectE1 : ZornMat R) * zornReflectE2) = 1 ∧
    zornMatNorm ((zornReflectE1 : ZornMat R) * zornReflectE2) =
      zornMatNorm (zornReflectE1 : ZornMat R) * zornMatNorm (zornReflectE2 : ZornMat R) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> simp [naiveBlockMul, zornPhi, zornDiag, Vec3.smulLeft, Vec3.smulRight]
  · simp [naiveBlockMul, zornPhi, zornMatNorm, Vec3.dot, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [zornReflectE1, zornPhi, vec3E1, Vec3.dot, Vec3.cross,
      Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [zornReflectE2, zornPhi, vec3E2, Vec3.dot, Vec3.cross,
      Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [naiveBlockMul, zornReflectE1, zornPhi, vec3E1, Vec3.dot,
      Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [naiveBlockMul, zornReflectE2, zornPhi, vec3E2, Vec3.dot,
      Vec3.smulLeft, Vec3.smulRight]
  · simp [zornReflectE1, zornPhi, vec3E1, zornMatNorm, Vec3.dot]
  · simp [zornReflectE2, zornPhi, vec3E2, zornMatNorm, Vec3.dot]
  · ext <;> simp [naiveBlockMul, zornReflectE1, zornReflectE2, zornPhi, vec3E1, vec3E2,
      Vec3.dot, Vec3.smulLeft, Vec3.smulRight]
  · simp [naiveBlockMul, zornReflectE1, zornReflectE2, zornPhi, vec3E1, vec3E2,
      zornMatNorm, Vec3.dot, Vec3.smulLeft, Vec3.smulRight]
  · simp [naiveBlockMul, zornReflectE1, zornReflectE2, zornPhi, vec3E1, vec3E2,
      zornMatNorm, Vec3.dot, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [zornReflectE1, zornReflectE2, zornPhi, vec3E1, vec3E2, vec3E3,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · simp [zornReflectE1, zornReflectE2, zornPhi, vec3E1, vec3E2, zornMatNorm,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · simp [zornReflectE1, zornReflectE2, zornPhi, vec3E1, vec3E2, zornMatNorm,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]

end StageZ2_NaiveBlockCollapseAporia

/-!
## 4. Rung 1 & Stage `ℨ₃`: Dimensional Selection Law `D(D - 1)/2 = D ⟺ D = 3` & Amari Ray Isotropy
-/

section StageZ3_DimensionalSelectionAndIsotropy

/-- **`(α, β)`-Parameterized Zorn Vector-Matrix Multiplication (`paramZornMul`)**:
General bilinear multiplication on `ZornMat K` with arbitrary cross-product couplings
`+α (u₁ × u₂)` in the lower-left `(2,1)` slot and `+β (v₁ × v₂)` in the upper-right `(1,2)` slot:
- `paramZornMul 0 0 X Y = naiveBlockMul X Y` (Naive Block Thesis `𝐓`),
- `paramZornMul 1 (-1) X Y = X * Y` (Canonical Zorn Shadow `𝐒`). -/
@[simp] def paramZornMul {R : Type*} [Ring R] (α β : R) (X Y : ZornMat R) : ZornMat R :=
  ⟨ X.a * Y.a + Vec3.dot X.u Y.v,
    Vec3.smulLeft X.a Y.u + Vec3.smulRight X.u Y.d + Vec3.smulLeft β (Vec3.cross X.v Y.v),
    Vec3.smulRight X.v Y.a + Vec3.smulLeft X.d Y.v + Vec3.smulLeft α (Vec3.cross X.u Y.u),
    Vec3.dot X.v Y.u + X.d * Y.d ⟩

/-- **Rung 1 & Stage `ℨ₃` (`z3_dimensional_selection_law_for_self_dual_isotropic_wedge`)**:
1. **Unique Non-Trivial Dimensional Fixed Point (`D = 3`)**:
   For an alternating bilinear map on a `D`-dimensional primal isotropic sheet `𝔫_+ ≅ K^D`
   to land isomorphically in the `D`-dimensional dual isotropic sheet `𝔫_- ≅ (K^D)*`, the
   exterior bivector rank `Nat.choose D 2 = D(D - 1)/2` must equal `D`:
   $$\binom{D}{2} = D \iff D = 0 \vee D = 3, \qquad
     \big(0 < D \wedge \binom{D}{2} = D\big) \iff D = 3,$$
   and hence total matrix dimension `2 + 2 D = 2 + 6 = 8` (`dim 𝕆_s = 8`).
2. **Exact Interpolation of `paramZornMul`**:
   `paramZornMul 0 0 X Y = naiveBlockMul X Y` and `paramZornMul 1 (-1) X Y = X * Y`.
3. **Amari Ray Isotropy (`N_+(u)² = 0`, `N_-(v)² = 0`)**:
   Over any `[CommRing K]`, because `u × u = 0` and `v × v = 0`, every `(α, β)`-parameterized
   product preserves `paramZornMul α β (zornConePlus u) (zornConePlus u) = 0`,
   `paramZornMul α β (zornConeMinus v) (zornConeMinus v) = 0`, and exact unipotent ray flatness
   `(1 + zornConePlus u) * (1 - zornConePlus u) = 1`. -/
theorem z3_dimensional_selection_law_for_self_dual_isotropic_wedge
    {K : Type*} [CommRing K] (D : ℕ) (α β : K) (u v : Vec3 K) (X Y : ZornMat K) :
    -- 1. Dimensional fixed point (D choose 2) = D ⟺ D = 0 ∨ D = 3:
    (Nat.choose D 2 = D ↔ D = 0 ∨ D = 3) ∧
    ((0 < D ∧ Nat.choose D 2 = D) ↔ D = 3) ∧
    (2 + 2 * 3 = 8) ∧
    -- 2. Parameterized Zorn product interpolates Naive (0, 0) and Zorn (1, -1):
    paramZornMul 0 0 X Y = naiveBlockMul X Y ∧
    paramZornMul 1 (-1) X Y = X * Y ∧
    -- 3. Amari ray isotropy and unipotent ray flatness:
    Vec3.cross u u = 0 ∧
    paramZornMul α β (zornConePlus u) (zornConePlus u) = 0 ∧
    paramZornMul α β (zornConeMinus v) (zornConeMinus v) = 0 ∧
    (1 + zornConePlus u) * (1 - zornConePlus u) = 1 ∧
    (1 + zornConeMinus v) * (1 - zornConeMinus v) = 1 := by
  have hChoose : Nat.choose D 2 = D ↔ D = 0 ∨ D = 3 := by
    constructor
    · intro h
      rcases D with _ | _ | _ | _ | n
      · exact Or.inl rfl
      · simp [Nat.choose] at h
      · simp [Nat.choose] at h
      · exact Or.inr rfl
      · simp [Nat.choose] at h
        omega
    · rintro (rfl | rfl) <;> decide
  refine ⟨hChoose, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · rintro ⟨hPos, hEq⟩
      rcases hChoose.mp hEq with rfl | rfl
      · omega
      · rfl
    · rintro rfl
      exact ⟨by decide, by decide⟩
  · ext <;> simp [paramZornMul, naiveBlockMul, Vec3.smulLeft]
  · ext <;>
    · simp only [paramZornMul, mul_a, mul_u,
        mul_v, mul_d, Vec3.smulLeft, Vec3.smulRight,
        Vec3.add_x, Vec3.add_y, Vec3.add_z,
        Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
      try ring
  · ext <;> simp [Vec3.cross] <;> ring
  · ext <;> simp [paramZornMul, zornConePlus, Vec3.dot, Vec3.cross,
      Vec3.smulLeft, Vec3.smulRight] <;> ring
  · ext <;> simp [paramZornMul, zornConeMinus, Vec3.dot, Vec3.cross,
      Vec3.smulLeft, Vec3.smulRight] <;> ring
  · ext <;> simp [zornConePlus, Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight] <;> ring
  · ext <;> simp [zornConeMinus, Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight] <;> ring

end StageZ3_DimensionalSelectionAndIsotropy

/-!
## 5. Rung 2, Rung 3, & Stages `ℨ₄ ≺ ℨ₅`: Binet–Cauchy / Lagrange Volume Repair, BAC–CAB Alternativity Cancellation, & Uniqueness of Opposite Signs (`α β = -1`)
-/

section StageZ4Z5_BinetCauchyLagrangeAndBacCab

variable {K : Type*} [CommRing K]

/-- **Rung 2 & Stage `ℨ₄` (`z4_binet_cauchy_lagrange_determinant_repair`)**:
1. **3D Binet–Cauchy / Lagrange Identity on `Vec3 K`**:
   $$(u_1 \cdot v_1)(u_2 \cdot v_2) - (u_1 \cdot v_2)(v_1 \cdot u_2)
     = (u_1 \times u_2) \cdot (v_1 \times v_2).$$
2. **Exact Off-Diagonal Norm Defect of `paramZornMul α β`**:
   For `X = zornPhi u₁ v₁` and `Y = zornPhi u₂ v₂`, the norm defect of `paramZornMul α β X Y` is
   proportional to `1 + α * β` times the Binet–Cauchy minor:
   $$\text{zornMatNorm}(\text{paramZornMul } \alpha \, \beta \, X \, Y)
     - \text{zornMatNorm}(X) \cdot \text{zornMatNorm}(Y)
     = -(1 + \alpha\beta)\big((u_1 \times u_2) \cdot (v_1 \times v_2)\big).$$
3. **Opposite-Sign Lock (`α * β = -1`) & Global Zorn Volume Multiplicativity**:
   - Whenever `α * β = -1`, `zornMatNorm (paramZornMul α β (zornPhi u₁ v₁) (zornPhi u₂ v₂)) =
     zornMatNorm (zornPhi u₁ v₁) * zornMatNorm (zornPhi u₂ v₂)`.
   - Conversely, if `zornMatNorm (paramZornMul α β X Y) = zornMatNorm X * zornMatNorm Y` holds for the
     orthogonal reflection pair `R₁ = zornReflectE1`, `R₂ = zornReflectE2`, then `α * β = -1`!
   - At canonical Zorn signs `(α, β) = (1, -1)`, `zornMatNorm (X * Y) = zornMatNorm X * zornMatNorm Y`
     holds for **all** `X, Y : ZornMat K` (matching `ZornVectorMatrix.norm_mul`). -/
theorem z4_binet_cauchy_lagrange_determinant_repair
    (α β : K) (u₁ v₁ u₂ v₂ : Vec3 K) (X Y : ZornMat K)
    (XZ YZ : ZornVectorMatrix K) :
    -- 1. 3D Binet–Cauchy / Lagrange identity:
    (Vec3.dot u₁ v₁) * (Vec3.dot u₂ v₂) - (Vec3.dot u₁ v₂) * (Vec3.dot v₁ u₂) =
      Vec3.dot (Vec3.cross u₁ u₂) (Vec3.cross v₁ v₂) ∧
    -- 2. Off-diagonal norm defect of paramZornMul α β:
    zornMatNorm (paramZornMul α β (zornPhi u₁ v₁) (zornPhi u₂ v₂)) -
      zornMatNorm (zornPhi u₁ v₁) * zornMatNorm (zornPhi u₂ v₂) =
      -(1 + α * β) * Vec3.dot (Vec3.cross u₁ u₂) (Vec3.cross v₁ v₂) ∧
    -- 3. Opposite-sign lock α * β = -1 repairs the off-diagonal determinant identically:
    (α * β = -1 →
      zornMatNorm (paramZornMul α β (zornPhi u₁ v₁) (zornPhi u₂ v₂)) =
        zornMatNorm (zornPhi u₁ v₁) * zornMatNorm (zornPhi u₂ v₂)) ∧
    -- 4. Norm multiplicativity on orthogonal reflections R₁, R₂ forces α * β = -1:
    (zornMatNorm (paramZornMul α β (zornReflectE1 : ZornMat K) zornReflectE2) =
      zornMatNorm (zornReflectE1 : ZornMat K) * zornMatNorm (zornReflectE2 : ZornMat K) ↔
      α * β = -1) ∧
    -- 5. Complete Zorn norm multiplicativity on ZornMat K and ZornVectorMatrix K:
    zornMatNorm (X * Y) = zornMatNorm X * zornMatNorm Y ∧
    InfoGeometry.Algebra.ZornVectorMatrix.norm (InfoGeometry.Algebra.ZornVectorMatrix.mul XZ YZ) =
      InfoGeometry.Algebra.ZornVectorMatrix.norm XZ * InfoGeometry.Algebra.ZornVectorMatrix.norm YZ := by
  have hLagrange :
      (Vec3.dot u₁ v₁) * (Vec3.dot u₂ v₂) - (Vec3.dot u₁ v₂) * (Vec3.dot v₁ u₂) =
        Vec3.dot (Vec3.cross u₁ u₂) (Vec3.cross v₁ v₂) := by
    simp only [Vec3.dot, Vec3.cross]
    ring
  have hDefect :
      zornMatNorm (paramZornMul α β (zornPhi u₁ v₁) (zornPhi u₂ v₂)) -
        zornMatNorm (zornPhi u₁ v₁) * zornMatNorm (zornPhi u₂ v₂) =
        -(1 + α * β) * Vec3.dot (Vec3.cross u₁ u₂) (Vec3.cross v₁ v₂) := by
    simp only [zornMatNorm, paramZornMul, zornPhi, Vec3.dot, Vec3.cross,
      Vec3.smulLeft, Vec3.smulRight,
      Vec3.add_x, Vec3.add_y, Vec3.add_z]
    ring
  refine ⟨hLagrange, hDefect, ?_, ?_, ?_, InfoGeometry.Algebra.ZornVectorMatrix.norm_mul XZ YZ⟩
  · intro hαβ
    have h0 : -(1 + α * β) = 0 := by
      rw [hαβ]
      ring
    have hSub := hDefect
    rw [h0, zero_mul] at hSub
    exact sub_eq_zero.mp hSub
  · constructor
    · intro hNorm
      have hEval :
          zornMatNorm (paramZornMul α β (zornReflectE1 : ZornMat K) zornReflectE2) = -(α * β) ∧
          zornMatNorm (zornReflectE1 : ZornMat K) * zornMatNorm (zornReflectE2 : ZornMat K) = 1 := by
        constructor <;>
        · simp only [zornReflectE1, zornReflectE2, zornPhi, vec3E1, vec3E2,
            paramZornMul, zornMatNorm, Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight,
            Vec3.add_x, Vec3.add_y, Vec3.add_z]
          ring
      rw [hEval.1, hEval.2] at hNorm
      linear_combination -hNorm
    · intro hαβ
      simp only [zornReflectE1, zornReflectE2, zornPhi, vec3E1, vec3E2,
        paramZornMul, zornMatNorm, Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight,
        Vec3.add_x, Vec3.add_y, Vec3.add_z]
      linear_combination -hαβ
  · simp only [zornMatNorm, mul_a, mul_u, mul_v, mul_d,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight,
      Vec3.add_x, Vec3.add_y, Vec3.add_z,
      Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
    ring

/-- **Rung 3 & Stage `ℨ₅` (`z5_bac_cab_triple_product_and_alternativity_sign_lock`)**:
1. **3D BAC–CAB Vector Triple Product Identity**:
   $$v \times (u \times u_2) = (v \cdot u_2) u - (u \cdot v) u_2.$$
2. **Parameterized Left-Alternativity Defect Formula**:
   For `X = zornPhi u v` and `Y = zornConePlus u₂`, the `(1,2)` upper-right vector of the
   left-alternativity defect
   `paramZornMul α β X (paramZornMul α β X Y) - paramZornMul α β (paramZornMul α β X X) Y`
   is given by the BAC–CAB vector triple product scaled by `1 + α * β`:
   $$\big(\text{paramZornMul } \alpha \, \beta \, X \, (\text{paramZornMul } \alpha \, \beta \, X \, Y)
     - \text{paramZornMul } \alpha \, \beta \, (\text{paramZornMul } \alpha \, \beta \, X \, X) \, Y\big).u
     = \text{Vec3.smulLeft } (1 + \alpha\beta) \, \big(v \times (u \times u_2)\big).$$
3. **Left Alternativity Uniquely Forces Opposite Cross-Product Signs (`α * β = -1`)**:
   Evaluating at `u = v = e₁` and `u₂ = e₂` (`e₁ × (e₁ × e₂) = -e₂`) proves that left
   alternativity on `(zornReflectE1, zornConePlus e₂)` is equivalent to `α * β = -1`.
4. **Full Left, Right, and Flexible Alternativity of Zorn Multiplication**:
   At `(α, β) = (1, -1)`, `(X * X) * Y = X * (X * Y)`, `(X * Y) * Y = X * (Y * Y)`, and
   `(X * Y) * X = X * (Y * X)` hold for all `X, Y : ZornMat K` (and via
   `ZornVectorMatrix.associator_left_alternative`, `associator_right_alternative`,
   `associator_flexible` on `ZornVectorMatrix K`). -/
theorem z5_bac_cab_triple_product_and_alternativity_sign_lock
    (α β : K) (u v u₂ : Vec3 K) (X Y : ZornMat K)
    (XZ YZ : ZornVectorMatrix K) :
    -- 1. 3D BAC–CAB vector triple product identity:
    Vec3.cross v (Vec3.cross u u₂) =
      Vec3.smulLeft (Vec3.dot v u₂) u - Vec3.smulLeft (Vec3.dot u v) u₂ ∧
    -- 2. BAC–CAB cancellation at canonical opposite signs: u(v·u₂) - v × (u × u₂) = (u·v)u₂:
    Vec3.smulRight u (Vec3.dot v u₂) - Vec3.cross v (Vec3.cross u u₂) =
      Vec3.smulLeft (Vec3.dot u v) u₂ ∧
    -- 3. Parameterized left-alternativity (1,2)-slot defect = (1 + α β) (v × (u × u₂)):
    (paramZornMul α β (zornPhi u v) (paramZornMul α β (zornPhi u v) (zornConePlus u₂)) -
      paramZornMul α β (paramZornMul α β (zornPhi u v) (zornPhi u v)) (zornConePlus u₂)).u =
      Vec3.smulLeft (1 + α * β) (Vec3.cross v (Vec3.cross u u₂)) ∧
    -- 4. Left alternativity on (R₁, N_+(e₂)) ↔ α * β = -1:
    (paramZornMul α β (zornReflectE1 : ZornMat K)
        (paramZornMul α β zornReflectE1 (zornConePlus vec3E2)) =
      paramZornMul α β (paramZornMul α β (zornReflectE1 : ZornMat K) zornReflectE1)
        (zornConePlus vec3E2) ↔
      α * β = -1) ∧
    -- 5. Full left, right, and flexible alternativity at (α, β) = (1, -1):
    (X * X) * Y = X * (X * Y) ∧
    (X * Y) * Y = X * (Y * Y) ∧
    (X * Y) * X = X * (Y * X) ∧
    InfoGeometry.Algebra.ZornVectorMatrix.associator XZ XZ YZ = InfoGeometry.Algebra.ZornVectorMatrix.zero ∧
    InfoGeometry.Algebra.ZornVectorMatrix.associator XZ YZ YZ = InfoGeometry.Algebra.ZornVectorMatrix.zero ∧
    InfoGeometry.Algebra.ZornVectorMatrix.associator XZ YZ XZ = InfoGeometry.Algebra.ZornVectorMatrix.zero := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
    InfoGeometry.Algebra.ZornVectorMatrix.associator_left_alternative XZ YZ,
    InfoGeometry.Algebra.ZornVectorMatrix.associator_right_alternative XZ YZ,
    InfoGeometry.Algebra.ZornVectorMatrix.associator_flexible XZ YZ⟩
  · ext <;>
    · simp only [Vec3.cross, Vec3.dot, Vec3.smulLeft, Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
      ring
  · ext <;>
    · simp only [Vec3.cross, Vec3.dot, Vec3.smulLeft, Vec3.smulRight,
        Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
      ring
  · ext <;>
    · simp only [paramZornMul, zornPhi, zornConePlus,
        sub_u, Vec3.cross, Vec3.dot, Vec3.smulLeft, Vec3.smulRight,
        Vec3.zero_x, Vec3.zero_y, Vec3.zero_z,
        Vec3.add_x, Vec3.add_y, Vec3.add_z,
        Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
      ring
  · constructor
    · intro hAlt
      have hy :
          (paramZornMul α β (zornReflectE1 : ZornMat K)
            (paramZornMul α β zornReflectE1 (zornConePlus vec3E2))).u.y =
          (paramZornMul α β (paramZornMul α β (zornReflectE1 : ZornMat K) zornReflectE1)
            (zornConePlus vec3E2)).u.y := by
        rw [hAlt]
      simp only [paramZornMul, zornReflectE1, zornPhi, zornConePlus, vec3E1, vec3E2,
        Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight,
        Vec3.zero_x, Vec3.zero_y, Vec3.zero_z,
        Vec3.add_x, Vec3.add_y, Vec3.add_z] at hy
      linear_combination -hy
    · intro hαβ
      ext <;>
      · simp only [paramZornMul, zornReflectE1, zornPhi, zornConePlus, vec3E1, vec3E2,
          Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight,
          Vec3.zero_x, Vec3.zero_y, Vec3.zero_z,
          Vec3.add_x, Vec3.add_y, Vec3.add_z]
        first | ring1 | linear_combination -hαβ
  · ext <;>
    · simp only [mul_a, mul_u, mul_v, mul_d,
        Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight,
        Vec3.add_x, Vec3.add_y, Vec3.add_z,
        Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
      ring
  · ext <;>
    · simp only [mul_a, mul_u, mul_v, mul_d,
        Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight,
        Vec3.add_x, Vec3.add_y, Vec3.add_z,
        Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
      ring
  · ext <;>
    · simp only [mul_a, mul_u, mul_v, mul_d,
        Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight,
        Vec3.add_x, Vec3.add_y, Vec3.add_z,
        Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
      ring

/-- Scalar trace `tr_Zorn(X) = a + d` on `ZornMat K`. -/
@[simp] def zornMatTrace (X : ZornMat K) : K :=
  X.a + X.d

/-- Zorn adjugate / octonionic conjugate `X̄ = [[d, -u], [-v, a]]` on `ZornMat K`. -/
@[simp] def zornMatAdj (X : ZornMat K) : ZornMat K :=
  ⟨X.d, -X.u, -X.v, X.a⟩

/-- **Universal Cayley–Hamilton Quadratic Law, Adjugate Inversion, & Moufang Identities
(`zornMat_cayley_hamilton_and_moufang`)**:
For all `X, Y, Z : ZornMat K` over `[CommRing K]`:
1. **Two-Sided Adjugate Inversion**:
   `X * zornMatAdj X = zornSmul (zornMatNorm X) 1` and
   `zornMatAdj X * X = zornSmul (zornMatNorm X) 1`.
2. **Universal Cayley–Hamilton Identity**:
   `X * X - zornSmul (zornMatTrace X) X + zornSmul (zornMatNorm X) 1 = 0`.
3. **Left, Right, and Middle Moufang Identities**:
   - `(X * (Y * X)) * Z = X * (Y * (X * Z))`,
   - `Z * (X * (Y * X)) = ((Z * X) * Y) * X`,
   - `(X * Y) * (Z * X) = X * ((Y * Z) * X)`. -/
theorem zornMat_cayley_hamilton_and_moufang
    (X Y Z : ZornMat K) :
    X * zornMatAdj X = zornSmul (zornMatNorm X) (1 : ZornMat K) ∧
    zornMatAdj X * X = zornSmul (zornMatNorm X) (1 : ZornMat K) ∧
    X * X - zornSmul (zornMatTrace X) X + zornSmul (zornMatNorm X) (1 : ZornMat K) = 0 ∧
    (X * (Y * X)) * Z = X * (Y * (X * Z)) ∧
    Z * (X * (Y * X)) = ((Z * X) * Y) * X ∧
    (X * Y) * (Z * X) = X * ((Y * Z) * X) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;>
    · simp only [zornMatAdj, zornSmul, zornMatNorm, ZornMatrix.smul,
        mul_a, mul_u, mul_v, mul_d, one_a, one_u, one_v, one_d,
        Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight,
        Vec3.zero_x, Vec3.zero_y, Vec3.zero_z,
        Vec3.neg_x, Vec3.neg_y, Vec3.neg_z,
        Vec3.add_x, Vec3.add_y, Vec3.add_z,
        Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
      ring
  · ext <;>
    · simp only [zornMatAdj, zornSmul, zornMatNorm, ZornMatrix.smul,
        mul_a, mul_u, mul_v, mul_d, one_a, one_u, one_v, one_d,
        Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight,
        Vec3.zero_x, Vec3.zero_y, Vec3.zero_z,
        Vec3.neg_x, Vec3.neg_y, Vec3.neg_z,
        Vec3.add_x, Vec3.add_y, Vec3.add_z,
        Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
      ring
  · ext <;>
    · simp only [zornMatTrace, zornMatNorm, zornSmul, ZornMatrix.smul,
        mul_a, mul_u, mul_v, mul_d,
        add_a, add_u, add_v, add_d,
        sub_a, sub_u, sub_v, sub_d,
        one_a, one_u, one_v, one_d,
        zero_a, zero_u, zero_v, zero_d,
        Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight,
        Vec3.zero_x, Vec3.zero_y, Vec3.zero_z,
        Vec3.add_x, Vec3.add_y, Vec3.add_z,
        Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
      ring
  · ext <;>
    · simp only [mul_a, mul_u, mul_v, mul_d,
        Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight,
        Vec3.add_x, Vec3.add_y, Vec3.add_z,
        Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
      ring
  · ext <;>
    · simp only [mul_a, mul_u, mul_v, mul_d,
        Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight,
        Vec3.add_x, Vec3.add_y, Vec3.add_z,
        Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
      ring
  · ext <;>
    · simp only [mul_a, mul_u, mul_v, mul_d,
        Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight,
        Vec3.add_x, Vec3.add_y, Vec3.add_z,
        Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
      ring

end StageZ4Z5_BinetCauchyLagrangeAndBacCab

/-!
## 6. The Transcendent Function: Operator Möbius Dual Translation = Push–Pull Legendre Expectation Map
-/

section OperatorMoebiusPushPullBridge

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.RadonNikodymKahlerParaKahlerBregmanPoset

/-- **The Transcendent Function (`operator_moebius_dual_translation_eq_push_pull_legendre_expectation`)**:
For the dual unipotent translation matrix `G = [[a, b], [c, d]] = [[1, -N_-], [0, 1]]` acting on the
primal chart coordinate `f = N_+(P, A)` in any associative ring `[Ring B]` with idempotent `P² = P`:
1. **Möbius Denominator = Lower-Sheet Bergman Kernel (`a + b f = 1 - Q_-`)**:
   `1 + (-coneMinus P C) * conePlus P A = 1 - qgtMinus P A C`.
2. **Möbius Numerator = Primal Coordinate (`c + d f = N_+`)**:
   `0 + 1 * conePlus P A = conePlus P A`.
3. **Choice-Free `[propext]` Push–Pull Intertwining (`(c + d f) R_- = N_+ R_- = R_+ N_+ = η_-`)**:
   Whenever `R_+` and `R_-` are two-sided resolvents of `1 - Q_+` and `1 - Q_-`
   (`R_+ * (1 - Q_+) = 1` and `(1 - Q_-) * R_- = 1`), the operator Möbius fractional transition
   `(0 + 1 * conePlus P A) * R_-` equals `conePlus P A * R_-`, which equals the Legendre expectation
   coordinate `R_+ * conePlus P A`! -/
theorem operator_moebius_dual_translation_eq_push_pull_legendre_expectation
    {B : Type*} [Ring B] {P : B} (hP : IsIdempotentElem P)
    (A C R_plus R_minus : B)
    (hR_plus : R_plus * (1 - qgtPlus P A C) = 1)
    (hR_minus : (1 - qgtMinus P A C) * R_minus = 1) :
    -- 1. Möbius denominator a + b f equals 1 - Q_-:
    1 + (-coneMinus P C) * conePlus P A = 1 - qgtMinus P A C ∧
    -- 2. Möbius numerator c + d f equals N_+:
    (0 : B) + 1 * conePlus P A = conePlus P A ∧
    -- 3. Polynomial Push–Pull intertwining (1 - Q_+) N_+ = N_+ (1 - Q_-):
    (1 - qgtPlus P A C) * conePlus P A = conePlus P A * (1 - qgtMinus P A C) ∧
    -- 4. Operator Möbius image (c + d f) R_- equals N_+ R_- and equals R_+ N_+:
    ((0 : B) + 1 * conePlus P A) * R_minus = conePlus P A * R_minus ∧
    ((0 : B) + 1 * conePlus P A) * R_minus = R_plus * conePlus P A := by
  have hIntertwine :
      (1 - qgtPlus P A C) * conePlus P A = conePlus P A * (1 - qgtMinus P A C) := by
    have hP_def : P * P = P := hP
    dsimp [qgtPlus, qgtMinus, conePlus, coneMinus]
    noncomm_ring [hP_def]
  refine ⟨?_, by noncomm_ring, hIntertwine, by noncomm_ring, ?_⟩
  · dsimp [qgtMinus]
    noncomm_ring
  · calc
      ((0 : B) + 1 * conePlus P A) * R_minus
          = (1 * conePlus P A) * R_minus := by noncomm_ring
      _ = ((R_plus * (1 - qgtPlus P A C)) * conePlus P A) * R_minus := by rw [hR_plus]
      _ = R_plus * ((1 - qgtPlus P A C) * conePlus P A) * R_minus := by noncomm_ring
      _ = R_plus * (conePlus P A * (1 - qgtMinus P A C)) * R_minus := by rw [hIntertwine]
      _ = R_plus * conePlus P A * ((1 - qgtMinus P A C) * R_minus) := by noncomm_ring
      _ = R_plus * conePlus P A * 1 := by rw [hR_minus]
      _ = R_plus * conePlus P A := by noncomm_ring

end OperatorMoebiusPushPullBridge

/-!
## 6. Rung 4 & Stage `ℨ₆`: Master Synthesis — Plücker Twistor Bridge, Amari Cubic Baryon Volume & Zorn Uniqueness (`ℨ₁ ≺ ⋯ ≺ ℨ₆`)
-/

section StageZ6_MasterSynthesis

/-- **Stage `ℨ₆` (`z6_zorn_plucker_hodge_amari_volume_master_synthesis`)**:
Master theorem unifying the 6-stage **Zorn Plücker–Hodge & Amari Dual-Isotropic Volume Closure
Poset** (`ℨ₁ ≺ ⋯ ≺ ℨ₆`) with the **Split-Octonion Circularly Polarized Isotropic Amari & Nambu
Poset** (`𝔒₁ ≺ ⋯ ≺ 𝔒₇`), the **Supergrassmannian & Para-Kähler Information Geometry Manifold
Poset** (`𝔊₁ ≺ ⋯ ≺ 𝔊₈`), and the **Twistor–Amplituhedron–Zorn–Baryon** Plücker correspondence. -/
theorem z6_zorn_plucker_hodge_amari_volume_master_synthesis
    {R : Type*} [Ring R] [Nontrivial R]
    {K : Type*} [CommRing K]
    (D : ℕ) (α β : K) (u₁ v₁ u₂ v₂ u₃ : Vec3 K) (X Y : ZornMat K)
    (Z0 Z1 Z2 Z3 : Twistor4 K) (z10 z20 z30 : K) :
    let Q1 : Twistor4 K := ⟨z10, u₁.x, u₁.y, u₁.z⟩
    let Q2 : Twistor4 K := ⟨z20, u₂.x, u₂.y, u₂.z⟩
    let Q3 : Twistor4 K := ⟨z30, u₃.x, u₃.y, u₃.z⟩
    -- 1. Poset acyclicity and cardinality of ℨ₁ ≺ ⋯ ≺ ℨ₆:
    (∀ st : ZornPluckerHodgeAmariStage,
      ¬ Relation.TransGen ZornPluckerHodgeAmariStage.causalEdge st st) ∧
    Fintype.card ZornPluckerHodgeAmariStage = 6 ∧
    -- 2. Stage ℨ₂ (Rung 0 Orthogonal Reflection Collapse vs. Zorn Rescue):
    naiveBlockMul (zornReflectE1 : ZornMat R) zornReflectE2 = 0 ∧
    (zornReflectE1 : ZornMat R) * zornReflectE2 = zornPhi (-vec3E3) vec3E3 ∧
    zornMatNorm ((zornReflectE1 : ZornMat R) * zornReflectE2) =
      zornMatNorm (zornReflectE1 : ZornMat R) * zornMatNorm (zornReflectE2 : ZornMat R) ∧
    -- 3. Stage ℨ₃ (Dimensional Selection Law D = 3 & Amari Ray Isotropy):
    ((0 < D ∧ Nat.choose D 2 = D) ↔ D = 3) ∧
    paramZornMul α β (zornConePlus u₁) (zornConePlus u₁) = 0 ∧
    paramZornMul α β (zornConeMinus v₁) (zornConeMinus v₁) = 0 ∧
    -- 4. Stage ℨ₄ (Binet–Cauchy / Lagrange Defect & Multiplicative Volume):
    (Vec3.dot u₁ v₁) * (Vec3.dot u₂ v₂) - (Vec3.dot u₁ v₂) * (Vec3.dot v₁ u₂) =
      Vec3.dot (Vec3.cross u₁ u₂) (Vec3.cross v₁ v₂) ∧
    zornMatNorm (paramZornMul α β (zornPhi u₁ v₁) (zornPhi u₂ v₂)) -
      zornMatNorm (zornPhi u₁ v₁) * zornMatNorm (zornPhi u₂ v₂) =
      -(1 + α * β) * Vec3.dot (Vec3.cross u₁ u₂) (Vec3.cross v₁ v₂) ∧
    zornMatNorm (X * Y) = zornMatNorm X * zornMatNorm Y ∧
    -- 5. Stage ℨ₅ (BAC–CAB Cancellation, Opposite-Sign Lock α β = -1, & Alternativity):
    Vec3.smulRight u₁ (Vec3.dot v₁ u₂) - Vec3.cross v₁ (Vec3.cross u₁ u₂) =
      Vec3.smulLeft (Vec3.dot u₁ v₁) u₂ ∧
    (paramZornMul α β (zornReflectE1 : ZornMat K)
        (paramZornMul α β zornReflectE1 (zornConePlus vec3E2)) =
      paramZornMul α β (paramZornMul α β (zornReflectE1 : ZornMat K) zornReflectE1)
        (zornConePlus vec3E2) ↔
      α * β = -1) ∧
    (X * X) * Y = X * (X * Y) ∧
    (X * Y) * Y = X * (Y * Y) ∧
    -- 6. Stage ℨ₆ (Twistor Plücker Magnetic Coordinate, Amplituhedron 4-Bracket & Baryon Volume):
    zornConeMinus (pluckerV Q1 Q2) = zornConePlus u₁ * zornConePlus u₂ ∧
    Vec3.baryonDet3 (spatialVec Q1) (spatialVec Q2) (spatialVec Q3) =
      Vec3.baryonDet3 u₁ u₂ u₃ ∧
    (zornConePlus u₁ * zornConePlus u₂) * zornConePlus u₃ +
      zornConePlus u₃ * (zornConePlus u₁ * zornConePlus u₂) =
      zornSmul (Vec3.baryonDet3 u₁ u₂ u₃) (1 : ZornMat K) ∧
    zornPlucker Z0 Z1 * zornPlucker Z2 Z3 + zornPlucker Z2 Z3 * zornPlucker Z0 Z1 =
      zornSmul (twistorBracket4 Z0 Z1 Z2 Z3) (1 : ZornMat K) := by
  have hZ2 := z2_naive_block_multiplication_aporia_and_orthogonal_reflection_collapse
    (R := R) vec3E1 vec3E1 vec3E2 vec3E2
  have hZ3 := z3_dimensional_selection_law_for_self_dual_isotropic_wedge D α β u₁ v₁ X Y
  have hZ4 := z4_binet_cauchy_lagrange_determinant_repair α β u₁ v₁ u₂ v₂ X Y
    InfoGeometry.Algebra.ZornVectorMatrix.zero InfoGeometry.Algebra.ZornVectorMatrix.zero
  have hZ5 := z5_bac_cab_triple_product_and_alternativity_sign_lock α β u₁ v₁ u₂ X Y
    InfoGeometry.Algebra.ZornVectorMatrix.zero InfoGeometry.Algebra.ZornVectorMatrix.zero
  have hTw := amplituhedron_4bracket_eq_zorn_plucker_anticommutator_and_baryon
    Z0 Z1 Z2 Z3 z10 z20 z30 0 u₁ u₂ u₃
  refine ⟨ZornPluckerHodgeAmariStage.causalEdge_acyclic,
    ZornPluckerHodgeAmariStage.card_eq_six,
    hZ2.2.2.2.2.2.2.2.2.1,
    hZ2.2.2.2.2.2.2.2.2.2.2.2.1,
    hZ2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    hZ3.2.1,
    hZ3.2.2.2.2.2.2.1,
    hZ3.2.2.2.2.2.2.2.1,
    hZ4.1,
    hZ4.2.1,
    hZ4.2.2.2.2.1,
    hZ5.2.1,
    hZ5.2.2.2.1,
    hZ5.2.2.2.2.1,
    hZ5.2.2.2.2.2.1,
    hTw.2.1,
    rfl,
    ?_,
    hTw.1⟩
  rw [hTw.2.2.2.1, hTw.2.2.1]
  rfl

end StageZ6_MasterSynthesis

end InfoGeometry.Canonical.ZornPluckerHodgeAmariVolumePoset
