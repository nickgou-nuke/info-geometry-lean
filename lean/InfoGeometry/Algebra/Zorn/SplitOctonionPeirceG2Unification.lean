/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Canonical.CanonicalZornNonUnitalNonAssocRing
import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Algebra.ZornDerivationBridge
import InfoGeometry.Algebra.RegularActionAssociator
import InfoGeometry.Algebra.ZornPeirceMixedAssociator
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
import InfoGeometry.Canonical.ZornMatrixVectorCarrierBridge
import InfoGeometry.Algebra.Zorn.SplitOctonionDerivationConjugation
import InfoGeometry.Canonical.SplitOctonionAutomorphism
import InfoGeometry.Canonical.SplitOctonionAutomorphismOperatorBridge
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Lie.CanonicalZornRegularOperators
import InfoGeometry.Lie.SplitOctonionStandardDerivation
import InfoGeometry.Lie.CanonicalZornStandardDerivationCovariance
import InfoGeometry.Lie.RealSplitOctonionG2Classification
import InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal
import InfoGeometry.OperatorAlgebra.SplitOctonionNonmultiplicativity
import InfoGeometry.Algebra.ZornMatrixRealModule
import InfoGeometry.Canonical.SplitOctonionGogberashviliVectorMultiplicationBridge
import InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge
import InfoGeometry.Algebra.Zorn.MatrixCayleyDicksonSeparation

/-!
# Peirce-Zorn-M₈(ℝ)-Associator-G₂(₂) Unification & R5 Non-Multiplicativity

This module unifies the five core components of the real split-octonion
representation on the canonical Zorn carrier `ZornCarrier := InfoGeometry.Canonical.ZornMatrix ℝ`:

1. **Peirce `2×2` Zorn block representation**: idempotent `peirceP = zornPlus`,
   complement `1 - peirceP = zornMinus`, the four Peirce projections (`peirce11`,
   `conePlus`, `coneMinus`, `peirce00`), sandwich bracketing `peirce_bracketing`,
   `zorn_peirce_decomposition`, explicit `2×2` Zorn block multiplication laws,
   and a non-associative associator witness involving `peirceP`.
2. **Full-carrier `M₈(ℝ) ≃ₐ[ℝ] Module.End ℝ ZornCarrier`**: genuine algebra
   equivalences `endToMat8` and `mat8EquivEndZorn` via the Peirce-ordered
   `(1 + 3 + 3 + 1)` coordinate equivalence `SplitOctonionPseudoReal.coordLE`,
   exposing `leftMulEnd`, `rightMulEnd`, `leftMulMat8`, `rightMulMat8` for all
   carrier elements (extending `SplitOctonionPseudoReal` beyond `Imaginary`),
   injectivity, Peirce diagonal projectors in `EndZorn` and `M₈(ℝ)`, and
   explicit matrix non-commutativity witnesses.
3. **Associator defect bridge**: `zornAssociator`, `lrComm`, and `lrCommMat8`,
   proving `[L_x, R_y] z = -zornAssociator x z y` and bridging directly to
   `InfoGeometry.Algebra.RegularActionAssociator` (`[L_x, R_y] z = zornAssociator x y z`
   under right alternativity) plus explicit Peirce-sector associator laws.
4. **`G_{2(2)}` automorphisms and derivations**: `RealSplitOctonionAut` and
   `canonicalZornDerivations` / Baez standard derivations `directCanonicalStanDerMap`
   equivariance for `L_x`, `R_y`, `zornAssociator`, `[L_x, R_y]`, the `peirceP`-stabilizer
   commutation with Peirce blocks, and the 14-dimensional `𝔤₂₍₂₎` Lie algebra span.
5. **R5 non-multiplicativity separation**: bridge from `MatrixCayleyDicksonSeparation`
   (`Mat2C ≃ₗ[ℝ] ZornCarrier`) and full-carrier regular-action defect
   `(L_x ∘ L_y - L_{x*y}) z = -zornAssociator x y z` with concrete Peirce-block and
   `Imaginary` counterexamples.

Note: `InfoGeometry.Canonical.ZornMatrix ℝ` intentionally carries no global
`IsScalarTower ℝ` or `SMulCommClass ℝ` instance (guarded by downstream E2E tests).
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.SplitOctonionPeirceG2Unification

open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.SplitOctonionStandardDerivation
open InfoGeometry.Lie.CanonicalZornStandardDerivationCovariance
open InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal
open InfoGeometry.OperatorAlgebra.SplitOctonionNonmultiplicativity
open InfoGeometry.Algebra.Zorn.MatrixCayleyDicksonSeparation

/-! ## Section 1: Unified Carrier, Cross-Carrier Bridges, and Peirce 2×2 Blocks -/

abbrev ZornCarrier := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev ZornVecCarrier := InfoGeometry.Algebra.ZornVectorMatrix ℝ
abbrev ZornAlgCarrier := InfoGeometry.Algebra.ZornMatrix ℝ
abbrev EndZorn := Module.End ℝ ZornCarrier
abbrev Mat8R := Matrix (Fin 8) (Fin 8) ℝ
abbrev Mat2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-- Linear equivalence from `ZornCarrier` to `InfoGeometry.Algebra.ZornVectorMatrix ℝ`. -/
def carrierToVecEquiv : ZornCarrier ≃ₗ[ℝ] ZornVecCarrier :=
  InfoGeometry.Canonical.zornMatrixVectorLinearEquiv

@[simp] theorem carrierToVecEquiv_apply (x : ZornCarrier) :
    carrierToVecEquiv x = ⟨x.a, x.x, x.y, x.b⟩ := rfl

@[simp] theorem carrierToVecEquiv_symm_apply (x : ZornVecCarrier) :
    carrierToVecEquiv.symm x = ⟨x.a, x.b, x.v, x.w⟩ := rfl

theorem carrierToVecEquiv_mul (x y : ZornCarrier) :
    carrierToVecEquiv (x * y) = carrierToVecEquiv x * carrierToVecEquiv y := by
  exact InfoGeometry.Canonical.zornMatrixToVector_mul x y

theorem carrierToVecEquiv_symm_mul (x y : ZornVecCarrier) :
    carrierToVecEquiv.symm (x * y) =
      carrierToVecEquiv.symm x * carrierToVecEquiv.symm y := by
  apply carrierToVecEquiv.injective
  simp only [LinearEquiv.apply_symm_apply, carrierToVecEquiv_mul]

theorem carrierToVecEquiv_one :
    carrierToVecEquiv (1 : ZornCarrier) = InfoGeometry.Algebra.ZornVectorMatrix.one := rfl

/-- Linear equivalence from `InfoGeometry.Algebra.ZornMatrix ℝ` to `ZornVecCarrier`. -/
def algToVecEquiv : ZornAlgCarrier ≃ₗ[ℝ] ZornVecCarrier where
  toFun := InfoGeometry.Canonical.SplitOctonionGogberashviliVectorMultiplicationBridge.oldToVector
  invFun := InfoGeometry.Canonical.SplitOctonionGogberashviliVectorMultiplicationBridge.vectorToOld
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  map_add' x y :=
    InfoGeometry.Canonical.SplitOctonionGogberashviliVectorMultiplicationBridge.oldToVector_add x y
  map_smul' r x :=
    InfoGeometry.Canonical.SplitOctonionGogberashviliVectorMultiplicationBridge.oldToVector_smul r x

theorem algToVecEquiv_mul (x y : ZornAlgCarrier) :
    algToVecEquiv (x * y) = algToVecEquiv x * algToVecEquiv y :=
  InfoGeometry.Canonical.SplitOctonionGogberashviliVectorMultiplicationBridge.oldToVector_mul x y

theorem algToVecEquiv_I :
    algToVecEquiv InfoGeometry.Algebra.ZornMatrix.I =
      InfoGeometry.Algebra.ZornVectorMatrix.one := by
  apply InfoGeometry.Algebra.ZornVectorMatrix.ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · rfl

/-- Linear and multiplicative equivalence from `InfoGeometry.Algebra.ZornMatrix ℝ`
to `ZornCarrier`. -/
def algToCarrierEquiv : ZornAlgCarrier ≃ₗ[ℝ] ZornCarrier :=
  InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge.paperCanonicalLinearEquiv

theorem algToCarrierEquiv_mul (x y : ZornAlgCarrier) :
    algToCarrierEquiv (x * y) = algToCarrierEquiv x * algToCarrierEquiv y :=
  InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge.paperCanonicalLinearEquiv_mul x y

theorem algToCarrierEquiv_I :
    algToCarrierEquiv InfoGeometry.Algebra.ZornMatrix.I = (1 : ZornCarrier) := by
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · rfl
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

/-- The canonical upper-diagonal Peirce idempotent `P = zornPlus`. -/
def peirceP : ZornCarrier := InfoGeometry.Canonical.ZornMatrix.zornPlus

theorem one_sub_peirceP :
    (1 : ZornCarrier) - peirceP = InfoGeometry.Canonical.ZornMatrix.zornMinus := by
  apply InfoGeometry.Canonical.ZornMatrix.ext <;>
    simp [peirceP, InfoGeometry.Canonical.ZornMatrix.zornPlus,
      InfoGeometry.Canonical.ZornMatrix.zornMinus]

theorem peirceP_idempotent : peirceP * peirceP = peirceP :=
  InfoGeometry.Canonical.ZornMatrix.zornPlus_idempotent

theorem one_sub_peirceP_idempotent :
    ((1 : ZornCarrier) - peirceP) * ((1 : ZornCarrier) - peirceP) = 1 - peirceP := by
  rw [one_sub_peirceP]
  exact InfoGeometry.Canonical.ZornMatrix.zornMinus_idempotent

theorem peirceP_mul_complement :
    peirceP * ((1 : ZornCarrier) - peirceP) = 0 := by
  rw [one_sub_peirceP]
  exact InfoGeometry.Canonical.ZornMatrix.zornPlus_mul_zornMinus

theorem complement_mul_peirceP :
    ((1 : ZornCarrier) - peirceP) * peirceP = 0 := by
  rw [one_sub_peirceP]
  exact InfoGeometry.Canonical.ZornMatrix.zornMinus_mul_zornPlus

/-- `(1,1)` Peirce projection `(P * x) * P`. -/
def peirce11 (P x : ZornCarrier) : ZornCarrier := (P * x) * P

/-- `(1,0)` / upper-chiral Peirce projection `(P * x) * (1 - P)`. -/
def conePlus (P x : ZornCarrier) : ZornCarrier := (P * x) * ((1 : ZornCarrier) - P)

/-- `(0,1)` / lower-chiral Peirce projection `((1 - P) * x) * P`. -/
def coneMinus (P x : ZornCarrier) : ZornCarrier := (((1 : ZornCarrier) - P) * x) * P

/-- `(0,0)` Peirce projection `((1 - P) * x) * (1 - P)`. -/
def peirce00 (P x : ZornCarrier) : ZornCarrier :=
  (((1 : ZornCarrier) - P) * x) * ((1 : ZornCarrier) - P)

theorem peirce11_peirceP_eq_peirceComponent (x : ZornCarrier) :
    peirce11 peirceP x =
      InfoGeometry.Canonical.ZornMatrix.peirceComponent
        InfoGeometry.Canonical.ZornMatrix.zornPlus
        InfoGeometry.Canonical.ZornMatrix.zornPlus x := rfl

theorem conePlus_peirceP_eq_colorProject (x : ZornCarrier) :
    conePlus peirceP x = InfoGeometry.Canonical.ZornMatrix.colorProject x := by
  unfold conePlus
  rw [one_sub_peirceP]
  rfl

theorem coneMinus_peirceP_eq_anticolorProject (x : ZornCarrier) :
    coneMinus peirceP x = InfoGeometry.Canonical.ZornMatrix.anticolorProject x := by
  unfold coneMinus
  rw [one_sub_peirceP]
  rfl

theorem peirce00_peirceP_eq_peirceComponent (x : ZornCarrier) :
    peirce00 peirceP x =
      InfoGeometry.Canonical.ZornMatrix.peirceComponent
        InfoGeometry.Canonical.ZornMatrix.zornMinus
        InfoGeometry.Canonical.ZornMatrix.zornMinus x := by
  unfold peirce00
  rw [one_sub_peirceP]
  rfl

@[simp] theorem peirce11_peirceP_apply (x : ZornCarrier) :
    peirce11 peirceP x = { a := x.a, b := 0, x := 0, y := 0 } := by
  rw [peirce11_peirceP_eq_peirceComponent]
  exact InfoGeometry.Canonical.ZornMatrix.peirce_plus_plus_apply x

@[simp] theorem conePlus_peirceP_apply (x : ZornCarrier) :
    conePlus peirceP x = { a := 0, b := 0, x := x.x, y := 0 } := by
  rw [conePlus_peirceP_eq_colorProject]
  exact InfoGeometry.Canonical.ZornMatrix.colorProject_apply x

@[simp] theorem coneMinus_peirceP_apply (x : ZornCarrier) :
    coneMinus peirceP x = { a := 0, b := 0, x := 0, y := x.y } := by
  rw [coneMinus_peirceP_eq_anticolorProject]
  exact InfoGeometry.Canonical.ZornMatrix.anticolorProject_apply x

@[simp] theorem peirce00_peirceP_apply (x : ZornCarrier) :
    peirce00 peirceP x = { a := 0, b := x.b, x := 0, y := 0 } := by
  rw [peirce00_peirceP_eq_peirceComponent]
  exact InfoGeometry.Canonical.ZornMatrix.peirce_minus_minus_apply x

/-- Left and right sandwich bracketings agree for the diagonal Peirce idempotents
`{peirceP, 1 - peirceP}`. -/
theorem peirce_bracketing
    (i j : InfoGeometry.Canonical.ZornMatrix.ZornSign) (x : ZornCarrier) :
    ((InfoGeometry.Canonical.ZornMatrix.idempotent (R := ℝ) i * x) *
        InfoGeometry.Canonical.ZornMatrix.idempotent (R := ℝ) j) =
      (InfoGeometry.Canonical.ZornMatrix.idempotent (R := ℝ) i *
        (x * InfoGeometry.Canonical.ZornMatrix.idempotent (R := ℝ) j)) :=
  InfoGeometry.Canonical.ZornMatrix.peirce_bracketing i j x

theorem peirce_bracketing_P_corners (x : ZornCarrier) :
    ((peirceP * x) * peirceP = peirceP * (x * peirceP)) ∧
    ((peirceP * x) * (1 - peirceP) = peirceP * (x * (1 - peirceP))) ∧
    (((1 - peirceP) * x) * peirceP = (1 - peirceP) * (x * peirceP)) ∧
    (((1 - peirceP) * x) * (1 - peirceP) = (1 - peirceP) * (x * (1 - peirceP))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact peirce_bracketing .plus .plus x
  · rw [one_sub_peirceP]; exact peirce_bracketing .plus .minus x
  · rw [one_sub_peirceP]; exact peirce_bracketing .minus .plus x
  · rw [one_sub_peirceP]; exact peirce_bracketing .minus .minus x

/-- The four Peirce projections decompose every Zorn cell. -/
theorem zorn_peirce_decomposition (x : ZornCarrier) :
    x = peirce11 peirceP x + conePlus peirceP x +
      coneMinus peirceP x + peirce00 peirceP x := by
  rw [peirce11_peirceP_eq_peirceComponent, conePlus_peirceP_eq_colorProject,
    coneMinus_peirceP_eq_anticolorProject, peirce00_peirceP_eq_peirceComponent]
  exact InfoGeometry.Canonical.ZornMatrix.zorn_peirce_decomposition x

/-- Explicit coordinate-level `2×2` Zorn block multiplication formula. -/
theorem zorn_peirce_block_mul_coords (z₁ z₂ : ZornCarrier) :
    z₁ * z₂ =
      { a := z₁.a * z₂.a + InfoGeometry.Canonical.ZornMatrix.dot z₁.x z₂.y
        b := z₁.b * z₂.b + InfoGeometry.Canonical.ZornMatrix.dot z₁.y z₂.x
        x := z₁.a • z₂.x + z₂.b • z₁.x -
          InfoGeometry.Canonical.ZornMatrix.cross z₁.y z₂.y
        y := z₁.b • z₂.y + z₂.a • z₁.y +
          InfoGeometry.Canonical.ZornMatrix.cross z₁.x z₂.x } := rfl

/-- Peirce `2×2` block multiplication laws showing how `peirce11, conePlus, coneMinus, peirce00`
multiply, including the Zorn cross-product couplings `coneMinus * coneMinus ⊆ conePlus` and
`conePlus * conePlus ⊆ coneMinus`. -/
theorem zorn_peirce_block_mul (z₁ z₂ : ZornCarrier) :
    peirce11 peirceP (z₁ * z₂) =
      peirce11 peirceP z₁ * peirce11 peirceP z₂ +
        conePlus peirceP z₁ * coneMinus peirceP z₂ ∧
    conePlus peirceP (z₁ * z₂) =
      peirce11 peirceP z₁ * conePlus peirceP z₂ +
        conePlus peirceP z₁ * peirce00 peirceP z₂ +
        coneMinus peirceP z₁ * coneMinus peirceP z₂ ∧
    coneMinus peirceP (z₁ * z₂) =
      coneMinus peirceP z₁ * peirce11 peirceP z₂ +
        peirce00 peirceP z₁ * coneMinus peirceP z₂ +
        conePlus peirceP z₁ * conePlus peirceP z₂ ∧
    peirce00 peirceP (z₁ * z₂) =
      coneMinus peirceP z₁ * conePlus peirceP z₂ +
        peirce00 peirceP z₁ * peirce00 peirceP z₂ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply InfoGeometry.Canonical.ZornMatrix.ext
    · simp [peirce11_peirceP_apply, conePlus_peirceP_apply, coneMinus_peirceP_apply,
        InfoGeometry.Canonical.ZornMatrix.mul_def, InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]
    · simp [peirce11_peirceP_apply, conePlus_peirceP_apply, coneMinus_peirceP_apply,
        InfoGeometry.Canonical.ZornMatrix.mul_def, InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]
    · funext i; fin_cases i <;>
        simp [peirce11_peirceP_apply, conePlus_peirceP_apply, coneMinus_peirceP_apply,
          InfoGeometry.Canonical.ZornMatrix.mul_def, InfoGeometry.Canonical.ZornMatrix.mul,
          InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]
    · funext i; fin_cases i <;>
        simp [peirce11_peirceP_apply, conePlus_peirceP_apply, coneMinus_peirceP_apply,
          InfoGeometry.Canonical.ZornMatrix.mul_def, InfoGeometry.Canonical.ZornMatrix.mul,
          InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]
  · apply InfoGeometry.Canonical.ZornMatrix.ext
    · simp [conePlus_peirceP_apply, peirce11_peirceP_apply, peirce00_peirceP_apply,
        coneMinus_peirceP_apply, InfoGeometry.Canonical.ZornMatrix.mul_def,
        InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross]
    · simp [conePlus_peirceP_apply, peirce11_peirceP_apply, peirce00_peirceP_apply,
        coneMinus_peirceP_apply, InfoGeometry.Canonical.ZornMatrix.mul_def,
        InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross]
    · funext i; fin_cases i <;>
        (simp [conePlus_peirceP_apply, peirce11_peirceP_apply, peirce00_peirceP_apply,
          coneMinus_peirceP_apply, InfoGeometry.Canonical.ZornMatrix.mul_def,
          InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
          InfoGeometry.Canonical.ZornMatrix.cross]; ring)
    · funext i; fin_cases i <;>
        simp [conePlus_peirceP_apply, peirce11_peirceP_apply, peirce00_peirceP_apply,
          coneMinus_peirceP_apply, InfoGeometry.Canonical.ZornMatrix.mul_def,
          InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
          InfoGeometry.Canonical.ZornMatrix.cross]
  · apply InfoGeometry.Canonical.ZornMatrix.ext
    · simp [coneMinus_peirceP_apply, peirce11_peirceP_apply, peirce00_peirceP_apply,
        conePlus_peirceP_apply, InfoGeometry.Canonical.ZornMatrix.mul_def,
        InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross]
    · simp [coneMinus_peirceP_apply, peirce11_peirceP_apply, peirce00_peirceP_apply,
        conePlus_peirceP_apply, InfoGeometry.Canonical.ZornMatrix.mul_def,
        InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross]
    · funext i; fin_cases i <;>
        simp [coneMinus_peirceP_apply, peirce11_peirceP_apply, peirce00_peirceP_apply,
          conePlus_peirceP_apply, InfoGeometry.Canonical.ZornMatrix.mul_def,
          InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
          InfoGeometry.Canonical.ZornMatrix.cross]
    · funext i; fin_cases i <;>
        (simp [coneMinus_peirceP_apply, peirce11_peirceP_apply, peirce00_peirceP_apply,
          conePlus_peirceP_apply, InfoGeometry.Canonical.ZornMatrix.mul_def,
          InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
          InfoGeometry.Canonical.ZornMatrix.cross]; ring)
  · rcases z₁ with ⟨a₁, b₁, x₁, y₁⟩; rcases z₂ with ⟨a₂, b₂, x₂, y₂⟩
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · simp [peirce00_peirceP_apply, coneMinus_peirceP_apply, conePlus_peirceP_apply,
        InfoGeometry.Canonical.ZornMatrix.mul_def, InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.dot]
    · simp [peirce00_peirceP_apply, coneMinus_peirceP_apply, conePlus_peirceP_apply,
        InfoGeometry.Canonical.ZornMatrix.mul_def, InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.dot]; ring
    · funext i
      simp [peirce00_peirceP_apply, coneMinus_peirceP_apply, conePlus_peirceP_apply,
        InfoGeometry.Canonical.ZornMatrix.mul_def, InfoGeometry.Canonical.ZornMatrix.mul]
      fin_cases i <;> simp [InfoGeometry.Canonical.ZornMatrix.cross]
    · funext i
      simp [peirce00_peirceP_apply, coneMinus_peirceP_apply, conePlus_peirceP_apply,
        InfoGeometry.Canonical.ZornMatrix.mul_def, InfoGeometry.Canonical.ZornMatrix.mul]
      fin_cases i <;> simp [InfoGeometry.Canonical.ZornMatrix.cross]

/-- Non-associative contrast witness involving the Peirce projector `peirceP`:
while sandwiching with `{peirceP, 1 - peirceP}` commutes (`peirce_bracketing`),
associativity fails on `(peirceP, chiralUpperBasis 0, chiralUpperBasis 1)`. -/
theorem associator_peirceP_upper_witness :
    (peirceP * InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0) *
        InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1 -
      peirceP * (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0 *
        InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1) =
      InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis (R := ℝ) 2 ∧
    (peirceP * InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0) *
        InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1 ≠
      peirceP * (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0 *
        InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1) := by
  have heq :
      (peirceP * InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0) *
          InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1 -
        peirceP * (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0 *
          InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1) =
        InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis (R := ℝ) 2 := by
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · simp [peirceP, InfoGeometry.Canonical.ZornMatrix.zornPlus,
        InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis,
        InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis,
        InfoGeometry.Canonical.ZornMatrix.mul_def, InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]
    · simp [peirceP, InfoGeometry.Canonical.ZornMatrix.zornPlus,
        InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis,
        InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis,
        InfoGeometry.Canonical.ZornMatrix.mul_def, InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]
    · funext i; fin_cases i <;>
        simp [peirceP, InfoGeometry.Canonical.ZornMatrix.zornPlus,
          InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis,
          InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis,
          InfoGeometry.Canonical.ZornMatrix.mul_def, InfoGeometry.Canonical.ZornMatrix.mul,
          InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]
    · funext i; fin_cases i <;>
        simp [peirceP, InfoGeometry.Canonical.ZornMatrix.zornPlus,
          InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis,
          InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis,
          InfoGeometry.Canonical.ZornMatrix.mul_def, InfoGeometry.Canonical.ZornMatrix.mul,
          InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]
  refine ⟨heq, ?_⟩
  intro hne
  have h0 : (InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis (R := ℝ) 2).y 2 = 0 := by
    rw [← heq, sub_eq_zero.mpr hne]
    rfl
  simp [InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis] at h0

/-! ## Section 2: Full-Carrier `M₈(ℝ) ≃ₐ[ℝ] Module.End ℝ ZornCarrier` & Peirce Matrix Blocks -/

/-- Algebra equivalence `Module.End ℝ ZornCarrier ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ`
in the Peirce-ordered `(1 + 3 + 3 + 1)` basis `(a, x₀, x₁, x₂, y₀, y₁, y₂, b)`. -/
def endToMat8 : EndZorn ≃ₐ[ℝ] Mat8R :=
  (coordLE.conjAlgEquiv ℝ).trans LinearMap.toMatrixAlgEquiv'

/-- Algebra equivalence `Matrix (Fin 8) (Fin 8) ℝ ≃ₐ[ℝ] Module.End ℝ ZornCarrier`. -/
def mat8EquivEndZorn : Mat8R ≃ₐ[ℝ] EndZorn :=
  endToMat8.symm

theorem endToMat8_symm : endToMat8.symm = mat8EquivEndZorn := rfl
@[simp] theorem mat8EquivEndZorn_symm : mat8EquivEndZorn.symm = endToMat8 := rfl

theorem endToMat8_mulVec (T : EndZorn) (z : ZornCarrier) :
    Matrix.mulVec (endToMat8 T) (coordLE z) = coordLE (T z) := by
  change Matrix.mulVec (LinearMap.toMatrix' (coordLE.toLinearMap ∘ₗ T ∘ₗ coordLE.symm.toLinearMap))
      (coordLE z) = coordLE (T z)
  rw [LinearMap.toMatrix'_mulVec]
  simp

theorem mat8EquivEndZorn_apply (M : Mat8R) (z : ZornCarrier) :
    coordLE (mat8EquivEndZorn M z) = Matrix.mulVec M (coordLE z) := by
  have h := endToMat8_mulVec (mat8EquivEndZorn M) z
  simpa only [mat8EquivEndZorn, AlgEquiv.apply_symm_apply] using h.symm

/-- Full-carrier left multiplication endomorphism `L_x` for any `x : ZornCarrier`. -/
def leftMulEnd (x : ZornCarrier) : EndZorn :=
  leftMultiplication x

/-- Full-carrier right multiplication endomorphism `R_y` for any `y : ZornCarrier`. -/
def rightMulEnd (y : ZornCarrier) : EndZorn :=
  rightMultiplication y

/-- Full-carrier `8 × 8` matrix representation of left multiplication `L_x`. -/
def leftMulMat8 (x : ZornCarrier) : Mat8R :=
  endToMat8 (leftMulEnd x)

/-- Full-carrier `8 × 8` matrix representation of right multiplication `R_y`. -/
def rightMulMat8 (y : ZornCarrier) : Mat8R :=
  endToMat8 (rightMulEnd y)

@[simp] theorem leftMulEnd_apply (x z : ZornCarrier) : leftMulEnd x z = x * z := rfl
@[simp] theorem rightMulEnd_apply (y z : ZornCarrier) : rightMulEnd y z = z * y := rfl

theorem leftMulMat8_mulVec (x z : ZornCarrier) :
    Matrix.mulVec (leftMulMat8 x) (coordLE z) = coordLE (x * z) := by
  exact endToMat8_mulVec (leftMulEnd x) z

theorem rightMulMat8_mulVec (y z : ZornCarrier) :
    Matrix.mulVec (rightMulMat8 y) (coordLE z) = coordLE (z * y) := by
  exact endToMat8_mulVec (rightMulEnd y) z

theorem leftMulEnd_imaginary
    (X : InfoGeometry.Lie.SplitOctonionImaginaryAction.Imaginary) :
    leftMulEnd X.1 = InfoGeometry.Lie.SplitOctonionImaginaryAction.imaginaryLeftMul X := by
  apply LinearMap.ext
  intro z
  rfl

/-- Compatibility with `SplitOctonionPseudoReal.leftMulMatrix` on the `Imaginary` subspace. -/
theorem leftMulMat8_imaginary
    (X : InfoGeometry.Lie.SplitOctonionImaginaryAction.Imaginary) :
    leftMulMat8 X.1 = leftMulMatrix X := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  rw [toLin_leftMulMatrix]
  change Matrix.toLin' (LinearMap.toMatrix' (coordLE.toLinearMap ∘ₗ leftMulEnd X.1 ∘ₗ
      coordLE.symm.toLinearMap)) v = leftMulLinear X v
  rw [Matrix.toLin'_toMatrix', leftMulEnd_imaginary]
  rfl

theorem leftMulEnd_injective : Function.Injective leftMulEnd :=
  leftRegularRepresentation_injective

theorem rightMulEnd_injective : Function.Injective rightMulEnd := by
  intro x y h
  have h1 := congrArg (fun T : EndZorn => T 1) h
  change (1 : ZornCarrier) * x = (1 : ZornCarrier) * y at h1
  rwa [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.one_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.one_mul] at h1

theorem leftMulMat8_injective : Function.Injective leftMulMat8 :=
  endToMat8.injective.comp leftMulEnd_injective

theorem rightMulMat8_injective : Function.Injective rightMulMat8 :=
  endToMat8.injective.comp rightMulEnd_injective

/-- Linear map `x ↦ leftMulMat8 x` on the full carrier. -/
def leftMulMat8Linear : ZornCarrier →ₗ[ℝ] Mat8R :=
  endToMat8.toLinearMap.comp leftRegularRepresentation

/-- Linear map `y ↦ rightMulMat8 y` on the full carrier. -/
def rightMulMat8Linear : ZornCarrier →ₗ[ℝ] Mat8R where
  toFun := rightMulMat8
  map_add' x y := by
    have h : rightMulEnd (x + y) = rightMulEnd x + rightMulEnd y := by
      apply LinearMap.ext; intro z
      exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_add z x y
    simp only [rightMulMat8, h, map_add]
  map_smul' r x := by
    have h : rightMulEnd (r • x) = r • rightMulEnd x := by
      apply LinearMap.ext; intro z
      exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_smul r z x
    simp only [rightMulMat8, h, map_smul, RingHom.id_apply]

/-- Peirce `(1,1)` projection as an endomorphism in `Module.End ℝ ZornCarrier`. -/
def peirce11End : EndZorn := rightMulEnd peirceP * leftMulEnd peirceP

/-- Peirce `(1,0)` projection as an endomorphism in `Module.End ℝ ZornCarrier`. -/
def conePlusEnd : EndZorn := rightMulEnd (1 - peirceP) * leftMulEnd peirceP

/-- Peirce `(0,1)` projection as an endomorphism in `Module.End ℝ ZornCarrier`. -/
def coneMinusEnd : EndZorn := rightMulEnd peirceP * leftMulEnd (1 - peirceP)

/-- Peirce `(0,0)` projection as an endomorphism in `Module.End ℝ ZornCarrier`. -/
def peirce00End : EndZorn := rightMulEnd (1 - peirceP) * leftMulEnd (1 - peirceP)

@[simp] theorem peirce11End_apply (x : ZornCarrier) :
    peirce11End x = peirce11 peirceP x := rfl

@[simp] theorem conePlusEnd_apply (x : ZornCarrier) :
    conePlusEnd x = conePlus peirceP x := rfl

@[simp] theorem coneMinusEnd_apply (x : ZornCarrier) :
    coneMinusEnd x = coneMinus peirceP x := rfl

@[simp] theorem peirce00End_apply (x : ZornCarrier) :
    peirce00End x = peirce00 peirceP x := rfl

theorem peirce_ends_sum_one :
    peirce11End + conePlusEnd + coneMinusEnd + peirce00End = (1 : EndZorn) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.add_apply, peirce11End_apply, conePlusEnd_apply,
    coneMinusEnd_apply, peirce00End_apply, Module.End.one_apply]
  exact (zorn_peirce_decomposition x).symm

theorem peirce_ends_idempotent :
    peirce11End * peirce11End = peirce11End ∧
    conePlusEnd * conePlusEnd = conePlusEnd ∧
    coneMinusEnd * coneMinusEnd = coneMinusEnd ∧
    peirce00End * peirce00End = peirce00End := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply LinearMap.ext; intro x
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · simp
    · simp
    · funext i; fin_cases i <;> simp
    · funext i; fin_cases i <;> simp
  · apply LinearMap.ext; intro x
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · simp
    · simp
    · funext i; fin_cases i <;> simp
    · funext i; fin_cases i <;> simp
  · apply LinearMap.ext; intro x
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · simp
    · simp
    · funext i; fin_cases i <;> simp
    · funext i; fin_cases i <;> simp
  · apply LinearMap.ext; intro x
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · simp
    · simp
    · funext i; fin_cases i <;> simp
    · funext i; fin_cases i <;> simp

theorem endToMat8_peirce11End :
    endToMat8 peirce11End = Matrix.diagonal ![1, 0, 0, 0, 0, 0, 0, 0] := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  ext i
  have hv := endToMat8_mulVec peirce11End (coordLE.symm v)
  simp only [coordLE.apply_symm_apply] at hv
  rw [Matrix.toLin'_apply, hv]
  fin_cases i <;>
    simp [coordLE, peirce11End_apply, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

theorem endToMat8_conePlusEnd :
    endToMat8 conePlusEnd = Matrix.diagonal ![0, 1, 1, 1, 0, 0, 0, 0] := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  ext i
  have hv := endToMat8_mulVec conePlusEnd (coordLE.symm v)
  simp only [coordLE.apply_symm_apply] at hv
  rw [Matrix.toLin'_apply, hv]
  fin_cases i <;>
    simp [coordLE, conePlusEnd_apply, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

theorem endToMat8_coneMinusEnd :
    endToMat8 coneMinusEnd = Matrix.diagonal ![0, 0, 0, 0, 1, 1, 1, 0] := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  ext i
  have hv := endToMat8_mulVec coneMinusEnd (coordLE.symm v)
  simp only [coordLE.apply_symm_apply] at hv
  rw [Matrix.toLin'_apply, hv]
  fin_cases i <;>
    simp [coordLE, coneMinusEnd_apply, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

theorem endToMat8_peirce00End :
    endToMat8 peirce00End = Matrix.diagonal ![0, 0, 0, 0, 0, 0, 0, 1] := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  ext i
  have hv := endToMat8_mulVec peirce00End (coordLE.symm v)
  simp only [coordLE.apply_symm_apply] at hv
  rw [Matrix.toLin'_apply, hv]
  fin_cases i <;>
    simp [coordLE, peirce00End_apply, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

/-- Explicit non-commutativity witness for `Matrix (Fin 8) (Fin 8) ℝ`. -/
theorem mat8_noncommutative :
    ∃ A B : Matrix (Fin 8) (Fin 8) ℝ, A * B ≠ B * A := by
  refine ⟨Matrix.of (fun i j : Fin 8 => if i = 0 ∧ j = 1 then (1 : ℝ) else 0),
    Matrix.of (fun i j : Fin 8 => if i = 1 ∧ j = 0 then (1 : ℝ) else 0), ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M 0 0) h
  simp [Matrix.mul_apply] at h00

/-- Explicit non-commutativity witness for `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem mat2C_noncommutative :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A := by
  refine ⟨!![(0 : ℂ), 1; 0, 0], !![(0 : ℂ), 0; 1, 0], ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

/-! ## Section 3: Associator Defect Bridge (`RegularActionAssociator`) -/

/-- Explicit non-associative associator on `ZornCarrier`. -/
def zornAssociator (x y z : ZornCarrier) : ZornCarrier :=
  (x * y) * z - x * (y * z)

theorem zornAssociator_eq_root (x y z : ZornCarrier) :
    zornAssociator x y z = _root_.associator x y z := rfl

/-- Regular-action commutator `[L_x, R_y] = L_x ∘ R_y - R_y ∘ L_x` in `EndZorn`. -/
def lrComm (x y : ZornCarrier) : EndZorn :=
  leftMulEnd x * rightMulEnd y - rightMulEnd y * leftMulEnd x

/-- Regular-action commutator `[L_x, R_y]` in `Matrix (Fin 8) (Fin 8) ℝ`. -/
def lrCommMat8 (x y : ZornCarrier) : Mat8R :=
  leftMulMat8 x * rightMulMat8 y - rightMulMat8 y * leftMulMat8 x

theorem endToMat8_lrComm (x y : ZornCarrier) :
    endToMat8 (lrComm x y) = lrCommMat8 x y := by
  simp [lrComm, lrCommMat8, leftMulMat8, rightMulMat8, map_sub, map_mul]

/-- Universal non-associative defect law: `[L_x, R_y] z = -(x, z, y)`. -/
theorem lrComm_apply_eq_neg_associator (x y z : ZornCarrier) :
    lrComm x y z = -zornAssociator x z y := by
  simp only [lrComm, LinearMap.sub_apply, Module.End.mul_apply,
    leftMulEnd_apply, rightMulEnd_apply, zornAssociator]
  abel

theorem mat8EquivEndZorn_lrCommMat8_apply (x y z : ZornCarrier) :
    mat8EquivEndZorn (lrCommMat8 x y) z = -zornAssociator x z y := by
  rw [← endToMat8_lrComm]
  change (endToMat8.symm (endToMat8 (lrComm x y))) z = -zornAssociator x z y
  rw [AlgEquiv.symm_apply_apply]
  exact lrComm_apply_eq_neg_associator x y z

theorem carrierToVecEquiv_zornAssociator (x y z : ZornCarrier) :
    carrierToVecEquiv (zornAssociator x y z) =
      _root_.associator (carrierToVecEquiv x) (carrierToVecEquiv y) (carrierToVecEquiv z) := by
  simp only [zornAssociator, _root_.associator, map_sub, carrierToVecEquiv_mul]

theorem carrierToVecEquiv_lrComm_apply (x y z : ZornCarrier) :
    carrierToVecEquiv (lrComm x y z) =
      InfoGeometry.Algebra.leftRightCommutator (R := ℝ)
        (carrierToVecEquiv x) (carrierToVecEquiv y) (carrierToVecEquiv z) := by
  rw [lrComm_apply_eq_neg_associator, InfoGeometry.Algebra.leftRightCommutator_apply,
    map_neg, carrierToVecEquiv_zornAssociator]

/-- Direct bridge to `InfoGeometry.Algebra.RegularActionAssociator.leftRightCommutator`
without installing global `IsScalarTower`/`SMulCommClass` instances on `ZornCarrier`. -/
theorem lrComm_eq_transported_regularAction (x y : ZornCarrier) :
    lrComm x y =
      carrierToVecEquiv.symm.toLinearMap ∘ₗ
        InfoGeometry.Algebra.leftRightCommutator (R := ℝ)
          (carrierToVecEquiv x) (carrierToVecEquiv y) ∘ₗ
        carrierToVecEquiv.toLinearMap := by
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [← carrierToVecEquiv_lrComm_apply, LinearEquiv.symm_apply_apply]

/-- By split-octonion right alternativity (transported from `RegularActionAssociator`),
`[L_x, R_y] z = zornAssociator x y z`. -/
theorem lrComm_apply_eq_associator (x y z : ZornCarrier) :
    lrComm x y z = zornAssociator x y z := by
  apply carrierToVecEquiv.injective
  rw [carrierToVecEquiv_lrComm_apply, carrierToVecEquiv_zornAssociator]
  exact InfoGeometry.Algebra.ZornVectorMatrix.zorn_leftRightCommutator_apply
    (carrierToVecEquiv x) (carrierToVecEquiv y) (carrierToVecEquiv z)

theorem mat8EquivEndZorn_lrCommMat8_apply_eq_associator (x y z : ZornCarrier) :
    mat8EquivEndZorn (lrCommMat8 x y) z = zornAssociator x y z := by
  rw [← endToMat8_lrComm]
  change (endToMat8.symm (endToMat8 (lrComm x y))) z = zornAssociator x y z
  rw [AlgEquiv.symm_apply_apply]
  exact lrComm_apply_eq_associator x y z

theorem lrComm_swap (x y : ZornCarrier) :
    lrComm y x = -lrComm x y := by
  apply LinearMap.ext
  intro z
  apply carrierToVecEquiv.injective
  rw [LinearMap.neg_apply, map_neg, carrierToVecEquiv_lrComm_apply,
    carrierToVecEquiv_lrComm_apply]
  have h := congrArg (fun f => f (carrierToVecEquiv z))
    (InfoGeometry.Algebra.ZornVectorMatrix.zorn_leftRightCommutator_swap
      (carrierToVecEquiv x) (carrierToVecEquiv y))
  simpa using h

theorem lrCommMat8_swap (x y : ZornCarrier) :
    lrCommMat8 y x = -lrCommMat8 x y := by
  rw [← endToMat8_lrComm, ← endToMat8_lrComm, lrComm_swap, map_neg]

theorem lrComm_self (x : ZornCarrier) :
    lrComm x x = 0 := by
  apply LinearMap.ext
  intro z
  apply carrierToVecEquiv.injective
  rw [LinearMap.zero_apply, map_zero, carrierToVecEquiv_lrComm_apply]
  have h := congrArg (fun f => f (carrierToVecEquiv z))
    (InfoGeometry.Algebra.ZornVectorMatrix.zorn_leftRightCommutator_self
      (carrierToVecEquiv x))
  simpa using h

theorem lrCommMat8_self (x : ZornCarrier) :
    lrCommMat8 x x = 0 := by
  rw [← endToMat8_lrComm, lrComm_self, map_zero]

/-- Explicit Peirce-block associator formula on three upper chiral vectors, transported
from `InfoGeometry.Algebra.ZornPeirceMixedAssociator`. -/
theorem lrComm_upper_upper_upper (u v w : Fin 3 → ℝ) :
    lrComm { a := 0, b := 0, x := u, y := 0 } { a := 0, b := 0, x := v, y := 0 }
        { a := 0, b := 0, x := w, y := 0 } =
      { a := -InfoGeometry.Canonical.ZornMatrix.dot (InfoGeometry.Canonical.ZornMatrix.cross u v) w
        b := InfoGeometry.Canonical.ZornMatrix.dot (InfoGeometry.Canonical.ZornMatrix.cross u v) w
        x := 0
        y := 0 } := by
  rw [lrComm_apply_eq_associator]
  apply carrierToVecEquiv.injective
  rw [carrierToVecEquiv_zornAssociator]
  have h := InfoGeometry.Algebra.ZornVectorMatrix.associator_upper_upper_upper (R := ℝ) u v w
  have hL :
      _root_.associator (carrierToVecEquiv { a := 0, b := 0, x := u, y := 0 })
          (carrierToVecEquiv { a := 0, b := 0, x := v, y := 0 })
          (carrierToVecEquiv { a := 0, b := 0, x := w, y := 0 }) =
        InfoGeometry.Algebra.ZornVectorMatrix.associator
          (InfoGeometry.Algebra.ZornVectorMatrix.offDiagonal u 0)
          (InfoGeometry.Algebra.ZornVectorMatrix.offDiagonal v 0)
          (InfoGeometry.Algebra.ZornVectorMatrix.offDiagonal w 0) := rfl
  rw [hL, h]
  apply InfoGeometry.Algebra.ZornVectorMatrix.ext
  · simp [InfoGeometry.Algebra.ZornVectorMatrix.diagonal,
      InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross,
      InfoGeometry.Algebra.ZornVec3.dot, InfoGeometry.Algebra.ZornVec3.cross,
      Fin.sum_univ_three]
  · funext i; rfl
  · funext i; rfl
  · simp [InfoGeometry.Algebra.ZornVectorMatrix.diagonal,
      InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross,
      InfoGeometry.Algebra.ZornVec3.dot, InfoGeometry.Algebra.ZornVec3.cross,
      Fin.sum_univ_three]

/-- Explicit mixed Peirce-block associator formula on two upper and one lower vector. -/
theorem lrComm_upper_upper_lower (u v w : Fin 3 → ℝ) :
    lrComm { a := 0, b := 0, x := u, y := 0 } { a := 0, b := 0, x := v, y := 0 }
        { a := 0, b := 0, x := 0, y := w } =
      { a := 0
        b := 0
        x := fun i => InfoGeometry.Canonical.ZornMatrix.dot v w * u i -
          InfoGeometry.Canonical.ZornMatrix.dot u w * v i
        y := 0 } := by
  rw [lrComm_apply_eq_associator]
  apply carrierToVecEquiv.injective
  rw [carrierToVecEquiv_zornAssociator]
  have h := InfoGeometry.Algebra.ZornVectorMatrix.associator_upper_upper_lower (R := ℝ) u v w
  have hL :
      _root_.associator (carrierToVecEquiv { a := 0, b := 0, x := u, y := 0 })
          (carrierToVecEquiv { a := 0, b := 0, x := v, y := 0 })
          (carrierToVecEquiv { a := 0, b := 0, x := 0, y := w }) =
        InfoGeometry.Algebra.ZornVectorMatrix.associator
          (InfoGeometry.Algebra.ZornVectorMatrix.offDiagonal u 0)
          (InfoGeometry.Algebra.ZornVectorMatrix.offDiagonal v 0)
          (InfoGeometry.Algebra.ZornVectorMatrix.offDiagonal 0 w) := rfl
  rw [hL, h]
  apply InfoGeometry.Algebra.ZornVectorMatrix.ext
  · rfl
  · funext i
    simp [InfoGeometry.Algebra.ZornVectorMatrix.offDiagonal,
      InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Algebra.ZornVec3.dot,
      Fin.sum_univ_three]
  · funext i; rfl
  · rfl

/-- Explicit mixed Peirce-block associator formula on one upper and two lower vectors. -/
theorem lrComm_upper_lower_lower (u v w : Fin 3 → ℝ) :
    lrComm { a := 0, b := 0, x := u, y := 0 } { a := 0, b := 0, x := 0, y := v }
        { a := 0, b := 0, x := 0, y := w } =
      { a := 0
        b := 0
        x := 0
        y := fun i => InfoGeometry.Canonical.ZornMatrix.dot u w * v i -
          InfoGeometry.Canonical.ZornMatrix.dot u v * w i } := by
  rw [lrComm_apply_eq_associator]
  apply carrierToVecEquiv.injective
  rw [carrierToVecEquiv_zornAssociator]
  have h := InfoGeometry.Algebra.ZornVectorMatrix.associator_upper_lower_lower (R := ℝ) u v w
  have hL :
      _root_.associator (carrierToVecEquiv { a := 0, b := 0, x := u, y := 0 })
          (carrierToVecEquiv { a := 0, b := 0, x := 0, y := v })
          (carrierToVecEquiv { a := 0, b := 0, x := 0, y := w }) =
        InfoGeometry.Algebra.ZornVectorMatrix.associator
          (InfoGeometry.Algebra.ZornVectorMatrix.offDiagonal u 0)
          (InfoGeometry.Algebra.ZornVectorMatrix.offDiagonal 0 v)
          (InfoGeometry.Algebra.ZornVectorMatrix.offDiagonal 0 w) := rfl
  rw [hL, h]
  apply InfoGeometry.Algebra.ZornVectorMatrix.ext
  · rfl
  · funext i; rfl
  · funext i
    simp [InfoGeometry.Algebra.ZornVectorMatrix.offDiagonal,
      InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Algebra.ZornVec3.dot,
      Fin.sum_univ_three]
  · rfl

/-- Concrete Peirce-block witness of nonzero `[L_x, R_y]`. -/
theorem lrComm_chiralUpper_witness :
    lrComm (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0)
        (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1)
        (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 2) =
      InfoGeometry.Canonical.ZornMatrix.zornMinus -
        InfoGeometry.Canonical.ZornMatrix.zornPlus ∧
    lrComm (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0)
      (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1) ≠ 0 ∧
    lrCommMat8 (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0)
      (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1) ≠ 0 := by
  have hval :
      lrComm (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0)
          (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1)
          (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 2) =
        InfoGeometry.Canonical.ZornMatrix.zornMinus -
          InfoGeometry.Canonical.ZornMatrix.zornPlus := by
    rw [lrComm_apply_eq_associator]
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · simp [zornAssociator, InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis,
        InfoGeometry.Canonical.ZornMatrix.zornMinus, InfoGeometry.Canonical.ZornMatrix.zornPlus,
        InfoGeometry.Canonical.ZornMatrix.mul_def, InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]
    · simp [zornAssociator, InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis,
        InfoGeometry.Canonical.ZornMatrix.zornMinus, InfoGeometry.Canonical.ZornMatrix.zornPlus,
        InfoGeometry.Canonical.ZornMatrix.mul_def, InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]
    · funext i; fin_cases i <;>
        simp [zornAssociator, InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis,
          InfoGeometry.Canonical.ZornMatrix.zornMinus, InfoGeometry.Canonical.ZornMatrix.zornPlus,
          InfoGeometry.Canonical.ZornMatrix.mul_def, InfoGeometry.Canonical.ZornMatrix.mul,
          InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]
    · funext i; fin_cases i <;>
        simp [zornAssociator, InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis,
          InfoGeometry.Canonical.ZornMatrix.zornMinus, InfoGeometry.Canonical.ZornMatrix.zornPlus,
          InfoGeometry.Canonical.ZornMatrix.mul_def, InfoGeometry.Canonical.ZornMatrix.mul,
          InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]
  have hne :
      lrComm (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0)
        (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1) ≠ 0 := by
    intro hzero
    have hz := congrArg (fun T : EndZorn =>
      T (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 2)) hzero
    rw [hval] at hz
    have hb := congrArg InfoGeometry.Canonical.ZornMatrix.b hz
    simp [InfoGeometry.Canonical.ZornMatrix.zornMinus,
      InfoGeometry.Canonical.ZornMatrix.zornPlus] at hb
  refine ⟨hval, hne, ?_⟩
  intro hm
  apply hne
  apply endToMat8.injective
  rw [endToMat8_lrComm, hm, map_zero]

/-! ## Section 4: `G_{2(2)}` Automorphisms (`RealSplitOctonionAut`) & Derivations -/

/-- `RealSplitOctonionAut` element as a linear endomorphism in `Module.End ℝ ZornCarrier`. -/
def autEnd (φ : InfoGeometry.Canonical.RealSplitOctonionAut) : EndZorn :=
  φ.1.toLinearMap

/-- Inverse of a `RealSplitOctonionAut` element in `Module.End ℝ ZornCarrier`. -/
def autInvEnd (φ : InfoGeometry.Canonical.RealSplitOctonionAut) : EndZorn :=
  φ.1.symm.toLinearMap

/-- `RealSplitOctonionAut` element as an `8 × 8` real matrix in `M₈(ℝ)`. -/
def autMat8 (φ : InfoGeometry.Canonical.RealSplitOctonionAut) : Mat8R :=
  endToMat8 (autEnd φ)

theorem autEnd_mul_autInvEnd (φ : InfoGeometry.Canonical.RealSplitOctonionAut) :
    autEnd φ * autInvEnd φ = 1 := by
  apply LinearMap.ext; intro x
  simp [autEnd, autInvEnd]

theorem autInvEnd_mul_autEnd (φ : InfoGeometry.Canonical.RealSplitOctonionAut) :
    autInvEnd φ * autEnd φ = 1 := by
  apply LinearMap.ext; intro x
  simp [autEnd, autInvEnd]

theorem autMat8_one : autMat8 1 = 1 := by
  have h : autEnd (1 : InfoGeometry.Canonical.RealSplitOctonionAut) = 1 := by
    apply LinearMap.ext; intro x; rfl
  simp [autMat8, h]

theorem autMat8_mul (φ ψ : InfoGeometry.Canonical.RealSplitOctonionAut) :
    autMat8 (φ * ψ) = autMat8 φ * autMat8 ψ := by
  have h : autEnd (φ * ψ) = autEnd φ * autEnd ψ := by
    apply LinearMap.ext; intro x; rfl
  simp [autMat8, h]

theorem autMat8_inv (φ : InfoGeometry.Canonical.RealSplitOctonionAut) :
    (autMat8 φ)⁻¹ = endToMat8 (autInvEnd φ) := by
  apply Matrix.inv_eq_right_inv
  rw [autMat8, ← map_mul, autEnd_mul_autInvEnd, _root_.map_one]

theorem isUnit_autMat8 (φ : InfoGeometry.Canonical.RealSplitOctonionAut) :
    IsUnit (autMat8 φ) := by
  refine ⟨⟨autMat8 φ, endToMat8 (autInvEnd φ), ?_, ?_⟩, rfl⟩
  · rw [autMat8, ← map_mul, autEnd_mul_autInvEnd, _root_.map_one]
  · rw [autMat8, ← map_mul, autInvEnd_mul_autEnd, _root_.map_one]

/-- Automorphism conjugation of left multiplication in `Module.End ℝ ZornCarrier`. -/
theorem autEnd_conj_leftMulEnd
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (x : ZornCarrier) :
    autEnd φ * leftMulEnd x * autInvEnd φ = leftMulEnd (φ.1 x) :=
  InfoGeometry.Canonical.SplitOctonionAutomorphismOperatorBridge.conjugateLeftRegular_eq_leftRegular
    φ x

/-- Automorphism conjugation of right multiplication in `Module.End ℝ ZornCarrier`. -/
theorem autEnd_conj_rightMulEnd
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (y : ZornCarrier) :
    autEnd φ * rightMulEnd y * autInvEnd φ = rightMulEnd (φ.1 y) :=
  InfoGeometry.Canonical.SplitOctonionAutomorphismOperatorBridge.conjugateRightRegular_eq_rightRegular
    φ y

/-- Automorphism conjugation of left multiplication in `Matrix (Fin 8) (Fin 8) ℝ`. -/
theorem autMat8_conj_leftMulMat8
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (x : ZornCarrier) :
    autMat8 φ * leftMulMat8 x * (autMat8 φ)⁻¹ = leftMulMat8 (φ.1 x) := by
  rw [autMat8_inv, autMat8, leftMulMat8, ← map_mul, ← map_mul, autEnd_conj_leftMulEnd]
  rfl

/-- Automorphism conjugation of right multiplication in `Matrix (Fin 8) (Fin 8) ℝ`. -/
theorem autMat8_conj_rightMulMat8
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (y : ZornCarrier) :
    autMat8 φ * rightMulMat8 y * (autMat8 φ)⁻¹ = rightMulMat8 (φ.1 y) := by
  rw [autMat8_inv, autMat8, rightMulMat8, ← map_mul, ← map_mul, autEnd_conj_rightMulEnd]
  rfl

/-- Every `RealSplitOctonionAut` preserves the Zorn associator. -/
theorem aut_preserves_zornAssociator
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (x z y : ZornCarrier) :
    φ.1 (zornAssociator x z y) = zornAssociator (φ.1 x) (φ.1 z) (φ.1 y) := by
  unfold zornAssociator
  rw [map_sub, φ.preserves_mul, φ.preserves_mul, φ.preserves_mul, φ.preserves_mul]

/-- Automorphism conjugation of `[L_x, R_y]` in `Module.End ℝ ZornCarrier`. -/
theorem autEnd_conj_lrComm
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (x y : ZornCarrier) :
    autEnd φ * lrComm x y * autInvEnd φ = lrComm (φ.1 x) (φ.1 y) := by
  apply LinearMap.ext
  intro z
  simp only [Module.End.mul_apply, autEnd, autInvEnd, LinearEquiv.coe_coe]
  rw [lrComm_apply_eq_neg_associator, lrComm_apply_eq_neg_associator, map_neg,
    aut_preserves_zornAssociator, LinearEquiv.apply_symm_apply]

/-- Automorphism conjugation of `[L_x, R_y]` in `Matrix (Fin 8) (Fin 8) ℝ`. -/
theorem autMat8_conj_lrCommMat8
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (x y : ZornCarrier) :
    autMat8 φ * lrCommMat8 x y * (autMat8 φ)⁻¹ = lrCommMat8 (φ.1 x) (φ.1 y) := by
  rw [autMat8_inv, autMat8, ← endToMat8_lrComm, ← endToMat8_lrComm,
    ← map_mul, ← map_mul, autEnd_conj_lrComm]

/-- Stabilizer subcase: automorphisms fixing `peirceP` also fix `1 - peirceP` and commute
with all four Peirce projections on `ZornCarrier`, in `EndZorn`, and in `M₈(ℝ)`. -/
theorem aut_stabilizes_complement_of_fix_P
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (hP : φ.1 peirceP = peirceP) :
    φ.1 (1 - peirceP) = 1 - peirceP := by
  rw [map_sub, φ.preserves_one, hP]

theorem aut_commutes_peirce_of_fix_P
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (hP : φ.1 peirceP = peirceP) (x : ZornCarrier) :
    (φ.1 (peirce11 peirceP x) = peirce11 peirceP (φ.1 x)) ∧
    (φ.1 (conePlus peirceP x) = conePlus peirceP (φ.1 x)) ∧
    (φ.1 (coneMinus peirceP x) = coneMinus peirceP (φ.1 x)) ∧
    (φ.1 (peirce00 peirceP x) = peirce00 peirceP (φ.1 x)) := by
  have hC := aut_stabilizes_complement_of_fix_P φ hP
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [peirce11, φ.preserves_mul, hP]
  · simp only [conePlus, φ.preserves_mul, hP, hC]
  · simp only [coneMinus, φ.preserves_mul, hP, hC]
  · simp only [peirce00, φ.preserves_mul, hC]

theorem autEnd_commutes_peirceEnd_of_fix_P
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (hP : φ.1 peirceP = peirceP) :
    (autEnd φ * peirce11End = peirce11End * autEnd φ) ∧
    (autEnd φ * conePlusEnd = conePlusEnd * autEnd φ) ∧
    (autEnd φ * coneMinusEnd = coneMinusEnd * autEnd φ) ∧
    (autEnd φ * peirce00End = peirce00End * autEnd φ) := by
  have h := aut_commutes_peirce_of_fix_P φ hP
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply LinearMap.ext; intro x; exact (h x).1
  · apply LinearMap.ext; intro x; exact (h x).2.1
  · apply LinearMap.ext; intro x; exact (h x).2.2.1
  · apply LinearMap.ext; intro x; exact (h x).2.2.2

theorem autMat8_commutes_peirceMat8_of_fix_P
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (hP : φ.1 peirceP = peirceP) :
    (autMat8 φ * endToMat8 peirce11End = endToMat8 peirce11End * autMat8 φ) ∧
    (autMat8 φ * endToMat8 conePlusEnd = endToMat8 conePlusEnd * autMat8 φ) ∧
    (autMat8 φ * endToMat8 coneMinusEnd = endToMat8 coneMinusEnd * autMat8 φ) ∧
    (autMat8 φ * endToMat8 peirce00End = endToMat8 peirce00End * autMat8 φ) := by
  obtain ⟨h11, h10, h01, h00⟩ := autEnd_commutes_peirceEnd_of_fix_P φ hP
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [autMat8, ← map_mul, h11]
  · simp only [autMat8, ← map_mul, h10]
  · simp only [autMat8, ← map_mul, h01]
  · simp only [autMat8, ← map_mul, h00]

/-- General `RealSplitOctonionAut` equivariance of the four parameterized Peirce projections
for any idempotent/carrier element `P` and `x`. -/
theorem aut_peirce11_equivariant
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (P x : ZornCarrier) :
    peirce11 (φ.1 P) (φ.1 x) = φ.1 (peirce11 P x) := by
  simp only [peirce11, φ.preserves_mul]

theorem aut_conePlus_equivariant
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (P x : ZornCarrier) :
    conePlus (φ.1 P) (φ.1 x) = φ.1 (conePlus P x) := by
  simp only [conePlus, map_sub, φ.preserves_one, φ.preserves_mul]

theorem aut_coneMinus_equivariant
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (P x : ZornCarrier) :
    coneMinus (φ.1 P) (φ.1 x) = φ.1 (coneMinus P x) := by
  simp only [coneMinus, map_sub, φ.preserves_one, φ.preserves_mul]

theorem aut_peirce00_equivariant
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (P x : ZornCarrier) :
    peirce00 (φ.1 P) (φ.1 x) = φ.1 (peirce00 P x) := by
  simp only [peirce00, map_sub, φ.preserves_one, φ.preserves_mul]

/-- Equivariance of the four Peirce projections for the conjugated idempotent `φ.1 peirceP`. -/
theorem aut_peirce11_conj
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (x : ZornCarrier) :
    peirce11 (φ.1 peirceP) (φ.1 x) = φ.1 (peirce11 peirceP x) :=
  aut_peirce11_equivariant φ peirceP x

theorem aut_conePlus_conj
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (x : ZornCarrier) :
    conePlus (φ.1 peirceP) (φ.1 x) = φ.1 (conePlus peirceP x) :=
  aut_conePlus_equivariant φ peirceP x

theorem aut_coneMinus_conj
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (x : ZornCarrier) :
    coneMinus (φ.1 peirceP) (φ.1 x) = φ.1 (coneMinus peirceP x) :=
  aut_coneMinus_equivariant φ peirceP x

theorem aut_peirce00_conj
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (x : ZornCarrier) :
    peirce00 (φ.1 peirceP) (φ.1 x) = φ.1 (peirce00 peirceP x) :=
  aut_peirce00_equivariant φ peirceP x

/-- Every `RealSplitOctonionAut` maps `peirceP` to an idempotent `φ.1 peirceP`. -/
theorem aut_peirce_conj_idempotent (φ : InfoGeometry.Canonical.RealSplitOctonionAut) :
    φ.1 peirceP * φ.1 peirceP = φ.1 peirceP := by
  rw [← φ.preserves_mul, peirceP_idempotent]

/-- Peirce decomposition of any Zorn cell relative to a conjugated idempotent `φ.1 peirceP`. -/
theorem aut_peirce_decomposition_conj
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (z : ZornCarrier) :
    z = peirce11 (φ.1 peirceP) z + conePlus (φ.1 peirceP) z +
      coneMinus (φ.1 peirceP) z + peirce00 (φ.1 peirceP) z := by
  have hdec := congrArg φ.1 (zorn_peirce_decomposition (φ.1.symm z))
  simp only [LinearEquiv.apply_symm_apply, map_add] at hdec
  rw [← aut_peirce11_conj, ← aut_conePlus_conj, ← aut_coneMinus_conj,
    ← aut_peirce00_conj] at hdec
  simpa only [LinearEquiv.apply_symm_apply] using hdec

/-- Peirce decomposition evaluated at `φ.1 x` for a conjugated idempotent `φ.1 peirceP`. -/
theorem aut_peirce_decomposition_conj_apply
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (x : ZornCarrier) :
    φ.1 x = peirce11 (φ.1 peirceP) (φ.1 x) + conePlus (φ.1 peirceP) (φ.1 x) +
      coneMinus (φ.1 peirceP) (φ.1 x) + peirce00 (φ.1 peirceP) (φ.1 x) :=
  aut_peirce_decomposition_conj φ (φ.1 x)

/-- Conjugated Peirce `2×2` block multiplication laws relative to `φ.1 peirceP`. -/
theorem aut_peirce_block_mul_conj
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (z₁ z₂ : ZornCarrier) :
    peirce11 (φ.1 peirceP) (z₁ * z₂) =
      peirce11 (φ.1 peirceP) z₁ * peirce11 (φ.1 peirceP) z₂ +
        conePlus (φ.1 peirceP) z₁ * coneMinus (φ.1 peirceP) z₂ ∧
    conePlus (φ.1 peirceP) (z₁ * z₂) =
      peirce11 (φ.1 peirceP) z₁ * conePlus (φ.1 peirceP) z₂ +
        conePlus (φ.1 peirceP) z₁ * peirce00 (φ.1 peirceP) z₂ +
        coneMinus (φ.1 peirceP) z₁ * coneMinus (φ.1 peirceP) z₂ ∧
    coneMinus (φ.1 peirceP) (z₁ * z₂) =
      coneMinus (φ.1 peirceP) z₁ * peirce11 (φ.1 peirceP) z₂ +
        peirce00 (φ.1 peirceP) z₁ * coneMinus (φ.1 peirceP) z₂ +
        conePlus (φ.1 peirceP) z₁ * conePlus (φ.1 peirceP) z₂ ∧
    peirce00 (φ.1 peirceP) (z₁ * z₂) =
      coneMinus (φ.1 peirceP) z₁ * conePlus (φ.1 peirceP) z₂ +
        peirce00 (φ.1 peirceP) z₁ * peirce00 (φ.1 peirceP) z₂ := by
  let x₁ := φ.1.symm z₁
  let x₂ := φ.1.symm z₂
  have hz₁ : z₁ = φ.1 x₁ := (LinearEquiv.apply_symm_apply φ.1 z₁).symm
  have hz₂ : z₂ = φ.1 x₂ := (LinearEquiv.apply_symm_apply φ.1 z₂).symm
  obtain ⟨h11, h10, h01, h00⟩ := zorn_peirce_block_mul x₁ x₂
  have hm : z₁ * z₂ = φ.1 (x₁ * x₂) := by rw [hz₁, hz₂, φ.preserves_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hm, hz₁, hz₂, aut_peirce11_conj, h11]
    simp only [map_add, φ.preserves_mul, aut_peirce11_conj, aut_conePlus_conj, aut_coneMinus_conj]
  · rw [hm, hz₁, hz₂, aut_conePlus_conj, h10]
    simp only [map_add, φ.preserves_mul, aut_peirce11_conj, aut_conePlus_conj, aut_coneMinus_conj,
      aut_peirce00_conj]
  · rw [hm, hz₁, hz₂, aut_coneMinus_conj, h01]
    simp only [map_add, φ.preserves_mul, aut_peirce11_conj, aut_conePlus_conj, aut_coneMinus_conj,
      aut_peirce00_conj]
  · rw [hm, hz₁, hz₂, aut_peirce00_conj, h00]
    simp only [map_add, φ.preserves_mul, aut_conePlus_conj, aut_coneMinus_conj, aut_peirce00_conj]

local instance : LieRing EndZorn := LieRing.ofAssociativeRing
local instance : LieRing Mat8R := LieRing.ofAssociativeRing

/-- Product Leibniz rule for canonical derivations. -/
theorem derivation_map_mul (D : canonicalZornDerivations) (x y : ZornCarrier) :
    D.1 (x * y) = D.1 x * y + x * D.1 y :=
  D.property x y

/-- Three-slot Leibniz rule for canonical derivations acting on `zornAssociator`. -/
theorem derivation_map_zornAssociator
    (D : canonicalZornDerivations) (x z y : ZornCarrier) :
    D.1 (zornAssociator x z y) =
      zornAssociator (D.1 x) z y + zornAssociator x (D.1 z) y +
        zornAssociator x z (D.1 y) := by
  unfold zornAssociator
  rw [map_sub, D.property, D.property, D.property, D.property]
  simp only [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.add_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_add]
  abel

/-- Lie-bracket equivariance of canonical derivations with `L_x` in `EndZorn` and `Mat8R`. -/
theorem derivation_lie_leftMulEnd (D : canonicalZornDerivations) (x : ZornCarrier) :
    ⁅D.1, leftMulEnd x⁆ = leftMulEnd (D.1 x) :=
  InfoGeometry.Canonical.SplitOctonionAutomorphismOperatorBridge.derivation_lie_leftRegular
    D.1 D.property x

theorem derivation_lie_leftMulMat8 (D : canonicalZornDerivations) (x : ZornCarrier) :
    ⁅endToMat8 D.1, leftMulMat8 x⁆ = leftMulMat8 (D.1 x) := by
  rw [LieRing.of_associative_ring_bracket, leftMulMat8, ← map_mul, ← map_mul, ← map_sub]
  rw [← LieRing.of_associative_ring_bracket, derivation_lie_leftMulEnd]
  rfl

/-- Lie-bracket equivariance of canonical derivations with `R_y` in `EndZorn` and `Mat8R`. -/
theorem derivation_lie_rightMulEnd (D : canonicalZornDerivations) (y : ZornCarrier) :
    ⁅D.1, rightMulEnd y⁆ = rightMulEnd (D.1 y) :=
  InfoGeometry.Canonical.SplitOctonionAutomorphismOperatorBridge.derivation_lie_rightRegular
    D.1 D.property y

theorem derivation_lie_rightMulMat8 (D : canonicalZornDerivations) (y : ZornCarrier) :
    ⁅endToMat8 D.1, rightMulMat8 y⁆ = rightMulMat8 (D.1 y) := by
  rw [LieRing.of_associative_ring_bracket, rightMulMat8, ← map_mul, ← map_mul, ← map_sub]
  rw [← LieRing.of_associative_ring_bracket, derivation_lie_rightMulEnd]
  rfl

/-- Lie-bracket equivariance of canonical derivations with `[L_x, R_y]` in `EndZorn` and `Mat8R`. -/
theorem derivation_lie_lrComm (D : canonicalZornDerivations) (x y : ZornCarrier) :
    ⁅D.1, lrComm x y⁆ = lrComm (D.1 x) y + lrComm x (D.1 y) := by
  rw [LieRing.of_associative_ring_bracket]
  apply LinearMap.ext
  intro z
  change D.1 (lrComm x y z) - lrComm x y (D.1 z) = lrComm (D.1 x) y z + lrComm x (D.1 y) z
  rw [lrComm_apply_eq_neg_associator, lrComm_apply_eq_neg_associator,
    lrComm_apply_eq_neg_associator, lrComm_apply_eq_neg_associator,
    map_neg, derivation_map_zornAssociator]
  abel

theorem derivation_lie_lrCommMat8 (D : canonicalZornDerivations) (x y : ZornCarrier) :
    ⁅endToMat8 D.1, lrCommMat8 x y⁆ = lrCommMat8 (D.1 x) y + lrCommMat8 x (D.1 y) := by
  rw [LieRing.of_associative_ring_bracket, ← endToMat8_lrComm, ← map_mul, ← map_mul, ← map_sub,
    ← LieRing.of_associative_ring_bracket, derivation_lie_lrComm, map_add,
    endToMat8_lrComm, endToMat8_lrComm]

/-- Baez standard derivation `directCanonicalStanDerMap x y` decomposes explicitly as
`[L_x, L_y] + [L_x, R_y] + [R_x, R_y]`. -/
theorem directCanonicalStanDerMap_eq_commutator_sum (x y : ZornCarrier) :
    directCanonicalStanDerMap x y =
      ⁅leftMulEnd x, leftMulEnd y⁆ + lrComm x y + ⁅rightMulEnd x, rightMulEnd y⁆ := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.add_apply, LinearMap.add_apply, LieRing.of_associative_ring_bracket,
    LieRing.of_associative_ring_bracket]
  simp only [directCanonicalStanDerMap_apply, LinearMap.sub_apply, Module.End.mul_apply,
    leftMulEnd_apply, rightMulEnd_apply, lrComm]

/-- Normal form of Baez standard derivations via `zornAssociator`. -/
theorem directCanonicalStanDerMap_normal_form_zornAssociator (x y z : ZornCarrier) :
    directCanonicalStanDerMap x y z =
      ((x * y - y * x) * z - z * (x * y - y * x)) - 3 • zornAssociator x y z :=
  directCanonicalStanDerMap_apply_normal_form x y z

/-- `RealSplitOctonionAut` conjugation equivariance of Baez standard derivations
in `EndZorn` and `Mat8R`. -/
theorem autEnd_conj_directCanonicalStanDerMap
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (x y : ZornCarrier) :
    autEnd φ * directCanonicalStanDerMap x y * autInvEnd φ =
      directCanonicalStanDerMap (φ.1 x) (φ.1 y) := by
  apply LinearMap.ext
  intro z
  simp only [Module.End.mul_apply, autEnd, autInvEnd, LinearEquiv.coe_coe,
    directCanonicalStanDerMap_apply, map_add, map_sub, φ.preserves_mul,
    LinearEquiv.apply_symm_apply]

theorem autMat8_conj_directCanonicalStanDerMap
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (x y : ZornCarrier) :
    autMat8 φ * endToMat8 (directCanonicalStanDerMap x y) * (autMat8 φ)⁻¹ =
      endToMat8 (directCanonicalStanDerMap (φ.1 x) (φ.1 y)) := by
  rw [autMat8_inv, autMat8, ← map_mul, ← map_mul, autEnd_conj_directCanonicalStanDerMap]

/-- Lie-bracket covariance of `canonicalZornDerivations` on Baez standard derivations
in both `EndZorn` and `Mat8R`. -/
theorem derivation_lie_directCanonicalStanDerMap
    (D : canonicalZornDerivations) (x y : ZornCarrier) :
    ⁅D.1, directCanonicalStanDerMap x y⁆ =
      directCanonicalStanDerMap (D.1 x) y + directCanonicalStanDerMap x (D.1 y) := by
  rw [LieRing.of_associative_ring_bracket]
  apply LinearMap.ext
  intro z
  exact standardDerivation_covariant D.1 D.property x y z

theorem derivation_lie_directCanonicalStanDerMat8
    (D : canonicalZornDerivations) (x y : ZornCarrier) :
    ⁅endToMat8 D.1, endToMat8 (directCanonicalStanDerMap x y)⁆ =
      endToMat8 (directCanonicalStanDerMap (D.1 x) y) +
        endToMat8 (directCanonicalStanDerMap x (D.1 y)) := by
  rw [LieRing.of_associative_ring_bracket, ← map_mul, ← map_mul, ← map_sub]
  rw [← LieRing.of_associative_ring_bracket, derivation_lie_directCanonicalStanDerMap, map_add]

/-- The 14-dimensional `𝔤₂₍₂₎` Lie algebra of canonical split-octonion derivations is
spanned by Baez standard derivations. -/
theorem g2_derivation_finrank_and_standard_span :
    Module.finrank ℝ canonicalZornDerivations = 14 ∧
      standardDerivationSpan = ⊤ :=
  ⟨InfoGeometry.Lie.RealSplitOctonionG2Classification.canonical_split_octonion_derivation_finrank,
   InfoGeometry.Lie.RealSplitOctonionG2Classification.standard_split_octonion_derivations_span⟩

/-! ## Section 5: R5 Non-Multiplicativity Separation -/

/-- Exact real-linear isomorphism `Mat2C ≃ₗ[ℝ] ZornCarrier`, bridging
`MatrixCayleyDicksonSeparation` directly onto `ZornCarrier`. -/
def mat2CToZornCarrier : Mat2C ≃ₗ[ℝ] ZornCarrier :=
  matrixSplitLinearEquiv.trans algToCarrierEquiv

/-- No surjective multiplicative map can exist from the associative algebra `Mat2C`
onto `ZornCarrier`. -/
theorem no_surjective_multiplicative_mat2C_to_zornCarrier :
    ¬ ∃ f : Mat2C → ZornCarrier,
      Function.Surjective f ∧ ∀ A B, f (A * B) = f A * f B := by
  rintro ⟨f, hsurj, hmul⟩
  refine no_surjective_multiplicative_matrix_map ?_
  refine ⟨fun A => algToCarrierEquiv.symm (f A), ?_, ?_⟩
  · exact algToCarrierEquiv.symm.surjective.comp hsurj
  · intro A B
    apply algToCarrierEquiv.injective
    rw [LinearEquiv.apply_symm_apply, hmul, algToCarrierEquiv_mul,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- The linear equivalence `mat2CToZornCarrier : Mat2C ≃ₗ[ℝ] ZornCarrier` does not
preserve multiplication. -/
theorem mat2CToZornCarrier_not_multiplicative :
    ¬ ∀ A B : Mat2C,
      mat2CToZornCarrier (A * B) = mat2CToZornCarrier A * mat2CToZornCarrier B := by
  intro h
  exact no_surjective_multiplicative_mat2C_to_zornCarrier
    ⟨mat2CToZornCarrier, mat2CToZornCarrier.surjective, h⟩

/-- Full-carrier regular-action non-multiplicativity defect measured by `-zornAssociator`:
`(L_x ∘ L_y - L_{x*y}) z = -(x, y, z)`. -/
theorem leftMulEnd_mul_sub_apply (x y z : ZornCarrier) :
    (leftMulEnd x ∘ₗ leftMulEnd y - leftMulEnd (x * y)) z = -zornAssociator x y z := by
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, leftMulEnd_apply, zornAssociator]
  abel

/-- Complementary sign convention: `(L_{x*y} - L_x ∘ L_y) z = (x, y, z)`. -/
theorem leftMulEnd_sub_mul_apply (x y z : ZornCarrier) :
    (leftMulEnd (x * y) - leftMulEnd x ∘ₗ leftMulEnd y) z = zornAssociator x y z := by
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, leftMulEnd_apply, zornAssociator]

theorem mat8EquivEndZorn_leftMulMat8_defect_apply (x y z : ZornCarrier) :
    mat8EquivEndZorn (leftMulMat8 x * leftMulMat8 y - leftMulMat8 (x * y)) z =
      -zornAssociator x y z := by
  rw [leftMulMat8, leftMulMat8, leftMulMat8, ← map_mul, ← map_sub]
  change (endToMat8.symm (endToMat8 (leftMulEnd x * leftMulEnd y - leftMulEnd (x * y)))) z =
    -zornAssociator x y z
  rw [AlgEquiv.symm_apply_apply]
  exact leftMulEnd_mul_sub_apply x y z

theorem leftMulEnd_multiplicative_iff_associator_zero (x y : ZornCarrier) :
    leftMulEnd x ∘ₗ leftMulEnd y = leftMulEnd (x * y) ↔ ∀ z, zornAssociator x y z = 0 := by
  constructor
  · intro h z
    have hz := congrArg (fun T : EndZorn => T z) h
    have hd : (leftMulEnd x ∘ₗ leftMulEnd y - leftMulEnd (x * y)) z = 0 := by
      rw [LinearMap.sub_apply, hz, sub_self]
    rw [leftMulEnd_mul_sub_apply] at hd
    exact neg_eq_zero.mp hd
  · intro h
    apply LinearMap.ext
    intro z
    have hd : (leftMulEnd x ∘ₗ leftMulEnd y - leftMulEnd (x * y)) z = 0 := by
      rw [leftMulEnd_mul_sub_apply, h z, neg_zero]
    exact sub_eq_zero.mp (by simpa [LinearMap.sub_apply] using hd)

theorem leftMulMat8_multiplicative_iff_associator_zero (x y : ZornCarrier) :
    leftMulMat8 x * leftMulMat8 y = leftMulMat8 (x * y) ↔ ∀ z, zornAssociator x y z = 0 := by
  rw [← leftMulEnd_multiplicative_iff_associator_zero]
  constructor
  · intro h
    apply endToMat8.injective
    change endToMat8 (leftMulEnd x * leftMulEnd y) = endToMat8 (leftMulEnd (x * y))
    simpa only [leftMulMat8, map_mul] using h
  · intro h
    have h' : endToMat8 (leftMulEnd x * leftMulEnd y) = endToMat8 (leftMulEnd (x * y)) :=
      congrArg endToMat8 h
    simpa only [leftMulMat8, map_mul] using h'

/-- Concrete Peirce-block witness of regular-action non-multiplicativity using
`chiralUpperBasis 0`, `chiralUpperBasis 1`, evaluated at `chiralUpperBasis 2`. -/
theorem peirce_nonmultiplicativity_defect_witness :
    (leftMulEnd (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0) ∘ₗ
        leftMulEnd (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1) -
      leftMulEnd (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0 *
        InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1))
        (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 2) =
      InfoGeometry.Canonical.ZornMatrix.zornPlus -
        InfoGeometry.Canonical.ZornMatrix.zornMinus ∧
    (InfoGeometry.Canonical.ZornMatrix.zornPlus (R := ℝ) -
      InfoGeometry.Canonical.ZornMatrix.zornMinus (R := ℝ)) ≠ 0 := by
  have hdef :
      (leftMulEnd (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0) ∘ₗ
          leftMulEnd (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1) -
        leftMulEnd (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0 *
          InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1))
          (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 2) =
        InfoGeometry.Canonical.ZornMatrix.zornPlus -
          InfoGeometry.Canonical.ZornMatrix.zornMinus := by
    rw [leftMulEnd_mul_sub_apply]
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · simp [zornAssociator, InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis,
        InfoGeometry.Canonical.ZornMatrix.zornPlus, InfoGeometry.Canonical.ZornMatrix.zornMinus,
        InfoGeometry.Canonical.ZornMatrix.mul_def, InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]
    · simp [zornAssociator, InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis,
        InfoGeometry.Canonical.ZornMatrix.zornPlus, InfoGeometry.Canonical.ZornMatrix.zornMinus,
        InfoGeometry.Canonical.ZornMatrix.mul_def, InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]
    · funext i; fin_cases i <;>
        simp [zornAssociator, InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis,
          InfoGeometry.Canonical.ZornMatrix.zornPlus, InfoGeometry.Canonical.ZornMatrix.zornMinus,
          InfoGeometry.Canonical.ZornMatrix.mul_def, InfoGeometry.Canonical.ZornMatrix.mul,
          InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]
    · funext i; fin_cases i <;>
        simp [zornAssociator, InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis,
          InfoGeometry.Canonical.ZornMatrix.zornPlus, InfoGeometry.Canonical.ZornMatrix.zornMinus,
          InfoGeometry.Canonical.ZornMatrix.mul_def, InfoGeometry.Canonical.ZornMatrix.mul,
          InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]
  refine ⟨hdef, ?_⟩
  intro hz
  have ha := congrArg InfoGeometry.Canonical.ZornMatrix.a hz
  simp [InfoGeometry.Canonical.ZornMatrix.zornPlus,
    InfoGeometry.Canonical.ZornMatrix.zornMinus] at ha

/-- Full-carrier operator non-multiplicativity theorem (`∃ x y, L_{x*y} ≠ L_x ∘ L_y`). -/
theorem leftMulEnd_not_multiplicative :
    ∃ x y : ZornCarrier, leftMulEnd (x * y) ≠ leftMulEnd x ∘ₗ leftMulEnd y := by
  refine ⟨InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis 0,
    InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis 1, ?_⟩
  intro h
  have h' : leftMulEnd (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0) ∘ₗ
      leftMulEnd (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1) =
      leftMulEnd (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0 *
        InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1) := h.symm
  have hzero := congrArg (fun T : EndZorn =>
    T (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 2))
    (sub_eq_zero.mpr h')
  rw [LinearMap.zero_apply] at hzero
  exact peirce_nonmultiplicativity_defect_witness.2
    (peirce_nonmultiplicativity_defect_witness.1 ▸ hzero)

/-- Full-carrier `M₈(ℝ)` non-multiplicativity theorem (`∃ x y, L_{x*y} ≠ L_x * L_y`). -/
theorem leftMulMat8_not_multiplicative :
    ∃ x y : ZornCarrier, leftMulMat8 (x * y) ≠ leftMulMat8 x * leftMulMat8 y := by
  obtain ⟨x, y, hxy⟩ := leftMulEnd_not_multiplicative
  refine ⟨x, y, ?_⟩
  intro hm
  apply hxy
  apply endToMat8.injective
  change endToMat8 (leftMulEnd (x * y)) = endToMat8 (leftMulEnd x * leftMulEnd y)
  simpa only [leftMulMat8, map_mul] using hm

/-- Compatibility link to `SplitOctonionNonmultiplicativity` on the `Imaginary` witnesses
`ex_X, ex_Y, ex_Z`. -/
theorem imaginary_nonmultiplicativity_via_leftMulEnd :
    leftMulEnd (InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_X.1 *
      InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_Y.1) ≠
      leftMulEnd InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_X.1 ∘ₗ
        leftMulEnd InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_Y.1 := by
  intro h
  apply nonmultiplicativity_obstruction
  rw [← leftMulEnd_imaginary InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_X,
    ← leftMulEnd_imaginary InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_Y]
  convert h.symm
  exact (leftMulEnd_imaginary _).symm

theorem imaginary_nonmultiplicativity_via_leftMulMat8 :
    leftMulMat8 (InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_X.1 *
      InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_Y.1) ≠
      leftMulMat8 InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_X.1 *
        leftMulMat8 InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_Y.1 := by
  intro h
  apply pseudoReal_nonmultiplicativity_obstruction
  rw [← leftMulMat8_imaginary InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_X,
    ← leftMulMat8_imaginary InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_Y]
  have hmem : InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_X.1 *
      InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_Y.1 ∈
      InfoGeometry.Lie.SplitOctonionImaginaryAction.Imaginary := by
    simp [InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_X,
      InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_Y,
      InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornTrace,
      InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  have hprod :
      leftMulMatrix
          ⟨InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_X.1 *
            InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_Y.1, hmem⟩ =
        leftMulMat8 (InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_X.1 *
          InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_Y.1) :=
    (leftMulMat8_imaginary ⟨InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_X.1 *
      InfoGeometry.Lie.SplitOctonionImaginaryAction.ex_Y.1, hmem⟩).symm
  rw [hprod]
  exact h.symm

end InfoGeometry.Algebra.Zorn.SplitOctonionPeirceG2Unification
