/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Synthesis.MathlibCliffordUniversalLiftSynthesis
import InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation
import InfoGeometry.Clifford.Cl11GradedTensorMorita
import InfoGeometry.Clifford.Cl11RecursiveUnrolling
import InfoGeometry.Algebra.NoncommutativeCliffordColimitMassGapSynthesis
import InfoGeometry.Clifford.Cl11SplitTowerMatrixEquiv
import InfoGeometry.Canonical.SplitCliffordHeadMorita
import InfoGeometry.Canonical.SplitCliffordHeadTailTower
import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.Canonical.SplitCliffordSuperGradeColimit
import InfoGeometry.OperatorAlgebra.ErlangenDoubleCylinderSymmetryInvariants
import InfoGeometry.Clifford.CliffordBitWordEquivalence
import InfoGeometry.Recovered.CantorCliffordLimitBridgeRecovered
import InfoGeometry.Canonical.CantorLocalCl11OrthogonalAction
import InfoGeometry.Clifford.Cl11ChiralityAlgebra
import InfoGeometry.Canonical.GradedTensorWeylBridge

/-!
# Split Clifford Tower Unification

Reconciles the three `Cl(1,1) ≃ M₂(ℝ)` bases (`cl11EquivMat`, `cl11StandardEquiv`,
`cl11MatrixAlgEquiv`), establishes finite-stage and colimit relationships between
Lane 1 (`Clsplit n` / `SplitCliffordInfinity`), Lane 2 (`Cl11TensorTowerLimit.Limit` /
`RealCantorOpLimit.Limit` / `DoubleCylinderColimit ℝ`), and Lane 3
(`ClTower A n` / `ClInf A`), and unifies the Klein-four (`V4`) atom and global
symmetries with the Erlangen `G_swap` and Cantor `BinaryWordTiltReadout` actions.

In the framing of Felix Klein's 1872 *Erlanger Programm* (§§4–5, Concluding Remarks,
and Footnote 37):
- Section 1 (`ThreeBasisReconciliation`) and Sections 2–3 (`Lane1Lane3Reconciliation`,
  `EmbeddingAndColimitReconciliation`) realize §4 (*Abbildung*) equivariant transfer
  conjugating representations across carriers (`walshConjugation`, `j1Conjugation`,
  `clSplitGradedTensorEquivClTower`, `clTowerEquivCliffordTensor`);
- Section 4 (`KleinFourLiftAndErlangenUnification`) realizes §5 faithful space-element
  actions (`SymmetryAction V4`) across `Cl(1,1)`, `evenOdd q11 ᵍ⊗ 𝒜`, `Clsplit n`,
  `SplitCliffordInfinity`, `DoubleCylinderColimit ℝ`, and `localCl11AlgebraHom`,
  complementing coordinate-system-independent `CliffordAlgebra Q` invariants (Footnote 37).
-/

noncomputable section

open scoped TensorProduct GradedTensorProduct Matrix Kronecker

attribute [local instance] InfoGeometry.Algebra.NoncommutativeCliffordColimitMassGapSynthesis.instAlgebraClTower

namespace InfoGeometry.Canonical.SplitCliffordTowerUnification

open InfoGeometry.Canonical.GradedTensorWeylBridge

private theorem add_gtmul {A B : Type*} [Ring A] [Ring B] [Algebra ℝ A] [Algebra ℝ B]
    {𝒜 : ZMod 2 → Submodule ℝ A} {ℬ : ZMod 2 → Submodule ℝ B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (a₁ a₂ : A) (b : B) : ((a₁ + a₂) ᵍ⊗ₜ[ℝ] b : 𝒜 ᵍ⊗[ℝ] ℬ) = a₁ ᵍ⊗ₜ b + a₂ ᵍ⊗ₜ b := by
  dsimp [GradedTensorProduct.tmul]; rw [TensorProduct.add_tmul, map_add]

private theorem gtmul_add {A B : Type*} [Ring A] [Ring B] [Algebra ℝ A] [Algebra ℝ B]
    {𝒜 : ZMod 2 → Submodule ℝ A} {ℬ : ZMod 2 → Submodule ℝ B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (a : A) (b₁ b₂ : B) : (a ᵍ⊗ₜ[ℝ] (b₁ + b₂) : 𝒜 ᵍ⊗[ℝ] ℬ) = a ᵍ⊗ₜ b₁ + a ᵍ⊗ₜ b₂ := by
  dsimp [GradedTensorProduct.tmul]; rw [TensorProduct.tmul_add, map_add]

private theorem smul_gtmul {A B : Type*} [Ring A] [Ring B] [Algebra ℝ A] [Algebra ℝ B]
    {𝒜 : ZMod 2 → Submodule ℝ A} {ℬ : ZMod 2 → Submodule ℝ B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (r : ℝ) (a : A) (b : B) : ((r • a) ᵍ⊗ₜ[ℝ] b : 𝒜 ᵍ⊗[ℝ] ℬ) = r • (a ᵍ⊗ₜ b) := by
  dsimp [GradedTensorProduct.tmul]; rw [← TensorProduct.smul_tmul', map_smul]

private theorem gtmul_smul {A B : Type*} [Ring A] [Ring B] [Algebra ℝ A] [Algebra ℝ B]
    {𝒜 : ZMod 2 → Submodule ℝ A} {ℬ : ZMod 2 → Submodule ℝ B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (r : ℝ) (a : A) (b : B) : (a ᵍ⊗ₜ[ℝ] (r • b) : 𝒜 ᵍ⊗[ℝ] ℬ) = r • (a ᵍ⊗ₜ b) := by
  dsimp [GradedTensorProduct.tmul]; rw [TensorProduct.tmul_smul, map_smul]

private theorem zero_gtmul {A B : Type*} [Ring A] [Ring B] [Algebra ℝ A] [Algebra ℝ B]
    {𝒜 : ZMod 2 → Submodule ℝ A} {ℬ : ZMod 2 → Submodule ℝ B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (b : B) : ((0 : A) ᵍ⊗ₜ[ℝ] b : 𝒜 ᵍ⊗[ℝ] ℬ) = 0 := by
  dsimp [GradedTensorProduct.tmul]; rw [TensorProduct.zero_tmul, map_zero]

private theorem gtmul_zero {A B : Type*} [Ring A] [Ring B] [Algebra ℝ A] [Algebra ℝ B]
    {𝒜 : ZMod 2 → Submodule ℝ A} {ℬ : ZMod 2 → Submodule ℝ B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (a : A) : (a ᵍ⊗ₜ[ℝ] (0 : B) : 𝒜 ᵍ⊗[ℝ] ℬ) = 0 := by
  dsimp [GradedTensorProduct.tmul]; rw [TensorProduct.tmul_zero, map_zero]

private theorem neg_gtmul {A B : Type*} [Ring A] [Ring B] [Algebra ℝ A] [Algebra ℝ B]
    {𝒜 : ZMod 2 → Submodule ℝ A} {ℬ : ZMod 2 → Submodule ℝ B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (a : A) (b : B) : ((-a) ᵍ⊗ₜ[ℝ] b : 𝒜 ᵍ⊗[ℝ] ℬ) = -(a ᵍ⊗ₜ b) := by
  dsimp [GradedTensorProduct.tmul]; rw [TensorProduct.neg_tmul, map_neg]

private theorem gtmul_neg {A B : Type*} [Ring A] [Ring B] [Algebra ℝ A] [Algebra ℝ B]
    {𝒜 : ZMod 2 → Submodule ℝ A} {ℬ : ZMod 2 → Submodule ℝ B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (a : A) (b : B) : (a ᵍ⊗ₜ[ℝ] (-b) : 𝒜 ᵍ⊗[ℝ] ℬ) = -(a ᵍ⊗ₜ b) := by
  dsimp [GradedTensorProduct.tmul]; rw [TensorProduct.tmul_neg, map_neg]

private theorem zsmul_gtmul {A B : Type*} [Ring A] [Ring B] [Algebra ℝ A] [Algebra ℝ B]
    {𝒜 : ZMod 2 → Submodule ℝ A} {ℬ : ZMod 2 → Submodule ℝ B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (k : ℤ) (a : A) (b : B) : ((k • a) ᵍ⊗ₜ[ℝ] b : 𝒜 ᵍ⊗[ℝ] ℬ) = k • (a ᵍ⊗ₜ b) := by
  dsimp [GradedTensorProduct.tmul]
  rw [← Int.cast_smul_eq_zsmul ℝ k a, ← TensorProduct.smul_tmul', map_smul,
    Int.cast_smul_eq_zsmul ℝ]

private theorem one_gtmul_mul_one_gtmul {A B : Type*} [Ring A] [Ring B] [Algebra ℝ A] [Algebra ℝ B]
    {𝒜 : ZMod 2 → Submodule ℝ A} {ℬ : ZMod 2 → Submodule ℝ B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (b₁ b₂ : B) :
    ((1 : A) ᵍ⊗ₜ[ℝ] b₁ : 𝒜 ᵍ⊗[ℝ] ℬ) * ((1 : A) ᵍ⊗ₜ[ℝ] b₂) = (1 : A) ᵍ⊗ₜ (b₁ * b₂) :=
  (map_mul (GradedTensorProduct.includeRight 𝒜 ℬ) b₁ b₂).symm

/-! ## Section 1: Three-Basis Reconciliation (`F3.1`) -/

section ThreeBasisReconciliation

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11GradedMorita
open InfoGeometry.Synthesis.MathlibCliffordUniversalLiftSynthesis
open InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation
open InfoGeometry.Canonical.SplitCliffordHeadMorita
open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.ClNN

/-- Conjugation by `J1 = ![![0, 1], ![1, 0]]` on `Mat2`: `M ↦ J1 * M * J1`. -/
def j1Conjugation : InfoGeometry.Clifford.Cl11Matrix.Mat2 ≃ₐ[ℝ]
    InfoGeometry.Clifford.Cl11Matrix.Mat2 :=
  adjointAlgEquiv bivectorUnit

@[simp] theorem j1Conjugation_apply (M : InfoGeometry.Clifford.Cl11Matrix.Mat2) :
    j1Conjugation M = J1 * M * J1 := rfl

theorem j1Conjugation_involutive (M : InfoGeometry.Clifford.Cl11Matrix.Mat2) :
    j1Conjugation (j1Conjugation M) = M := by
  rw [j1Conjugation_apply, j1Conjugation_apply, ← mul_assoc, ← mul_assoc, J1_sq, one_mul,
    mul_assoc, J1_sq, mul_one]

@[simp] theorem j1Conjugation_Eplus : j1Conjugation Eplus = -Eplus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [j1Conjugation_apply, J1, Eplus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem j1Conjugation_Eminus : j1Conjugation Eminus = -Eminus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [j1Conjugation_apply, J1, Eminus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem j1Conjugation_J1 : j1Conjugation J1 = J1 := by
  simp [j1Conjugation_apply]

/-- `cl11StandardEquiv` is literally `cl11EquivMat` followed by `walshConjugation`. -/
theorem cl11StandardEquiv_eq_walsh_trans_cl11EquivMat :
    cl11StandardEquiv = cl11EquivMat.trans walshConjugation := rfl

/-- `cl11MatrixAlgEquiv` (from `MathlibCliffordUniversalLiftSynthesis`) equals
`cl11StandardEquiv` followed by `j1Conjugation` (matching `q11Form ≃qᵢ q11`). -/
theorem cl11MatrixAlgEquiv_eq_j1Conj_trans_cl11StandardEquiv :
    cl11MatrixAlgEquiv =
      (cliffordQ11FormEquivCl11MatrixQ11.trans cl11StandardEquiv).trans j1Conjugation := by
  apply AlgEquiv.ext
  intro x
  have hhom :
      cl11MatrixAlgEquiv.toAlgHom =
        ((cliffordQ11FormEquivCl11MatrixQ11.trans cl11StandardEquiv).trans
          j1Conjugation).toAlgHom := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    rcases v with ⟨a, b⟩
    have hv : (a, b) = a • ((1 : ℝ), (0 : ℝ)) + b • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    conv_lhs => rw [hv]
    conv_rhs => rw [hv]
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_add, map_smul]
    have h10 : cl11MatrixAlgEquiv (CliffordAlgebra.ι q11Form (1, 0)) =
        j1Conjugation (cl11StandardEquiv
          (cliffordQ11FormEquivCl11MatrixQ11 (CliffordAlgebra.ι q11Form (1, 0)))) := by
      change cl11MatrixAlgEquiv (CliffordAlgebra.ι q11Form (1, 0)) =
        j1Conjugation (cl11StandardEquiv
          (CliffordAlgebra.equivOfIsometry q11FormIsometryEquivCl11MatrixQ11
            (CliffordAlgebra.ι q11Form (1, 0))))
      rw [CliffordAlgebra.equivOfIsometry_apply, CliffordAlgebra.map_apply_ι]
      change cl11MatrixAlgEquiv (CliffordAlgebra.ι q11Form (1, 0)) =
        j1Conjugation (cl11StandardEquiv (CliffordAlgebra.ι q11 (1, 0)))
      rw [cl11StandardEquiv_iota_pos, j1Conjugation_J1, cl11MatrixAlgEquiv_ι]
      ext i j; fin_cases i <;> fin_cases j <;> simp [cl11MatrixLinear, J1, Eminus]
    have h01 : cl11MatrixAlgEquiv (CliffordAlgebra.ι q11Form (0, 1)) =
        j1Conjugation (cl11StandardEquiv
          (cliffordQ11FormEquivCl11MatrixQ11 (CliffordAlgebra.ι q11Form (0, 1)))) := by
      change cl11MatrixAlgEquiv (CliffordAlgebra.ι q11Form (0, 1)) =
        j1Conjugation (cl11StandardEquiv
          (CliffordAlgebra.equivOfIsometry q11FormIsometryEquivCl11MatrixQ11
            (CliffordAlgebra.ι q11Form (0, 1))))
      rw [CliffordAlgebra.equivOfIsometry_apply, CliffordAlgebra.map_apply_ι]
      change cl11MatrixAlgEquiv (CliffordAlgebra.ι q11Form (0, 1)) =
        j1Conjugation (cl11StandardEquiv (CliffordAlgebra.ι q11 (0, 1)))
      rw [cl11StandardEquiv_iota_neg, j1Conjugation_apply]
      have hneg : J1 * (-Eminus) * J1 = Eminus := by
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [J1, Eminus, Matrix.mul_apply, Fin.sum_univ_two]
      rw [hneg, cl11MatrixAlgEquiv_ι]
      ext i j; fin_cases i <;> fin_cases j <;> simp [cl11MatrixLinear, J1, Eminus]
    change a • cl11MatrixAlgEquiv (CliffordAlgebra.ι q11Form (1, 0)) +
        b • cl11MatrixAlgEquiv (CliffordAlgebra.ι q11Form (0, 1)) =
      a • j1Conjugation (cl11StandardEquiv
          (cliffordQ11FormEquivCl11MatrixQ11 (CliffordAlgebra.ι q11Form (1, 0)))) +
        b • j1Conjugation (cl11StandardEquiv
          (cliffordQ11FormEquivCl11MatrixQ11 (CliffordAlgebra.ι q11Form (0, 1))))
    rw [h10, h01]
  exact AlgHom.congr_fun hhom x

/-- Full 3-basis reconciliation: `cl11MatrixAlgEquiv` equals `cl11EquivMat` conjugated by
`walshConjugation` then `j1Conjugation`. -/
theorem cl11MatrixAlgEquiv_eq_walsh_j1_cl11EquivMat :
    cl11MatrixAlgEquiv =
      ((cliffordQ11FormEquivCl11MatrixQ11.trans cl11EquivMat).trans walshConjugation).trans
        j1Conjugation :=
  cl11MatrixAlgEquiv_eq_j1Conj_trans_cl11StandardEquiv

/-- Explicit generator table across the 3 bases on `(1, 0)`, `(0, 1)`, and `ι(1,0) * ι(0,1)`. -/
theorem threeBasis_generator_table :
    (cl11EquivMat (CliffordAlgebra.ι q11 (1, 0)) = Eplus ∧
      cl11EquivMat (CliffordAlgebra.ι q11 (0, 1)) = Eminus ∧
      cl11EquivMat (CliffordAlgebra.ι q11 (1, 0) * CliffordAlgebra.ι q11 (0, 1)) = J1) ∧
    (cl11StandardEquiv (CliffordAlgebra.ι q11 (1, 0)) = J1 ∧
      cl11StandardEquiv (CliffordAlgebra.ι q11 (0, 1)) = -Eminus ∧
      cl11StandardEquiv (CliffordAlgebra.ι q11 (1, 0) * CliffordAlgebra.ι q11 (0, 1)) = Eplus) ∧
    (cl11MatrixAlgEquiv (CliffordAlgebra.ι q11Form (1, 0)) = J1 ∧
      cl11MatrixAlgEquiv (CliffordAlgebra.ι q11Form (0, 1)) = Eminus ∧
      cl11MatrixAlgEquiv (CliffordAlgebra.ι q11Form (1, 0) * CliffordAlgebra.ι q11Form (0, 1)) =
        -Eplus) := by
  refine ⟨⟨cl11EquivMat_iota_pos, cl11EquivMat_iota_neg, ?_⟩,
    ⟨cl11StandardEquiv_iota_pos, cl11StandardEquiv_iota_neg, ?_⟩,
    ⟨?_, ?_, ?_⟩⟩
  · rw [map_mul, cl11EquivMat_iota_pos, cl11EquivMat_iota_neg, Eplus_mul_Eminus]
  · rw [map_mul, cl11StandardEquiv_iota_pos, cl11StandardEquiv_iota_neg, mul_neg]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [J1, Eminus, Eplus]
  · rw [cl11MatrixAlgEquiv_ι]; ext i j; fin_cases i <;> fin_cases j <;> simp [cl11MatrixLinear]
  · rw [cl11MatrixAlgEquiv_ι]; ext i j; fin_cases i <;> fin_cases j <;> simp [cl11MatrixLinear]
  · rw [map_mul, cl11MatrixAlgEquiv_ι, cl11MatrixAlgEquiv_ι]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [cl11MatrixLinear, J1, Eminus, Eplus, Matrix.mul_apply, Fin.sum_univ_two]

end ThreeBasisReconciliation

/-! ## Section 2: Lane 1 ↔ Lane 3 Reconciliation (`Clsplit` ↔ `ClTower`) (`F3.1`) -/

section Lane1Lane3Reconciliation

open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.ClNN
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11GradedMorita
open InfoGeometry.Clifford.Cl11GradedTensorMorita
open InfoGeometry.Clifford.Cl11RecursiveUnrolling
open InfoGeometry.Clifford.Cl11SplitTowerMatrixEquiv
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordSuperGradeColimit
open InfoGeometry.Algebra.NoncommutativeCliffordColimitMassGapSynthesis

/-- Recursive grading involution on `ClTower A n` starting from an arbitrary involution `θ` on
a noncommutative real algebra `A`. -/
def clTowerParity (A : Type*) [Ring A] [Algebra ℝ A] (θ : A ≃ₐ[ℝ] A) :
    (n : ℕ) → ClTower A n ≃ₐ[ℝ] ClTower A n
  | 0 => θ
  | n + 1 => matrixAlgGrade (clTowerParity A θ n)

theorem clTowerParity_involutive (A : Type*) [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ) :
    Function.Involutive (clTowerParity A θ n) := by
  induction n with
  | zero => exact hθ
  | succ n ih => exact matrixAlgGrade_involutive (clTowerParity A θ n) ih

/-- Recursive `ZMod 2`-grading on `ClTower A n` induced by `clTowerParity`. -/
def clTowerGrading (A : Type*) [Ring A] [Algebra ℝ A] (θ : A ≃ₐ[ℝ] A)
    (hθ : Function.Involutive θ) (n : ℕ) : ZMod 2 → Submodule ℝ (ClTower A n) :=
  involutionGrading (clTowerParity A θ n) (clTowerParity_involutive A θ hθ n)

instance instGradedAlgebraClTower (A : Type*) [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ) :
    GradedAlgebra (clTowerGrading A θ hθ n) :=
  instGradedAlgebraInvolutionGrading (clTowerParity A θ n)
    (clTowerParity_involutive A θ hθ n)

/-- `Clsplit 0 ≃ₐ[ℝ] ℝ` because `SplitSpace 0` is subsingleton. -/
def splitZeroEquivReal : Clsplit 0 ≃ₐ[ℝ] ℝ :=
  AlgEquiv.ofAlgHom
    (CliffordAlgebra.lift (Qsplit 0) ⟨0, fun v => by
      have hv : v = 0 := Subsingleton.elim v 0
      rw [hv]; simp [Qsplit]⟩)
    (Algebra.ofId ℝ (Clsplit 0))
    (by
      apply AlgHom.ext; intro r
      simp)
    (by
      apply CliffordAlgebra.hom_ext
      apply LinearMap.ext; intro v
      have hv : v = 0 := Subsingleton.elim v 0
      rw [hv, map_zero, map_zero])

@[simp] theorem splitZeroEquivReal_algebraMap (r : ℝ) :
    splitZeroEquivReal (algebraMap ℝ (Clsplit 0) r) = r := by
  simp

private theorem zmod2_cases (i : ZMod 2) : i = 0 ∨ i = 1 := by
  revert i; decide

@[simp] private theorem units_neg_one_zmod2_zero : (-1 : ℤˣ) ^ (0 : ZMod 2) = 1 := rfl
@[simp] private theorem units_neg_one_zmod2_one : (-1 : ℤˣ) ^ (1 : ZMod 2) = -1 := rfl

private theorem evenOdd_involute_mem {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : QuadraticForm ℝ V} (i : ZMod 2) {x : CliffordAlgebra Q}
    (hx : x ∈ CliffordAlgebra.evenOdd Q i) :
    CliffordAlgebra.involute x = (-1 : ℤˣ) ^ i.val • x := by
  rcases zmod2_cases i with rfl | rfl
  · simp [CliffordAlgebra.involute_eq_of_mem_even hx]
  · simp [CliffordAlgebra.involute_eq_of_mem_odd hx, ZMod.val_one]

private theorem mem_evenOdd_zero_iff_involute {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (x : CliffordAlgebra Q) :
    x ∈ CliffordAlgebra.evenOdd Q 0 ↔ CliffordAlgebra.involute x = x := by
  constructor
  · exact fun hx => CliffordAlgebra.involute_eq_of_mem_even hx
  · intro hfix
    obtain ⟨e, o, heo, _⟩ :=
      Submodule.existsUnique_add_of_isCompl (CliffordAlgebra.evenOdd_isCompl (Q := Q)) x
    have hinvol : CliffordAlgebra.involute x = (e : CliffordAlgebra Q) - o := by
      rw [← heo, map_add, CliffordAlgebra.involute_eq_of_mem_even e.property,
        CliffordAlgebra.involute_eq_of_mem_odd o.property, sub_eq_add_neg]
    have hsum : (e : CliffordAlgebra Q) + o = (e : CliffordAlgebra Q) - o :=
      heo.trans (hfix.symm.trans hinvol)
    have honeg : (o : CliffordAlgebra Q) = -o :=
      add_left_cancel (by simpa only [sub_eq_add_neg] using hsum)
    have hozero : (o : CliffordAlgebra Q) = 0 := by
      have htwo : (2 : ℝ) • (o : CliffordAlgebra Q) = 0 := by
        rw [two_smul]; nth_rw 2 [honeg]; exact add_neg_cancel _
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    rw [← heo, hozero, add_zero]
    exact e.property

private theorem mem_evenOdd_one_iff_involute {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (x : CliffordAlgebra Q) :
    x ∈ CliffordAlgebra.evenOdd Q 1 ↔ CliffordAlgebra.involute x = -x := by
  constructor
  · exact fun hx => CliffordAlgebra.involute_eq_of_mem_odd hx
  · intro hneg
    obtain ⟨e, o, heo, _⟩ :=
      Submodule.existsUnique_add_of_isCompl (CliffordAlgebra.evenOdd_isCompl (Q := Q)) x
    have hinvol : CliffordAlgebra.involute x = (e : CliffordAlgebra Q) - o := by
      rw [← heo, map_add, CliffordAlgebra.involute_eq_of_mem_even e.property,
        CliffordAlgebra.involute_eq_of_mem_odd o.property, sub_eq_add_neg]
    have hneg_e : (e : CliffordAlgebra Q) = -(e : CliffordAlgebra Q) := by
      have hsum : (e : CliffordAlgebra Q) - o = -((e : CliffordAlgebra Q) + o) :=
        hinvol.symm.trans (hneg.trans (congrArg Neg.neg heo.symm))
      exact add_right_cancel (by simpa only [sub_eq_add_neg, neg_add] using hsum)
    have hezero : (e : CliffordAlgebra Q) = 0 := by
      have htwo : (2 : ℝ) • (e : CliffordAlgebra Q) = 0 := by
        rw [two_smul]; nth_rw 2 [hneg_e]; exact add_neg_cancel _
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    rw [← heo, hezero, zero_add]
    exact o.property

private theorem evenOdd_qsplit_zero_odd_eq_bot (x : Clsplit 0)
    (hx : x ∈ CliffordAlgebra.evenOdd (Qsplit 0) 1) : x = 0 := by
  have hinv := CliffordAlgebra.involute_eq_of_mem_odd hx
  have htriv : CliffordAlgebra.involute x = x := by
    rw [← splitZeroEquivReal.symm_apply_apply x]
    have hx' : splitZeroEquivReal.symm (splitZeroEquivReal x) =
        algebraMap ℝ (Clsplit 0) (splitZeroEquivReal x) := rfl
    rw [hx', AlgHom.commutes]
  rw [htriv] at hinv
  have htwo : (2 : ℝ) • x = 0 := by
    rw [two_smul]; nth_rw 2 [hinv]; exact add_neg_cancel _
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Stage-0 graded tensor unital algebra isomorphism `(evenOdd (Qsplit 0) ᵍ⊗[ℝ] 𝒜) ≃ₐ[ℝ] A`
for any `ZMod 2`-graded algebra `𝒜` over `A`. -/
def gradedSplitZeroTensorEquiv {A : Type*} [Ring A] [Algebra ℝ A]
    (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜] :
    (CliffordAlgebra.evenOdd (Qsplit 0) ᵍ⊗[ℝ] 𝒜) ≃ₐ[ℝ] A :=
  AlgEquiv.ofAlgHom
    (GradedTensorProduct.lift (CliffordAlgebra.evenOdd (Qsplit 0)) 𝒜
      ((Algebra.ofId ℝ A).comp splitZeroEquivReal.toAlgHom)
      (AlgHom.id ℝ A)
      (by
        intro i j a b
        rcases zmod2_cases i with rfl | rfl
        · simp only [AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.id_apply, mul_zero,
            units_neg_one_zmod2_zero, one_smul]
          change algebraMap ℝ A (splitZeroEquivReal (a : Clsplit 0)) * (b : A) =
            (b : A) * algebraMap ℝ A (splitZeroEquivReal (a : Clsplit 0))
          exact Algebra.commutes _ _
        · have ha0 : (a : Clsplit 0) = 0 := evenOdd_qsplit_zero_odd_eq_bot a a.prop
          simp [ha0]))
    (GradedTensorProduct.includeRight (CliffordAlgebra.evenOdd (Qsplit 0)) 𝒜)
    (by
      apply AlgHom.ext; intro a
      rw [AlgHom.comp_apply, GradedTensorProduct.includeRight_apply]
      change GradedTensorProduct.lift (CliffordAlgebra.evenOdd (Qsplit 0)) 𝒜 _ _ _
        ((1 : Clsplit 0) ᵍ⊗ₜ a) = a
      rw [GradedTensorProduct.lift_tmul]
      simp)
    (by
      apply GradedTensorProduct.algHom_ext
      · apply AlgHom.ext; intro x
        simp only [AlgHom.comp_apply, GradedTensorProduct.includeLeft_apply, AlgHom.id_apply]
        rw [GradedTensorProduct.lift_tmul, AlgHom.comp_apply, Algebra.ofId_apply,
          AlgHom.id_apply, mul_one, GradedTensorProduct.includeRight_apply,
          Algebra.algebraMap_eq_smul_one, gtmul_smul, ← smul_gtmul,
          ← Algebra.algebraMap_eq_smul_one]
        congr 1
        apply splitZeroEquivReal.injective
        simp
      · apply AlgHom.ext; intro a
        simp only [AlgHom.comp_apply, GradedTensorProduct.includeRight_apply, AlgHom.id_apply]
        rw [GradedTensorProduct.lift_tmul]
        simp)

@[simp] theorem gradedSplitZeroTensorEquiv_tmul {A : Type*} [Ring A] [Algebra ℝ A]
    (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜] (x : Clsplit 0) (a : A) :
    gradedSplitZeroTensorEquiv 𝒜 (x ᵍ⊗ₜ a) = splitZeroEquivReal x • a := by
  dsimp only [gradedSplitZeroTensorEquiv]
  rw [AlgEquiv.ofAlgHom_apply]
  rw [GradedTensorProduct.lift_tmul]
  simp [Algebra.smul_def]

@[simp] theorem gradedSplitZeroTensorEquiv_symm {A : Type*} [Ring A] [Algebra ℝ A]
    (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜] (a : A) :
    (gradedSplitZeroTensorEquiv 𝒜).symm a = (1 : Clsplit 0) ᵍ⊗ₜ a := rfl

private theorem zmod2_mul_add_sign (i j k : ZMod 2) :
    ((-1 : ℤˣ) ^ (j * i : ZMod 2).val : ℤ) * ((-1 : ℤˣ) ^ (k * i : ZMod 2).val : ℤ) =
      ((-1 : ℤˣ) ^ ((j + k) * i : ZMod 2).val : ℤ) := by
  rcases zmod2_cases i with rfl | rfl <;>
    rcases zmod2_cases j with rfl | rfl <;>
    rcases zmod2_cases k with rfl | rfl <;> decide

/-- Auxiliary grading on `𝒜 ᵍ⊗[ℝ] ℬ` as an `Submodule ℝ` family matching Mathlib's
`GradedTensorProduct.gradedAlgebra`. -/
def gradedTensorMapAlgHom {A B C D : Type*} [Ring A] [Ring B] [Ring C] [Ring D]
    [Algebra ℝ A] [Algebra ℝ B] [Algebra ℝ C] [Algebra ℝ D]
    (𝒜 : ZMod 2 → Submodule ℝ A) (ℬ : ZMod 2 → Submodule ℝ B)
    (𝒞 : ZMod 2 → Submodule ℝ C) (𝒟 : ZMod 2 → Submodule ℝ D)
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞] [GradedAlgebra 𝒟]
    (f : A →ₐ[ℝ] C) (g : B →ₐ[ℝ] D)
    (hf : ∀ i, ∀ a ∈ 𝒜 i, f a ∈ 𝒞 i)
    (hg : ∀ j, ∀ b ∈ ℬ j, g b ∈ 𝒟 j) :
    (𝒜 ᵍ⊗[ℝ] ℬ) →ₐ[ℝ] (𝒞 ᵍ⊗[ℝ] 𝒟) :=
  GradedTensorProduct.lift 𝒜 ℬ
    ((GradedTensorProduct.includeLeft 𝒞 𝒟).comp f)
    ((GradedTensorProduct.includeRight 𝒞 𝒟).comp g)
    (by
      intro i j a b
      change ((f (a : A) ᵍ⊗ₜ (1 : D)) * ((1 : C) ᵍ⊗ₜ g (b : B))) =
        (-1 : ℤˣ) ^ (j * i) • (((1 : C) ᵍ⊗ₜ g (b : B)) * (f (a : A) ᵍ⊗ₜ (1 : D)))
      let a' : 𝒞 i := ⟨f a, hf i a a.prop⟩
      let b' : 𝒟 j := ⟨g b, hg j b b.prop⟩
      have h1 : ((f (a : A) ᵍ⊗ₜ (1 : D) : 𝒞 ᵍ⊗[ℝ] 𝒟) * ((1 : C) ᵍ⊗ₜ g (b : B))) =
          (f (a : A) ᵍ⊗ₜ g (b : B)) :=
        GradedTensorProduct.tmul_one_mul_one_tmul 𝒞 𝒟 (f a) (g b)
      have h2 := GradedTensorProduct.tmul_coe_mul_coe_tmul 𝒞 𝒟 (1 : C) b' a' (1 : D)
      simp only [a', b', one_mul, mul_one] at h2
      rw [h1, h2, smul_smul, Int.units_mul_self, one_smul])

@[simp] theorem gradedTensorMapAlgHom_tmul {A B C D : Type*} [Ring A] [Ring B] [Ring C] [Ring D]
    [Algebra ℝ A] [Algebra ℝ B] [Algebra ℝ C] [Algebra ℝ D]
    (𝒜 : ZMod 2 → Submodule ℝ A) (ℬ : ZMod 2 → Submodule ℝ B)
    (𝒞 : ZMod 2 → Submodule ℝ C) (𝒟 : ZMod 2 → Submodule ℝ D)
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞] [GradedAlgebra 𝒟]
    (f : A →ₐ[ℝ] C) (g : B →ₐ[ℝ] D)
    (hf : ∀ i, ∀ a ∈ 𝒜 i, f a ∈ 𝒞 i)
    (hg : ∀ j, ∀ b ∈ ℬ j, g b ∈ 𝒟 j) (a : A) (b : B) :
    gradedTensorMapAlgHom 𝒜 ℬ 𝒞 𝒟 f g hf hg (a ᵍ⊗ₜ b) = f a ᵍ⊗ₜ g b := by
  dsimp [gradedTensorMapAlgHom]
  simp only [GradedTensorProduct.includeLeft_apply, GradedTensorProduct.includeRight_apply]
  exact GradedTensorProduct.tmul_one_mul_one_tmul 𝒞 𝒟 (f a) (g b)

private def gradedTensorMapAlgEquiv_comp_left {A B C D : Type*}
    [Ring A] [Ring B] [Ring C] [Ring D] [Algebra ℝ A] [Algebra ℝ B] [Algebra ℝ C] [Algebra ℝ D]
    (𝒜 : ZMod 2 → Submodule ℝ A) (ℬ : ZMod 2 → Submodule ℝ B)
    (𝒞 : ZMod 2 → Submodule ℝ C) (𝒟 : ZMod 2 → Submodule ℝ D)
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞] [GradedAlgebra 𝒟]
    (eA : A ≃ₐ[ℝ] C) (eB : B ≃ₐ[ℝ] D)
    (hf : ∀ i, ∀ a ∈ 𝒜 i, eA a ∈ 𝒞 i) (hf' : ∀ i, ∀ c ∈ 𝒞 i, eA.symm c ∈ 𝒜 i)
    (hg : ∀ j, ∀ b ∈ ℬ j, eB b ∈ 𝒟 j) (hg' : ∀ j, ∀ d ∈ 𝒟 j, eB.symm d ∈ ℬ j) :
    (𝒜 ᵍ⊗[ℝ] ℬ) ≃ₐ[ℝ] (𝒞 ᵍ⊗[ℝ] 𝒟) :=
  let fwd := gradedTensorMapAlgHom 𝒜 ℬ 𝒞 𝒟 eA.toAlgHom eB.toAlgHom
    (fun i a ha => by simpa using hf i a ha) (fun j b hb => by simpa using hg j b hb)
  let bwd := gradedTensorMapAlgHom 𝒞 𝒟 𝒜 ℬ eA.symm.toAlgHom eB.symm.toAlgHom
    (fun i c hc => by simpa using hf' i c hc) (fun j d hd => by simpa using hg' j d hd)
  AlgEquiv.ofAlgHom fwd bwd
    (by
      apply GradedTensorProduct.algHom_ext
      · apply AlgHom.ext; intro c
        change fwd (bwd (c ᵍ⊗ₜ (1 : D))) = c ᵍ⊗ₜ (1 : D)
        dsimp only [fwd, bwd]
        rw [gradedTensorMapAlgHom_tmul, gradedTensorMapAlgHom_tmul]
        simp
      · apply AlgHom.ext; intro d
        change fwd (bwd ((1 : C) ᵍ⊗ₜ d)) = (1 : C) ᵍ⊗ₜ d
        dsimp only [fwd, bwd]
        rw [gradedTensorMapAlgHom_tmul, gradedTensorMapAlgHom_tmul]
        simp)
    (by
      apply GradedTensorProduct.algHom_ext
      · apply AlgHom.ext; intro a
        change bwd (fwd (a ᵍ⊗ₜ (1 : B))) = a ᵍ⊗ₜ (1 : B)
        dsimp only [fwd, bwd]
        rw [gradedTensorMapAlgHom_tmul, gradedTensorMapAlgHom_tmul]
        simp
      · apply AlgHom.ext; intro b
        change bwd (fwd ((1 : A) ᵍ⊗ₜ b)) = (1 : A) ᵍ⊗ₜ b
        dsimp only [fwd, bwd]
        rw [gradedTensorMapAlgHom_tmul, gradedTensorMapAlgHom_tmul]
        simp)

private theorem cl11StandardEquiv_preserves_matrixGrading {i : ZMod 2}
    {x : CliffordAlgebra q11} (hx : x ∈ CliffordAlgebra.evenOdd q11 i) :
    cl11StandardEquiv x ∈ matrixGrading i := by
  rcases zmod2_cases i with hi | hi
  · subst i
    change GradedTensorWeylBridge.matrixParity (cl11StandardEquiv x) = cl11StandardEquiv x
    have h := cl11StandardEquiv_grade x
    change cl11StandardEquiv (CliffordAlgebra.involute x) = _ at h
    rw [CliffordAlgebra.involute_eq_of_mem_even hx] at h
    simpa [GradedTensorWeylBridge.matrixParity,
      InfoGeometry.Clifford.Cl11GradedTensorMorita.matrixAlgGrade] using h.symm
  · subst i
    change GradedTensorWeylBridge.matrixParity (cl11StandardEquiv x) = -cl11StandardEquiv x
    have h := cl11StandardEquiv_grade x
    change cl11StandardEquiv (CliffordAlgebra.involute x) = _ at h
    rw [CliffordAlgebra.involute_eq_of_mem_odd hx, map_neg] at h
    simpa [GradedTensorWeylBridge.matrixParity,
      InfoGeometry.Clifford.Cl11GradedTensorMorita.matrixAlgGrade] using h.symm

private theorem cl11StandardEquiv_symm_preserves_matrixGrading {i : ZMod 2}
    {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A ∈ matrixGrading i) :
    cl11StandardEquiv.symm A ∈ CliffordAlgebra.evenOdd q11 i := by
  rcases zmod2_cases i with hi | hi
  · subst i
    change GradedTensorWeylBridge.matrixParity A = A at hA
    apply (mem_evenOdd_zero_iff_involute q11 _).2
    apply cl11StandardEquiv.injective
    have h := cl11StandardEquiv_grade (cl11StandardEquiv.symm A)
    rw [AlgEquiv.apply_symm_apply] at h
    have hA' : InfoGeometry.OperatorAlgebra.GradedMatrixMorita.matrixGrade
        (RingEquiv.refl ℝ) A = A := by
      simpa [GradedTensorWeylBridge.matrixParity,
        InfoGeometry.Clifford.Cl11GradedTensorMorita.matrixAlgGrade] using hA
    calc
      cl11StandardEquiv (CliffordAlgebra.involute (cl11StandardEquiv.symm A)) =
          InfoGeometry.OperatorAlgebra.GradedMatrixMorita.matrixGrade
            (RingEquiv.refl ℝ) A := h
      _ = A := hA'
      _ = cl11StandardEquiv (cl11StandardEquiv.symm A) := by simp
  · subst i
    change GradedTensorWeylBridge.matrixParity A = -A at hA
    apply (mem_evenOdd_one_iff_involute q11 _).2
    apply cl11StandardEquiv.injective
    have h := cl11StandardEquiv_grade (cl11StandardEquiv.symm A)
    rw [AlgEquiv.apply_symm_apply] at h
    have hA' : InfoGeometry.OperatorAlgebra.GradedMatrixMorita.matrixGrade
        (RingEquiv.refl ℝ) A = -A := by
      simpa [GradedTensorWeylBridge.matrixParity,
        InfoGeometry.Clifford.Cl11GradedTensorMorita.matrixAlgGrade] using hA
    calc
      cl11StandardEquiv (CliffordAlgebra.involute (cl11StandardEquiv.symm A)) =
          InfoGeometry.OperatorAlgebra.GradedMatrixMorita.matrixGrade
            (RingEquiv.refl ℝ) A := h
      _ = -A := hA'
      _ = cl11StandardEquiv (-cl11StandardEquiv.symm A) := by simp

/-- The native Koszul product of the repository's two checkerboard-graded
real matrix factors is identified with the existing `Cl(1,1)` graded head
tensor the second real matrix factor. This is the grading-preserving change
of first factor needed before applying the owned Clifford-head Morita map. -/
noncomputable def twoMatrixGradedTensorToCl11Tensor :
    twoMatrixGradedTensor ≃ₐ[ℝ]
      (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] matrixGrading) :=
  gradedTensorMapAlgEquiv_comp_left matrixGrading matrixGrading
    (CliffordAlgebra.evenOdd q11) matrixGrading
    cl11StandardEquiv.symm
    (AlgEquiv.refl : Matrix (Fin 2) (Fin 2) ℝ ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ)
    (fun _ _ h => cl11StandardEquiv_symm_preserves_matrixGrading h)
    (fun _ _ h => cl11StandardEquiv_preserves_matrixGrading h)
    (fun _ _ h => h) (fun _ _ h => h)

@[simp] theorem twoMatrixGradedTensorToCl11Tensor_tmul
    (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    twoMatrixGradedTensorToCl11Tensor (A ᵍ⊗ₜ[ℝ] B) =
      (cl11StandardEquiv.symm A) ᵍ⊗ₜ[ℝ] B := by
  simp [twoMatrixGradedTensorToCl11Tensor, gradedTensorMapAlgEquiv_comp_left,
    gradedTensorMapAlgHom_tmul]

/-- The actual two-factor real matrix superalgebra acts on the nested `2 × 2`
block matrix carrier through its graded Morita representation. The Koszul sign
is retained by the preceding graded-factor equivalence. -/
noncomputable def twoMatrixGradedTensorMoritaEquiv :
    twoMatrixGradedTensor ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℝ) :=
  twoMatrixGradedTensorToCl11Tensor.trans
    (tensorMatrixEquiv matrixGrading GradedTensorWeylBridge.matrixParity
      (fun {_} h => involutionGrading_even GradedTensorWeylBridge.matrixParity
        GradedTensorWeylBridge.matrixParity_involutive h)
      (fun {_} h => involutionGrading_odd GradedTensorWeylBridge.matrixParity
        GradedTensorWeylBridge.matrixParity_involutive h))

/-- On pure tensors this equivalence first sends the left matrix factor through
the proved graded `Cl(1,1)` representation, then uses the owned graded Morita
matrix action. -/
theorem twoMatrixGradedTensorMoritaEquiv_tmul
    (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    twoMatrixGradedTensorMoritaEquiv (A ᵍ⊗ₜ[ℝ] B) =
      tensorMatrixEquiv matrixGrading GradedTensorWeylBridge.matrixParity
        (fun {_} h => involutionGrading_even GradedTensorWeylBridge.matrixParity
          GradedTensorWeylBridge.matrixParity_involutive h)
        (fun {_} h => involutionGrading_odd GradedTensorWeylBridge.matrixParity
          GradedTensorWeylBridge.matrixParity_involutive h)
        ((cl11StandardEquiv.symm A) ᵍ⊗ₜ[ℝ] B) := by
  rw [twoMatrixGradedTensorMoritaEquiv, AlgEquiv.trans_apply,
    twoMatrixGradedTensorToCl11Tensor_tmul, tensorMatrixEquiv_apply,
    tensorToMatrix_tmul, tail_apply]

/-- The second odd matrix factor acquires the first factor's parity matrix in
the nested block representation. This is the explicit Koszul/Jordan–Wigner
sign that distinguishes the supertensor action from an ordinary tensor map. -/
theorem twoMatrixGradedTensorMoritaEquiv_annihilation₁ :
    twoMatrixGradedTensorMoritaEquiv annihilation₁ =
      !![matrixE01, 0; 0, GradedTensorWeylBridge.matrixParity matrixE01] := by
  rw [annihilation₁, twoMatrixGradedTensorMoritaEquiv_tmul]
  have hOne : cl11StandardEquiv.symm (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := map_one _
  rw [hOne]
  exact tensorMatrixEquiv_tail matrixGrading GradedTensorWeylBridge.matrixParity
    (fun {_} h => involutionGrading_even GradedTensorWeylBridge.matrixParity
      GradedTensorWeylBridge.matrixParity_involutive h)
    (fun {_} h => involutionGrading_odd GradedTensorWeylBridge.matrixParity
      GradedTensorWeylBridge.matrixParity_involutive h) matrixE01

/-- The second mode creator has the corresponding nested block form. This
explicit owner formula is useful for checking parity on the actual second
factor, rather than inferring it from a similarly named first-mode theorem. -/
theorem twoMatrixGradedTensorMoritaEquiv_creation₁ :
    twoMatrixGradedTensorMoritaEquiv creation₁ =
      !![matrixE10, 0; 0, GradedTensorWeylBridge.matrixParity matrixE10] := by
  rw [creation₁, twoMatrixGradedTensorMoritaEquiv_tmul]
  have hOne : cl11StandardEquiv.symm (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := map_one _
  rw [hOne]
  exact tensorMatrixEquiv_tail matrixGrading GradedTensorWeylBridge.matrixParity
    (fun {_} h => involutionGrading_even GradedTensorWeylBridge.matrixParity
      GradedTensorWeylBridge.matrixParity_involutive h)
    (fun {_} h => involutionGrading_odd GradedTensorWeylBridge.matrixParity
      GradedTensorWeylBridge.matrixParity_involutive h) matrixE10

private theorem clifford_evenOdd_supercommute {V R : Type*}
    [AddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V} [Ring R] [Algebra ℝ R]
    (f : CliffordAlgebra Q →ₐ[ℝ] R) (b : R) (j : ZMod 2)
    (hgen : ∀ v : V, f (CliffordAlgebra.ι Q v) * b = (-1 : ℤˣ) ^ j.val • (b * f (CliffordAlgebra.ι Q v))) :
    ∀ (i : ZMod 2) (x : CliffordAlgebra Q), x ∈ CliffordAlgebra.evenOdd Q i →
      f x * b = (-1 : ℤˣ) ^ (j * i) • (b * f x) := by
  intro i x hx
  rcases zmod2_cases i with rfl | rfl
  · simp only [mul_zero, units_neg_one_zmod2_zero, one_smul]
    induction x, hx using CliffordAlgebra.even_induction with
    | algebraMap r =>
        rw [AlgHom.commutes, Algebra.commutes]
    | add x y hx hy ihx ihy =>
        rw [map_add, add_mul, mul_add, ihx, ihy]
    | ι_mul_ι_mul m₁ m₂ x hx ih =>
        rw [map_mul, map_mul, mul_assoc, mul_assoc, ih,
          ← mul_assoc (f (CliffordAlgebra.ι Q m₂)), hgen m₂,
          smul_mul_assoc, mul_smul_comm, mul_assoc,
          ← mul_assoc (f (CliffordAlgebra.ι Q m₁)), hgen m₁,
          smul_mul_assoc, smul_smul, ← pow_add, ← two_mul, pow_mul, Int.units_sq,
          one_pow, one_smul, mul_assoc, ← mul_assoc (f (CliffordAlgebra.ι Q m₁))]
  · simp only [mul_one]
    rcases zmod2_cases j with rfl | rfl
    · simp only [ZMod.val_zero, pow_zero, one_smul, units_neg_one_zmod2_zero] at hgen ⊢
      induction x, hx using CliffordAlgebra.odd_induction with
      | ι v => exact hgen v
      | add x y hx hy ihx ihy => rw [map_add, add_mul, mul_add, ihx, ihy]
      | ι_mul_ι_mul m₁ m₂ x hx ih =>
          rw [map_mul, map_mul, mul_assoc, mul_assoc, ih,
            ← mul_assoc (f (CliffordAlgebra.ι Q m₂)), hgen m₂,
            mul_assoc, ← mul_assoc (f (CliffordAlgebra.ι Q m₁)), hgen m₁, mul_assoc, mul_assoc]
    · simp only [ZMod.val_one, pow_one, units_neg_one_zmod2_one, Units.neg_smul, one_smul] at hgen ⊢
      induction x, hx using CliffordAlgebra.odd_induction with
      | ι v => exact hgen v
      | add x y hx hy ihx ihy => rw [map_add, add_mul, mul_add, ihx, ihy, neg_add]
      | ι_mul_ι_mul m₁ m₂ x hx ih =>
          rw [map_mul, map_mul, mul_assoc, mul_assoc, ih, mul_neg,
            ← mul_assoc (f (CliffordAlgebra.ι Q m₂)), hgen m₂,
            neg_mul, mul_neg, mul_neg, neg_neg, mul_assoc,
            ← mul_assoc (f (CliffordAlgebra.ι Q m₁)), hgen m₁,
            neg_mul, mul_assoc, ← mul_assoc (f (CliffordAlgebra.ι Q m₁))]

private def towerParityAux (A : Type*) [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ) :
    (CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ) →ₐ[ℝ]
      (CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ) :=
  GradedTensorProduct.lift (CliffordAlgebra.evenOdd (Qsplit n)) (involutionGrading θ hθ)
    ((GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd (Qsplit n)) (involutionGrading θ hθ)).comp
      (CliffordAlgebra.involute : Clsplit n →ₐ[ℝ] Clsplit n))
    ((GradedTensorProduct.includeRight (CliffordAlgebra.evenOdd (Qsplit n)) (involutionGrading θ hθ)).comp
      θ.toAlgHom)
    (fun {i j} x a => by
      have hx_mem : CliffordAlgebra.involute (x : Clsplit n) ∈ CliffordAlgebra.evenOdd (Qsplit n) i := by
        rcases zmod2_cases i with rfl | rfl
        · rw [CliffordAlgebra.involute_eq_of_mem_even x.prop]; exact x.prop
        · rw [CliffordAlgebra.involute_eq_of_mem_odd x.prop]; exact Submodule.neg_mem _ x.prop
      have ha_mem : θ (a : A) ∈ involutionGrading θ hθ j := by
        rcases zmod2_cases j with rfl | rfl
        · change θ (θ (a : A)) = θ (a : A)
          rw [hθ (a : A), involutionGrading_even θ hθ a.prop]
        · change θ (θ (a : A)) = -(θ (a : A))
          rw [hθ (a : A), involutionGrading_odd θ hθ a.prop, neg_neg]
      let x' : CliffordAlgebra.evenOdd (Qsplit n) i := ⟨_, hx_mem⟩
      let a' : involutionGrading θ hθ j := ⟨_, ha_mem⟩
      have h1 : ((CliffordAlgebra.involute (x : Clsplit n) ᵍ⊗ₜ (1 : A) :
            CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ) *
            ((1 : Clsplit n) ᵍ⊗ₜ θ (a : A))) =
          (CliffordAlgebra.involute (x : Clsplit n) ᵍ⊗ₜ θ (a : A)) :=
        GradedTensorProduct.tmul_one_mul_one_tmul _ _ _ _
      have h2 := GradedTensorProduct.tmul_coe_mul_coe_tmul
        (CliffordAlgebra.evenOdd (Qsplit n)) (involutionGrading θ hθ)
        (1 : Clsplit n) a' x' (1 : A)
      simp only [x', a', one_mul, mul_one] at h2
      change (CliffordAlgebra.involute (x : Clsplit n) ᵍ⊗ₜ (1 : A)) * ((1 : Clsplit n) ᵍ⊗ₜ θ (a : A)) =
        (-1 : ℤˣ) ^ (j * i) • (((1 : Clsplit n) ᵍ⊗ₜ θ (a : A)) * (CliffordAlgebra.involute (x : Clsplit n) ᵍ⊗ₜ (1 : A)))
      rw [h1, h2, smul_smul, Int.units_mul_self, one_smul])

private theorem towerParityAux_tmul (A : Type*) [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ) (x : Clsplit n) (a : A) :
    towerParityAux A θ hθ n (x ᵍ⊗ₜ a) = CliffordAlgebra.involute x ᵍ⊗ₜ θ a := by
  change GradedTensorProduct.lift (CliffordAlgebra.evenOdd (Qsplit n)) (involutionGrading θ hθ) _ _ _ (x ᵍ⊗ₜ a) = _
  rw [GradedTensorProduct.lift_tmul]
  simp only [AlgHom.comp_apply, GradedTensorProduct.includeLeft_apply,
    GradedTensorProduct.includeRight_apply]
  exact GradedTensorProduct.tmul_one_mul_one_tmul _ _ _ _

private theorem towerParityAux_involutive (A : Type*) [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ) (z : CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ) :
    towerParityAux A θ hθ n (towerParityAux A θ hθ n z) = z := by
  obtain ⟨t, rfl⟩ := (GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd (Qsplit n)) (involutionGrading θ hθ)).surjective z
  induction t using TensorProduct.inductionOn with
  | tmul x a =>
      change towerParityAux A θ hθ n (towerParityAux A θ hθ n (x ᵍ⊗ₜ a)) = x ᵍ⊗ₜ a
      rw [towerParityAux_tmul, towerParityAux_tmul, CliffordAlgebra.involute_involute, hθ a]
  | add u v hu hv =>
      simp only [map_add] at hu hv ⊢
      rw [hu, hv]

private def headTensorToClTowerStep (A : Type*) [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ)
    (ih : (CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ) ≃ₐ[ℝ] ClTower A n)
    (hih : ∀ z, clTowerParity A θ n (ih z) = ih (towerParityAux A θ hθ n z)) :
    Clsplit (n + 1) →ₐ[ℝ] (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] clTowerGrading A θ hθ n) :=
  CliffordAlgebra.lift (Qsplit (n + 1))
    ⟨({ toFun := fun v =>
          (CliffordAlgebra.ι q11 v.1) ᵍ⊗ₜ (1 : ClTower A n) +
            (1 : CliffordAlgebra q11) ᵍ⊗ₜ (ih ((CliffordAlgebra.ι (Qsplit n) v.2) ᵍ⊗ₜ (1 : A)))
        map_add' := fun u v => by
          simp only [Prod.fst_add, Prod.snd_add, map_add]
          rw [add_gtmul, add_gtmul, map_add, gtmul_add]
          abel
        map_smul' := fun r v => by
          simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply]
          rw [smul_gtmul, smul_gtmul, map_smul, gtmul_smul, smul_add] } :
        SplitSpace (n + 1) →ₗ[ℝ]
          (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] clTowerGrading A θ hθ n)),
      fun v => by
        let X : CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] clTowerGrading A θ hθ n :=
          (CliffordAlgebra.ι q11 v.1) ᵍ⊗ₜ (1 : ClTower A n)
        let Y : CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] clTowerGrading A θ hθ n :=
          (1 : CliffordAlgebra q11) ᵍ⊗ₜ (ih ((CliffordAlgebra.ι (Qsplit n) v.2) ᵍ⊗ₜ (1 : A)))
        have hY_odd : ih ((CliffordAlgebra.ι (Qsplit n) v.2) ᵍ⊗ₜ (1 : A)) ∈
            clTowerGrading A θ hθ n 1 := by
          change clTowerParity A θ n (ih ((CliffordAlgebra.ι (Qsplit n) v.2) ᵍ⊗ₜ (1 : A))) =
            -(ih ((CliffordAlgebra.ι (Qsplit n) v.2) ᵍ⊗ₜ (1 : A)))
          rw [hih, towerParityAux_tmul, CliffordAlgebra.involute_ι, map_one,
            neg_gtmul, map_neg]
        have hanti : X * Y = -(Y * X) := by
          let x₀ : CliffordAlgebra.evenOdd q11 1 := ⟨CliffordAlgebra.ι q11 v.1, CliffordAlgebra.ι_mem_evenOdd_one q11 v.1⟩
          let y₀ : clTowerGrading A θ hθ n 1 := ⟨ih ((CliffordAlgebra.ι (Qsplit n) v.2) ᵍ⊗ₜ 1), hY_odd⟩
          have h1 : X * Y = (CliffordAlgebra.ι q11 v.1) ᵍ⊗ₜ
              (ih ((CliffordAlgebra.ι (Qsplit n) v.2) ᵍ⊗ₜ (1 : A))) :=
            GradedTensorProduct.tmul_one_mul_one_tmul _ _ _ _
          have h2 := GradedTensorProduct.tmul_coe_mul_coe_tmul
            (CliffordAlgebra.evenOdd q11) (clTowerGrading A θ hθ n)
            (1 : CliffordAlgebra q11) y₀ x₀ (1 : ClTower A n)
          simp only [x₀, y₀, one_mul, mul_one, mul_one, units_neg_one_zmod2_one,
            Units.neg_smul, one_smul] at h2
          rw [h1]
          change _ = -(Y * X)
          rw [h2, neg_neg]
        have hX2 : X * X = algebraMap ℝ _ (q11 v.1) := by
          have hX2' := GradedTensorProduct.tmul_coe_mul_coe_tmul (CliffordAlgebra.evenOdd q11)
            (clTowerGrading A θ hθ n)
            (CliffordAlgebra.ι q11 v.1) (1 : clTowerGrading A θ hθ n 0)
            ⟨CliffordAlgebra.ι q11 v.1, CliffordAlgebra.ι_mem_evenOdd_one q11 v.1⟩ (1 : ClTower A n)
          have hX2'' : X * X = (CliffordAlgebra.ι q11 v.1 * CliffordAlgebra.ι q11 v.1) ᵍ⊗ₜ (1 : ClTower A n) := by
            simpa only [X, show ((1 : clTowerGrading A θ hθ n 0) : ClTower A n) = 1 from rfl,
              mul_one, zero_mul, units_neg_one_zmod2_zero, one_smul] using hX2'
          rw [hX2'', CliffordAlgebra.ι_sq_scalar, Algebra.algebraMap_eq_smul_one, smul_gtmul]
          rw [Algebra.algebraMap_eq_smul_one]
          rfl
        have hY2 : Y * Y = algebraMap ℝ _ (Qsplit n v.2) := by
          have hY2' := GradedTensorProduct.tmul_coe_mul_coe_tmul (CliffordAlgebra.evenOdd q11)
            (clTowerGrading A θ hθ n)
            (1 : CliffordAlgebra q11) ⟨_, hY_odd⟩
            (1 : CliffordAlgebra.evenOdd q11 0) (ih ((CliffordAlgebra.ι (Qsplit n) v.2) ᵍ⊗ₜ (1 : A)))
          have hY2'' : Y * Y = (1 : CliffordAlgebra q11) ᵍ⊗ₜ
              (ih ((CliffordAlgebra.ι (Qsplit n) v.2 ᵍ⊗ₜ (1 : A)) *
                (CliffordAlgebra.ι (Qsplit n) v.2 ᵍ⊗ₜ (1 : A)))) := by
            simpa only [Y, show ((1 : CliffordAlgebra.evenOdd q11 0) : CliffordAlgebra q11) = 1 from rfl,
              one_mul, mul_zero, units_neg_one_zmod2_zero, one_smul, ← map_mul] using hY2'
          have hsq' := GradedTensorProduct.tmul_coe_mul_coe_tmul (CliffordAlgebra.evenOdd (Qsplit n))
            (involutionGrading θ hθ)
            (CliffordAlgebra.ι (Qsplit n) v.2) (1 : involutionGrading θ hθ 0)
            ⟨CliffordAlgebra.ι (Qsplit n) v.2, CliffordAlgebra.ι_mem_evenOdd_one _ _⟩ (1 : A)
          have hsq : ((CliffordAlgebra.ι (Qsplit n) v.2 ᵍ⊗ₜ (1 : A) :
              CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ) *
              (CliffordAlgebra.ι (Qsplit n) v.2 ᵍ⊗ₜ (1 : A))) =
              algebraMap ℝ _ (Qsplit n v.2) := by
            have hsq'' : ((CliffordAlgebra.ι (Qsplit n) v.2 ᵍ⊗ₜ (1 : A) :
                CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ) *
                (CliffordAlgebra.ι (Qsplit n) v.2 ᵍ⊗ₜ (1 : A))) =
                (CliffordAlgebra.ι (Qsplit n) v.2 * CliffordAlgebra.ι (Qsplit n) v.2) ᵍ⊗ₜ (1 : A) := by
              simpa only [show ((1 : involutionGrading θ hθ 0) : A) = 1 from rfl,
                mul_one, zero_mul, units_neg_one_zmod2_zero, one_smul] using hsq'
            rw [hsq'', CliffordAlgebra.ι_sq_scalar, Algebra.algebraMap_eq_smul_one, smul_gtmul]
            rw [Algebra.algebraMap_eq_smul_one]
            rfl
          rw [hY2'', hsq, AlgEquiv.commutes]
          rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, gtmul_smul]
          rfl
        change (X + Y) * (X + Y) = algebraMap ℝ _ (Qsplit (n + 1) v)
        rw [add_mul, mul_add, mul_add, hanti, hX2, hY2, Qsplit_succ_apply, map_add,
          InfoGeometry.CliffordTower.Q11, ← q11_eq_splitQ11]
        abel⟩

@[simp] private theorem headTensorToClTowerStep_ι (A : Type*) [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ)
    (ih : (CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ) ≃ₐ[ℝ] ClTower A n)
    (hih : ∀ z, clTowerParity A θ n (ih z) = ih (towerParityAux A θ hθ n z))
    (v : SplitSpace (n + 1)) :
    headTensorToClTowerStep A θ hθ n ih hih (CliffordAlgebra.ι (Qsplit (n + 1)) v) =
      (CliffordAlgebra.ι q11 v.1) ᵍ⊗ₜ (1 : ClTower A n) +
        (1 : CliffordAlgebra q11) ᵍ⊗ₜ (ih ((CliffordAlgebra.ι (Qsplit n) v.2) ᵍ⊗ₜ (1 : A))) := by
  simp [headTensorToClTowerStep]

private theorem gradedLift_includeLeft {A B C : Type*} [Ring A] [Ring B] [Ring C]
    [Algebra ℝ A] [Algebra ℝ B] [Algebra ℝ C]
    (𝒜 : ZMod 2 → Submodule ℝ A) (ℬ : ZMod 2 → Submodule ℝ B)
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (f : A →ₐ[ℝ] C) (g : B →ₐ[ℝ] C)
    (h : ∀ ⦃i j⦄ (a : 𝒜 i) (b : ℬ j), f a * g b = (-1 : ℤˣ) ^ (j * i) • (g b * f a))
    (a : A) :
    GradedTensorProduct.lift 𝒜 ℬ f g h (GradedTensorProduct.includeLeft 𝒜 ℬ a) = f a := by
  change GradedTensorProduct.lift 𝒜 ℬ f g h (a ᵍ⊗ₜ 1) = f a
  rw [GradedTensorProduct.lift_tmul, map_one, mul_one]

private theorem gradedLift_includeRight {A B C : Type*} [Ring A] [Ring B] [Ring C]
    [Algebra ℝ A] [Algebra ℝ B] [Algebra ℝ C]
    (𝒜 : ZMod 2 → Submodule ℝ A) (ℬ : ZMod 2 → Submodule ℝ B)
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (f : A →ₐ[ℝ] C) (g : B →ₐ[ℝ] C)
    (h : ∀ ⦃i j⦄ (a : 𝒜 i) (b : ℬ j), f a * g b = (-1 : ℤˣ) ^ (j * i) • (g b * f a))
    (b : B) :
    GradedTensorProduct.lift 𝒜 ℬ f g h (GradedTensorProduct.includeRight 𝒜 ℬ b) = g b := by
  change GradedTensorProduct.lift 𝒜 ℬ f g h (1 ᵍ⊗ₜ b) = g b
  rw [GradedTensorProduct.lift_tmul, map_one, one_mul]

private theorem splitCliffordStep_ι (n : ℕ) (u : SplitSpace n) :
    splitCliffordStep n (CliffordAlgebra.ι (Qsplit n) u) =
      CliffordAlgebra.ι (Qsplit (n + 1)) ((0, 0), u) := by
  rw [← InfoGeometry.Canonical.SplitCliffordExteriorTowerBridge.stageCliffordMap_eq_canonicalStep,
    InfoGeometry.Clifford.ClNNSuperGrassmannianBridge.splitStageCliffordMap_generator_eq_gammaTail]
  rfl

private theorem headTensorEquiv_splitCliffordStep (n : ℕ) (x : Clsplit n) :
    headTensorEquiv n (splitCliffordStep n x) = (1 : CliffordAlgebra q11) ᵍ⊗ₜ x := by
  have hhom :
      (headTensorEquiv n).toAlgHom.comp (splitCliffordStep n) =
        GradedTensorProduct.includeRight (CliffordAlgebra.evenOdd q11) (CliffordAlgebra.evenOdd (Qsplit n)) := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext; intro u
    simp only [AlgHom.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      GradedTensorProduct.includeRight_apply]
    rw [splitCliffordStep_ι]
    change headTensorEquiv n (CliffordAlgebra.ι (Qsplit (n + 1)) ((0, 0), u)) = _
    rw [headTensorEquiv_ι, show (((0 : ℝ), (0 : ℝ)), u).1 = (0 : ℝ × ℝ) from rfl,
      map_zero, zero_gtmul, zero_add]
  exact AlgHom.congr_fun hhom x

private def clSplitGradedTensorStep_fwd (A : Type*) [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ)
    (ih : (CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ) ≃ₐ[ℝ] ClTower A n)
    (hih : ∀ z, clTowerParity A θ n (ih z) = ih (towerParityAux A θ hθ n z)) :
    (CliffordAlgebra.evenOdd (Qsplit (n + 1)) ᵍ⊗[ℝ] involutionGrading θ hθ) →ₐ[ℝ]
      (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] clTowerGrading A θ hθ n) :=
  let f := headTensorToClTowerStep A θ hθ n ih hih
  let g : A →ₐ[ℝ] (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] clTowerGrading A θ hθ n) :=
    (GradedTensorProduct.includeRight (CliffordAlgebra.evenOdd q11)
      (clTowerGrading A θ hθ n)).comp (ih.toAlgHom.comp
        (GradedTensorProduct.includeRight (CliffordAlgebra.evenOdd (Qsplit n))
          (involutionGrading θ hθ)))
  have hg_apply : ∀ a : A, g a = (1 : CliffordAlgebra q11) ᵍ⊗ₜ (ih ((1 : Clsplit n) ᵍ⊗ₜ a)) :=
    fun _ => rfl
  have hcomm : ∀ {i j} (x : CliffordAlgebra.evenOdd (Qsplit (n + 1)) i)
      (a : involutionGrading θ hθ j),
      f (x : Clsplit (n + 1)) * g (a : A) =
        (-1 : ℤˣ) ^ (j * i) • (g (a : A) * f (x : Clsplit (n + 1))) := by
    intro i j x a
    have hga_mem : ih ((1 : Clsplit n) ᵍ⊗ₜ (a : A)) ∈ clTowerGrading A θ hθ n j := by
      rcases zmod2_cases j with rfl | rfl
      · change clTowerParity A θ n (ih ((1 : Clsplit n) ᵍ⊗ₜ (a : A))) =
          ih ((1 : Clsplit n) ᵍ⊗ₜ (a : A))
        rw [hih, towerParityAux_tmul, map_one, involutionGrading_even θ hθ a.prop]
      · change clTowerParity A θ n (ih ((1 : Clsplit n) ᵍ⊗ₜ (a : A))) =
          -(ih ((1 : Clsplit n) ᵍ⊗ₜ (a : A)))
        rw [hih, towerParityAux_tmul, map_one, involutionGrading_odd θ hθ a.prop,
          gtmul_neg, map_neg]
    apply clifford_evenOdd_supercommute f (g a) j _ i x x.prop
    intro v
    rw [headTensorToClTowerStep_ι, hg_apply, add_mul, mul_add, smul_add]
    congr 1
    · let c₀ : CliffordAlgebra.evenOdd q11 1 :=
        ⟨CliffordAlgebra.ι q11 v.1, CliffordAlgebra.ι_mem_evenOdd_one q11 v.1⟩
      let b₀ : clTowerGrading A θ hθ n j := ⟨ih ((1 : Clsplit n) ᵍ⊗ₜ (a : A)), hga_mem⟩
      have hc1 := GradedTensorProduct.tmul_one_mul_one_tmul (CliffordAlgebra.evenOdd q11)
        (clTowerGrading A θ hθ n) (c₀ : CliffordAlgebra q11) (b₀ : ClTower A n)
      have hc2 := GradedTensorProduct.tmul_coe_mul_coe_tmul (CliffordAlgebra.evenOdd q11)
        (clTowerGrading A θ hθ n) (1 : CliffordAlgebra q11) b₀ c₀ (1 : ClTower A n)
      simp only [c₀, b₀, one_mul, mul_one] at hc1 hc2
      rw [hc1, hc2]
      rcases zmod2_cases j with rfl | rfl <;>
        simp [ZMod.val_zero, ZMod.val_one]
    · let b₁ : CliffordAlgebra.evenOdd (Qsplit n) 1 :=
        ⟨CliffordAlgebra.ι (Qsplit n) v.2, CliffordAlgebra.ι_mem_evenOdd_one (Qsplit n) v.2⟩
      have hpair : ((CliffordAlgebra.ι (Qsplit n) v.2 ᵍ⊗ₜ (1 : A) :
          CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ) *
          ((1 : Clsplit n) ᵍ⊗ₜ (a : A))) =
          (-1 : ℤˣ) ^ j.val • (((1 : Clsplit n) ᵍ⊗ₜ (a : A)) *
            (CliffordAlgebra.ι (Qsplit n) v.2 ᵍ⊗ₜ (1 : A))) := by
        have hh1 := GradedTensorProduct.tmul_one_mul_one_tmul
          (CliffordAlgebra.evenOdd (Qsplit n)) (involutionGrading θ hθ)
          (b₁ : Clsplit n) (a : A)
        have hh2 := GradedTensorProduct.tmul_coe_mul_coe_tmul
          (CliffordAlgebra.evenOdd (Qsplit n)) (involutionGrading θ hθ)
          (1 : Clsplit n) a b₁ (1 : A)
        simp only [b₁, one_mul, mul_one] at hh1 hh2
        rw [hh1, hh2]
        rcases zmod2_cases j with rfl | rfl <;> simp [ZMod.val_zero, ZMod.val_one]
      have hY_odd : ih ((CliffordAlgebra.ι (Qsplit n) v.2) ᵍ⊗ₜ (1 : A)) ∈
          clTowerGrading A θ hθ n 1 := by
        change clTowerParity A θ n (ih ((CliffordAlgebra.ι (Qsplit n) v.2) ᵍ⊗ₜ (1 : A))) =
          -(ih ((CliffordAlgebra.ι (Qsplit n) v.2) ᵍ⊗ₜ (1 : A)))
        rw [hih, towerParityAux_tmul, CliffordAlgebra.involute_ι, map_one,
          neg_gtmul, map_neg]
      have h1 : ((1 : CliffordAlgebra q11) ᵍ⊗ₜ (ih (CliffordAlgebra.ι (Qsplit n) v.2 ᵍ⊗ₜ (1 : A))) :
          CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] clTowerGrading A θ hθ n) *
          ((1 : CliffordAlgebra q11) ᵍ⊗ₜ (ih ((1 : Clsplit n) ᵍ⊗ₜ (a : A)))) =
          (1 : CliffordAlgebra q11) ᵍ⊗ₜ
            (ih ((CliffordAlgebra.ι (Qsplit n) v.2 ᵍ⊗ₜ (1 : A)) * ((1 : Clsplit n) ᵍ⊗ₜ (a : A)))) := by
        have h1' := GradedTensorProduct.tmul_coe_mul_coe_tmul (CliffordAlgebra.evenOdd q11)
          (clTowerGrading A θ hθ n) (1 : CliffordAlgebra q11)
          ⟨_, hY_odd⟩ (1 : CliffordAlgebra.evenOdd q11 0) (ih ((1 : Clsplit n) ᵍ⊗ₜ (a : A)))
        simpa only [show ((1 : CliffordAlgebra.evenOdd q11 0) : CliffordAlgebra q11) = 1 from rfl,
          one_mul, mul_zero, units_neg_one_zmod2_zero, one_smul, ← map_mul] using h1'
      have h2 : ((1 : CliffordAlgebra q11) ᵍ⊗ₜ (ih ((1 : Clsplit n) ᵍ⊗ₜ (a : A))) :
          CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] clTowerGrading A θ hθ n) *
          ((1 : CliffordAlgebra q11) ᵍ⊗ₜ (ih (CliffordAlgebra.ι (Qsplit n) v.2 ᵍ⊗ₜ (1 : A)))) =
          (1 : CliffordAlgebra q11) ᵍ⊗ₜ
            (ih (((1 : Clsplit n) ᵍ⊗ₜ (a : A)) * (CliffordAlgebra.ι (Qsplit n) v.2 ᵍ⊗ₜ (1 : A)))) := by
        have h2' := GradedTensorProduct.tmul_coe_mul_coe_tmul (CliffordAlgebra.evenOdd q11)
          (clTowerGrading A θ hθ n) (1 : CliffordAlgebra q11) ⟨_, hga_mem⟩
          (1 : CliffordAlgebra.evenOdd q11 0) (ih (CliffordAlgebra.ι (Qsplit n) v.2 ᵍ⊗ₜ (1 : A)))
        simpa only [show ((1 : CliffordAlgebra.evenOdd q11 0) : CliffordAlgebra q11) = 1 from rfl,
          one_mul, mul_zero, units_neg_one_zmod2_zero, one_smul, ← map_mul] using h2'
      rw [h1, h2, hpair]
      rcases zmod2_cases j with rfl | rfl
      · simp
      · simp [ZMod.val_one, map_neg, gtmul_neg]
  GradedTensorProduct.lift (CliffordAlgebra.evenOdd (Qsplit (n + 1))) (involutionGrading θ hθ)
    f g (fun {i j} x a => hcomm x a)

private theorem clSplitGradedTensorStep_fwd_tmul_one (A : Type*) [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ)
    (ih : (CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ) ≃ₐ[ℝ] ClTower A n)
    (hih : ∀ z, clTowerParity A θ n (ih z) = ih (towerParityAux A θ hθ n z))
    (x : Clsplit (n + 1)) :
    clSplitGradedTensorStep_fwd A θ hθ n ih hih (x ᵍ⊗ₜ (1 : A)) =
      headTensorToClTowerStep A θ hθ n ih hih x := by
  dsimp only [clSplitGradedTensorStep_fwd]
  rw [GradedTensorProduct.lift_tmul, map_one, mul_one]

private theorem clSplitGradedTensorStep_fwd_one_tmul (A : Type*) [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ)
    (ih : (CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ) ≃ₐ[ℝ] ClTower A n)
    (hih : ∀ z, clTowerParity A θ n (ih z) = ih (towerParityAux A θ hθ n z))
    (a : A) :
    clSplitGradedTensorStep_fwd A θ hθ n ih hih ((1 : Clsplit (n + 1)) ᵍ⊗ₜ a) =
      (1 : CliffordAlgebra q11) ᵍ⊗ₜ (ih ((1 : Clsplit n) ᵍ⊗ₜ a)) := by
  dsimp only [clSplitGradedTensorStep_fwd]
  rw [GradedTensorProduct.lift_tmul, map_one, one_mul]
  rfl

private def clSplitGradedTensorStep_rightTail (A : Type*) [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ) :
    (CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ) →ₐ[ℝ]
      (CliffordAlgebra.evenOdd (Qsplit (n + 1)) ᵍ⊗[ℝ] involutionGrading θ hθ) :=
  GradedTensorProduct.lift (CliffordAlgebra.evenOdd (Qsplit n)) (involutionGrading θ hθ)
    ((GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd (Qsplit (n + 1)))
      (involutionGrading θ hθ)).comp (splitCliffordStep n))
    (GradedTensorProduct.includeRight (CliffordAlgebra.evenOdd (Qsplit (n + 1)))
      (involutionGrading θ hθ))
    (by
      intro i j x a
      have hx_mem : splitCliffordStep n (x : Clsplit n) ∈
          CliffordAlgebra.evenOdd (Qsplit (n + 1)) i := by
        have hst : CliffordAlgebra.involute (splitCliffordStep n (x : Clsplit n)) =
            splitCliffordStep n (CliffordAlgebra.involute (x : Clsplit n)) :=
          splitCliffordStep_involute n (x : Clsplit n)
        rcases zmod2_cases i with rfl | rfl
        · rw [CliffordAlgebra.involute_eq_of_mem_even x.prop] at hst
          exact (mem_evenOdd_zero_iff_involute _ _).mpr hst
        · rw [CliffordAlgebra.involute_eq_of_mem_odd x.prop, map_neg] at hst
          exact (mem_evenOdd_one_iff_involute _ _).mpr hst
      let x' : CliffordAlgebra.evenOdd (Qsplit (n + 1)) i := ⟨_, hx_mem⟩
      have h1 : ((splitCliffordStep n (x : Clsplit n) ᵍ⊗ₜ (1 : A) :
            CliffordAlgebra.evenOdd (Qsplit (n + 1)) ᵍ⊗[ℝ] involutionGrading θ hθ) *
            ((1 : Clsplit (n + 1)) ᵍ⊗ₜ (a : A))) =
          (splitCliffordStep n (x : Clsplit n) ᵍ⊗ₜ (a : A)) :=
        GradedTensorProduct.tmul_one_mul_one_tmul _ _ _ _
      have h2 := GradedTensorProduct.tmul_coe_mul_coe_tmul
        (CliffordAlgebra.evenOdd (Qsplit (n + 1))) (involutionGrading θ hθ)
        (1 : Clsplit (n + 1)) a x' (1 : A)
      simp only [x', one_mul, mul_one] at h2
      change (splitCliffordStep n x ᵍ⊗ₜ (1 : A)) * ((1 : Clsplit (n + 1)) ᵍ⊗ₜ (a : A)) =
        (-1 : ℤˣ) ^ (j * i) • (((1 : Clsplit (n + 1)) ᵍ⊗ₜ (a : A)) * (splitCliffordStep n x ᵍ⊗ₜ (1 : A)))
      rw [h1, h2, smul_smul, Int.units_mul_self, one_smul])

private theorem clSplitGradedTensorStep_rightTail_tmul (A : Type*) [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ) (x : Clsplit n) (a : A) :
    clSplitGradedTensorStep_rightTail A θ hθ n (x ᵍ⊗ₜ a) =
      splitCliffordStep n x ᵍ⊗ₜ a := by
  dsimp only [clSplitGradedTensorStep_rightTail]
  rw [GradedTensorProduct.lift_tmul]
  simp only [AlgHom.comp_apply, GradedTensorProduct.includeLeft_apply,
    GradedTensorProduct.includeRight_apply]
  exact GradedTensorProduct.tmul_one_mul_one_tmul _ _ _ _

private def clSplitGradedTensorStep_bwd (A : Type*) [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ)
    (ih : (CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ) ≃ₐ[ℝ] ClTower A n)
    (hih : ∀ z, clTowerParity A θ n (ih z) = ih (towerParityAux A θ hθ n z)) :
    (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] clTowerGrading A θ hθ n) →ₐ[ℝ]
      (CliffordAlgebra.evenOdd (Qsplit (n + 1)) ᵍ⊗[ℝ] involutionGrading θ hθ) :=
  let rightTail := clSplitGradedTensorStep_rightTail A θ hθ n
  let leftHead : CliffordAlgebra q11 →ₐ[ℝ]
      (CliffordAlgebra.evenOdd (Qsplit (n + 1)) ᵍ⊗[ℝ] involutionGrading θ hθ) :=
    (GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd (Qsplit (n + 1)))
      (involutionGrading θ hθ)).comp
        ((headTensorEquiv n).symm.toAlgHom.comp
          (GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd q11)
            (CliffordAlgebra.evenOdd (Qsplit n))))
  let rightB : ClTower A n →ₐ[ℝ]
      (CliffordAlgebra.evenOdd (Qsplit (n + 1)) ᵍ⊗[ℝ] involutionGrading θ hθ) :=
    rightTail.comp ih.symm.toAlgHom
  have hcomm_bwd : ∀ {i j} (c : CliffordAlgebra.evenOdd q11 i)
      (d : clTowerGrading A θ hθ n j),
      leftHead (c : CliffordAlgebra q11) * rightB (d : ClTower A n) =
        (-1 : ℤˣ) ^ (j * i) • (rightB (d : ClTower A n) * leftHead (c : CliffordAlgebra q11)) := by
    intro i j c d
    have hc_mem : (headTensorEquiv n).symm ((c : CliffordAlgebra q11) ᵍ⊗ₜ (1 : Clsplit n)) ∈
        CliffordAlgebra.evenOdd (Qsplit (n + 1)) i := by
      have hinv := headTensorEquiv_involute n ((headTensorEquiv n).symm (c ᵍ⊗ₜ 1))
      change headTensorEquiv n (CliffordAlgebra.involute ((headTensorEquiv n).symm (c ᵍ⊗ₜ 1))) = _ at hinv
      rw [AlgEquiv.apply_symm_apply, tensorParity_tmul, map_one] at hinv
      rcases zmod2_cases i with rfl | rfl
      · rw [CliffordAlgebra.involute_eq_of_mem_even c.prop] at hinv
        exact (mem_evenOdd_zero_iff_involute _ _).mpr (by
          apply (headTensorEquiv n).injective; rw [hinv, AlgEquiv.apply_symm_apply])
      · rw [CliffordAlgebra.involute_eq_of_mem_odd c.prop, neg_gtmul] at hinv
        exact (mem_evenOdd_one_iff_involute _ _).mpr (by
          apply (headTensorEquiv n).injective; rw [hinv, map_neg, AlgEquiv.apply_symm_apply])
    have hlin_even : ∀ z : CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ,
        leftHead c * rightTail (z + towerParityAux A θ hθ n z) =
          rightTail (z + towerParityAux A θ hθ n z) * leftHead c := by
      intro z
      obtain ⟨t, rfl⟩ := (GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd (Qsplit n)) (involutionGrading θ hθ)).surjective z
      induction t using TensorProduct.inductionOn with
      | tmul y a =>
          let y0 : Clsplit n := (1 / 2 : ℝ) • (y + CliffordAlgebra.involute y)
          let y1 : Clsplit n := (1 / 2 : ℝ) • (y - CliffordAlgebra.involute y)
          let a0 : A := (1 / 2 : ℝ) • (a + θ a)
          let a1 : A := (1 / 2 : ℝ) • (a - θ a)
          have hy_eq : y = y0 + y1 := by
            dsimp [y0, y1]; rw [← smul_add]; ring_nf; module
          have ha_eq : a = a0 + a1 := by
            dsimp [a0, a1]; rw [← smul_add]; ring_nf; module
          have hy0 : y0 ∈ CliffordAlgebra.evenOdd (Qsplit n) 0 := by
            rw [mem_evenOdd_zero_iff_involute]
            dsimp [y0]; rw [map_smul, map_add, CliffordAlgebra.involute_involute, add_comm]
          have hy1 : y1 ∈ CliffordAlgebra.evenOdd (Qsplit n) 1 := by
            rw [mem_evenOdd_one_iff_involute]
            dsimp [y1]; rw [map_smul, map_sub, CliffordAlgebra.involute_involute, ← smul_neg]; congr 1; abel
          have ha0 : a0 ∈ involutionGrading θ hθ 0 := by
            change θ a0 = a0; dsimp [a0]; rw [map_smul, map_add, hθ a, add_comm]
          have ha1 : a1 ∈ involutionGrading θ hθ 1 := by
            change θ a1 = -a1; dsimp [a1]; rw [map_smul, map_sub, hθ a, ← smul_neg]; congr 1; abel
          have hcomm_pure : ∀ {p q : ZMod 2} (yp : CliffordAlgebra.evenOdd (Qsplit n) p)
              (aq : involutionGrading θ hθ q),
              p + q = 0 → leftHead c * rightTail ((yp : Clsplit n) ᵍ⊗ₜ (aq : A)) =
                rightTail ((yp : Clsplit n) ᵍ⊗ₜ (aq : A)) * leftHead c := by
            intro p q yp aq hpq
            have hrt : rightTail ((yp : Clsplit n) ᵍ⊗ₜ (aq : A)) =
                splitCliffordStep n yp ᵍ⊗ₜ (aq : A) :=
              clSplitGradedTensorStep_rightTail_tmul A θ hθ n yp aq
            have hlh : leftHead c = (headTensorEquiv n).symm (c ᵍ⊗ₜ 1) ᵍ⊗ₜ (1 : A) := rfl
            rw [hlh, hrt]
            have hy_step : splitCliffordStep n yp ∈ CliffordAlgebra.evenOdd (Qsplit (n + 1)) p := by
              have hst : CliffordAlgebra.involute (splitCliffordStep n (yp : Clsplit n)) =
                  splitCliffordStep n (CliffordAlgebra.involute (yp : Clsplit n)) :=
                splitCliffordStep_involute n _
              rcases zmod2_cases p with rfl | rfl
              · rw [CliffordAlgebra.involute_eq_of_mem_even yp.prop] at hst
                exact (mem_evenOdd_zero_iff_involute _ _).mpr hst
              · rw [CliffordAlgebra.involute_eq_of_mem_odd yp.prop, map_neg] at hst
                exact (mem_evenOdd_one_iff_involute _ _).mpr hst
            have hswap_step : (headTensorEquiv n).symm (c ᵍ⊗ₜ 1) * splitCliffordStep n yp =
                (-1 : ℤˣ) ^ (p * i) • (splitCliffordStep n yp * (headTensorEquiv n).symm (c ᵍ⊗ₜ 1)) := by
              apply (headTensorEquiv n).injective
              rw [map_mul, Units.smul_def, map_zsmul, map_mul, AlgEquiv.apply_symm_apply,
                headTensorEquiv_splitCliffordStep n yp, ← Units.smul_def]
              have hh1 := GradedTensorProduct.tmul_one_mul_one_tmul (CliffordAlgebra.evenOdd q11)
                (CliffordAlgebra.evenOdd (Qsplit n)) (c : CliffordAlgebra q11) (yp : Clsplit n)
              have hh2 := GradedTensorProduct.tmul_coe_mul_coe_tmul (CliffordAlgebra.evenOdd q11)
                (CliffordAlgebra.evenOdd (Qsplit n)) (1 : CliffordAlgebra q11)
                (⟨yp, yp.prop⟩ : CliffordAlgebra.evenOdd (Qsplit n) p) c (1 : Clsplit n)
              simp only [one_mul, mul_one] at hh2
              rw [hh1, hh2, smul_smul, Int.units_mul_self, one_smul]
            have hm1 : ((headTensorEquiv n).symm (c ᵍ⊗ₜ (1 : Clsplit n)) ᵍ⊗ₜ (1 : A) :
                  CliffordAlgebra.evenOdd (Qsplit (n + 1)) ᵍ⊗[ℝ] involutionGrading θ hθ) *
                  (splitCliffordStep n yp ᵍ⊗ₜ (aq : A)) =
                ((headTensorEquiv n).symm (c ᵍ⊗ₜ (1 : Clsplit n)) * splitCliffordStep n yp) ᵍ⊗ₜ (aq : A) := by
              have hm1' := GradedTensorProduct.tmul_coe_mul_coe_tmul
                (CliffordAlgebra.evenOdd (Qsplit (n + 1))) (involutionGrading θ hθ)
                ((headTensorEquiv n).symm (c ᵍ⊗ₜ 1)) (1 : involutionGrading θ hθ 0)
                ⟨_, hy_step⟩ (aq : A)
              simpa only [show ((1 : involutionGrading θ hθ 0) : A) = 1 from rfl,
                one_mul, zero_mul, units_neg_one_zmod2_zero, one_smul] using hm1'
            have hm2 : (splitCliffordStep n yp ᵍ⊗ₜ (aq : A) :
                  CliffordAlgebra.evenOdd (Qsplit (n + 1)) ᵍ⊗[ℝ] involutionGrading θ hθ) *
                  ((headTensorEquiv n).symm (c ᵍ⊗ₜ (1 : Clsplit n)) ᵍ⊗ₜ (1 : A)) =
                (-1 : ℤˣ) ^ (q * i) •
                  ((splitCliffordStep n yp * (headTensorEquiv n).symm (c ᵍ⊗ₜ (1 : Clsplit n))) ᵍ⊗ₜ (aq : A)) := by
              have hm2' := GradedTensorProduct.tmul_coe_mul_coe_tmul
                (CliffordAlgebra.evenOdd (Qsplit (n + 1))) (involutionGrading θ hθ)
                (splitCliffordStep n yp) aq ⟨_, hc_mem⟩ (1 : A)
              simpa only [mul_one, one_mul, zero_mul, units_neg_one_zmod2_zero, one_smul] using hm2'
            have hpow : (-1 : ℤˣ) ^ (p * i) = (-1 : ℤˣ) ^ (q * i) := by
              rcases zmod2_cases i with rfl | rfl <;>
                rcases zmod2_cases p with rfl | rfl <;>
                rcases zmod2_cases q with rfl | rfl <;>
                first
                | exact absurd hpq (by decide)
                | decide
            rw [hm1, hm2, hswap_step, Units.smul_def, zsmul_gtmul, ← Units.smul_def, hpow]
          have hy_split : (y ᵍ⊗ₜ a :
              CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ) =
              (y0 ᵍ⊗ₜ a0 + y1 ᵍ⊗ₜ a1) + (y0 ᵍ⊗ₜ a1 + y1 ᵍ⊗ₜ a0) := by
            conv_lhs => rw [hy_eq, ha_eq]
            rw [add_gtmul, gtmul_add, gtmul_add]
            abel
          have htau_00 : towerParityAux A θ hθ n (y0 ᵍ⊗ₜ a0) = y0 ᵍ⊗ₜ a0 := by
            rw [towerParityAux_tmul, (mem_evenOdd_zero_iff_involute _ _).mp hy0,
              involutionGrading_even θ hθ ha0]
          have htau_11 : towerParityAux A θ hθ n (y1 ᵍ⊗ₜ a1) = y1 ᵍ⊗ₜ a1 := by
            rw [towerParityAux_tmul, (mem_evenOdd_one_iff_involute _ _).mp hy1,
              involutionGrading_odd θ hθ ha1, neg_gtmul, gtmul_neg, neg_neg]
          have htau_01 : towerParityAux A θ hθ n (y0 ᵍ⊗ₜ a1) = -(y0 ᵍ⊗ₜ a1) := by
            rw [towerParityAux_tmul, (mem_evenOdd_zero_iff_involute _ _).mp hy0,
              involutionGrading_odd θ hθ ha1, gtmul_neg]
          have htau_10 : towerParityAux A θ hθ n (y1 ᵍ⊗ₜ a0) = -(y1 ᵍ⊗ₜ a0) := by
            rw [towerParityAux_tmul, (mem_evenOdd_one_iff_involute _ _).mp hy1,
              involutionGrading_even θ hθ ha0, neg_gtmul]
          have hzsum : (y ᵍ⊗ₜ a) + towerParityAux A θ hθ n (y ᵍ⊗ₜ a) =
              (2 : ℝ) • (y0 ᵍ⊗ₜ a0 + y1 ᵍ⊗ₜ a1) := by
            rw [hy_split, map_add, map_add, map_add, htau_00, htau_11, htau_01, htau_10]
            module
          rw [hzsum, map_smul, map_add, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
            mul_add, add_mul, hcomm_pure ⟨y0, hy0⟩ ⟨a0, ha0⟩ rfl,
            hcomm_pure ⟨y1, hy1⟩ ⟨a1, ha1⟩ (by decide)]
      | add u v hu hv =>
          simp only [map_add] at hu hv ⊢
          rw [add_add_add_comm, mul_add, add_mul, hu, hv]
    have hlin_odd : ∀ z : CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ,
        leftHead c * rightTail (z - towerParityAux A θ hθ n z) =
          (-1 : ℤˣ) ^ i.val • (rightTail (z - towerParityAux A θ hθ n z) * leftHead c) := by
      intro z
      obtain ⟨t, rfl⟩ := (GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd (Qsplit n)) (involutionGrading θ hθ)).surjective z
      induction t using TensorProduct.inductionOn with
      | tmul y a =>
          let y0 : Clsplit n := (1 / 2 : ℝ) • (y + CliffordAlgebra.involute y)
          let y1 : Clsplit n := (1 / 2 : ℝ) • (y - CliffordAlgebra.involute y)
          let a0 : A := (1 / 2 : ℝ) • (a + θ a)
          let a1 : A := (1 / 2 : ℝ) • (a - θ a)
          have hy_eq : y = y0 + y1 := by dsimp [y0, y1]; rw [← smul_add]; ring_nf; module
          have ha_eq : a = a0 + a1 := by dsimp [a0, a1]; rw [← smul_add]; ring_nf; module
          have hy0 : y0 ∈ CliffordAlgebra.evenOdd (Qsplit n) 0 := by
            rw [mem_evenOdd_zero_iff_involute]
            dsimp [y0]; rw [map_smul, map_add, CliffordAlgebra.involute_involute, add_comm]
          have hy1 : y1 ∈ CliffordAlgebra.evenOdd (Qsplit n) 1 := by
            rw [mem_evenOdd_one_iff_involute]
            dsimp [y1]; rw [map_smul, map_sub, CliffordAlgebra.involute_involute, ← smul_neg]; congr 1; abel
          have ha0 : a0 ∈ involutionGrading θ hθ 0 := by
            change θ a0 = a0; dsimp [a0]; rw [map_smul, map_add, hθ a, add_comm]
          have ha1 : a1 ∈ involutionGrading θ hθ 1 := by
            change θ a1 = -a1; dsimp [a1]; rw [map_smul, map_sub, hθ a, ← smul_neg]; congr 1; abel
          have hcomm_pure : ∀ {p q : ZMod 2} (yp : CliffordAlgebra.evenOdd (Qsplit n) p)
              (aq : involutionGrading θ hθ q),
              p + q = 1 → leftHead c * rightTail ((yp : Clsplit n) ᵍ⊗ₜ (aq : A)) =
                (-1 : ℤˣ) ^ i.val • (rightTail ((yp : Clsplit n) ᵍ⊗ₜ (aq : A)) * leftHead c) := by
            intro p q yp aq hpq
            have hrt : rightTail ((yp : Clsplit n) ᵍ⊗ₜ (aq : A)) =
                splitCliffordStep n yp ᵍ⊗ₜ (aq : A) :=
              clSplitGradedTensorStep_rightTail_tmul A θ hθ n yp aq
            have hlh : leftHead c = (headTensorEquiv n).symm (c ᵍ⊗ₜ 1) ᵍ⊗ₜ (1 : A) := rfl
            rw [hlh, hrt]
            have hy_step : splitCliffordStep n yp ∈ CliffordAlgebra.evenOdd (Qsplit (n + 1)) p := by
              have hst : CliffordAlgebra.involute (splitCliffordStep n (yp : Clsplit n)) =
                  splitCliffordStep n (CliffordAlgebra.involute (yp : Clsplit n)) :=
                splitCliffordStep_involute n _
              rcases zmod2_cases p with rfl | rfl
              · rw [CliffordAlgebra.involute_eq_of_mem_even yp.prop] at hst
                exact (mem_evenOdd_zero_iff_involute _ _).mpr hst
              · rw [CliffordAlgebra.involute_eq_of_mem_odd yp.prop, map_neg] at hst
                exact (mem_evenOdd_one_iff_involute _ _).mpr hst
            have hswap_step : (headTensorEquiv n).symm (c ᵍ⊗ₜ 1) * splitCliffordStep n yp =
                (-1 : ℤˣ) ^ (p * i) • (splitCliffordStep n yp * (headTensorEquiv n).symm (c ᵍ⊗ₜ 1)) := by
              apply (headTensorEquiv n).injective
              rw [map_mul, Units.smul_def, map_zsmul, map_mul, AlgEquiv.apply_symm_apply,
                headTensorEquiv_splitCliffordStep n yp, ← Units.smul_def]
              have hh1 := GradedTensorProduct.tmul_one_mul_one_tmul (CliffordAlgebra.evenOdd q11)
                (CliffordAlgebra.evenOdd (Qsplit n)) (c : CliffordAlgebra q11) (yp : Clsplit n)
              have hh2 := GradedTensorProduct.tmul_coe_mul_coe_tmul (CliffordAlgebra.evenOdd q11)
                (CliffordAlgebra.evenOdd (Qsplit n)) (1 : CliffordAlgebra q11)
                (⟨yp, yp.prop⟩ : CliffordAlgebra.evenOdd (Qsplit n) p) c (1 : Clsplit n)
              simp only [one_mul, mul_one] at hh2
              rw [hh1, hh2, smul_smul, Int.units_mul_self, one_smul]
            have hm1 : ((headTensorEquiv n).symm (c ᵍ⊗ₜ (1 : Clsplit n)) ᵍ⊗ₜ (1 : A) :
                  CliffordAlgebra.evenOdd (Qsplit (n + 1)) ᵍ⊗[ℝ] involutionGrading θ hθ) *
                  (splitCliffordStep n yp ᵍ⊗ₜ (aq : A)) =
                ((headTensorEquiv n).symm (c ᵍ⊗ₜ (1 : Clsplit n)) * splitCliffordStep n yp) ᵍ⊗ₜ (aq : A) := by
              have hm1' := GradedTensorProduct.tmul_coe_mul_coe_tmul
                (CliffordAlgebra.evenOdd (Qsplit (n + 1))) (involutionGrading θ hθ)
                ((headTensorEquiv n).symm (c ᵍ⊗ₜ 1)) (1 : involutionGrading θ hθ 0)
                ⟨_, hy_step⟩ (aq : A)
              simpa only [show ((1 : involutionGrading θ hθ 0) : A) = 1 from rfl,
                one_mul, zero_mul, units_neg_one_zmod2_zero, one_smul] using hm1'
            have hm2 : (splitCliffordStep n yp ᵍ⊗ₜ (aq : A) :
                  CliffordAlgebra.evenOdd (Qsplit (n + 1)) ᵍ⊗[ℝ] involutionGrading θ hθ) *
                  ((headTensorEquiv n).symm (c ᵍ⊗ₜ (1 : Clsplit n)) ᵍ⊗ₜ (1 : A)) =
                (-1 : ℤˣ) ^ (q * i) •
                  ((splitCliffordStep n yp * (headTensorEquiv n).symm (c ᵍ⊗ₜ (1 : Clsplit n))) ᵍ⊗ₜ (aq : A)) := by
              have hm2' := GradedTensorProduct.tmul_coe_mul_coe_tmul
                (CliffordAlgebra.evenOdd (Qsplit (n + 1))) (involutionGrading θ hθ)
                (splitCliffordStep n yp) aq ⟨_, hc_mem⟩ (1 : A)
              simpa only [mul_one, one_mul, zero_mul, units_neg_one_zmod2_zero, one_smul] using hm2'
            have hpow : (-1 : ℤˣ) ^ (p * i) = (-1 : ℤˣ) ^ i.val * (-1 : ℤˣ) ^ (q * i) := by
              rcases zmod2_cases i with rfl | rfl <;>
                rcases zmod2_cases p with rfl | rfl <;>
                rcases zmod2_cases q with rfl | rfl <;>
                first
                | exact absurd hpq (by decide)
                | decide
            rw [hm1, hm2, hswap_step, Units.smul_def, zsmul_gtmul, ← Units.smul_def, hpow, mul_smul]
          have hy_split : (y ᵍ⊗ₜ a :
              CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ) =
              (y0 ᵍ⊗ₜ a0 + y1 ᵍ⊗ₜ a1) + (y0 ᵍ⊗ₜ a1 + y1 ᵍ⊗ₜ a0) := by
            conv_lhs => rw [hy_eq, ha_eq]
            rw [add_gtmul, gtmul_add, gtmul_add]
            abel
          have htau_00 : towerParityAux A θ hθ n (y0 ᵍ⊗ₜ a0) = y0 ᵍ⊗ₜ a0 := by
            rw [towerParityAux_tmul, (mem_evenOdd_zero_iff_involute _ _).mp hy0,
              involutionGrading_even θ hθ ha0]
          have htau_11 : towerParityAux A θ hθ n (y1 ᵍ⊗ₜ a1) = y1 ᵍ⊗ₜ a1 := by
            rw [towerParityAux_tmul, (mem_evenOdd_one_iff_involute _ _).mp hy1,
              involutionGrading_odd θ hθ ha1, neg_gtmul, gtmul_neg, neg_neg]
          have htau_01 : towerParityAux A θ hθ n (y0 ᵍ⊗ₜ a1) = -(y0 ᵍ⊗ₜ a1) := by
            rw [towerParityAux_tmul, (mem_evenOdd_zero_iff_involute _ _).mp hy0,
              involutionGrading_odd θ hθ ha1, gtmul_neg]
          have htau_10 : towerParityAux A θ hθ n (y1 ᵍ⊗ₜ a0) = -(y1 ᵍ⊗ₜ a0) := by
            rw [towerParityAux_tmul, (mem_evenOdd_one_iff_involute _ _).mp hy1,
              involutionGrading_even θ hθ ha0, neg_gtmul]
          have hzdiff : (y ᵍ⊗ₜ a) - towerParityAux A θ hθ n (y ᵍ⊗ₜ a) =
              (2 : ℝ) • (y0 ᵍ⊗ₜ a1 + y1 ᵍ⊗ₜ a0) := by
            rw [hy_split, map_add, map_add, map_add, htau_00, htau_11, htau_01, htau_10]
            module
          rw [hzdiff, map_smul, map_add, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
            mul_add, add_mul,
            hcomm_pure ⟨y0, hy0⟩ ⟨a1, ha1⟩ (by decide),
            hcomm_pure ⟨y1, hy1⟩ ⟨a0, ha0⟩ (by decide),
            ← smul_add, smul_comm]
      | add u v hu hv =>
          simp only [map_add] at hu hv ⊢
          simp only [add_sub_add_comm, map_add, mul_add, add_mul, smul_add, hu, hv]
    let z := ih.symm (d : ClTower A n)
    change leftHead c * rightTail z = (-1 : ℤˣ) ^ (j * i) • (rightTail z * leftHead c)
    rcases zmod2_cases j with rfl | rfl
    · have hz_par : towerParityAux A θ hθ n z = z := by
        apply ih.injective
        rw [← hih, AlgEquiv.apply_symm_apply, involutionGrading_even _ _ d.prop]
      have hz2 : z = (1 / 2 : ℝ) • (z + towerParityAux A θ hθ n z) := by
        rw [hz_par, ← two_smul ℝ, smul_smul]; norm_num
      conv_lhs => rw [hz2]
      conv_rhs => rw [hz2]
      rw [map_smul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hlin_even z,
        zero_mul, units_neg_one_zmod2_zero, one_smul]
    · have hz_par : towerParityAux A θ hθ n z = -z := by
        apply ih.injective
        rw [← hih, AlgEquiv.apply_symm_apply, involutionGrading_odd _ _ d.prop,
          map_neg, AlgEquiv.apply_symm_apply]
      have hz2 : z = (1 / 2 : ℝ) • (z - towerParityAux A θ hθ n z) := by
        rw [hz_par, sub_neg_eq_add, ← two_smul ℝ, smul_smul]; norm_num
      conv_lhs => rw [hz2]
      conv_rhs => rw [hz2]
      rw [map_smul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hlin_odd z,
        smul_comm (1 / 2 : ℝ) ((-1 : ℤˣ) ^ i.val), one_mul]
      rcases zmod2_cases i with rfl | rfl <;> simp [ZMod.val_zero, ZMod.val_one]
  GradedTensorProduct.lift (CliffordAlgebra.evenOdd q11) (clTowerGrading A θ hθ n)
    leftHead rightB (fun {i j} c d => hcomm_bwd c d)

private theorem clSplitGradedTensorStep_bwd_left (A : Type*) [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ)
    (ih : (CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ) ≃ₐ[ℝ] ClTower A n)
    (hih : ∀ z, clTowerParity A θ n (ih z) = ih (towerParityAux A θ hθ n z))
    (c : CliffordAlgebra q11) :
    clSplitGradedTensorStep_bwd A θ hθ n ih hih (c ᵍ⊗ₜ (1 : ClTower A n)) =
      (headTensorEquiv n).symm (c ᵍ⊗ₜ (1 : Clsplit n)) ᵍ⊗ₜ (1 : A) := by
  dsimp only [clSplitGradedTensorStep_bwd]
  rw [GradedTensorProduct.lift_tmul, map_one, mul_one]
  rfl

private theorem clSplitGradedTensorStep_bwd_right (A : Type*) [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ)
    (ih : (CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ) ≃ₐ[ℝ] ClTower A n)
    (hih : ∀ z, clTowerParity A θ n (ih z) = ih (towerParityAux A θ hθ n z))
    (d : ClTower A n) :
    clSplitGradedTensorStep_bwd A θ hθ n ih hih ((1 : CliffordAlgebra q11) ᵍ⊗ₜ d) =
      clSplitGradedTensorStep_rightTail A θ hθ n (ih.symm d) := by
  dsimp only [clSplitGradedTensorStep_bwd]
  rw [GradedTensorProduct.lift_tmul, map_one, one_mul]
  rfl

private theorem clSplitGradedTensorStep_bwd_fwd (A : Type*) [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ)
    (ih : (CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ) ≃ₐ[ℝ] ClTower A n)
    (hih : ∀ z, clTowerParity A θ n (ih z) = ih (towerParityAux A θ hθ n z))
    (w : CliffordAlgebra.evenOdd (Qsplit (n + 1)) ᵍ⊗[ℝ] involutionGrading θ hθ) :
    clSplitGradedTensorStep_bwd A θ hθ n ih hih
      (clSplitGradedTensorStep_fwd A θ hθ n ih hih w) = w := by
  have hhom : (clSplitGradedTensorStep_bwd A θ hθ n ih hih).comp
      (clSplitGradedTensorStep_fwd A θ hθ n ih hih) = AlgHom.id ℝ _ := by
    apply GradedTensorProduct.algHom_ext
    · apply CliffordAlgebra.hom_ext; apply LinearMap.ext; intro v
      simp only [AlgHom.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        AlgHom.id_apply, GradedTensorProduct.includeLeft_apply]
      rw [clSplitGradedTensorStep_fwd_tmul_one, headTensorToClTowerStep_ι, map_add,
        clSplitGradedTensorStep_bwd_left, clSplitGradedTensorStep_bwd_right,
        AlgEquiv.symm_apply_apply, clSplitGradedTensorStep_rightTail_tmul, splitCliffordStep_ι]
      have hfst : ((headTensorEquiv n).symm ((CliffordAlgebra.ι q11 v.1) ᵍ⊗ₜ (1 : Clsplit n)) :
          Clsplit (n + 1)) = CliffordAlgebra.ι (Qsplit (n + 1)) (v.1, (0 : SplitSpace n)) := by
        apply (headTensorEquiv n).injective
        rw [AlgEquiv.apply_symm_apply, headTensorEquiv_ι]
        simp [gtmul_zero]
      rw [hfst, ← add_gtmul, ← map_add]
      congr 2
      ext <;> simp
    · apply AlgHom.ext; intro a
      simp only [AlgHom.comp_apply, AlgHom.id_apply, GradedTensorProduct.includeRight_apply]
      rw [clSplitGradedTensorStep_fwd_one_tmul, clSplitGradedTensorStep_bwd_right,
        AlgEquiv.symm_apply_apply, clSplitGradedTensorStep_rightTail_tmul, map_one]
  exact AlgHom.congr_fun hhom w

private theorem clSplitGradedTensorStep_fwd_bwd (A : Type*) [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ)
    (ih : (CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ) ≃ₐ[ℝ] ClTower A n)
    (hih : ∀ z, clTowerParity A θ n (ih z) = ih (towerParityAux A θ hθ n z))
    (y : CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] clTowerGrading A θ hθ n) :
    clSplitGradedTensorStep_fwd A θ hθ n ih hih
      (clSplitGradedTensorStep_bwd A θ hθ n ih hih y) = y := by
  have hhom : (clSplitGradedTensorStep_fwd A θ hθ n ih hih).comp
      (clSplitGradedTensorStep_bwd A θ hθ n ih hih) = AlgHom.id ℝ _ := by
    apply GradedTensorProduct.algHom_ext
    · apply CliffordAlgebra.hom_ext; apply LinearMap.ext; intro w
      simp only [AlgHom.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        AlgHom.id_apply, GradedTensorProduct.includeLeft_apply]
      rw [clSplitGradedTensorStep_bwd_left]
      have hlh : ((headTensorEquiv n).symm ((CliffordAlgebra.ι q11 w) ᵍ⊗ₜ (1 : Clsplit n)) :
          Clsplit (n + 1)) = CliffordAlgebra.ι (Qsplit (n + 1)) (w, (0 : SplitSpace n)) := by
        apply (headTensorEquiv n).injective
        rw [AlgEquiv.apply_symm_apply, headTensorEquiv_ι]
        simp [gtmul_zero]
      rw [hlh, clSplitGradedTensorStep_fwd_tmul_one, headTensorToClTowerStep_ι]
      simp only [map_zero, zero_gtmul, gtmul_zero, add_zero]
    · apply AlgHom.ext; intro d
      obtain ⟨z, rfl⟩ := ih.surjective d
      simp only [AlgHom.comp_apply, AlgHom.id_apply, GradedTensorProduct.includeRight_apply]
      rw [clSplitGradedTensorStep_bwd_right, AlgEquiv.symm_apply_apply]
      have hcomp :
          ((clSplitGradedTensorStep_fwd A θ hθ n ih hih).comp
            (clSplitGradedTensorStep_rightTail A θ hθ n) :
            (CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ) →ₐ[ℝ] _) =
          (GradedTensorProduct.includeRight (CliffordAlgebra.evenOdd q11)
            (clTowerGrading A θ hθ n)).comp ih.toAlgHom := by
        apply GradedTensorProduct.algHom_ext
        · apply CliffordAlgebra.hom_ext; apply LinearMap.ext; intro u
          simp only [AlgHom.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
            GradedTensorProduct.includeLeft_apply, GradedTensorProduct.includeRight_apply]
          rw [clSplitGradedTensorStep_rightTail_tmul, splitCliffordStep_ι,
            clSplitGradedTensorStep_fwd_tmul_one, headTensorToClTowerStep_ι,
            show (((0 : ℝ), (0 : ℝ)), u).1 = (0 : ℝ × ℝ) from rfl]
          simp only [map_zero, zero_gtmul, zero_add]
          rfl
        · apply AlgHom.ext; intro a
          simp only [AlgHom.comp_apply, GradedTensorProduct.includeRight_apply]
          rw [clSplitGradedTensorStep_rightTail_tmul, map_one,
            clSplitGradedTensorStep_fwd_one_tmul]
          rfl
      exact AlgHom.congr_fun hcomp z
  exact AlgHom.congr_fun hhom y

private def clSplitGradedTensorEquivStep (A : Type*) [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ)
    (ih : (CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ) ≃ₐ[ℝ] ClTower A n)
    (hih : ∀ z, clTowerParity A θ n (ih z) = ih (towerParityAux A θ hθ n z)) :
    { e : (CliffordAlgebra.evenOdd (Qsplit (n + 1)) ᵍ⊗[ℝ] involutionGrading θ hθ) ≃ₐ[ℝ]
        ClTower A (n + 1) //
      ∀ z, clTowerParity A θ (n + 1) (e z) = e (towerParityAux A θ hθ (n + 1) z) } :=
  let fwd := clSplitGradedTensorStep_fwd A θ hθ n ih hih
  let bwd := clSplitGradedTensorStep_bwd A θ hθ n ih hih
  let eStep : (CliffordAlgebra.evenOdd (Qsplit (n + 1)) ᵍ⊗[ℝ] involutionGrading θ hθ) ≃ₐ[ℝ]
      (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] clTowerGrading A θ hθ n) :=
    { toFun := fwd
      invFun := bwd
      left_inv := clSplitGradedTensorStep_bwd_fwd A θ hθ n ih hih
      right_inv := clSplitGradedTensorStep_fwd_bwd A θ hθ n ih hih
      map_mul' := fwd.map_mul'
      map_add' := fwd.map_add'
      commutes' := fwd.commutes' }
  let matEquiv : (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] clTowerGrading A θ hθ n) ≃ₐ[ℝ]
      ClTower A (n + 1) :=
    tensorMatrixEquiv (clTowerGrading A θ hθ n) (clTowerParity A θ n)
      (fun {_} ha => involutionGrading_even _ _ ha)
      (fun {_} ha => involutionGrading_odd _ _ ha)
  let e := eStep.trans matEquiv
  have hmat_par : ∀ y : CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] clTowerGrading A θ hθ n,
      matrixAlgGrade (clTowerParity A θ n) (matEquiv y) =
        matEquiv (tensorParity (clTowerGrading A θ hθ n) (clTowerParity A θ n)
          (fun {_} hb => involutionGrading_even _ _ hb)
          (fun {_} hb => involutionGrading_odd _ _ hb) y) := by
    intro y
    obtain ⟨t, rfl⟩ := (GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11) (clTowerGrading A θ hθ n)).surjective y
    induction t using TensorProduct.inductionOn with
    | tmul c d =>
        change matrixAlgGrade (clTowerParity A θ n) (matEquiv (c ᵍ⊗ₜ d)) =
          matEquiv (tensorParity (clTowerGrading A θ hθ n) (clTowerParity A θ n) _ _ (c ᵍ⊗ₜ d))
        rw [tensorParity_tmul]
        dsimp only [matEquiv]
        rw [tensorMatrixEquiv_apply, tensorToMatrix_tmul_matrix,
          tensorMatrixEquiv_apply, tensorToMatrix_tmul_matrix, cl11StandardEquiv_involute]
        have hinv : clTowerParity A θ n (clTowerParity A θ n d) = d :=
          clTowerParity_involutive A θ hθ n d
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [matrixAlgGrade_apply, Eplus, Matrix.mul_apply, Matrix.vecMul, dotProduct,
            Fin.sum_univ_two, Algebra.smul_def, hinv]
    | add u v hu hv =>
        simp only [map_add] at hu hv ⊢; rw [hu, hv]
  have hstep_par : ∀ w : CliffordAlgebra.evenOdd (Qsplit (n + 1)) ᵍ⊗[ℝ] involutionGrading θ hθ,
      clTowerParity A θ (n + 1) (e w) = e (towerParityAux A θ hθ (n + 1) w) := by
    let tp := tensorParity (clTowerGrading A θ hθ n) (clTowerParity A θ n)
      (fun {_} hb => involutionGrading_even _ _ hb)
      (fun {_} hb => involutionGrading_odd _ _ hb)
    have htp : ∀ c d, tp.toAlgHom (c ᵍ⊗ₜ d) = CliffordAlgebra.involute c ᵍ⊗ₜ clTowerParity A θ n d :=
      fun c d => tensorParity_tmul (clTowerGrading A θ hθ n) (clTowerParity A θ n)
        (fun {_} hb => involutionGrading_even _ _ hb)
        (fun {_} hb => involutionGrading_odd _ _ hb) c d
    have hhom : tp.toAlgHom.comp fwd = fwd.comp (towerParityAux A θ hθ (n + 1)) := by
      apply GradedTensorProduct.algHom_ext
      · apply CliffordAlgebra.hom_ext; apply LinearMap.ext; intro v
        simp only [AlgHom.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
          GradedTensorProduct.includeLeft_apply]
        rw [towerParityAux_tmul, CliffordAlgebra.involute_ι, map_one, neg_gtmul, map_neg,
          clSplitGradedTensorStep_fwd_tmul_one, headTensorToClTowerStep_ι, map_add,
          htp, htp, hih, towerParityAux_tmul]
        simp only [CliffordAlgebra.involute_ι, map_one, neg_gtmul, gtmul_neg, map_neg, neg_add]
      · apply AlgHom.ext; intro a
        simp only [AlgHom.comp_apply, GradedTensorProduct.includeRight_apply]
        rw [towerParityAux_tmul, map_one, clSplitGradedTensorStep_fwd_one_tmul,
          clSplitGradedTensorStep_fwd_one_tmul, htp, map_one,
          hih, towerParityAux_tmul, map_one]
    intro w
    change matrixAlgGrade (clTowerParity A θ n) (matEquiv (fwd w)) =
      matEquiv (fwd (towerParityAux A θ hθ (n + 1) w))
    rw [hmat_par (fwd w)]
    exact congrArg matEquiv (AlgHom.congr_fun hhom w)
  ⟨e, hstep_par⟩

private def clSplitGradedTensorEquivPair (A : Type*) [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) :
    (n : ℕ) →
      { e : (CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ) ≃ₐ[ℝ] ClTower A n //
        ∀ z, clTowerParity A θ n (e z) = e (towerParityAux A θ hθ n z) }
  | 0 =>
      ⟨gradedSplitZeroTensorEquiv (involutionGrading θ hθ), fun z => by
        obtain ⟨t, rfl⟩ := (GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd (Qsplit 0)) (involutionGrading θ hθ)).surjective z
        induction t using TensorProduct.inductionOn with
        | tmul x a =>
            change clTowerParity A θ 0 (gradedSplitZeroTensorEquiv (involutionGrading θ hθ) (x ᵍ⊗ₜ a)) =
              gradedSplitZeroTensorEquiv (involutionGrading θ hθ) (towerParityAux A θ hθ 0 (x ᵍ⊗ₜ a))
            rw [gradedSplitZeroTensorEquiv_tmul, towerParityAux_tmul,
              gradedSplitZeroTensorEquiv_tmul, map_smul]
            have hx : splitZeroEquivReal (CliffordAlgebra.involute x) = splitZeroEquivReal x := by
              have hhom : splitZeroEquivReal.toAlgHom.comp (CliffordAlgebra.involute (Q := Qsplit 0)) =
                  splitZeroEquivReal.toAlgHom := by
                apply CliffordAlgebra.hom_ext; apply LinearMap.ext; intro v
                have hv : v = 0 := Subsingleton.elim v 0
                rw [hv, map_zero, map_zero]
              exact AlgHom.congr_fun hhom x
            rw [hx]
            rfl
        | add u v hu hv =>
            simp only [map_add] at hu hv ⊢
            rw [hu, hv]⟩
  | n + 1 =>
      let recP := clSplitGradedTensorEquivPair A θ hθ n
      clSplitGradedTensorEquivStep A θ hθ n recP.1 recP.2

/-- Recursive `ℝ`-algebra isomorphism between Lane 1's graded tensor
`(CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ)` and Lane 3's `ClTower A n`
for any noncommutative real algebra `A` with involution `θ`. -/
def clSplitGradedTensorEquivClTower (A : Type*) [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ) :
    (CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ) ≃ₐ[ℝ] ClTower A n :=
  (clSplitGradedTensorEquivPair A θ hθ n).1

theorem clSplitGradedTensorEquivClTower_parity (A : Type*) [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ)
    (z : CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ) :
    clTowerParity A θ n (clSplitGradedTensorEquivClTower A θ hθ n z) =
      clSplitGradedTensorEquivClTower A θ hθ n (towerParityAux A θ hθ n z) :=
  (clSplitGradedTensorEquivPair A θ hθ n).2 z

private theorem clSplitGradedTensorEquivClTower_succ_tmul_one {A : Type*} [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ) (x : Clsplit (n + 1)) :
    clSplitGradedTensorEquivClTower A θ hθ (n + 1) (x ᵍ⊗ₜ (1 : A)) =
      tensorMatrixEquiv (clTowerGrading A θ hθ n) (clTowerParity A θ n)
        (fun {_} ha => involutionGrading_even _ _ ha)
        (fun {_} ha => involutionGrading_odd _ _ ha)
        (headTensorToClTowerStep A θ hθ n (clSplitGradedTensorEquivClTower A θ hθ n)
          (clSplitGradedTensorEquivClTower_parity A θ hθ n) x) := by
  dsimp only [clSplitGradedTensorEquivClTower, clSplitGradedTensorEquivPair,
    clSplitGradedTensorEquivStep]
  change tensorMatrixEquiv (clTowerGrading A θ hθ n) (clTowerParity A θ n)
      (fun {_} ha => involutionGrading_even _ _ ha)
      (fun {_} ha => involutionGrading_odd _ _ ha)
      (clSplitGradedTensorStep_fwd A θ hθ n (clSplitGradedTensorEquivClTower A θ hθ n)
        (clSplitGradedTensorEquivClTower_parity A θ hθ n) (x ᵍ⊗ₜ (1 : A))) = _
  rw [clSplitGradedTensorStep_fwd_tmul_one]
  rfl

private theorem clSplitGradedTensorEquivClTower_succ_one_tmul {A : Type*} [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ) (b : A) :
    clSplitGradedTensorEquivClTower A θ hθ (n + 1) ((1 : Clsplit (n + 1)) ᵍ⊗ₜ b) =
      tensorMatrixEquiv (clTowerGrading A θ hθ n) (clTowerParity A θ n)
        (fun {_} ha => involutionGrading_even _ _ ha)
        (fun {_} ha => involutionGrading_odd _ _ ha)
        ((1 : CliffordAlgebra q11) ᵍ⊗ₜ
          (clSplitGradedTensorEquivClTower A θ hθ n ((1 : Clsplit n) ᵍ⊗ₜ b))) := by
  dsimp only [clSplitGradedTensorEquivClTower, clSplitGradedTensorEquivPair,
    clSplitGradedTensorEquivStep]
  change tensorMatrixEquiv (clTowerGrading A θ hθ n) (clTowerParity A θ n)
      (fun {_} ha => involutionGrading_even _ _ ha)
      (fun {_} ha => involutionGrading_odd _ _ ha)
      (clSplitGradedTensorStep_fwd A θ hθ n (clSplitGradedTensorEquivClTower A θ hθ n)
        (clSplitGradedTensorEquivClTower_parity A θ hθ n) ((1 : Clsplit (n + 1)) ᵍ⊗ₜ b)) = _
  rw [clSplitGradedTensorStep_fwd_one_tmul]
  rfl

private theorem trivialInvolution_involutive (A : Type*) [Ring A] [Algebra ℝ A] :
    Function.Involutive (AlgEquiv.refl : A ≃ₐ[ℝ] A) :=
  fun _ => rfl

instance instGradedAlgebraTrivialInvolution (A : Type*) [Ring A] [Algebra ℝ A] :
    GradedAlgebra (involutionGrading (AlgEquiv.refl : A ≃ₐ[ℝ] A) (trivialInvolution_involutive A)) :=
  instGradedAlgebraInvolutionGrading _ _

/-- For the trivial involution `AlgEquiv.refl` on an arbitrary noncommutative `ℝ`-algebra `A`,
`evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading AlgEquiv.refl` is ungraded `Clsplit n ⊗[ℝ] A`. -/
def gradedTrivialTensorEquiv (A : Type*) [Ring A] [Algebra ℝ A] (n : ℕ) :
    (CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ]
      involutionGrading (AlgEquiv.refl : A ≃ₐ[ℝ] A) (trivialInvolution_involutive A)) ≃ₐ[ℝ]
      (Clsplit n ⊗[ℝ] A) :=
  let ℬ := involutionGrading (AlgEquiv.refl : A ≃ₐ[ℝ] A) (trivialInvolution_involutive A)
  let fwd : (CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] ℬ) →ₐ[ℝ] (Clsplit n ⊗[ℝ] A) :=
    GradedTensorProduct.lift (CliffordAlgebra.evenOdd (Qsplit n)) ℬ
      (Algebra.TensorProduct.includeLeft)
      (Algebra.TensorProduct.includeRight)
      (by
        intro i j x a
        rcases zmod2_cases j with rfl | rfl
        · simp
        · have ha : (a : A) = -(a : A) := involutionGrading_odd _ _ a.prop
          have htwo : (2 : ℝ) • (a : A) = 0 := by
            rw [two_smul]; nth_rw 2 [ha]; exact add_neg_cancel _
          have hz : (a : A) = 0 := (smul_eq_zero.mp htwo).resolve_left (by norm_num)
          simp [hz])
  let bwd : (Clsplit n ⊗[ℝ] A) →ₐ[ℝ] (CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] ℬ) :=
    Algebra.TensorProduct.lift
      (GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd (Qsplit n)) ℬ)
      (GradedTensorProduct.includeRight (CliffordAlgebra.evenOdd (Qsplit n)) ℬ)
      (fun x a => by
        have ha0 : a ∈ ℬ 0 := by change (AlgEquiv.refl : A ≃ₐ[ℝ] A) a = a; rfl
        have hlin : ∀ (y : Clsplit n),
            ((y ᵍ⊗ₜ (1 : A) : CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] ℬ) *
              ((1 : Clsplit n) ᵍ⊗ₜ a)) =
              ((1 : Clsplit n) ᵍ⊗ₜ a) * (y ᵍ⊗ₜ (1 : A)) := by
          intro y
          let y0 : Clsplit n := (1 / 2 : ℝ) • (y + CliffordAlgebra.involute y)
          let y1 : Clsplit n := (1 / 2 : ℝ) • (y - CliffordAlgebra.involute y)
          have hy_eq : y = y0 + y1 := by dsimp [y0, y1]; rw [← smul_add]; ring_nf; module
          have hy0 : y0 ∈ CliffordAlgebra.evenOdd (Qsplit n) 0 := by
            rw [mem_evenOdd_zero_iff_involute]
            dsimp [y0]; rw [map_smul, map_add, CliffordAlgebra.involute_involute, add_comm]
          have hy1 : y1 ∈ CliffordAlgebra.evenOdd (Qsplit n) 1 := by
            rw [mem_evenOdd_one_iff_involute]
            dsimp [y1]; rw [map_smul, map_sub, CliffordAlgebra.involute_involute, ← smul_neg]; congr 1; abel
          have hc0 := GradedTensorProduct.tmul_one_mul_one_tmul (CliffordAlgebra.evenOdd (Qsplit n)) ℬ y0 a
          have hc0' := GradedTensorProduct.tmul_coe_mul_coe_tmul (CliffordAlgebra.evenOdd (Qsplit n)) ℬ
            (1 : Clsplit n) ⟨a, ha0⟩ ⟨y0, hy0⟩ (1 : A)
          have hc1 := GradedTensorProduct.tmul_one_mul_one_tmul (CliffordAlgebra.evenOdd (Qsplit n)) ℬ y1 a
          have hc1' := GradedTensorProduct.tmul_coe_mul_coe_tmul (CliffordAlgebra.evenOdd (Qsplit n)) ℬ
            (1 : Clsplit n) ⟨a, ha0⟩ ⟨y1, hy1⟩ (1 : A)
          simp only [one_mul, mul_one, zero_mul, units_neg_one_zmod2_zero, one_smul] at hc0' hc1'
          rw [hy_eq, add_gtmul, add_mul, mul_add, hc0, hc0', hc1, hc1']
        exact Commute.eq (hlin x))
  AlgEquiv.ofAlgHom fwd bwd
    (by
      apply Algebra.TensorProduct.ext
      · apply AlgHom.ext; intro x
        change fwd (bwd (x ⊗ₜ[ℝ] (1 : A))) = x ⊗ₜ[ℝ] (1 : A)
        have hb : bwd (x ⊗ₜ[ℝ] (1 : A)) = x ᵍ⊗ₜ (1 : A) := by
          change GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd (Qsplit n)) ℬ x *
              GradedTensorProduct.includeRight (CliffordAlgebra.evenOdd (Qsplit n)) ℬ (1 : A) =
            x ᵍ⊗ₜ (1 : A)
          rw [GradedTensorProduct.includeLeft_apply, GradedTensorProduct.includeRight_apply,
            GradedTensorProduct.tmul_one_mul_one_tmul]
        have hf : fwd (x ᵍ⊗ₜ (1 : A)) = x ⊗ₜ[ℝ] (1 : A) := by
          dsimp only [fwd]
          rw [GradedTensorProduct.lift_tmul, Algebra.TensorProduct.includeLeft_apply,
            Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
            mul_one, one_mul]
        rw [hb, hf]
      · apply AlgHom.ext; intro a
        change fwd (bwd ((1 : Clsplit n) ⊗ₜ[ℝ] a)) = (1 : Clsplit n) ⊗ₜ[ℝ] a
        have hb : bwd ((1 : Clsplit n) ⊗ₜ[ℝ] a) = (1 : Clsplit n) ᵍ⊗ₜ a := by
          change GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd (Qsplit n)) ℬ (1 : Clsplit n) *
              GradedTensorProduct.includeRight (CliffordAlgebra.evenOdd (Qsplit n)) ℬ a =
            (1 : Clsplit n) ᵍ⊗ₜ a
          rw [GradedTensorProduct.includeLeft_apply, GradedTensorProduct.includeRight_apply,
            GradedTensorProduct.tmul_one_mul_one_tmul]
        have hf : fwd ((1 : Clsplit n) ᵍ⊗ₜ a) = (1 : Clsplit n) ⊗ₜ[ℝ] a := by
          dsimp only [fwd]
          rw [GradedTensorProduct.lift_tmul, Algebra.TensorProduct.includeLeft_apply,
            Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
            mul_one, one_mul]
        rw [hb, hf])
    (by
      apply GradedTensorProduct.algHom_ext
      · apply AlgHom.ext; intro x
        change bwd (fwd (x ᵍ⊗ₜ (1 : A))) = x ᵍ⊗ₜ (1 : A)
        have hf : fwd (x ᵍ⊗ₜ (1 : A)) = x ⊗ₜ[ℝ] (1 : A) := by
          dsimp only [fwd]
          rw [GradedTensorProduct.lift_tmul, Algebra.TensorProduct.includeLeft_apply,
            Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
            mul_one, one_mul]
        have hb : bwd (x ⊗ₜ[ℝ] (1 : A)) = x ᵍ⊗ₜ (1 : A) := by
          change GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd (Qsplit n)) ℬ x *
              GradedTensorProduct.includeRight (CliffordAlgebra.evenOdd (Qsplit n)) ℬ (1 : A) =
            x ᵍ⊗ₜ (1 : A)
          rw [GradedTensorProduct.includeLeft_apply, GradedTensorProduct.includeRight_apply,
            GradedTensorProduct.tmul_one_mul_one_tmul]
        rw [hf, hb]
      · apply AlgHom.ext; intro a
        change bwd (fwd ((1 : Clsplit n) ᵍ⊗ₜ a)) = (1 : Clsplit n) ᵍ⊗ₜ a
        have hf : fwd ((1 : Clsplit n) ᵍ⊗ₜ a) = (1 : Clsplit n) ⊗ₜ[ℝ] a := by
          dsimp only [fwd]
          rw [GradedTensorProduct.lift_tmul, Algebra.TensorProduct.includeLeft_apply,
            Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
            mul_one, one_mul]
        have hb : bwd ((1 : Clsplit n) ⊗ₜ[ℝ] a) = (1 : Clsplit n) ᵍ⊗ₜ a := by
          change GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd (Qsplit n)) ℬ (1 : Clsplit n) *
              GradedTensorProduct.includeRight (CliffordAlgebra.evenOdd (Qsplit n)) ℬ a =
            (1 : Clsplit n) ᵍ⊗ₜ a
          rw [GradedTensorProduct.includeLeft_apply, GradedTensorProduct.includeRight_apply,
            GradedTensorProduct.tmul_one_mul_one_tmul]
        rw [hf, hb])

/-- Ungraded `ℝ`-algebra equivalence `ClTower A n ≃ₐ[ℝ] Clsplit n ⊗[ℝ] A` for an arbitrary
noncommutative real algebra `A` (no involution required). -/
def clTowerEquivCliffordTensor (A : Type*) [Ring A] [Algebra ℝ A] (n : ℕ) :
    ClTower A n ≃ₐ[ℝ] (Clsplit n ⊗[ℝ] A) :=
  (clSplitGradedTensorEquivClTower A AlgEquiv.refl (trivialInvolution_involutive A) n).symm.trans
    (gradedTrivialTensorEquiv A n)

/-- Full matrix-tower equivalence `ClTower A n ≃ₐ[ℝ] Matrix (Fin (2^n)) (Fin (2^n)) A`
for any noncommutative real algebra `A`. -/
def clTowerEquivMatrix (A : Type*) [Ring A] [Algebra ℝ A] (n : ℕ) :
    ClTower A n ≃ₐ[ℝ] Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) A :=
  (clTowerEquivCliffordTensor A n).trans (matrixEquivCliffordTensor n A).symm

/-- Scalar specialization `Clsplit n ≃ₐ[ℝ] ClTower ℝ n`. -/
def clSplitEquivClTowerReal (n : ℕ) : Clsplit n ≃ₐ[ℝ] ClTower ℝ n :=
  (Algebra.TensorProduct.rid ℝ ℝ (Clsplit n)).symm.trans
    (clTowerEquivCliffordTensor ℝ n).symm

end Lane1Lane3Reconciliation

/-! ## Section 3: Embedding & Colimit Reconciliation (`diagEmbed` / `splitCliffordStep` vs `bottEmbed` / `ClInf`) (`F3.1`) -/

section EmbeddingAndColimitReconciliation

open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.ClNN
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11GradedMorita
open InfoGeometry.Clifford.Cl11GradedTensorMorita
open InfoGeometry.Clifford.Cl11RecursiveUnrolling
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordSuperGradeColimit
open InfoGeometry.Canonical.SplitCliffordHeadMorita
open InfoGeometry.Algebra.NoncommutativeCliffordColimitMassGapSynthesis

/-- Under `tensorMatrixEquiv`, `(1 : CliffordAlgebra q11) ᵍ⊗ₜ a` is the parity-twisted
block-diagonal `2 × 2` matrix `mat2 a 0 0 (θ a)`. -/
theorem tensorMatrixEquiv_one_tmul_eq_mat2 {A : Type*} [Ring A] [Algebra ℝ A]
    (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜]
    (θ : A ≃ₐ[ℝ] A) (hEven : ∀ {a}, a ∈ 𝒜 0 → θ a = a) (hOdd : ∀ {a}, a ∈ 𝒜 1 → θ a = -a) (a : A) :
    tensorMatrixEquiv 𝒜 θ hEven hOdd ((1 : CliffordAlgebra q11) ᵍ⊗ₜ a) = mat2 a 0 0 (θ a) := by
  rw [tensorMatrixEquiv_apply, tensorToMatrix_tmul_matrix, map_one]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [mat2, Algebra.smul_def]

/-- When `a` is even (`θ a = a`), `(1 : CliffordAlgebra q11) ᵍ⊗ₜ a` maps to the untwisted
diagonal matrix `mat2 a 0 0 a`. -/
theorem tensorMatrixEquiv_one_tmul_eq_mat2_of_even {A : Type*} [Ring A] [Algebra ℝ A]
    (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜]
    (θ : A ≃ₐ[ℝ] A) (hEven : ∀ {a}, a ∈ 𝒜 0 → θ a = a) (hOdd : ∀ {a}, a ∈ 𝒜 1 → θ a = -a)
    {a : A} (ha : θ a = a) :
    tensorMatrixEquiv 𝒜 θ hEven hOdd ((1 : CliffordAlgebra q11) ᵍ⊗ₜ a) = mat2 a 0 0 a := by
  rw [tensorMatrixEquiv_one_tmul_eq_mat2, ha]

/-- Under `tensorMatrixEquiv`, `(1 : CliffordAlgebra q11) ᵍ⊗ₜ X` is the parity-twisted
diagonal `mat2 X 0 0 (clTowerParity A θ n X)` on `ClTower A n`. -/
theorem tensorMatrixEquiv_one_tmul_eq_twistedDiag {A : Type*} [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ) (X : ClTower A n) :
    tensorMatrixEquiv (clTowerGrading A θ hθ n) (clTowerParity A θ n)
      (fun {_} ha => involutionGrading_even _ _ ha)
      (fun {_} ha => involutionGrading_odd _ _ ha) ((1 : CliffordAlgebra q11) ᵍ⊗ₜ X) =
      mat2 X 0 0 (clTowerParity A θ n X) :=
  tensorMatrixEquiv_one_tmul_eq_mat2 _ _ _ _ X

/-- On even elements (`clTowerParity A θ n X = X`), `(1 : CliffordAlgebra q11) ᵍ⊗ₜ X`
maps directly to `diagEmbed X`. -/
theorem tensorMatrixEquiv_one_tmul_eq_diagEmbed {A : Type*} [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ) {X : ClTower A n}
    (hX : clTowerParity A θ n X = X) :
    tensorMatrixEquiv (clTowerGrading A θ hθ n) (clTowerParity A θ n)
      (fun {_} ha => involutionGrading_even _ _ ha)
      (fun {_} ha => involutionGrading_odd _ _ ha) ((1 : CliffordAlgebra q11) ᵍ⊗ₜ X) =
      diagEmbed X := by
  rw [tensorMatrixEquiv_one_tmul_eq_twistedDiag, hX]
  rfl

/-- Exact preimage of `diagEmbed X` for arbitrary (mixed-parity) `X : ClTower A n`,
splitting `X` into even (`1 ᵍ⊗ₜ X_even`) and odd (`J1_cl ᵍ⊗ₜ X_odd`) parts. -/
theorem tensorMatrixEquiv_diagEmbed_symm {A : Type*} [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ) (X : ClTower A n) :
    (tensorMatrixEquiv (clTowerGrading A θ hθ n) (clTowerParity A θ n)
      (fun {_} ha => involutionGrading_even _ _ ha)
      (fun {_} ha => involutionGrading_odd _ _ ha)).symm (diagEmbed X) =
      (1 : CliffordAlgebra q11) ᵍ⊗ₜ ((1 / 2 : ℝ) • (X + clTowerParity A θ n X)) +
        J1_cl ᵍ⊗ₜ ((1 / 2 : ℝ) • (X - clTowerParity A θ n X)) := by
  let e := tensorMatrixEquiv (clTowerGrading A θ hθ n) (clTowerParity A θ n)
    (fun {_} ha => involutionGrading_even _ _ ha)
    (fun {_} ha => involutionGrading_odd _ _ ha)
  apply e.injective
  rw [AlgEquiv.apply_symm_apply, map_add]
  have he1 : e ((1 : CliffordAlgebra q11) ᵍ⊗ₜ ((1 / 2 : ℝ) • (X + clTowerParity A θ n X))) =
      mat2 ((1 / 2 : ℝ) • (X + clTowerParity A θ n X)) 0 0
        ((1 / 2 : ℝ) • (clTowerParity A θ n X + X)) := by
    change tensorMatrixEquiv (clTowerGrading A θ hθ n) (clTowerParity A θ n) _ _ _ = _
    rw [tensorMatrixEquiv_one_tmul_eq_mat2, map_smul, map_add,
      clTowerParity_involutive A θ hθ n X, add_comm X]
  have heJ : e (J1_cl ᵍ⊗ₜ ((1 / 2 : ℝ) • (X - clTowerParity A θ n X))) =
      mat2 ((1 / 2 : ℝ) • (X - clTowerParity A θ n X)) 0 0
        (-((1 / 2 : ℝ) • (clTowerParity A θ n X - X))) := by
    change tensorMatrixEquiv (clTowerGrading A θ hθ n) (clTowerParity A θ n) _ _ _ = _
    rw [tensorMatrixEquiv_apply, tensorToMatrix_tmul_matrix, cl11StandardEquiv_J1_cl,
      map_smul, map_sub, clTowerParity_involutive A θ hθ n X]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Eplus, mat2, Algebra.smul_def]
  rw [he1, heJ]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diagEmbed, mat2] <;> module

theorem tensorMatrixEquiv_diagEmbed_symm_of_even {A : Type*} [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ) {X : ClTower A n}
    (hX : clTowerParity A θ n X = X) :
    (tensorMatrixEquiv (clTowerGrading A θ hθ n) (clTowerParity A θ n)
      (fun {_} ha => involutionGrading_even _ _ ha)
      (fun {_} ha => involutionGrading_odd _ _ ha)).symm (diagEmbed X) =
      (1 : CliffordAlgebra q11) ᵍ⊗ₜ X := by
  apply (tensorMatrixEquiv (clTowerGrading A θ hθ n) (clTowerParity A θ n)
    (fun {_} ha => involutionGrading_even _ _ ha)
    (fun {_} ha => involutionGrading_odd _ _ ha)).injective
  rw [AlgEquiv.apply_symm_apply, tensorMatrixEquiv_one_tmul_eq_diagEmbed θ hθ n hX]

/-- Under `tensorMatrixEquiv`, `pPlus ᵍ⊗ₜ X` is `bottEmbed X` on `ClTower A n`. -/
theorem tensorMatrixEquiv_pPlus_tmul_eq_bottEmbed {A : Type*} [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ) (X : ClTower A n) :
    tensorMatrixEquiv (clTowerGrading A θ hθ n) (clTowerParity A θ n)
      (fun {_} ha => involutionGrading_even _ _ ha)
      (fun {_} ha => involutionGrading_odd _ _ ha) (pPlus ᵍ⊗ₜ X) =
      bottEmbed X := by
  rw [tensorMatrixEquiv_pPlus_tmul]
  ext i j; fin_cases i <;> fin_cases j <;> simp [bottEmbed, mat2]

/-- Non-unital corner embedding `Clsplit n →ₙₐ[ℝ] Clsplit (n + 1)` sending `x ↦ (headTensorEquiv n).symm (pPlus ᵍ⊗ₜ x)`,
corresponding to `bottEmbed` in Lane 3 (whereas `splitCliffordStep` corresponds to `diagEmbed`). -/
def splitCliffordCornerStep (n : ℕ) : Clsplit n →ₙₐ[ℝ] Clsplit (n + 1) where
  toFun x := (headTensorEquiv n).symm (pPlus ᵍ⊗ₜ x)
  map_zero' := by simp [gtmul_zero]
  map_add' x y := by rw [gtmul_add, map_add]
  map_smul' r x := by rw [gtmul_smul, map_smul]; rfl
  map_mul' x y := by
    rw [← map_mul]
    congr 1
    have hp : pPlus ∈ CliffordAlgebra.evenOdd q11 0 := pPlus_mem_even
    have hmul : (pPlus ᵍ⊗ₜ (x * y) :
        CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n)) =
        (pPlus ᵍ⊗ₜ x) * (pPlus ᵍ⊗ₜ y) := by
      have h1 : (pPlus ᵍ⊗ₜ x :
          CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n)) =
          (pPlus ᵍ⊗ₜ (1 : Clsplit n)) * ((1 : CliffordAlgebra q11) ᵍ⊗ₜ x) :=
        (GradedTensorProduct.tmul_one_mul_one_tmul _ _ pPlus x).symm
      have hcomm_pPlus : ∀ z : Clsplit n,
          ((1 : CliffordAlgebra q11) ᵍ⊗ₜ z :
            CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n)) *
            (pPlus ᵍ⊗ₜ (1 : Clsplit n)) =
          (pPlus ᵍ⊗ₜ (1 : Clsplit n)) * ((1 : CliffordAlgebra q11) ᵍ⊗ₜ z) := by
        intro z
        let z0 : Clsplit n := (1 / 2 : ℝ) • (z + CliffordAlgebra.involute z)
        let z1 : Clsplit n := (1 / 2 : ℝ) • (z - CliffordAlgebra.involute z)
        have hz_eq : z = z0 + z1 := by dsimp [z0, z1]; rw [← smul_add]; ring_nf; module
        have hz0 : z0 ∈ CliffordAlgebra.evenOdd (Qsplit n) 0 := by
          rw [mem_evenOdd_zero_iff_involute]
          dsimp [z0]; rw [map_smul, map_add, CliffordAlgebra.involute_involute, add_comm]
        have hz1 : z1 ∈ CliffordAlgebra.evenOdd (Qsplit n) 1 := by
          rw [mem_evenOdd_one_iff_involute]
          dsimp [z1]; rw [map_smul, map_sub, CliffordAlgebra.involute_involute, ← smul_neg]; congr 1; abel
        have hc0 := GradedTensorProduct.tmul_coe_mul_coe_tmul
          (CliffordAlgebra.evenOdd q11) (CliffordAlgebra.evenOdd (Qsplit n))
          (1 : CliffordAlgebra q11) ⟨z0, hz0⟩ ⟨pPlus, hp⟩ (1 : Clsplit n)
        have hc1 := GradedTensorProduct.tmul_coe_mul_coe_tmul
          (CliffordAlgebra.evenOdd q11) (CliffordAlgebra.evenOdd (Qsplit n))
          (1 : CliffordAlgebra q11) ⟨z1, hz1⟩ ⟨pPlus, hp⟩ (1 : Clsplit n)
        simp only [one_mul, mul_one, mul_zero, units_neg_one_zmod2_zero, one_smul] at hc0 hc1
        rw [hz_eq, gtmul_add, add_mul, mul_add, hc0, hc1,
          GradedTensorProduct.tmul_one_mul_one_tmul,
          GradedTensorProduct.tmul_one_mul_one_tmul]
      have h2 : (pPlus ᵍ⊗ₜ y :
          CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n)) =
          ((1 : CliffordAlgebra q11) ᵍ⊗ₜ y) * (pPlus ᵍ⊗ₜ (1 : Clsplit n)) := by
        rw [hcomm_pPlus y]
        exact (GradedTensorProduct.tmul_one_mul_one_tmul _ _ pPlus y).symm
      rw [h1, h2]
      symm
      calc ((pPlus ᵍ⊗ₜ (1 : Clsplit n) :
              CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n)) *
              ((1 : CliffordAlgebra q11) ᵍ⊗ₜ x)) *
              (((1 : CliffordAlgebra q11) ᵍ⊗ₜ y) * (pPlus ᵍ⊗ₜ (1 : Clsplit n)))
          = (pPlus ᵍ⊗ₜ (1 : Clsplit n)) * (((1 : CliffordAlgebra q11) ᵍ⊗ₜ x) * ((1 : CliffordAlgebra q11) ᵍ⊗ₜ y)) *
              (pPlus ᵍ⊗ₜ (1 : Clsplit n)) := by
            rw [mul_assoc, ← mul_assoc ((1 : CliffordAlgebra q11) ᵍ⊗ₜ x),
              ← mul_assoc (pPlus ᵍ⊗ₜ (1 : Clsplit n))]
        _ = (pPlus ᵍ⊗ₜ (1 : Clsplit n)) * ((1 : CliffordAlgebra q11) ᵍ⊗ₜ (x * y)) * (pPlus ᵍ⊗ₜ (1 : Clsplit n)) := by
            rw [← GradedTensorProduct.includeRight_apply (CliffordAlgebra.evenOdd q11)
                (CliffordAlgebra.evenOdd (Qsplit n)) x,
              ← GradedTensorProduct.includeRight_apply (CliffordAlgebra.evenOdd q11)
                (CliffordAlgebra.evenOdd (Qsplit n)) y,
              ← map_mul, GradedTensorProduct.includeRight_apply]
        _ = (pPlus ᵍ⊗ₜ (1 : Clsplit n)) * ((pPlus ᵍ⊗ₜ (1 : Clsplit n)) * ((1 : CliffordAlgebra q11) ᵍ⊗ₜ (x * y))) := by
            rw [mul_assoc, hcomm_pPlus (x * y)]
        _ = ((pPlus ᵍ⊗ₜ (1 : Clsplit n)) * (pPlus ᵍ⊗ₜ (1 : Clsplit n))) * ((1 : CliffordAlgebra q11) ᵍ⊗ₜ (x * y)) := by
            rw [mul_assoc]
        _ = (pPlus ᵍ⊗ₜ (1 : Clsplit n)) * ((1 : CliffordAlgebra q11) ᵍ⊗ₜ (x * y)) := by
            have hpp : (pPlus ᵍ⊗ₜ (1 : Clsplit n) :
                CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n)) *
                (pPlus ᵍ⊗ₜ (1 : Clsplit n)) = pPlus ᵍ⊗ₜ (1 : Clsplit n) := by
              change GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd q11)
                  (CliffordAlgebra.evenOdd (Qsplit n)) pPlus *
                GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd q11)
                  (CliffordAlgebra.evenOdd (Qsplit n)) pPlus = _
              rw [← map_mul, pPlus_sq]
              rfl
            rw [hpp]
        _ = pPlus ᵍ⊗ₜ (x * y) :=
            GradedTensorProduct.tmul_one_mul_one_tmul _ _ pPlus (x * y)
    exact hmul

/-- Unconditional compatibility of `clSplitGradedTensorEquivClTower` with `splitCliffordStep`:
for every `x : Clsplit n` and `a : A`, `splitCliffordStep n x ᵍ⊗ₜ a` maps to the parity-twisted
block diagonal `mat2 Y 0 0 (clTowerParity A θ n Y)` where `Y = clSplitGradedTensorEquivClTower n (x ᵍ⊗ₜ a)`. -/
theorem clSplitGradedTensorEquivClTower_splitCliffordStep (A : Type*) [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ) (x : Clsplit n) (a : A) :
    clSplitGradedTensorEquivClTower A θ hθ (n + 1) ((splitCliffordStep n x) ᵍ⊗ₜ a) =
      mat2 (clSplitGradedTensorEquivClTower A θ hθ n (x ᵍ⊗ₜ a)) 0 0
        (clTowerParity A θ n (clSplitGradedTensorEquivClTower A θ hθ n (x ᵍ⊗ₜ a))) := by
  have hstep_head :
      headTensorToClTowerStep A θ hθ n
          (clSplitGradedTensorEquivClTower A θ hθ n)
          (clSplitGradedTensorEquivClTower_parity A θ hθ n)
          (splitCliffordStep n x) =
        (1 : CliffordAlgebra q11) ᵍ⊗ₜ
          (clSplitGradedTensorEquivClTower A θ hθ n (x ᵍ⊗ₜ (1 : A))) := by
    have hhom :
        (headTensorToClTowerStep A θ hθ n
          (clSplitGradedTensorEquivClTower A θ hθ n)
          (clSplitGradedTensorEquivClTower_parity A θ hθ n)).comp (splitCliffordStep n) =
          (GradedTensorProduct.includeRight (CliffordAlgebra.evenOdd q11)
            (clTowerGrading A θ hθ n)).comp
            ((clSplitGradedTensorEquivClTower A θ hθ n).toAlgHom.comp
              (GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd (Qsplit n))
                (involutionGrading θ hθ))) := by
      apply CliffordAlgebra.hom_ext; apply LinearMap.ext; intro u
      simp only [AlgHom.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        GradedTensorProduct.includeRight_apply, GradedTensorProduct.includeLeft_apply]
      rw [splitCliffordStep_ι, headTensorToClTowerStep_ι,
        show (((0 : ℝ), (0 : ℝ)), u).1 = (0 : ℝ × ℝ) from rfl,
        map_zero, zero_gtmul, zero_add]
      rfl
    exact AlgHom.congr_fun hhom x
  have htmul : ((splitCliffordStep n x) ᵍ⊗ₜ a :
      CliffordAlgebra.evenOdd (Qsplit (n + 1)) ᵍ⊗[ℝ] involutionGrading θ hθ) =
      (splitCliffordStep n x ᵍ⊗ₜ (1 : A)) * ((1 : Clsplit (n + 1)) ᵍ⊗ₜ a) :=
    (GradedTensorProduct.tmul_one_mul_one_tmul _ _ _ _).symm
  rw [htmul, map_mul, clSplitGradedTensorEquivClTower_succ_tmul_one,
    clSplitGradedTensorEquivClTower_succ_one_tmul, hstep_head, ← map_mul]
  have hprod : (((1 : CliffordAlgebra q11) ᵍ⊗ₜ
        clSplitGradedTensorEquivClTower A θ hθ n (x ᵍ⊗ₜ (1 : A)) :
        CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] clTowerGrading A θ hθ n) *
      ((1 : CliffordAlgebra q11) ᵍ⊗ₜ
        clSplitGradedTensorEquivClTower A θ hθ n ((1 : Clsplit n) ᵍ⊗ₜ a))) =
      (1 : CliffordAlgebra q11) ᵍ⊗ₜ
        clSplitGradedTensorEquivClTower A θ hθ n (x ᵍ⊗ₜ a) := by
    rw [one_gtmul_mul_one_gtmul, ← map_mul,
      GradedTensorProduct.tmul_one_mul_one_tmul]
  rw [hprod]
  exact tensorMatrixEquiv_one_tmul_eq_twistedDiag θ hθ n _

/-- On the even sector (`clTowerParity A θ n (clSplitGradedTensorEquivClTower n (x ᵍ⊗ₜ a)) = ...`),
`splitCliffordStep` (Lane 1) intertwines directly with `diagEmbed` (Lane 3). -/
theorem clSplitGradedTensorEquivClTower_diagEmbed_even (A : Type*) [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ) (x : Clsplit n) (a : A)
    (heven : clTowerParity A θ n (clSplitGradedTensorEquivClTower A θ hθ n (x ᵍ⊗ₜ a)) =
      clSplitGradedTensorEquivClTower A θ hθ n (x ᵍ⊗ₜ a)) :
    clSplitGradedTensorEquivClTower A θ hθ (n + 1) ((splitCliffordStep n x) ᵍ⊗ₜ a) =
      diagEmbed (clSplitGradedTensorEquivClTower A θ hθ n (x ᵍ⊗ₜ a)) := by
  rw [clSplitGradedTensorEquivClTower_splitCliffordStep, heven]
  rfl

/-- Compatibility of `clSplitGradedTensorEquivClTower` with `splitCliffordCornerStep` (Lane 1) and
`bottEmbed` (Lane 3), reconciling unital `SplitCliffordInfinity` (along `splitCliffordStep`)
with non-unital `ClInf A` (along `bottEmbed` = `cornerProj * diagEmbed`). -/
theorem clSplitGradedTensorEquivClTower_bottEmbed (A : Type*) [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ) (x : Clsplit n) (a : A) :
    clSplitGradedTensorEquivClTower A θ hθ (n + 1) ((splitCliffordCornerStep n x) ᵍ⊗ₜ a) =
      bottEmbed (clSplitGradedTensorEquivClTower A θ hθ n (x ᵍ⊗ₜ a)) := by
  let cp : Clsplit (n + 1) := (headTensorEquiv n).symm (pPlus ᵍ⊗ₜ (1 : Clsplit n))
  have hcorner : splitCliffordCornerStep n x = cp * splitCliffordStep n x := by
    apply (headTensorEquiv n).injective
    change headTensorEquiv n ((headTensorEquiv n).symm (pPlus ᵍ⊗ₜ x)) =
      headTensorEquiv n (cp * splitCliffordStep n x)
    rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply,
      headTensorEquiv_splitCliffordStep]
    exact (GradedTensorProduct.tmul_one_mul_one_tmul _ _ pPlus x).symm
  have hmul_tmul : ((cp * splitCliffordStep n x) ᵍ⊗ₜ a :
      CliffordAlgebra.evenOdd (Qsplit (n + 1)) ᵍ⊗[ℝ] involutionGrading θ hθ) =
      (cp ᵍ⊗ₜ (1 : A)) * ((splitCliffordStep n x) ᵍ⊗ₜ a) := by
    have hcp1 : (cp ᵍ⊗ₜ (1 : A) :
        CliffordAlgebra.evenOdd (Qsplit (n + 1)) ᵍ⊗[ℝ] involutionGrading θ hθ) =
        GradedTensorProduct.includeLeft _ _ cp := rfl
    have h2 : ((splitCliffordStep n x) ᵍ⊗ₜ a :
        CliffordAlgebra.evenOdd (Qsplit (n + 1)) ᵍ⊗[ℝ] involutionGrading θ hθ) =
        GradedTensorProduct.includeLeft _ _ (splitCliffordStep n x) *
          GradedTensorProduct.includeRight _ _ a :=
      (GradedTensorProduct.tmul_one_mul_one_tmul _ _ _ _).symm
    rw [hcp1, h2, ← mul_assoc,
      ← map_mul (GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd (Qsplit (n + 1)))
        (involutionGrading θ hθ))]
    exact (GradedTensorProduct.tmul_one_mul_one_tmul (CliffordAlgebra.evenOdd (Qsplit (n + 1)))
      (involutionGrading θ hθ) (cp * splitCliffordStep n x) a).symm
  rw [hcorner, hmul_tmul, map_mul, clSplitGradedTensorEquivClTower_splitCliffordStep]
  have hcp_val : clSplitGradedTensorEquivClTower A θ hθ (n + 1) (cp ᵍ⊗ₜ (1 : A)) =
      cornerProj (A := A) n := by
    rw [clSplitGradedTensorEquivClTower_succ_tmul_one]
    have hcp_head : headTensorToClTowerStep A θ hθ n
        (clSplitGradedTensorEquivClTower A θ hθ n)
        (clSplitGradedTensorEquivClTower_parity A θ hθ n) cp =
        pPlus ᵍ⊗ₜ (1 : ClTower A n) := by
      have hp_def : pPlus =
          (1 / 2 : ℝ) • ((1 : CliffordAlgebra q11) +
            CliffordAlgebra.ι q11 (1, 0) * CliffordAlgebra.ι q11 (0, 1)) := rfl
      have hcp_expr : cp =
          (1 / 2 : ℝ) • ((1 : Clsplit (n + 1)) +
            CliffordAlgebra.ι (Qsplit (n + 1)) ((1, 0), 0) *
              CliffordAlgebra.ι (Qsplit (n + 1)) ((0, 1), 0)) := by
        apply (headTensorEquiv n).injective
        rw [AlgEquiv.apply_symm_apply, map_smul, map_add, map_one, map_mul,
          headTensorEquiv_ι, headTensorEquiv_ι]
        simp only [map_zero, gtmul_zero, add_zero]
        have hmul := GradedTensorProduct.tmul_coe_mul_coe_tmul (CliffordAlgebra.evenOdd q11)
          (CliffordAlgebra.evenOdd (Qsplit n))
          (CliffordAlgebra.ι q11 (1, 0)) (1 : CliffordAlgebra.evenOdd (Qsplit n) 0)
          ⟨CliffordAlgebra.ι q11 (0, 1), CliffordAlgebra.ι_mem_evenOdd_one _ _⟩ (1 : Clsplit n)
        simp only [show ((1 : CliffordAlgebra.evenOdd (Qsplit n) 0) : Clsplit n) = 1 from rfl,
          mul_one, units_neg_one_zmod2_zero, one_smul] at hmul
        rw [hmul, hp_def, smul_gtmul, add_gtmul]
        rfl
      rw [hcp_expr, map_smul, map_add, map_one, map_mul,
        headTensorToClTowerStep_ι, headTensorToClTowerStep_ι]
      simp only [map_zero, zero_gtmul, gtmul_zero, add_zero]
      have hmul2 := GradedTensorProduct.tmul_coe_mul_coe_tmul (CliffordAlgebra.evenOdd q11)
        (clTowerGrading A θ hθ n)
        (CliffordAlgebra.ι q11 (1, 0)) (1 : clTowerGrading A θ hθ n 0)
        ⟨CliffordAlgebra.ι q11 (0, 1), CliffordAlgebra.ι_mem_evenOdd_one _ _⟩ (1 : ClTower A n)
      simp only [show ((1 : clTowerGrading A θ hθ n 0) : ClTower A n) = 1 from rfl,
        mul_one, units_neg_one_zmod2_zero, one_smul] at hmul2
      rw [hmul2, hp_def, smul_gtmul, add_gtmul]
      rfl
    rw [hcp_head, tensorMatrixEquiv_pPlus_tmul]
    ext i j; fin_cases i <;> fin_cases j <;> simp [cornerProj]
  rw [hcp_val]
  apply ext_fin2 <;> simp [cornerProj, bottEmbed]

/-- Recursive chirality element in `Clsplit n` mapping to `chiralityOp (A := A) n` under
`clSplitGradedTensorEquivClTower`. -/
def splitChiralityElement : (n : ℕ) → Clsplit n
  | 0 => 1
  | n + 1 => (headTensorEquiv n).symm (J1_cl ᵍ⊗ₜ splitChiralityElement n)

theorem splitChiralityElement_even (n : ℕ) :
    splitChiralityElement n ∈ CliffordAlgebra.evenOdd (Qsplit n) 0 := by
  induction n with
  | zero => exact (mem_evenOdd_zero_iff_involute _ _).mpr (map_one _)
  | succ n ih =>
      rw [mem_evenOdd_zero_iff_involute]
      apply (headTensorEquiv n).injective
      change headTensorEquiv n (nativeParity (n + 1) (splitChiralityElement (n + 1))) =
        headTensorEquiv n (splitChiralityElement (n + 1))
      rw [headTensorEquiv_involute, splitChiralityElement, AlgEquiv.apply_symm_apply,
        tensorParity_tmul]
      have hJ : CliffordAlgebra.involute J1_cl = J1_cl := by
        rw [J1_cl, map_mul, CliffordAlgebra.involute_ι, CliffordAlgebra.involute_ι, neg_mul_neg]
      have hn : nativeParity n (splitChiralityElement n) = splitChiralityElement n :=
        nativeParity_even n ih
      rw [hJ, hn]

theorem clSplitGradedTensorEquivClTower_chiralityOp (A : Type*) [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ) :
    clSplitGradedTensorEquivClTower A θ hθ n ((splitChiralityElement n) ᵍ⊗ₜ (1 : A)) =
      chiralityOp (A := A) n := by
  induction n with
  | zero =>
      dsimp only [clSplitGradedTensorEquivClTower, clSplitGradedTensorEquivPair,
        splitChiralityElement]
      rw [gradedSplitZeroTensorEquiv_tmul]
      simp [chiralityOp]
  | succ n ih =>
      have hj_expr : (headTensorEquiv n).symm (J1_cl ᵍ⊗ₜ splitChiralityElement n) =
          ((headTensorEquiv n).symm (J1_cl ᵍ⊗ₜ (1 : Clsplit n))) *
            splitCliffordStep n (splitChiralityElement n) := by
        apply (headTensorEquiv n).injective
        rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply,
          headTensorEquiv_splitCliffordStep]
        exact (GradedTensorProduct.tmul_one_mul_one_tmul _ _ _ _).symm
      have hhead_j1 : headTensorToClTowerStep A θ hθ n
          (clSplitGradedTensorEquivClTower A θ hθ n)
          (clSplitGradedTensorEquivClTower_parity A θ hθ n)
          ((headTensorEquiv n).symm (J1_cl ᵍ⊗ₜ (1 : Clsplit n))) =
          J1_cl ᵍ⊗ₜ (1 : ClTower A n) := by
        have h1 : (headTensorEquiv n).symm (J1_cl ᵍ⊗ₜ (1 : Clsplit n)) =
            CliffordAlgebra.ι (Qsplit (n + 1)) ((1, 0), 0) *
              CliffordAlgebra.ι (Qsplit (n + 1)) ((0, 1), 0) := by
          apply (headTensorEquiv n).injective
          rw [AlgEquiv.apply_symm_apply, map_mul, headTensorEquiv_ι, headTensorEquiv_ι]
          simp only [map_zero, gtmul_zero, add_zero]
          have hmul := GradedTensorProduct.tmul_coe_mul_coe_tmul (CliffordAlgebra.evenOdd q11)
            (CliffordAlgebra.evenOdd (Qsplit n))
            (CliffordAlgebra.ι q11 (1, 0)) (1 : CliffordAlgebra.evenOdd (Qsplit n) 0)
            ⟨CliffordAlgebra.ι q11 (0, 1), CliffordAlgebra.ι_mem_evenOdd_one _ _⟩ (1 : Clsplit n)
          simp only [show ((1 : CliffordAlgebra.evenOdd (Qsplit n) 0) : Clsplit n) = 1 from rfl,
            mul_one, units_neg_one_zmod2_zero, one_smul] at hmul
          rw [hmul]
          simp [J1_cl]
        rw [h1, map_mul, headTensorToClTowerStep_ι, headTensorToClTowerStep_ι]
        simp only [map_zero, zero_gtmul, gtmul_zero, add_zero]
        change (GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd q11)
            (clTowerGrading A θ hθ n) (CliffordAlgebra.ι q11 (1, 0))) *
          (GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd q11)
            (clTowerGrading A θ hθ n) (CliffordAlgebra.ι q11 (0, 1))) = _
        rw [← map_mul]
        rfl
      have hstep_ch : headTensorToClTowerStep A θ hθ n
          (clSplitGradedTensorEquivClTower A θ hθ n)
          (clSplitGradedTensorEquivClTower_parity A θ hθ n)
          (splitCliffordStep n (splitChiralityElement n)) =
          (1 : CliffordAlgebra q11) ᵍ⊗ₜ chiralityOp (A := A) n := by
        have hhom :
            (headTensorToClTowerStep A θ hθ n
              (clSplitGradedTensorEquivClTower A θ hθ n)
              (clSplitGradedTensorEquivClTower_parity A θ hθ n)).comp (splitCliffordStep n) =
              (GradedTensorProduct.includeRight (CliffordAlgebra.evenOdd q11)
                (clTowerGrading A θ hθ n)).comp
                ((clSplitGradedTensorEquivClTower A θ hθ n).toAlgHom.comp
                  (GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd (Qsplit n))
                    (involutionGrading θ hθ))) := by
          apply CliffordAlgebra.hom_ext; apply LinearMap.ext; intro u
          simp only [AlgHom.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
            GradedTensorProduct.includeRight_apply, GradedTensorProduct.includeLeft_apply]
          rw [splitCliffordStep_ι, headTensorToClTowerStep_ι,
            show (((0 : ℝ), (0 : ℝ)), u).1 = (0 : ℝ × ℝ) from rfl,
            map_zero, zero_gtmul, zero_add]
          rfl
        have happ := AlgHom.congr_fun hhom (splitChiralityElement n)
        simp only [AlgHom.comp_apply, GradedTensorProduct.includeRight_apply,
          GradedTensorProduct.includeLeft_apply] at happ
        rw [happ]
        change (1 : CliffordAlgebra q11) ᵍ⊗ₜ
          clSplitGradedTensorEquivClTower A θ hθ n (splitChiralityElement n ᵍ⊗ₜ (1 : A)) = _
        rw [ih]
      rw [splitChiralityElement, clSplitGradedTensorEquivClTower_succ_tmul_one, hj_expr,
        map_mul, hhead_j1, hstep_ch, GradedTensorProduct.tmul_one_mul_one_tmul]
      have hch_even : clTowerParity A θ n (chiralityOp (A := A) n) = chiralityOp (A := A) n := by
        rw [← ih, clSplitGradedTensorEquivClTower_parity, towerParityAux_tmul,
          CliffordAlgebra.involute_eq_of_mem_even (splitChiralityElement_even n), map_one]
      rw [tensorMatrixEquiv_apply, tensorToMatrix_tmul_matrix, cl11StandardEquiv_J1_cl, hch_even]
      ext i j; fin_cases i <;> fin_cases j <;> simp [chiralityOp, Eplus, mat2]

/-- Recursive Cantor vacuum projection in `Clsplit n`, starting at `1` and iterating
`splitCliffordCornerStep`. -/
def splitCantorProj : (n : ℕ) → Clsplit n
  | 0 => 1
  | n + 1 => splitCliffordCornerStep n (splitCantorProj n)

theorem clSplitGradedTensorEquivClTower_cornerProj (A : Type*) [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ) :
    clSplitGradedTensorEquivClTower A θ hθ (n + 1)
        (((headTensorEquiv n).symm (pPlus ᵍ⊗ₜ (1 : Clsplit n))) ᵍ⊗ₜ (1 : A)) =
      cornerProj (A := A) n := by
  have h : clSplitGradedTensorEquivClTower A θ hθ (n + 1)
      ((splitCliffordCornerStep n 1) ᵍ⊗ₜ (1 : A)) =
      bottEmbed (clSplitGradedTensorEquivClTower A θ hθ n ((1 : Clsplit n) ᵍ⊗ₜ (1 : A))) :=
    clSplitGradedTensorEquivClTower_bottEmbed A θ hθ n 1 1
  change clSplitGradedTensorEquivClTower A θ hθ (n + 1)
      ((splitCliffordCornerStep n 1) ᵍ⊗ₜ (1 : A)) = cornerProj (A := A) n
  rw [h]
  have hone : ((1 : Clsplit n) ᵍ⊗ₜ (1 : A) :
      CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ) = 1 := rfl
  rw [hone, map_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [bottEmbed, cornerProj]

theorem clSplitGradedTensorEquivClTower_cantorProj (A : Type*) [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (hθ : Function.Involutive θ) (n : ℕ) :
    clSplitGradedTensorEquivClTower A θ hθ n (splitCantorProj n ᵍ⊗ₜ (1 : A)) =
      cantorProj (A := A) n := by
  induction n with
  | zero =>
      dsimp only [clSplitGradedTensorEquivClTower, clSplitGradedTensorEquivPair, splitCantorProj]
      rw [gradedSplitZeroTensorEquiv_tmul]
      simp [cantorProj]
  | succ n ih =>
      change clSplitGradedTensorEquivClTower A θ hθ (n + 1)
          ((splitCliffordCornerStep n (splitCantorProj n)) ᵍ⊗ₜ (1 : A)) =
        bottEmbed (cantorProj (A := A) n)
      rw [clSplitGradedTensorEquivClTower_bottEmbed, ih]

end EmbeddingAndColimitReconciliation

/-! ## Section 4: `V4` Lifts, Erlangen `G_swap`, and Cantor `LocalCl11` Compatibility (`F3.2`) -/

section KleinFourLiftAndErlangenUnification

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11GradedMorita
open InfoGeometry.Clifford.Cl11GradedTensorMorita
open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.ClNN
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Topology.V4RootSystem
open InfoGeometry.Canonical.KleinFourTagRootNormalization hiding V4
open InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation
open InfoGeometry.Canonical.SplitCliffordHeadMorita
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordSuperGradeColimit
open InfoGeometry.Canonical.SplitCliffordHeadTailTower
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.CantorDoubleCylinderFractalColimit
open InfoGeometry.OperatorAlgebra.ErlangenDoubleCylinderSymmetryInvariants
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Algebra.CliffordBitWordEquivalence
open InfoGeometry.Recovered.CantorCliffordLimitBridge
open InfoGeometry.Canonical.CantorBinaryTiltCARCCRBridge
open InfoGeometry.Canonical.CantorLocalCl11Universal
open InfoGeometry.Canonical.CantorLocalCl11OrthogonalAction

/-- Lift `cl11V4Auto` to the `Cl(1,1)` head factor of `evenOdd q11 ᵍ⊗[ℝ] 𝒜`. -/
def tensorHeadV4Action {A : Type*} [Ring A] [Algebra ℝ A]
    (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜] :
    V4 →* ((CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) ≃ₐ[ℝ]
      (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜)) where
  toFun g := headLiftAlgEquiv 𝒜 (cl11V4Auto g) (cl11V4_involute_comm g)
  map_one' := by
    apply AlgEquiv.ext; intro z
    change headLiftAlgEquiv 𝒜 (cl11V4Auto 1) _ z = z
    obtain ⟨t, rfl⟩ := (GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11) 𝒜).surjective z
    induction t using TensorProduct.inductionOn with
    | tmul x a =>
        rw [headLiftAlgEquiv_tmul]; simp [cl11V4Auto_one]
    | add u v hu hv =>
        simp only [map_add] at hu hv ⊢; rw [hu, hv]
  map_mul' g h := by
    apply AlgEquiv.ext; intro z
    obtain ⟨t, rfl⟩ := (GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11) 𝒜).surjective z
    induction t using TensorProduct.inductionOn with
    | tmul x a =>
        change headLiftAlgEquiv 𝒜 (cl11V4Auto (g * h)) (cl11V4_involute_comm (g * h)) (x ᵍ⊗ₜ a) =
          headLiftAlgEquiv 𝒜 (cl11V4Auto g) (cl11V4_involute_comm g)
            (headLiftAlgEquiv 𝒜 (cl11V4Auto h) (cl11V4_involute_comm h) (x ᵍ⊗ₜ a))
        rw [headLiftAlgEquiv_tmul, headLiftAlgEquiv_tmul, headLiftAlgEquiv_tmul, map_mul]
        rfl
    | add u v hu hv =>
        simp only [map_add] at hu hv ⊢; rw [hu, hv]

/-- `SymmetryAction V4` on `evenOdd q11 ᵍ⊗[ℝ] 𝒜`. -/
def tensorHeadV4SymmetryAction {A : Type*} [Ring A] [Algebra ℝ A]
    (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜] :
    SymmetryAction V4 (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) where
  act g := (tensorHeadV4Action 𝒜 g).toRingEquiv
  act_one x := by
    change tensorHeadV4Action 𝒜 1 x = x
    rw [map_one]; rfl
  act_mul g h x := by simp [map_mul]

/-- Head `V4` symmetry on `Matrix (Fin 2) (Fin 2) A` (with `walshV4Swap`, matching `cl11StandardEquiv`
and `θ` entrywise twist for `P` / `PT`). -/
def matrixHeadV4Act {A : Type*} [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (g : V4) :
    Matrix (Fin 2) (Fin 2) A ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) A :=
  if g = 1 then AlgEquiv.refl
  else if g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T then
    matrixScalarAdjoint (A := A) gammaUnit
  else if g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P then
    let twist : Matrix (Fin 2) (Fin 2) A ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) A :=
      AlgEquiv.ofRingEquiv
        (f := (RingEquiv.mapMatrix θ.toRingEquiv : Matrix (Fin 2) (Fin 2) A ≃+* Matrix (Fin 2) (Fin 2) A))
        (fun (r : ℝ) => by
          ext i j; fin_cases i <;> fin_cases j <;> simp [Algebra.algebraMap_eq_smul_one])
    twist.trans (matrixScalarAdjoint (A := A) bivectorUnit)
  else
    let twist : Matrix (Fin 2) (Fin 2) A ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) A :=
      AlgEquiv.ofRingEquiv
        (f := (RingEquiv.mapMatrix θ.toRingEquiv : Matrix (Fin 2) (Fin 2) A ≃+* Matrix (Fin 2) (Fin 2) A))
        (fun (r : ℝ) => by
          ext i j; fin_cases i <;> fin_cases j <;> simp [Algebra.algebraMap_eq_smul_one])
    twist.trans (matrixScalarAdjoint (A := A) causalUnit)

/-- Equivariance of `tensorMatrixEquiv` between `tensorHeadV4Action` and `matrixHeadV4Act`. -/
theorem tensorMatrixEquiv_headV4_equivariant {A : Type*} [Ring A] [Algebra ℝ A]
    (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜]
    (θ : A ≃ₐ[ℝ] A) (hEven : ∀ {a}, a ∈ 𝒜 0 → θ a = a) (hOdd : ∀ {a}, a ∈ 𝒜 1 → θ a = -a)
    (g : V4) (z : CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) :
    tensorMatrixEquiv 𝒜 θ hEven hOdd (tensorHeadV4Action 𝒜 g z) =
      matrixHeadV4Act θ g
        (tensorMatrixEquiv 𝒜 θ hEven hOdd z) := by
  have hcases : g = 1 ∨ g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P ∨
      g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T ∨
      g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT := by
    revert g; decide
  rcases hcases with rfl | rfl | rfl | rfl
  · simp only [matrixHeadV4Act, ↓reduceIte, tensorHeadV4Action, MonoidHom.coe_mk, OneHom.coe_mk]
    have h1 : cl11V4Auto (1 : V4) = AlgEquiv.refl := cl11V4Auto_one
    obtain ⟨t, rfl⟩ := (GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11) 𝒜).surjective z
    induction t using TensorProduct.inductionOn with
    | tmul x a => rw [headLiftAlgEquiv_tmul, h1]; rfl
    | add u v hu hv => simp only [map_add] at hu hv ⊢; rw [hu, hv]
  · simp only [matrixHeadV4Act, tensorHeadV4Action]
    exact tensorMatrixEquiv_headLift_splitReflection 𝒜 θ hEven hOdd z
  · simp only [matrixHeadV4Act, tensorHeadV4Action]
    exact tensorMatrixEquiv_headLift_involute 𝒜 θ hEven hOdd z
  · simp only [matrixHeadV4Act, tensorHeadV4Action]
    exact tensorMatrixEquiv_headLift_splitReflectionFirstCoordinate 𝒜 θ hEven hOdd z

/-- Root-head `V4` automorphisms on `Clsplit 1` via `splitOneClifford`. -/
def headV4ClsplitOneAuto (g : V4) : Clsplit 1 ≃ₐ[ℝ] Clsplit 1 :=
  (splitOneClifford.trans (cl11V4Auto g)).trans splitOneClifford.symm

theorem splitOneClifford_involute (x : Clsplit 1) :
    splitOneClifford (CliffordAlgebra.involute x) =
      CliffordAlgebra.involute (splitOneClifford x) := by
  have hhom : splitOneClifford.toAlgHom.comp (CliffordAlgebra.involute (Q := Qsplit 1)) =
      (CliffordAlgebra.involute (Q := q11)).comp splitOneClifford.toAlgHom := by
    apply CliffordAlgebra.hom_ext; apply LinearMap.ext; intro v
    simp [splitOneClifford, CliffordAlgebra.equivOfIsometry_apply, CliffordAlgebra.map_apply_ι]
  exact AlgHom.congr_fun hhom x

theorem headV4ClsplitOneAuto_involute (g : V4) (x : Clsplit 1) :
    headV4ClsplitOneAuto g (CliffordAlgebra.involute x) =
      CliffordAlgebra.involute (headV4ClsplitOneAuto g x) := by
  dsimp [headV4ClsplitOneAuto]
  rw [splitOneClifford_involute, cl11V4_involute_comm]
  apply splitOneClifford.injective
  rw [AlgEquiv.apply_symm_apply, splitOneClifford_involute, AlgEquiv.apply_symm_apply]

/-- Root-head `V4` lift on `SplitCliffordHeadTailStage 1 n = evenOdd (Qsplit 1) ᵍ⊗ evenOdd (Qsplit n)`. -/
def headV4HeadTailStageAuto (n : ℕ) (g : V4) :
    SplitCliffordHeadTailStage 1 n ≃ₐ[ℝ] SplitCliffordHeadTailStage 1 n :=
  let f : Clsplit 1 →ₐ[ℝ] SplitCliffordHeadTailStage 1 n :=
    (GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd (Qsplit 1))
      (CliffordAlgebra.evenOdd (Qsplit n))).comp (headV4ClsplitOneAuto g).toAlgHom
  let f_inv : Clsplit 1 →ₐ[ℝ] SplitCliffordHeadTailStage 1 n :=
    (GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd (Qsplit 1))
      (CliffordAlgebra.evenOdd (Qsplit n))).comp (headV4ClsplitOneAuto g).symm.toAlgHom
  have hmem : ∀ (φ : Clsplit 1 →ₐ[ℝ] Clsplit 1)
      (hφ : ∀ y, φ (CliffordAlgebra.involute y) = CliffordAlgebra.involute (φ y))
      (i : ZMod 2) (a : Clsplit 1),
      a ∈ CliffordAlgebra.evenOdd (Qsplit 1) i →
      φ a ∈ CliffordAlgebra.evenOdd (Qsplit 1) i := by
    intro φ hφ i a ha
    have hinv := evenOdd_involute_mem (Q := Qsplit 1) i ha
    have h2 : CliffordAlgebra.involute (φ a) = (-1 : ℤˣ) ^ i.val • φ a := by
      rw [← hφ a, hinv, Units.smul_def, map_zsmul, ← Units.smul_def]
    rcases zmod2_cases i with rfl | rfl
    · exact (mem_evenOdd_zero_iff_involute _ _).mpr (by simpa using h2)
    · exact (mem_evenOdd_one_iff_involute _ _).mpr (by simpa [ZMod.val_one] using h2)
  let fwd := gradedTensorMapAlgHom
    (CliffordAlgebra.evenOdd (Qsplit 1)) (CliffordAlgebra.evenOdd (Qsplit n))
    (CliffordAlgebra.evenOdd (Qsplit 1)) (CliffordAlgebra.evenOdd (Qsplit n))
    (headV4ClsplitOneAuto g).toAlgHom (AlgHom.id ℝ (Clsplit n))
    (fun i a ha => hmem (headV4ClsplitOneAuto g).toAlgHom (headV4ClsplitOneAuto_involute g) i a ha)
    (fun j b hb => by simpa only [AlgHom.id_apply] using hb)
  let bwd := gradedTensorMapAlgHom
    (CliffordAlgebra.evenOdd (Qsplit 1)) (CliffordAlgebra.evenOdd (Qsplit n))
    (CliffordAlgebra.evenOdd (Qsplit 1)) (CliffordAlgebra.evenOdd (Qsplit n))
    (headV4ClsplitOneAuto g).symm.toAlgHom (AlgHom.id ℝ (Clsplit n))
    (fun i a ha => hmem (headV4ClsplitOneAuto g).symm.toAlgHom (fun y => by
      apply (headV4ClsplitOneAuto g).injective
      change headV4ClsplitOneAuto g ((headV4ClsplitOneAuto g).symm (CliffordAlgebra.involute y)) =
        headV4ClsplitOneAuto g (CliffordAlgebra.involute ((headV4ClsplitOneAuto g).symm y))
      rw [AlgEquiv.apply_symm_apply, headV4ClsplitOneAuto_involute, AlgEquiv.apply_symm_apply]) i a ha)
    (fun j b hb => by simpa only [AlgHom.id_apply] using hb)
  AlgEquiv.ofAlgHom fwd bwd
    (by
      apply GradedTensorProduct.algHom_ext
      · apply AlgHom.ext; intro a
        change fwd (bwd (a ᵍ⊗ₜ (1 : Clsplit n))) = a ᵍ⊗ₜ (1 : Clsplit n)
        dsimp only [fwd, bwd]
        rw [gradedTensorMapAlgHom_tmul, gradedTensorMapAlgHom_tmul]
        simp
      · apply AlgHom.ext; intro b
        change fwd (bwd ((1 : Clsplit 1) ᵍ⊗ₜ b)) = (1 : Clsplit 1) ᵍ⊗ₜ b
        dsimp only [fwd, bwd]
        rw [gradedTensorMapAlgHom_tmul, gradedTensorMapAlgHom_tmul]
        simp)
    (by
      apply GradedTensorProduct.algHom_ext
      · apply AlgHom.ext; intro a
        change bwd (fwd (a ᵍ⊗ₜ (1 : Clsplit n))) = a ᵍ⊗ₜ (1 : Clsplit n)
        dsimp only [fwd, bwd]
        rw [gradedTensorMapAlgHom_tmul, gradedTensorMapAlgHom_tmul]
        simp
      · apply AlgHom.ext; intro b
        change bwd (fwd ((1 : Clsplit 1) ᵍ⊗ₜ b)) = (1 : Clsplit 1) ᵍ⊗ₜ b
        dsimp only [fwd, bwd]
        rw [gradedTensorMapAlgHom_tmul, gradedTensorMapAlgHom_tmul]
        simp)

@[simp] private theorem headV4HeadTailStageAuto_tmul (n : ℕ) (g : V4)
    (a : Clsplit 1) (b : Clsplit n) :
    headV4HeadTailStageAuto n g (a ᵍ⊗ₜ b) = headV4ClsplitOneAuto g a ᵍ⊗ₜ b := by
  dsimp only [headV4HeadTailStageAuto]
  rw [AlgEquiv.ofAlgHom_apply, gradedTensorMapAlgHom_tmul]
  rfl

theorem headV4HeadTailStageAuto_bond (m n : ℕ) (h : m ≤ n) (g : V4)
    (z : SplitCliffordHeadTailStage 1 m) :
    headV4HeadTailStageAuto n g (splitCliffordHeadTailMap 1 m n h z) =
      splitCliffordHeadTailMap 1 m n h (headV4HeadTailStageAuto m g z) := by
  have hhom :
      (headV4HeadTailStageAuto n g).toAlgHom.comp (splitCliffordHeadTailMap 1 m n h) =
        (splitCliffordHeadTailMap 1 m n h).comp (headV4HeadTailStageAuto m g).toAlgHom := by
    apply GradedTensorProduct.algHom_ext
    · apply AlgHom.ext; intro a
      simp only [AlgHom.comp_apply, GradedTensorProduct.includeLeft_apply]
      have hm1 : splitCliffordHeadTailMap 1 m n h (a ᵍ⊗ₜ (1 : Clsplit m)) = a ᵍ⊗ₜ (1 : Clsplit n) := by
        induction n, h using Nat.le_induction with
        | base => simp [splitCliffordHeadTailMap]
        | succ k hk ih =>
            have hstep : splitCliffordHeadTailMap 1 m (k + 1) (Nat.le_succ_of_le hk) =
                (splitCliffordHeadTailStep 1 k).comp (splitCliffordHeadTailMap 1 m k hk) := by
              rw [← splitCliffordHeadTailMap_succ]
              apply AlgHom.ext; intro y
              change splitCliffordHeadTailMap 1 m (k + 1) (hk.trans (Nat.le_succ k)) y =
                splitCliffordHeadTailMap 1 k (k + 1) (Nat.le_succ k) (splitCliffordHeadTailMap 1 m k hk y)
              exact (DirectedSystem.map_map (f := fun i j hij => splitCliffordHeadTailMap 1 i j hij) hk (Nat.le_succ k) y).symm
            rw [hstep, AlgHom.comp_apply, ih, splitCliffordHeadTailStep_tmul,
              map_one, GradedTensorProduct.includeLeft_apply, GradedTensorProduct.includeRight_apply]
            exact mul_one (a ᵍ⊗ₜ (1 : Clsplit (k + 1)))
      have hm2 : splitCliffordHeadTailMap 1 m n h ((headV4ClsplitOneAuto g a) ᵍ⊗ₜ (1 : Clsplit m)) =
          (headV4ClsplitOneAuto g a) ᵍ⊗ₜ (1 : Clsplit n) := by
        clear hm1
        induction n, h using Nat.le_induction with
        | base => simp [splitCliffordHeadTailMap]
        | succ k hk ih =>
            have hstep : splitCliffordHeadTailMap 1 m (k + 1) (Nat.le_succ_of_le hk) =
                (splitCliffordHeadTailStep 1 k).comp (splitCliffordHeadTailMap 1 m k hk) := by
              rw [← splitCliffordHeadTailMap_succ]
              apply AlgHom.ext; intro y
              change splitCliffordHeadTailMap 1 m (k + 1) (hk.trans (Nat.le_succ k)) y =
                splitCliffordHeadTailMap 1 k (k + 1) (Nat.le_succ k) (splitCliffordHeadTailMap 1 m k hk y)
              exact (DirectedSystem.map_map (f := fun i j hij => splitCliffordHeadTailMap 1 i j hij) hk (Nat.le_succ k) y).symm
            rw [hstep, AlgHom.comp_apply, ih, splitCliffordHeadTailStep_tmul,
              map_one, GradedTensorProduct.includeLeft_apply, GradedTensorProduct.includeRight_apply]
            exact mul_one ((headV4ClsplitOneAuto g a) ᵍ⊗ₜ (1 : Clsplit (k + 1)))
      change headV4HeadTailStageAuto n g (splitCliffordHeadTailMap 1 m n h (a ᵍ⊗ₜ (1 : Clsplit m))) =
        splitCliffordHeadTailMap 1 m n h (headV4HeadTailStageAuto m g (a ᵍ⊗ₜ (1 : Clsplit m)))
      rw [hm1, headV4HeadTailStageAuto_tmul, headV4HeadTailStageAuto_tmul, hm2]
    · apply AlgHom.ext; intro b
      simp only [AlgHom.comp_apply, GradedTensorProduct.includeRight_apply]
      have hm1 : splitCliffordHeadTailMap 1 m n h ((1 : Clsplit 1) ᵍ⊗ₜ b) =
          (1 : Clsplit 1) ᵍ⊗ₜ splitCliffordMap m n h b := by
        induction n, h using Nat.le_induction with
        | base => simp [splitCliffordHeadTailMap, splitCliffordMap_refl]
        | succ k hk ih =>
            have hstep : splitCliffordHeadTailMap 1 m (k + 1) (Nat.le_succ_of_le hk) =
                (splitCliffordHeadTailStep 1 k).comp (splitCliffordHeadTailMap 1 m k hk) := by
              rw [← splitCliffordHeadTailMap_succ]
              apply AlgHom.ext; intro y
              change splitCliffordHeadTailMap 1 m (k + 1) (hk.trans (Nat.le_succ k)) y =
                splitCliffordHeadTailMap 1 k (k + 1) (Nat.le_succ k) (splitCliffordHeadTailMap 1 m k hk y)
              exact (DirectedSystem.map_map (f := fun i j hij => splitCliffordHeadTailMap 1 i j hij) hk (Nat.le_succ k) y).symm
            rw [hstep, AlgHom.comp_apply, ih, splitCliffordHeadTailStep_tmul,
              splitCliffordMap_succ m k hk, GradedTensorProduct.includeLeft_apply,
              GradedTensorProduct.includeRight_apply, one_gtmul_mul_one_gtmul, one_mul]
            rfl
      change headV4HeadTailStageAuto n g (splitCliffordHeadTailMap 1 m n h ((1 : Clsplit 1) ᵍ⊗ₜ b)) =
        splitCliffordHeadTailMap 1 m n h (headV4HeadTailStageAuto m g ((1 : Clsplit 1) ᵍ⊗ₜ b))
      rw [hm1, headV4HeadTailStageAuto_tmul, headV4HeadTailStageAuto_tmul, map_one, hm1]
  exact AlgHom.congr_fun hhom z

private theorem splitCliffordHeadTailOf_eq (n : ℕ) (x : SplitCliffordHeadTailStage 1 n) :
    splitCliffordHeadTailOf 1 n x =
      DirectLimit.Ring.of (SplitCliffordHeadTailStage 1)
        (fun i j hij => splitCliffordHeadTailMap 1 i j hij) n x := rfl

private def headV4HTLift (g : V4) :
    SplitCliffordHeadTailInfinity 1 ≃+* SplitCliffordHeadTailInfinity 1 :=
  let fwd : SplitCliffordHeadTailInfinity 1 →+* SplitCliffordHeadTailInfinity 1 :=
    DirectLimit.Ring.lift (SplitCliffordHeadTailStage 1)
      (fun m n h => splitCliffordHeadTailMap 1 m n h)
      (SplitCliffordHeadTailInfinity 1)
      (fun n => (DirectLimit.Ring.of (SplitCliffordHeadTailStage 1)
        (fun m l h => splitCliffordHeadTailMap 1 m l h) n).comp
          (headV4HeadTailStageAuto n g).toRingHom)
      (fun m n h x => by
        change DirectLimit.Ring.of (SplitCliffordHeadTailStage 1)
            (fun m l h => splitCliffordHeadTailMap 1 m l h) n
            (headV4HeadTailStageAuto n g (splitCliffordHeadTailMap 1 m n h x)) =
          DirectLimit.Ring.of (SplitCliffordHeadTailStage 1)
            (fun m l h => splitCliffordHeadTailMap 1 m l h) m
            (headV4HeadTailStageAuto m g x)
        rw [headV4HeadTailStageAuto_bond]
        exact DirectLimit.Ring.of_f (G := SplitCliffordHeadTailStage 1)
          (f := fun i j hij => splitCliffordHeadTailMap 1 i j hij)
          h (headV4HeadTailStageAuto m g x))
  let bwd : SplitCliffordHeadTailInfinity 1 →+* SplitCliffordHeadTailInfinity 1 :=
    DirectLimit.Ring.lift (SplitCliffordHeadTailStage 1)
      (fun m n h => splitCliffordHeadTailMap 1 m n h)
      (SplitCliffordHeadTailInfinity 1)
      (fun n => (DirectLimit.Ring.of (SplitCliffordHeadTailStage 1)
        (fun m l h => splitCliffordHeadTailMap 1 m l h) n).comp
          (headV4HeadTailStageAuto n g).symm.toRingHom)
      (fun m n h x => by
        have hbond : (headV4HeadTailStageAuto n g).symm (splitCliffordHeadTailMap 1 m n h x) =
            splitCliffordHeadTailMap 1 m n h ((headV4HeadTailStageAuto m g).symm x) := by
          apply (headV4HeadTailStageAuto n g).injective
          rw [AlgEquiv.apply_symm_apply, headV4HeadTailStageAuto_bond, AlgEquiv.apply_symm_apply]
        change DirectLimit.Ring.of (SplitCliffordHeadTailStage 1)
            (fun m l h => splitCliffordHeadTailMap 1 m l h) n
            ((headV4HeadTailStageAuto n g).symm (splitCliffordHeadTailMap 1 m n h x)) =
          DirectLimit.Ring.of (SplitCliffordHeadTailStage 1)
            (fun m l h => splitCliffordHeadTailMap 1 m l h) m
            ((headV4HeadTailStageAuto m g).symm x)
        rw [hbond]
        exact DirectLimit.Ring.of_f (G := SplitCliffordHeadTailStage 1)
          (f := fun i j hij => splitCliffordHeadTailMap 1 i j hij)
          h ((headV4HeadTailStageAuto m g).symm x))
  RingEquiv.ofRingHom fwd bwd
    (by
      apply DirectLimit.Ring.hom_ext; intro n; ext x
      dsimp only [fwd, bwd, RingHom.comp_apply, RingHom.id_apply]
      rw [DirectLimit.Ring.lift_of, RingHom.comp_apply, DirectLimit.Ring.lift_of]
      simp)
    (by
      apply DirectLimit.Ring.hom_ext; intro n; ext x
      dsimp only [fwd, bwd, RingHom.comp_apply, RingHom.id_apply]
      rw [DirectLimit.Ring.lift_of, RingHom.comp_apply, DirectLimit.Ring.lift_of]
      simp)

@[simp] private theorem headV4HTLift_of (g : V4) (n : ℕ) (z : SplitCliffordHeadTailStage 1 n) :
    headV4HTLift g (splitCliffordHeadTailOf 1 n z) =
      splitCliffordHeadTailOf 1 n (headV4HeadTailStageAuto n g z) := by
  rw [splitCliffordHeadTailOf_eq, splitCliffordHeadTailOf_eq]
  dsimp only [headV4HTLift]
  rw [RingEquiv.ofRingHom_apply, DirectLimit.Ring.lift_of]
  rfl

private theorem headV4ClsplitOneAuto_one (a : Clsplit 1) :
    headV4ClsplitOneAuto 1 a = a := by
  dsimp only [headV4ClsplitOneAuto]
  simp [cl11V4Auto_one]

private theorem headV4ClsplitOneAuto_mul (g h : V4) (a : Clsplit 1) :
    headV4ClsplitOneAuto (g * h) a = headV4ClsplitOneAuto g (headV4ClsplitOneAuto h a) := by
  dsimp only [headV4ClsplitOneAuto]
  simp only [AlgEquiv.trans_apply]
  rw [AlgEquiv.apply_symm_apply, map_mul]
  rfl

private theorem headV4HeadTailStageAuto_one (n : ℕ) (z : SplitCliffordHeadTailStage 1 n) :
    headV4HeadTailStageAuto n 1 z = z := by
  obtain ⟨t, rfl⟩ := (GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd (Qsplit 1))
    (CliffordAlgebra.evenOdd (Qsplit n))).surjective z
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
      change headV4HeadTailStageAuto n 1 (a ᵍ⊗ₜ b) = a ᵍ⊗ₜ b
      rw [headV4HeadTailStageAuto_tmul, headV4ClsplitOneAuto_one]
  | add u v hu hv =>
      simp only [map_add] at hu hv ⊢; rw [hu, hv]

private theorem headV4HeadTailStageAuto_mul (n : ℕ) (g h : V4)
    (z : SplitCliffordHeadTailStage 1 n) :
    headV4HeadTailStageAuto n (g * h) z =
      headV4HeadTailStageAuto n g (headV4HeadTailStageAuto n h z) := by
  obtain ⟨t, rfl⟩ := (GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd (Qsplit 1))
    (CliffordAlgebra.evenOdd (Qsplit n))).surjective z
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
      change headV4HeadTailStageAuto n (g * h) (a ᵍ⊗ₜ b) =
        headV4HeadTailStageAuto n g (headV4HeadTailStageAuto n h (a ᵍ⊗ₜ b))
      rw [headV4HeadTailStageAuto_tmul, headV4HeadTailStageAuto_tmul,
        headV4HeadTailStageAuto_tmul, headV4ClsplitOneAuto_mul]
  | add u v hu hv =>
      simp only [map_add] at hu hv ⊢; rw [hu, hv]

private theorem headV4HTLift_one (y : SplitCliffordHeadTailInfinity 1) :
    headV4HTLift 1 y = y := by
  induction y using DirectLimit.induction with
  | _ n z =>
      change headV4HTLift 1 (splitCliffordHeadTailOf 1 n z) = splitCliffordHeadTailOf 1 n z
      rw [headV4HTLift_of, headV4HeadTailStageAuto_one]

private theorem headV4HTLift_mul (g h : V4) (y : SplitCliffordHeadTailInfinity 1) :
    headV4HTLift (g * h) y = headV4HTLift g (headV4HTLift h y) := by
  induction y using DirectLimit.induction with
  | _ n z =>
      change headV4HTLift (g * h) (splitCliffordHeadTailOf 1 n z) =
        headV4HTLift g (headV4HTLift h (splitCliffordHeadTailOf 1 n z))
      rw [headV4HTLift_of, headV4HTLift_of, headV4HTLift_of, headV4HeadTailStageAuto_mul]

/-- Root-head `V4` symmetry action descended to `SplitCliffordHeadTailInfinity 1` and
transported along `splitCliffordHeadTailInfinity_ringEquiv 1` onto `SplitCliffordInfinity`. -/
def headV4InfinitySymmetryAction : SymmetryAction V4 SplitCliffordInfinity where
  act g :=
    let eHT := splitCliffordHeadTailInfinity_ringEquiv 1
    (eHT.symm.trans (headV4HTLift g)).trans eHT
  act_one x := by
    dsimp only [RingEquiv.trans_apply]
    rw [headV4HTLift_one, RingEquiv.apply_symm_apply]
  act_mul g h x := by
    dsimp only [RingEquiv.trans_apply]
    rw [headV4HTLift_mul, RingEquiv.symm_apply_apply]

private def diagV4Fun (n : ℕ) (g : V4) (v : SplitSpace n) : SplitSpace n :=
  match v4RootHom g with
  | InfoGeometry.Topology.V4RootSystem.V4Group.I => v
  | InfoGeometry.Topology.V4RootSystem.V4Group.W2 => -v
  | InfoGeometry.Topology.V4RootSystem.V4Group.W1 =>
      Nat.rec (motive := fun m => SplitSpace m → SplitSpace m) id
        (fun _ rec ⟨⟨a, b⟩, xs⟩ => ((a, -b), rec xs)) n v
  | InfoGeometry.Topology.V4RootSystem.V4Group.W12 =>
      Nat.rec (motive := fun m => SplitSpace m → SplitSpace m) id
        (fun _ rec ⟨⟨a, b⟩, xs⟩ => ((-a, b), rec xs)) n v

@[simp] private theorem diagV4Fun_one (n : ℕ) (v : SplitSpace n) :
    diagV4Fun n 1 v = v := by
  dsimp [diagV4Fun]
  have h : v4RootHom (1 : V4) = InfoGeometry.Topology.V4RootSystem.V4Group.I := map_one v4RootHom
  rw [h]

@[simp] private theorem diagV4Fun_T (n : ℕ) (v : SplitSpace n) :
    diagV4Fun n (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T) v = -v := by
  dsimp [diagV4Fun, v4RootHom]
  rw [v4RootMap_T]

@[simp] private theorem diagV4Fun_P_zero (v : SplitSpace 0) :
    diagV4Fun 0 (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P) v = v := by
  dsimp [diagV4Fun, v4RootHom]
  rw [v4RootMap_P]

@[simp] private theorem diagV4Fun_P_succ (n : ℕ) (a b : ℝ) (xs : SplitSpace n) :
    diagV4Fun (n + 1) (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P) ((a, b), xs) =
      ((a, -b), diagV4Fun n (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P) xs) := by
  dsimp [diagV4Fun, v4RootHom]
  rw [v4RootMap_P]

@[simp] private theorem diagV4Fun_PT_zero (v : SplitSpace 0) :
    diagV4Fun 0 (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT) v = v := by
  dsimp [diagV4Fun, v4RootHom]
  rw [v4RootMap_PT]

@[simp] private theorem diagV4Fun_PT_succ (n : ℕ) (a b : ℝ) (xs : SplitSpace n) :
    diagV4Fun (n + 1) (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT) ((a, b), xs) =
      ((-a, b), diagV4Fun n (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT) xs) := by
  dsimp [diagV4Fun, v4RootHom]
  rw [v4RootMap_PT]

/-- Global diagonal `V4` sign isometry on `SplitSpace n`. -/
def diagV4Isometry (n : ℕ) (g : V4) : (Qsplit n).IsometryEquiv (Qsplit n) where
  toLinearEquiv :=
    { toFun := diagV4Fun n g
      map_add' := fun u v => by
        have hcases : g = 1 ∨ g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P ∨
            g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T ∨
            g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT := by
          revert g; decide
        rcases hcases with rfl | rfl | rfl | rfl
        · simp
        · induction n with
          | zero => simp
          | succ n ih =>
              rcases u with ⟨⟨a₁, b₁⟩, us⟩; rcases v with ⟨⟨a₂, b₂⟩, vs⟩
              simp [Prod.ext_iff, ih us vs]; ring
        · simp only [diagV4Fun_T, neg_add_rev, add_comm]
        · induction n with
          | zero => simp
          | succ n ih =>
              rcases u with ⟨⟨a₁, b₁⟩, us⟩; rcases v with ⟨⟨a₂, b₂⟩, vs⟩
              simp [Prod.ext_iff, ih us vs]; ring
      map_smul' := fun r v => by
        have hcases : g = 1 ∨ g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P ∨
            g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T ∨
            g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT := by
          revert g; decide
        rcases hcases with rfl | rfl | rfl | rfl
        · simp
        · induction n with
          | zero => simp
          | succ n ih =>
              rcases v with ⟨⟨a, b⟩, vs⟩
              simp [ih vs]
        · simp [smul_neg]
        · induction n with
          | zero => simp
          | succ n ih =>
              rcases v with ⟨⟨a, b⟩, vs⟩
              simp [ih vs]
      invFun := diagV4Fun n g
      left_inv := fun v => by
        have hcases : g = 1 ∨ g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P ∨
            g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T ∨
            g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT := by
          revert g; decide
        rcases hcases with rfl | rfl | rfl | rfl
        · simp
        · induction n with
          | zero => simp
          | succ n ih =>
              rcases v with ⟨⟨a, b⟩, vs⟩; simp [ih vs]
        · simp
        · induction n with
          | zero => simp
          | succ n ih =>
              rcases v with ⟨⟨a, b⟩, vs⟩; simp [ih vs]
      right_inv := fun v => by
        have hcases : g = 1 ∨ g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P ∨
            g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T ∨
            g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT := by
          revert g; decide
        rcases hcases with rfl | rfl | rfl | rfl
        · simp
        · induction n with
          | zero => simp
          | succ n ih =>
              rcases v with ⟨⟨a, b⟩, vs⟩; simp [ih vs]
        · simp
        · induction n with
          | zero => simp
          | succ n ih =>
              rcases v with ⟨⟨a, b⟩, vs⟩; simp [ih vs] }
  map_app' v := by
    have hcases : g = 1 ∨ g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P ∨
        g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T ∨
        g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT := by
      revert g; decide
    rcases hcases with rfl | rfl | rfl | rfl
    · simp
    · induction n with
      | zero => simp [Qsplit]
      | succ n ih =>
          rcases v with ⟨⟨a, b⟩, vs⟩
          rw [Qsplit_succ_apply, Qsplit_succ_apply, diagV4Fun_P_succ, ih vs]
          simp [InfoGeometry.CliffordTower.Q11, ← q11_eq_splitQ11, q11_apply]
    · simp [QuadraticMap.map_neg]
    · induction n with
      | zero => simp [Qsplit]
      | succ n ih =>
          rcases v with ⟨⟨a, b⟩, vs⟩
          rw [Qsplit_succ_apply, Qsplit_succ_apply, diagV4Fun_PT_succ, ih vs]
          simp [InfoGeometry.CliffordTower.Q11, ← q11_eq_splitQ11, q11_apply]

/-- Global diagonal `V4` automorphism on `Clsplit n`, with `T` equal to `CliffordAlgebra.involuteEquiv`. -/
def diagV4ClsplitAuto (n : ℕ) (g : V4) : Clsplit n ≃ₐ[ℝ] Clsplit n :=
  CliffordAlgebra.equivOfIsometry (diagV4Isometry n g)

@[simp] private theorem diagV4ClsplitAuto_ι (n : ℕ) (g : V4) (v : SplitSpace n) :
    diagV4ClsplitAuto n g (CliffordAlgebra.ι (Qsplit n) v) =
      CliffordAlgebra.ι (Qsplit n) (diagV4Fun n g v) := by
  dsimp [diagV4ClsplitAuto]
  rw [CliffordAlgebra.equivOfIsometry_apply, CliffordAlgebra.map_apply_ι]
  rfl

theorem diagV4ClsplitAuto_T (n : ℕ) (x : Clsplit n) :
    diagV4ClsplitAuto n (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T) x =
      CliffordAlgebra.involute x := by
  have hhom :
      (diagV4ClsplitAuto n (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T)).toAlgHom =
        CliffordAlgebra.involute (Q := Qsplit n) := by
    apply CliffordAlgebra.hom_ext; apply LinearMap.ext; intro v
    dsimp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply]
    change diagV4ClsplitAuto n (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T)
        (CliffordAlgebra.ι (Qsplit n) v) =
      CliffordAlgebra.involute (CliffordAlgebra.ι (Qsplit n) v)
    rw [diagV4ClsplitAuto_ι, diagV4Fun_T, map_neg, CliffordAlgebra.involute_ι]
  exact AlgHom.congr_fun hhom x

theorem diagV4ClsplitAuto_bond (n : ℕ) (g : V4) (x : Clsplit n) :
    diagV4ClsplitAuto (n + 1) g (splitCliffordStep n x) =
      splitCliffordStep n (diagV4ClsplitAuto n g x) := by
  have hhom :
      (diagV4ClsplitAuto (n + 1) g).toAlgHom.comp (splitCliffordStep n) =
        (splitCliffordStep n).comp (diagV4ClsplitAuto n g).toAlgHom := by
    apply CliffordAlgebra.hom_ext; apply LinearMap.ext; intro v
    have hcases : g = 1 ∨ g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P ∨
        g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T ∨
        g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT := by
      revert g; decide
    have hst : ∀ u : SplitSpace n, splitCliffordStep n (CliffordAlgebra.ι (Qsplit n) u) =
        CliffordAlgebra.ι (Qsplit (n + 1)) ((0, 0), u) := splitCliffordStep_ι n
    change diagV4ClsplitAuto (n + 1) g (splitCliffordStep n (CliffordAlgebra.ι (Qsplit n) v)) =
      splitCliffordStep n (diagV4ClsplitAuto n g (CliffordAlgebra.ι (Qsplit n) v))
    rw [hst, diagV4ClsplitAuto_ι, diagV4ClsplitAuto_ι]
    rcases hcases with rfl | rfl | rfl | rfl
    · simp [hst]
    · simp only [diagV4Fun_P_succ, neg_zero]
      exact (hst _).symm
    · rw [diagV4Fun_T, map_neg, hst, ← map_neg]
      congr 2
      ext <;> simp
    · simp only [diagV4Fun_PT_succ, neg_zero]
      exact (hst _).symm
  exact AlgHom.congr_fun hhom x

private theorem diagV4Fun_mul (n : ℕ) (g h : V4) (v : SplitSpace n) :
    diagV4Fun n (g * h) v = diagV4Fun n g (diagV4Fun n h v) := by
  have hg : g = 1 ∨ g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P ∨
      g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T ∨
      g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT := by revert g; decide
  have hh : h = 1 ∨ h = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P ∨
      h = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T ∨
      h = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT := by revert h; decide
  have hP_T : Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P *
      Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T =
      Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT := by decide
  have hT_P : Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T *
      Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P =
      Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT := by decide
  have hP_PT : Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P *
      Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT =
      Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T := by decide
  have hPT_P : Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT *
      Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P =
      Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T := by decide
  have hT_PT : Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T *
      Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT =
      Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P := by decide
  have hPT_T : Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT *
      Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T =
      Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P := by decide
  have hP_P : Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P *
      Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P = (1 : V4) := by decide
  have hT_T : Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T *
      Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T = (1 : V4) := by decide
  have hPT_PT : Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT *
      Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT = (1 : V4) := by decide
  rcases hg with rfl | rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp
  · simp
  · rw [hP_P, diagV4Fun_one]
    induction n with
    | zero => funext i; exact Fin.elim0 i
    | succ n ih =>
        rcases v with ⟨⟨a, b⟩, vs⟩
        rw [diagV4Fun_P_succ n a b vs, diagV4Fun_P_succ n a (-b) _, ← ih vs, neg_neg]
  · rw [hP_T]
    induction n with
    | zero => funext i; exact Fin.elim0 i
    | succ n ih =>
        rcases v with ⟨⟨a, b⟩, vs⟩
        rw [diagV4Fun_PT_succ, diagV4Fun_T, diagV4Fun_P_succ]
        change ((-a, b), diagV4Fun n (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT) vs) =
          ((-a, -(-b)), diagV4Fun n (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P) (-vs))
        rw [neg_neg, ← diagV4Fun_T n vs, ih vs]
  · rw [hP_PT]
    induction n with
    | zero => funext i; exact Fin.elim0 i
    | succ n ih =>
        rcases v with ⟨⟨a, b⟩, vs⟩
        rw [diagV4Fun_T, diagV4Fun_PT_succ, diagV4Fun_P_succ]
        change ((-a, -b), -vs) =
          ((-a, -b), diagV4Fun n (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P)
            (diagV4Fun n (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT) vs))
        rw [← diagV4Fun_T n vs, ih vs]
  · simp
  · rw [hT_P]
    induction n with
    | zero => funext i; exact Fin.elim0 i
    | succ n ih =>
        rcases v with ⟨⟨a, b⟩, vs⟩
        rw [diagV4Fun_PT_succ, diagV4Fun_P_succ, diagV4Fun_T]
        change ((-a, b), diagV4Fun n (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT) vs) =
          ((-a, -(-b)), -(diagV4Fun n (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P) vs))
        rw [neg_neg, ← diagV4Fun_T n, ih vs]
  · rw [hT_T, diagV4Fun_one, diagV4Fun_T, diagV4Fun_T, neg_neg]
  · rw [hT_PT]
    induction n with
    | zero => funext i; exact Fin.elim0 i
    | succ n ih =>
        rcases v with ⟨⟨a, b⟩, vs⟩
        rw [diagV4Fun_P_succ, diagV4Fun_PT_succ, diagV4Fun_T]
        change ((a, -b), diagV4Fun n (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P) vs) =
          ((-(-a), -b), -(diagV4Fun n (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT) vs))
        rw [neg_neg, ← diagV4Fun_T n, ih vs]
  · simp
  · rw [hPT_P]
    induction n with
    | zero => funext i; exact Fin.elim0 i
    | succ n ih =>
        rcases v with ⟨⟨a, b⟩, vs⟩
        rw [diagV4Fun_T, diagV4Fun_P_succ, diagV4Fun_PT_succ]
        change ((-a, -b), -vs) =
          ((-a, -b), diagV4Fun n (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT)
            (diagV4Fun n (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P) vs))
        rw [← diagV4Fun_T n vs, ih vs]
  · rw [hPT_T]
    induction n with
    | zero => funext i; exact Fin.elim0 i
    | succ n ih =>
        rcases v with ⟨⟨a, b⟩, vs⟩
        rw [diagV4Fun_P_succ, diagV4Fun_T, diagV4Fun_PT_succ]
        change ((a, -b), diagV4Fun n (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P) vs) =
          ((-(-a), -b), diagV4Fun n (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT) (-vs))
        rw [neg_neg, ← diagV4Fun_T n vs, ih vs]
  · rw [hPT_PT, diagV4Fun_one]
    induction n with
    | zero => funext i; exact Fin.elim0 i
    | succ n ih =>
        rcases v with ⟨⟨a, b⟩, vs⟩
        rw [diagV4Fun_PT_succ n a b vs, diagV4Fun_PT_succ n (-a) b _, ← ih vs, neg_neg]

/-- Descended global diagonal `V4` symmetry action on `SplitCliffordInfinity`, whose `T`
generator equals `splitCliffordInfinityInvolute`. -/
def diagV4InfinityAuto (g : V4) : SplitCliffordInfinity ≃ₐ[ℝ] SplitCliffordInfinity :=
  let fwd : SplitCliffordInfinity →ₐ[ℝ] SplitCliffordInfinity :=
    DirectLimit.Algebra.lift SplitCliffordTensorBridge.SplitClNNAlg (fun i j hij => splitCliffordMap i j hij)
      SplitCliffordInfinity
      (fun n => (DirectLimit.Algebra.of SplitCliffordTensorBridge.SplitClNNAlg (fun i j hij => splitCliffordMap i j hij) n).comp
        (diagV4ClsplitAuto n g).toAlgHom)
      (by
        intro m n h x
        induction n, h using Nat.le_induction with
        | base => simp [splitCliffordMap_refl]
        | succ n hn ih =>
            rw [splitCliffordMap_succ m n hn]
            change DirectLimit.Algebra.of SplitCliffordTensorBridge.SplitClNNAlg (fun i j hij => splitCliffordMap i j hij) (n + 1)
                (diagV4ClsplitAuto (n + 1) g (splitCliffordStep n (splitCliffordMap m n hn x))) = _
            have hstep : ∀ y : Clsplit n,
                splitCliffordStep n y = splitCliffordMap n (n + 1) (Nat.le_succ n) y := fun y => by
              change splitCliffordStep n y =
                splitCliffordMap n (n + 1) (Nat.le_trans le_rfl (Nat.le_succ n)) y
              rw [splitCliffordMap_succ n n le_rfl, splitCliffordMap_refl]; rfl
            rw [diagV4ClsplitAuto_bond, hstep,
              DirectLimit.Algebra.of_f (f := fun i j hij => splitCliffordMap i j hij) (Nat.le_succ n)]
            exact ih)
  let bwd : SplitCliffordInfinity →ₐ[ℝ] SplitCliffordInfinity :=
    DirectLimit.Algebra.lift SplitCliffordTensorBridge.SplitClNNAlg (fun i j hij => splitCliffordMap i j hij)
      SplitCliffordInfinity
      (fun n => (DirectLimit.Algebra.of SplitCliffordTensorBridge.SplitClNNAlg (fun i j hij => splitCliffordMap i j hij) n).comp
        (diagV4ClsplitAuto n g).symm.toAlgHom)
      (by
        intro m n h x
        induction n, h using Nat.le_induction with
        | base => simp [splitCliffordMap_refl]
        | succ n hn ih =>
            rw [splitCliffordMap_succ m n hn]
            change DirectLimit.Algebra.of SplitCliffordTensorBridge.SplitClNNAlg (fun i j hij => splitCliffordMap i j hij) (n + 1)
                ((diagV4ClsplitAuto (n + 1) g).symm
                  (splitCliffordStep n (splitCliffordMap m n hn x))) = _
            have hsymm : (diagV4ClsplitAuto (n + 1) g).symm
                (splitCliffordStep n (splitCliffordMap m n hn x)) =
                splitCliffordStep n ((diagV4ClsplitAuto n g).symm (splitCliffordMap m n hn x)) := by
              apply (diagV4ClsplitAuto (n + 1) g).injective
              rw [AlgEquiv.apply_symm_apply, diagV4ClsplitAuto_bond, AlgEquiv.apply_symm_apply]
            have hstep : ∀ y : Clsplit n,
                splitCliffordStep n y = splitCliffordMap n (n + 1) (Nat.le_succ n) y := fun y => by
              change splitCliffordStep n y =
                splitCliffordMap n (n + 1) (Nat.le_trans le_rfl (Nat.le_succ n)) y
              rw [splitCliffordMap_succ n n le_rfl, splitCliffordMap_refl]; rfl
            rw [hsymm, hstep,
              DirectLimit.Algebra.of_f (f := fun i j hij => splitCliffordMap i j hij) (Nat.le_succ n)]
            exact ih)
  AlgEquiv.ofAlgHom fwd bwd
    (by
      apply DirectLimit.Algebra.hom_ext
      intro n
      apply AlgHom.ext; intro x
      dsimp only [fwd, bwd, AlgHom.comp_apply, AlgHom.id_apply]
      rw [DirectLimit.Algebra.lift_of, AlgHom.comp_apply, DirectLimit.Algebra.lift_of]
      simp)
    (by
      apply DirectLimit.Algebra.hom_ext
      intro n
      apply AlgHom.ext; intro x
      dsimp only [fwd, bwd, AlgHom.comp_apply, AlgHom.id_apply]
      rw [DirectLimit.Algebra.lift_of, AlgHom.comp_apply, DirectLimit.Algebra.lift_of]
      simp)

def diagV4InfinitySymmetryAction : SymmetryAction V4 SplitCliffordInfinity where
  act g := (diagV4InfinityAuto g).toRingEquiv
  act_one x := by
    induction x using DirectLimit.induction with
    | _ n a =>
        change diagV4InfinityAuto 1 (DirectLimit.Algebra.of _ _ n a) = _
        change DirectLimit.Algebra.of SplitCliffordTensorBridge.SplitClNNAlg _ n (diagV4ClsplitAuto n 1 a) = _
        have h1 : diagV4ClsplitAuto n 1 a = a := by
          have hhom : (diagV4ClsplitAuto n 1).toAlgHom = AlgHom.id ℝ (Clsplit n) := by
            apply CliffordAlgebra.hom_ext; apply LinearMap.ext; intro v
            change diagV4ClsplitAuto n 1 (CliffordAlgebra.ι (Qsplit n) v) = CliffordAlgebra.ι (Qsplit n) v
            rw [diagV4ClsplitAuto_ι, diagV4Fun_one]
          exact AlgHom.congr_fun hhom a
        rw [h1]
        rfl
  act_mul g h x := by
    induction x using DirectLimit.induction with
    | _ n a =>
        change DirectLimit.Algebra.of SplitCliffordTensorBridge.SplitClNNAlg _ n (diagV4ClsplitAuto n (g * h) a) =
          DirectLimit.Algebra.of SplitCliffordTensorBridge.SplitClNNAlg _ n (diagV4ClsplitAuto n g (diagV4ClsplitAuto n h a))
        congr 1
        have hhom : (diagV4ClsplitAuto n (g * h)).toAlgHom =
            (diagV4ClsplitAuto n g).toAlgHom.comp (diagV4ClsplitAuto n h).toAlgHom := by
          apply CliffordAlgebra.hom_ext; apply LinearMap.ext; intro v
          change diagV4ClsplitAuto n (g * h) (CliffordAlgebra.ι (Qsplit n) v) =
            diagV4ClsplitAuto n g (diagV4ClsplitAuto n h (CliffordAlgebra.ι (Qsplit n) v))
          rw [diagV4ClsplitAuto_ι, diagV4ClsplitAuto_ι, diagV4ClsplitAuto_ι, diagV4Fun_mul]
        exact AlgHom.congr_fun hhom a

theorem diagV4Infinity_T_eq_involute (x : SplitCliffordInfinity) :
    diagV4InfinitySymmetryAction.act (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T) x =
      splitCliffordInfinityInvolute x := by
  induction x using DirectLimit.induction with
  | _ n a =>
      change DirectLimit.Algebra.of SplitCliffordTensorBridge.SplitClNNAlg
          (fun i j hij => splitCliffordMap i j hij) n
          (diagV4ClsplitAuto n (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T) a) =
        splitCliffordInfinityInvolute
          (DirectLimit.Algebra.of SplitCliffordTensorBridge.SplitClNNAlg
            (fun i j hij => splitCliffordMap i j hij) n a)
      rw [diagV4ClsplitAuto_T, splitCliffordInfinityInvolute_ofStage]

/-- `G_swap ↪ V4` sending swap (`Multiplicative.ofAdd 1`) to grade parity `T` (`J1` conjugation). -/
def gSwapToV4 : G_swap →* V4 where
  toFun g := if g = 1 then 1 else Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T
  map_one' := by simp
  map_mul' g h := by
    have hg : g = 1 ∨ g = Multiplicative.ofAdd (1 : ZMod 2) := g_swap_cases g
    have hh : h = 1 ∨ h = Multiplicative.ofAdd (1 : ZMod 2) := g_swap_cases h
    rcases hg with rfl | rfl <;> rcases hh with rfl | rfl <;> decide

@[simp] theorem gSwapToV4_one : gSwapToV4 1 = 1 := rfl

@[simp] theorem gSwapToV4_swap :
    gSwapToV4 (Multiplicative.ofAdd (1 : ZMod 2)) =
      Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T := by decide

/-- Equivalence `BitWord 1 ≃ Fin 2` (`fun _ => false ↦ 0`, `fun _ => true ↦ 1`). -/
def bitWordOneEquivFin2 : BitWord 1 ≃ Fin 2 where
  toFun w := if w 0 then 1 else 0
  invFun i _ := if i = 0 then false else true
  left_inv w := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst hi
    cases hw : w 0 <;> simp [hw]
  right_inv i := by fin_cases i <;> simp

/-- `DoubleCylinderStage ℝ 1 ≃ₐ[ℝ] Mat2`. -/
def doubleCylinderStageEquivMat2 : DoubleCylinderStage ℝ 1 ≃ₐ[ℝ] InfoGeometry.Clifford.Cl11Matrix.Mat2 :=
  Matrix.reindexAlgEquiv ℝ ℝ bitWordOneEquivFin2

/-- At stage `1`, the Erlangen cylinder bit-flip `stageSwapEquiv ℝ 1` is literally `localCl11Map T`
(`J1` conjugation) on `Mat2`. -/
theorem stageSwapEquiv_one_eq_localCl11Map_T (M : DoubleCylinderStage ℝ 1) :
    doubleCylinderStageEquivMat2 (stageSwapEquiv ℝ 1 M) =
      localCl11Map (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T)
        (doubleCylinderStageEquivMat2 M) := by
  have hT : localCl11Map (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T) =
      adjointAlgEquiv bivectorUnit := rfl
  rw [hT, adjointAlgEquiv_apply, bivectorUnit_value]
  have hbinv : (↑(bivectorUnit⁻¹) : InfoGeometry.Clifford.Cl11Matrix.Mat2) = J1 := rfl
  rw [hbinv]
  have hf : notWord 1 (fun _ => false) = (fun _ => true) := by
    funext k; fin_cases k; rfl
  have ht : notWord 1 (fun _ => true) = (fun _ => false) := by
    funext k; fin_cases k; rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [doubleCylinderStageEquivMat2, stageSwapEquiv, stageSwapFun,
      bitWordOneEquivFin2, J1, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, hf, ht]

/-- Diagonal `V4` conjugation on `MatStage n` via `kronPow u n`, commuting with `matStageEmbed n`. -/
def matStageDiagV4Auto (n : ℕ) (g : V4) : MatStage n ≃ₐ[ℝ] MatStage n :=
  let u : InfoGeometry.Clifford.Cl11Matrix.Mat2ˣ := rootUnit (v4RootHom g)
  let un : MatStage n := kronPow (u : InfoGeometry.Clifford.Cl11Matrix.Mat2) n
  let un_inv : MatStage n := kronPow ((↑(u⁻¹) : InfoGeometry.Clifford.Cl11Matrix.Mat2)) n
  have hmul : un * un_inv = (1 : MatStage n) := by
    induction n with
    | zero => exact Matrix.mul_one _
    | succ n ih =>
        change (kronPow (u : InfoGeometry.Clifford.Cl11Matrix.Mat2) n ⊗ₖ
            (u : InfoGeometry.Clifford.Cl11Matrix.Mat2)) *
            (kronPow ((↑(u⁻¹) : InfoGeometry.Clifford.Cl11Matrix.Mat2)) n ⊗ₖ
              (↑(u⁻¹) : InfoGeometry.Clifford.Cl11Matrix.Mat2)) = 1
        rw [← Matrix.mul_kronecker_mul, ih, Units.mul_inv, Matrix.one_kronecker_one]
  have hmul' : un_inv * un = (1 : MatStage n) := by
    clear hmul
    induction n with
    | zero => exact Matrix.mul_one _
    | succ n ih =>
        change (kronPow ((↑(u⁻¹) : InfoGeometry.Clifford.Cl11Matrix.Mat2)) n ⊗ₖ
            (↑(u⁻¹) : InfoGeometry.Clifford.Cl11Matrix.Mat2)) *
            (kronPow (u : InfoGeometry.Clifford.Cl11Matrix.Mat2) n ⊗ₖ
              (u : InfoGeometry.Clifford.Cl11Matrix.Mat2)) = 1
        rw [← Matrix.mul_kronecker_mul, ih, Units.inv_mul, Matrix.one_kronecker_one]
  let U : (MatStage n)ˣ := Units.mkOfMulEqOne un un_inv hmul
  MulSemiringAction.toAlgEquiv ℝ (MatStage n) (ConjAct.toConjAct U)

/-- Note: at `g = T`, `matStageDiagV4Auto n T` is conjugation by `Jn J1 n` (`kronPow J1 n`),
which under `clStageEquiv n` equals `stageSwapEquiv ℝ n` on `DoubleCylinderStage ℝ n`! -/
theorem matStageDiagV4Auto_bond (n : ℕ) (g : V4) (A : MatStage n) :
    matStageDiagV4Auto (n + 1) g (matStageEmbed n A) =
      matStageEmbed n (matStageDiagV4Auto n g A) := by
  dsimp [matStageDiagV4Auto, matStageEmbed]
  change (kronPow _ n ⊗ₖ (rootUnit (v4RootHom g) : InfoGeometry.Clifford.Cl11Matrix.Mat2)) *
      (A ⊗ₖ 1) *
      (kronPow _ n ⊗ₖ (↑((rootUnit (v4RootHom g))⁻¹) : InfoGeometry.Clifford.Cl11Matrix.Mat2)) =
    ((kronPow _ n * A * kronPow _ n) ⊗ₖ (1 : InfoGeometry.Clifford.Cl11Matrix.Mat2))
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, mul_one, Units.mul_inv]

/-- Global diagonal `V4` symmetry action descended onto `Cl11TensorTowerLimit.Limit`. -/
private def matTowerLimitV4_fwd (g : V4) :
    InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit →+*
      InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit :=
  directLimitLift stageBond
    (fun n => (ofStage n).comp (matStageDiagV4Auto n g).toRingHom)
    (fun n A => by
      change ofStage (n + 1) (matStageDiagV4Auto (n + 1) g (matStageEmbed n A)) =
        ofStage n (matStageDiagV4Auto n g A)
      rw [matStageDiagV4Auto_bond]
      exact directLimitOf_bond stageBond n (matStageDiagV4Auto n g A))

private theorem matTowerLimitV4_fwd_ofStage (g : V4) (n : ℕ) (A : Stage n) :
    matTowerLimitV4_fwd g (ofStage n A) = ofStage n (matStageDiagV4Auto n g A) :=
  directLimitLift_of _ _ _ n A

private def matTowerLimitV4_bwd (g : V4) :
    InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit →+*
      InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit :=
  directLimitLift stageBond
    (fun n => (ofStage n).comp (matStageDiagV4Auto n g).symm.toRingHom)
    (fun n A => by
      have hbond : (matStageDiagV4Auto (n + 1) g).symm (stageBond n A) =
          stageBond n ((matStageDiagV4Auto n g).symm A) :=
        (matStageDiagV4Auto (n + 1) g).injective (by
          rw [AlgEquiv.apply_symm_apply]
          change _ = matStageDiagV4Auto (n + 1) g (matStageEmbed n ((matStageDiagV4Auto n g).symm A))
          rw [matStageDiagV4Auto_bond, AlgEquiv.apply_symm_apply]
          rfl)
      change ofStage (n + 1) ((matStageDiagV4Auto (n + 1) g).symm (stageBond n A)) =
        ofStage n ((matStageDiagV4Auto n g).symm A)
      rw [hbond]
      exact directLimitOf_bond stageBond n ((matStageDiagV4Auto n g).symm A))

private theorem matTowerLimitV4_bwd_ofStage (g : V4) (n : ℕ) (A : Stage n) :
    matTowerLimitV4_bwd g (ofStage n A) = ofStage n ((matStageDiagV4Auto n g).symm A) :=
  directLimitLift_of _ _ _ n A

def matTowerLimitV4Auto (g : V4) :
    InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit ≃ₐ[ℝ]
      InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit :=
  let re : InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit ≃+*
      InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit :=
    { toFun := matTowerLimitV4_fwd g
      invFun := matTowerLimitV4_bwd g
      left_inv := fun x => by
        induction x using DirectLimit.induction with
        | _ n A =>
            change matTowerLimitV4_bwd g (matTowerLimitV4_fwd g (ofStage n A)) = ofStage n A
            rw [matTowerLimitV4_fwd_ofStage, matTowerLimitV4_bwd_ofStage,
              AlgEquiv.symm_apply_apply]
      right_inv := fun x => by
        induction x using DirectLimit.induction with
        | _ n A =>
            change matTowerLimitV4_fwd g (matTowerLimitV4_bwd g (ofStage n A)) = ofStage n A
            rw [matTowerLimitV4_bwd_ofStage, matTowerLimitV4_fwd_ofStage,
              AlgEquiv.apply_symm_apply]
      map_add' := map_add (matTowerLimitV4_fwd g)
      map_mul' := map_mul (matTowerLimitV4_fwd g) }
  AlgEquiv.ofRingEquiv (f := re)
    (fun r => by
      change matTowerLimitV4_fwd g (realAlgebraMap r) = realAlgebraMap r
      rw [realAlgebraMap_stage 0 r, matTowerLimitV4_fwd_ofStage]
      rw [(matStageDiagV4Auto 0 g).commutes])

@[simp] private theorem matTowerLimitV4Auto_ofStage (g : V4) (n : ℕ) (A : Stage n) :
    matTowerLimitV4Auto g (ofStage n A) = ofStage n (matStageDiagV4Auto n g A) :=
  matTowerLimitV4_fwd_ofStage g n A

private theorem matStageDiagV4Auto_mul (n : ℕ) (g h : V4) (A : MatStage n) :
    matStageDiagV4Auto n (g * h) A = matStageDiagV4Auto n g (matStageDiagV4Auto n h A) := by
  induction n with
  | zero =>
      have h0 : ∀ (k : V4) (B : MatStage 0), matStageDiagV4Auto 0 k B = B := fun k B => by
        dsimp [matStageDiagV4Auto]
        change (1 : MatStage 0) * B * (1 : MatStage 0) = B
        simp
      rw [h0, h0, h0]
  | succ n ih =>
      let e := Matrix.kroneckerAlgEquiv (Idx n) (Fin 2) ℝ
      rw [← e.apply_symm_apply A]
      induction (e.symm A) using TensorProduct.inductionOn with
      | tmul P Q =>
          change matStageDiagV4Auto (n + 1) (g * h) (P ⊗ₖ Q) =
            matStageDiagV4Auto (n + 1) g (matStageDiagV4Auto (n + 1) h (P ⊗ₖ Q))
          have hkron : ∀ (k : V4) (P : MatStage n) (Q : InfoGeometry.Clifford.Cl11Matrix.Mat2),
              matStageDiagV4Auto (n + 1) k (P ⊗ₖ Q) =
                matStageDiagV4Auto n k P ⊗ₖ localCl11Map k Q := fun k P Q => by
            dsimp [matStageDiagV4Auto, localCl11Map]
            change (kronPow _ n ⊗ₖ (rootUnit (v4RootHom k) : InfoGeometry.Clifford.Cl11Matrix.Mat2)) *
                (P ⊗ₖ Q) *
                (kronPow _ n ⊗ₖ (↑((rootUnit (v4RootHom k))⁻¹) : InfoGeometry.Clifford.Cl11Matrix.Mat2)) =
              (kronPow _ n * P * kronPow _ n) ⊗ₖ
                ((rootUnit (v4RootHom k) : InfoGeometry.Clifford.Cl11Matrix.Mat2) * Q *
                  (↑((rootUnit (v4RootHom k))⁻¹) : InfoGeometry.Clifford.Cl11Matrix.Mat2))
            rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
          rw [hkron (g * h), hkron h, hkron g, ih P, map_mul]
          rfl
      | add u v hu hv =>
          rw [map_add e u v]
          calc matStageDiagV4Auto (n + 1) (g * h) ((e u : MatStage (n + 1)) + e v)
              = matStageDiagV4Auto (n + 1) (g * h) (e u) +
                  matStageDiagV4Auto (n + 1) (g * h) (e v) :=
                map_add (matStageDiagV4Auto (n + 1) (g * h)) (e u) (e v)
            _ = matStageDiagV4Auto (n + 1) g (matStageDiagV4Auto (n + 1) h (e u)) +
                  matStageDiagV4Auto (n + 1) g (matStageDiagV4Auto (n + 1) h (e v)) := by
                rw [hu, hv]
            _ = matStageDiagV4Auto (n + 1) g
                  (matStageDiagV4Auto (n + 1) h (e u) + matStageDiagV4Auto (n + 1) h (e v)) :=
                (map_add (matStageDiagV4Auto (n + 1) g) _ _).symm
            _ = matStageDiagV4Auto (n + 1) g
                  (matStageDiagV4Auto (n + 1) h ((e u : MatStage (n + 1)) + e v)) :=
                congrArg (matStageDiagV4Auto (n + 1) g)
                  (map_add (matStageDiagV4Auto (n + 1) h) (e u) (e v)).symm

/-- `SymmetryAction V4` on `Cl11TensorTowerLimit.Limit`. -/
def matTowerLimitV4SymmetryAction :
    SymmetryAction V4 InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit where
  act g := (matTowerLimitV4Auto g).toRingEquiv
  act_one x := by
    induction x using DirectLimit.induction with
    | _ n A =>
        change matTowerLimitV4Auto 1 (ofStage n A) = ofStage n A
        rw [matTowerLimitV4Auto_ofStage]
        congr 1
        dsimp [matStageDiagV4Auto]
        have h1 : ∀ m : ℕ, kronPow ((rootUnit (v4RootHom (1 : V4)) : InfoGeometry.Clifford.Cl11Matrix.Mat2)) m = 1 := by
          intro m
          induction m with
          | zero => rfl
          | succ m ih =>
              change kronPow _ m ⊗ₖ (1 : InfoGeometry.Clifford.Cl11Matrix.Mat2) = 1
              rw [ih, Matrix.one_kronecker_one]
        change (kronPow ((rootUnit (v4RootHom 1) : InfoGeometry.Clifford.Cl11Matrix.Mat2)) n) * A *
            (kronPow ((↑((rootUnit (v4RootHom 1))⁻¹) : InfoGeometry.Clifford.Cl11Matrix.Mat2)) n) = A
        have h1' : ∀ m : ℕ, kronPow ((↑((rootUnit (v4RootHom (1 : V4)))⁻¹) : InfoGeometry.Clifford.Cl11Matrix.Mat2)) m = 1 := by
          intro m
          induction m with
          | zero => rfl
          | succ m ih =>
              change kronPow _ m ⊗ₖ (1 : InfoGeometry.Clifford.Cl11Matrix.Mat2) = 1
              rw [ih, Matrix.one_kronecker_one]
        rw [h1 n, h1' n, one_mul, mul_one]
  act_mul g h x := by
    induction x using DirectLimit.induction with
    | _ n A =>
        change matTowerLimitV4Auto (g * h) (ofStage n A) =
          matTowerLimitV4Auto g (matTowerLimitV4Auto h (ofStage n A))
        rw [matTowerLimitV4Auto_ofStage, matTowerLimitV4Auto_ofStage,
          matTowerLimitV4Auto_ofStage]
        exact congrArg (ofStage n) (matStageDiagV4Auto_mul n g h A)

/-- Transported diagonal `V4` symmetry action on `RealCantorOpLimit.Limit` via `limitRingEquiv`. -/
def realCantorLimitV4SymmetryAction :
    SymmetryAction V4 InfoGeometry.Clifford.RealCantorOpLimit.Limit where
  act g := (limitRingEquiv.symm.trans (matTowerLimitV4SymmetryAction.act g)).trans limitRingEquiv
  act_one x := by simp [matTowerLimitV4SymmetryAction.act_one]
  act_mul g h x := by simp [matTowerLimitV4SymmetryAction.act_mul]

/-- Canonical ring equivalence `Cl11TensorTowerLimit.Limit ≃+* DoubleCylinderColimit ℝ` via
`clStageEquiv n : MatStage n ≃ₐ[ℝ] DoubleCylinderStage ℝ n`. -/
private theorem clStageEquiv_doubleCylinderBond (n : ℕ) (A : MatStage n) :
    clStageEquiv (n + 1) (matStageEmbed n A) = doubleCylinderBond ℝ n (clStageEquiv n A) := by
  exact clStageEquiv_bond n A

private def matTowerLimitDoubleCyl_fwd :
    InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit →+* DoubleCylinderColimit ℝ :=
  directLimitLift stageBond
    (fun n => (doubleCylinderInclusion ℝ n).comp (clStageEquiv n).toRingHom)
    (fun n A => by
      change doubleCylinderInclusion ℝ (n + 1) (clStageEquiv (n + 1) (matStageEmbed n A)) =
        doubleCylinderInclusion ℝ n (clStageEquiv n A)
      rw [clStageEquiv_doubleCylinderBond, doubleCylinderInclusion_bond])

private theorem matTowerLimitDoubleCyl_fwd_ofStage (n : ℕ) (A : Stage n) :
    matTowerLimitDoubleCyl_fwd (ofStage n A) = doubleCylinderInclusion ℝ n (clStageEquiv n A) :=
  directLimitLift_of _ _ _ n A

private def matTowerLimitDoubleCyl_bwd :
    DoubleCylinderColimit ℝ →+* InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit :=
  directLimitLift (doubleCylinderBond ℝ)
    (fun n => (ofStage n).comp (clStageEquiv n).symm.toRingHom)
    (fun n M => by
      have hstep : (clStageEquiv (n + 1)).symm (doubleCylinderBond ℝ n M) =
          stageBond n ((clStageEquiv n).symm M) :=
        (clStageEquiv (n + 1)).injective (by
          rw [AlgEquiv.apply_symm_apply]
          change _ = clStageEquiv (n + 1) (matStageEmbed n ((clStageEquiv n).symm M))
          rw [clStageEquiv_doubleCylinderBond, AlgEquiv.apply_symm_apply])
      change ofStage (n + 1) ((clStageEquiv (n + 1)).symm (doubleCylinderBond ℝ n M)) =
        ofStage n ((clStageEquiv n).symm M)
      rw [hstep]
      exact directLimitOf_bond stageBond n ((clStageEquiv n).symm M))

private theorem matTowerLimitDoubleCyl_bwd_ofStage (n : ℕ) (M : DoubleCylinderStage ℝ n) :
    matTowerLimitDoubleCyl_bwd (doubleCylinderInclusion ℝ n M) =
      ofStage n ((clStageEquiv n).symm M) :=
  directLimitLift_of _ _ _ n M

def matTowerLimitEquivDoubleCylinderColimit :
    InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit ≃+* DoubleCylinderColimit ℝ where
  toFun := matTowerLimitDoubleCyl_fwd
  invFun := matTowerLimitDoubleCyl_bwd
  left_inv x := by
    induction x using DirectLimit.induction with
    | _ n A =>
        change matTowerLimitDoubleCyl_bwd (matTowerLimitDoubleCyl_fwd (ofStage n A)) = ofStage n A
        rw [matTowerLimitDoubleCyl_fwd_ofStage, matTowerLimitDoubleCyl_bwd_ofStage,
          AlgEquiv.symm_apply_apply]
  right_inv x := by
    induction x using DirectLimit.induction with
    | _ n M =>
        change matTowerLimitDoubleCyl_fwd (matTowerLimitDoubleCyl_bwd (doubleCylinderInclusion ℝ n M)) =
          doubleCylinderInclusion ℝ n M
        rw [matTowerLimitDoubleCyl_bwd_ofStage, matTowerLimitDoubleCyl_fwd_ofStage,
          AlgEquiv.apply_symm_apply]
  map_add' := map_add matTowerLimitDoubleCyl_fwd
  map_mul' := map_mul matTowerLimitDoubleCyl_fwd

@[simp] private theorem matTowerLimitEquivDoubleCylinderColimit_ofStage (n : ℕ) (A : Stage n) :
    matTowerLimitEquivDoubleCylinderColimit (ofStage n A) =
      doubleCylinderInclusion ℝ n (clStageEquiv n A) :=
  matTowerLimitDoubleCyl_fwd_ofStage n A

/-- Transported diagonal `V4` symmetry action on `DoubleCylinderColimit ℝ`. -/
def doubleCylinderColimitV4SymmetryAction : SymmetryAction V4 (DoubleCylinderColimit ℝ) where
  act g := (matTowerLimitEquivDoubleCylinderColimit.symm.trans
    (matTowerLimitV4SymmetryAction.act g)).trans matTowerLimitEquivDoubleCylinderColimit
  act_one x := by simp [matTowerLimitV4SymmetryAction.act_one]
  act_mul g h x := by simp [matTowerLimitV4SymmetryAction.act_mul]

/-- At `g = T`, `clStageEquiv n` intertwines `matStageDiagV4Auto n T` (`kronPow J1 n` conjugation)
with the Erlangen `stageSwapEquiv ℝ n` (`notWord n` flip). -/
theorem clStageEquiv_diagV4_T (n : ℕ) (A : MatStage n) :
    clStageEquiv n (matStageDiagV4Auto n (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T) A) =
      stageSwapEquiv ℝ n (clStageEquiv n A) := by
  induction n with
  | zero =>
      ext u v
      have huv : u = v := Subsingleton.elim u v
      subst huv
      have h0 : matStageDiagV4Auto 0 (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T) A = A := by
        dsimp [matStageDiagV4Auto]
        change (1 : MatStage 0) * A * (1 : MatStage 0) = A
        simp
      rw [h0, clStageEquiv_apply, stageSwapEquiv_apply]
      have hnot : notWord 0 u = u := Subsingleton.elim _ _
      rw [hnot]
  | succ n ih =>
      let e := Matrix.kroneckerAlgEquiv (Idx n) (Fin 2) ℝ
      rw [← e.apply_symm_apply A]
      induction (e.symm A) using TensorProduct.inductionOn with
      | tmul P Q =>
          have hmul : matStageDiagV4Auto (n + 1) (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T)
              (P ⊗ₖ Q) =
              matStageDiagV4Auto n (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T) P ⊗ₖ
                (J1 * Q * J1) := by
            dsimp [matStageDiagV4Auto]
            change (kronPow _ n ⊗ₖ J1) * (P ⊗ₖ Q) * (kronPow _ n ⊗ₖ J1) = _
            rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
            rfl
          rw [show (e (P ⊗ₜ[ℝ] Q) : MatStage (n + 1)) = P ⊗ₖ Q from rfl, hmul]
          ext u v
          have hpu : prefixSucc n (notWord (n + 1) u) = notWord n (prefixSucc n u) := rfl
          have hpv : prefixSucc n (notWord (n + 1) v) = notWord n (prefixSucc n v) := rfl
          have hih := congrFun (congrFun (ih P) (prefixSucc n u)) (prefixSucc n v)
          rw [clStageEquiv_apply, stageSwapEquiv_apply] at hih
          simp only [Matrix.reindex_apply, Matrix.submatrix_apply] at hih
          let M1 : ClStage (n + 1) :=
            matStageDiagV4Auto n (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T) P ⊗ₖ
              (J1 * Q * J1)
          let M2 : ClStage (n + 1) := P ⊗ₖ Q
          have hcl1 : clStageEquiv (n + 1) M1 u v =
              M1 ((idxBitWordEquiv (n + 1)).symm u) ((idxBitWordEquiv (n + 1)).symm v) := by
            rw [clStageEquiv_apply]; rfl
          have hcl2 : stageSwapEquiv ℝ (n + 1) (clStageEquiv (n + 1) M2) u v =
              M2 ((idxBitWordEquiv (n + 1)).symm (notWord (n + 1) u))
                 ((idxBitWordEquiv (n + 1)).symm (notWord (n + 1) v)) := by
            rw [stageSwapEquiv_apply, clStageEquiv_apply]; rfl
          change clStageEquiv (n + 1) M1 u v = stageSwapEquiv ℝ (n + 1) (clStageEquiv (n + 1) M2) u v
          rw [hcl1, hcl2, idxBitWordEquiv_succ_symm_apply, idxBitWordEquiv_succ_symm_apply,
            idxBitWordEquiv_succ_symm_apply, idxBitWordEquiv_succ_symm_apply]
          simp only [M1, M2, Matrix.kronecker_apply, hpu, hpv, hih]
          congr 1
          have hbu : InfoGeometry.Canonical.FiniteCantorCuntzBranches.lastBit n (notWord (n + 1) u) =
              !(InfoGeometry.Canonical.FiniteCantorCuntzBranches.lastBit n u) := rfl
          have hbv : InfoGeometry.Canonical.FiniteCantorCuntzBranches.lastBit n (notWord (n + 1) v) =
              !(InfoGeometry.Canonical.FiniteCantorCuntzBranches.lastBit n v) := rfl
          rw [hbu, hbv]
          cases InfoGeometry.Canonical.FiniteCantorCuntzBranches.lastBit n u <;>
            cases InfoGeometry.Canonical.FiniteCantorCuntzBranches.lastBit n v <;>
            simp [finTwoEquivBool, J1, Matrix.mul_apply, Matrix.vecMul, dotProduct,
              Fin.sum_univ_two]
      | add x y hx hy =>
          have hadd : (e (x + y) : MatStage (n + 1)) =
              (e x : MatStage (n + 1)) + (e y : MatStage (n + 1)) :=
            map_add e x y
          rw [hadd]
          exact ((congrArg (clStageEquiv (n + 1))
              (map_add (matStageDiagV4Auto (n + 1)
                  (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T))
                (e x : MatStage (n + 1)) (e y : MatStage (n + 1)))).trans
            (map_add (clStageEquiv (n + 1))
              (matStageDiagV4Auto (n + 1)
                (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T)
                (e x : MatStage (n + 1)))
              (matStageDiagV4Auto (n + 1)
                (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T)
                (e y : MatStage (n + 1))))).trans
            ((congrArg₂ (· + ·) hx hy).trans
              ((map_add (stageSwapEquiv ℝ (n + 1))
                  (clStageEquiv (n + 1) (e x : MatStage (n + 1)))
                  (clStageEquiv (n + 1) (e y : MatStage (n + 1)))).symm.trans
                (congrArg (stageSwapEquiv ℝ (n + 1))
                  (map_add (clStageEquiv (n + 1))
                    (e x : MatStage (n + 1)) (e y : MatStage (n + 1))).symm)))

/-- Restricting `doubleCylinderColimitV4SymmetryAction` along `gSwapToV4 : G_swap →* V4`
reproduces `erlangenDoubleCylinderSymmetryAction ℝ`! -/
theorem doubleCylinderColimitV4_restrict_gSwap (g : G_swap) (x : DoubleCylinderColimit ℝ) :
    doubleCylinderColimitV4SymmetryAction.act (gSwapToV4 g) x =
      (erlangenDoubleCylinderSymmetryAction ℝ).act g x := by
  rcases g_swap_cases g with rfl | rfl
  · rw [gSwapToV4_one]
    simp [doubleCylinderColimitV4SymmetryAction.act_one,
      (erlangenDoubleCylinderSymmetryAction ℝ).act_one]
  · rw [gSwapToV4_swap]
    obtain ⟨y, rfl⟩ := matTowerLimitEquivDoubleCylinderColimit.surjective x
    induction y using DirectLimit.induction with
    | _ n A =>
        dsimp only [doubleCylinderColimitV4SymmetryAction, RingEquiv.trans_apply]
        change matTowerLimitEquivDoubleCylinderColimit
            (matTowerLimitV4Auto (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T)
              (matTowerLimitEquivDoubleCylinderColimit.symm
                (matTowerLimitEquivDoubleCylinderColimit (ofStage n A)))) =
          (erlangenDoubleCylinderSymmetryAction ℝ).act (Multiplicative.ofAdd (1 : ZMod 2))
            (matTowerLimitEquivDoubleCylinderColimit (ofStage n A))
        rw [RingEquiv.symm_apply_apply, matTowerLimitV4Auto_ofStage,
          matTowerLimitEquivDoubleCylinderColimit_ofStage,
          matTowerLimitEquivDoubleCylinderColimit_ofStage, clStageEquiv_diagV4_T]
        exact (colimitSwapEquiv_inclusion ℝ n (clStageEquiv n A)).symm

/-- Cantor `localCl11AlgebraHom P` equivariance under all three nontrivial `V4` generators
(`T` via `P.bitOperator true`, `P` via `P.bitOperator false`, `PT` via `localCl11Negative P`). -/
theorem localCl11AlgebraHom_v4_equivariant {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (P : CantorBinaryTiltCARCCRBridge.BinaryWordTiltReadout Op) (a : CliffordAlgebra q11) :
    (P.bitOperator true * localCl11AlgebraHom P a * P.bitOperator true =
      localCl11AlgebraHom P (cl11V4Auto (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T) a)) ∧
    (P.bitOperator false * localCl11AlgebraHom P a * P.bitOperator false =
      localCl11AlgebraHom P (cl11V4Auto (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P) a)) ∧
    (localCl11Negative P * localCl11AlgebraHom P a * (-localCl11Negative P) =
      localCl11AlgebraHom P (cl11V4Auto (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT) a)) := by
  have h1 :
      ({ toFun := fun y : Op => P.bitOperator true * y * P.bitOperator true
         map_one' := by rw [mul_one, P.bitOperator_true_sq]
         map_mul' := fun x y => by
           calc P.bitOperator true * (x * y) * P.bitOperator true
               = P.bitOperator true * x * (P.bitOperator true * P.bitOperator true) *
                   (y * P.bitOperator true) := by rw [P.bitOperator_true_sq]; noncomm_ring
             _ = (P.bitOperator true * x * P.bitOperator true) *
                   (P.bitOperator true * y * P.bitOperator true) := by noncomm_ring
         map_zero' := by simp
         map_add' := fun x y => by rw [mul_add, add_mul]
         commutes' := fun r => by
           rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc,
             P.bitOperator_true_sq] } : Op →ₐ[ℝ] Op).comp (localCl11AlgebraHom P) =
      (localCl11AlgebraHom P).comp
        (cl11V4Auto (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T)).toAlgHom := by
    apply CliffordAlgebra.hom_ext; apply LinearMap.ext; intro v
    rcases v with ⟨x, y⟩
    have hv : (x, y) = x • ((1 : ℝ), (0 : ℝ)) + y • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    conv_lhs => rw [hv]
    conv_rhs => rw [hv]
    have hinv0 : cl11V4Auto (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T)
        (CliffordAlgebra.ι q11 (1, 0)) = -CliffordAlgebra.ι q11 (1, 0) := by
      rw [cl11V4Auto_T]; exact CliffordAlgebra.involute_ι _
    have hinv1 : cl11V4Auto (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T)
        (CliffordAlgebra.ι q11 (0, 1)) = -CliffordAlgebra.ι q11 (0, 1) := by
      rw [cl11V4Auto_T]; exact CliffordAlgebra.involute_ι _
    have hT0 : P.bitOperator true * localCl11Positive P * P.bitOperator true =
        -localCl11Positive P := by
      change P.bitOperator true * P.bitOperator false * P.bitOperator true = -P.bitOperator false
      rw [eq_neg_of_add_eq_zero_right P.bitOperator_anticomm, neg_mul, mul_assoc,
        P.bitOperator_true_sq, mul_one]
    have hT1 : P.bitOperator true * localCl11Negative P * P.bitOperator true =
        -localCl11Negative P := by
      calc P.bitOperator true * (P.bitOperator false * P.bitOperator true) * P.bitOperator true
          = (P.bitOperator true * P.bitOperator false) * (P.bitOperator true * P.bitOperator true) := by
            noncomm_ring
        _ = -(P.bitOperator false * P.bitOperator true) * 1 := by
            rw [eq_neg_of_add_eq_zero_right P.bitOperator_anticomm, P.bitOperator_true_sq]
        _ = -(P.bitOperator false * P.bitOperator true) := mul_one _
    simp only [AlgHom.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      map_add, map_smul]
    change x • (P.bitOperator true * localCl11AlgebraHom P (CliffordAlgebra.ι q11 (1, 0)) *
          P.bitOperator true) +
        y • (P.bitOperator true * localCl11AlgebraHom P (CliffordAlgebra.ι q11 (0, 1)) *
          P.bitOperator true) =
      x • localCl11AlgebraHom P
          (cl11V4Auto (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T)
            (CliffordAlgebra.ι q11 (1, 0))) +
        y • localCl11AlgebraHom P
          (cl11V4Auto (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T)
            (CliffordAlgebra.ι q11 (0, 1)))
    rw [hinv0, hinv1, map_neg, map_neg, localCl11AlgebraHom_pos, localCl11AlgebraHom_neg, hT0, hT1]
  have h2 :
      ({ toFun := fun y : Op => P.bitOperator false * y * P.bitOperator false
         map_one' := by rw [mul_one, P.bitOperator_false_sq]
         map_mul' := fun x y => by
           calc P.bitOperator false * (x * y) * P.bitOperator false
               = P.bitOperator false * x * (P.bitOperator false * P.bitOperator false) *
                   (y * P.bitOperator false) := by rw [P.bitOperator_false_sq]; noncomm_ring
             _ = (P.bitOperator false * x * P.bitOperator false) *
                   (P.bitOperator false * y * P.bitOperator false) := by noncomm_ring
         map_zero' := by simp
         map_add' := fun x y => by rw [mul_add, add_mul]
         commutes' := fun r => by
           rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc,
             P.bitOperator_false_sq] } : Op →ₐ[ℝ] Op).comp (localCl11AlgebraHom P) =
      (localCl11AlgebraHom P).comp
        (cl11V4Auto (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P)).toAlgHom := by
    apply CliffordAlgebra.hom_ext; apply LinearMap.ext; intro v
    rcases v with ⟨x, y⟩
    have hv : (x, y) = x • ((1 : ℝ), (0 : ℝ)) + y • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    conv_lhs => rw [hv]
    conv_rhs => rw [hv]
    have hP_i0 : cl11V4Auto (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P)
        (CliffordAlgebra.ι q11 (1, 0)) = CliffordAlgebra.ι q11 (1, 0) := by
      rw [cl11V4Auto_P, splitReflectionCliffordAuto_ι]
      congr 1; ext <;> simp [splitReflection]
    have hP_i1 : cl11V4Auto (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P)
        (CliffordAlgebra.ι q11 (0, 1)) = -CliffordAlgebra.ι q11 (0, 1) := by
      rw [cl11V4Auto_P, splitReflectionCliffordAuto_ι, ← map_neg]
      congr 1; ext <;> simp [splitReflection]
    have hP0 : P.bitOperator false * localCl11Positive P * P.bitOperator false =
        localCl11Positive P := by
      change P.bitOperator false * P.bitOperator false * P.bitOperator false = P.bitOperator false
      rw [P.bitOperator_false_sq, one_mul]
    have hP1 : P.bitOperator false * localCl11Negative P * P.bitOperator false =
        -localCl11Negative P := by
      change P.bitOperator false * (P.bitOperator false * P.bitOperator true) * P.bitOperator false =
        -(P.bitOperator false * P.bitOperator true)
      calc P.bitOperator false * (P.bitOperator false * P.bitOperator true) * P.bitOperator false
          = (P.bitOperator false * P.bitOperator false) * (P.bitOperator true * P.bitOperator false) := by
            noncomm_ring
        _ = P.bitOperator true * P.bitOperator false := by rw [P.bitOperator_false_sq, one_mul]
        _ = -(P.bitOperator false * P.bitOperator true) :=
            eq_neg_of_add_eq_zero_right P.bitOperator_anticomm
    simp only [AlgHom.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      map_add, map_smul]
    change x • (P.bitOperator false * localCl11AlgebraHom P (CliffordAlgebra.ι q11 (1, 0)) *
          P.bitOperator false) +
        y • (P.bitOperator false * localCl11AlgebraHom P (CliffordAlgebra.ι q11 (0, 1)) *
          P.bitOperator false) =
      x • localCl11AlgebraHom P
          (cl11V4Auto (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P)
            (CliffordAlgebra.ι q11 (1, 0))) +
        y • localCl11AlgebraHom P
          (cl11V4Auto (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P)
            (CliffordAlgebra.ι q11 (0, 1)))
    rw [hP_i0, hP_i1, map_neg, localCl11AlgebraHom_pos, localCl11AlgebraHom_neg, hP0, hP1]
  have hneg_sq : localCl11Negative P * (-localCl11Negative P) = 1 := by
    rw [mul_neg, (binaryWordLocalCl11Relation P).2.1, neg_neg]
  have h3 :
      ({ toFun := fun y : Op => localCl11Negative P * y * (-localCl11Negative P)
         map_one' := by rw [mul_one, hneg_sq]
         map_mul' := fun x y => by
           calc localCl11Negative P * (x * y) * (-localCl11Negative P)
               = localCl11Negative P * x * ((-localCl11Negative P) * localCl11Negative P) *
                   (y * (-localCl11Negative P)) := by
                 have hneg_sq' : (-localCl11Negative P) * localCl11Negative P = 1 := by
                   rw [neg_mul, (binaryWordLocalCl11Relation P).2.1, neg_neg]
                 rw [hneg_sq']; noncomm_ring
             _ = (localCl11Negative P * x * (-localCl11Negative P)) *
                   (localCl11Negative P * y * (-localCl11Negative P)) := by noncomm_ring
         map_zero' := by simp
         map_add' := fun x y => by rw [mul_add, add_mul]
         commutes' := fun r => by
           rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc,
             hneg_sq] } : Op →ₐ[ℝ] Op).comp (localCl11AlgebraHom P) =
      (localCl11AlgebraHom P).comp
        (cl11V4Auto (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT)).toAlgHom := by
    apply CliffordAlgebra.hom_ext; apply LinearMap.ext; intro v
    rcases v with ⟨x, y⟩
    have hv : (x, y) = x • ((1 : ℝ), (0 : ℝ)) + y • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    conv_lhs => rw [hv]
    conv_rhs => rw [hv]
    have hPT_i0 : cl11V4Auto (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT)
        (CliffordAlgebra.ι q11 (1, 0)) = -CliffordAlgebra.ι q11 (1, 0) := by
      rw [cl11V4Auto_PT, splitReflectionFirstCoordinateCliffordAuto_ι, ← map_neg]
      congr 1; ext <;> simp [splitReflectionFirstCoordinate]
    have hPT_i1 : cl11V4Auto (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT)
        (CliffordAlgebra.ι q11 (0, 1)) = CliffordAlgebra.ι q11 (0, 1) := by
      rw [cl11V4Auto_PT, splitReflectionFirstCoordinateCliffordAuto_ι]
      congr 1; ext <;> simp [splitReflectionFirstCoordinate]
    have hPT0 : localCl11Negative P * localCl11Positive P * (-localCl11Negative P) =
        -localCl11Positive P := by
      have hanti : localCl11Negative P * localCl11Positive P =
          -(localCl11Positive P * localCl11Negative P) :=
        eq_neg_of_add_eq_zero_right (binaryWordLocalCl11Relation P).2.2
      calc localCl11Negative P * localCl11Positive P * (-localCl11Negative P)
          = -(localCl11Positive P * localCl11Negative P) * (-localCl11Negative P) := by rw [hanti]
        _ = localCl11Positive P * (localCl11Negative P * localCl11Negative P) := by noncomm_ring
        _ = localCl11Positive P * (-1) := by rw [(binaryWordLocalCl11Relation P).2.1]
        _ = -localCl11Positive P := by noncomm_ring
    have hPT1 : localCl11Negative P * localCl11Negative P * (-localCl11Negative P) =
        localCl11Negative P := by
      rw [(binaryWordLocalCl11Relation P).2.1, neg_one_mul, neg_neg]
    simp only [AlgHom.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      map_add, map_smul]
    change x • (localCl11Negative P * localCl11AlgebraHom P (CliffordAlgebra.ι q11 (1, 0)) *
          (-localCl11Negative P)) +
        y • (localCl11Negative P * localCl11AlgebraHom P (CliffordAlgebra.ι q11 (0, 1)) *
          (-localCl11Negative P)) =
      x • localCl11AlgebraHom P
          (cl11V4Auto (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT)
            (CliffordAlgebra.ι q11 (1, 0))) +
        y • localCl11AlgebraHom P
          (cl11V4Auto (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT)
            (CliffordAlgebra.ι q11 (0, 1)))
    rw [hPT_i0, hPT_i1, map_neg, localCl11AlgebraHom_pos, localCl11AlgebraHom_neg, hPT0, hPT1]
  exact ⟨AlgHom.congr_fun h1 a, AlgHom.congr_fun h2 a, AlgHom.congr_fun h3 a⟩

end KleinFourLiftAndErlangenUnification

/-- Closed noncommutativity witness on `Matrix (Fin 2) (Fin 2) ℝ` (`E₊ * E₋ ≠ E₋ * E₊`), certifying
genuinely noncommutative operator algebra content across the unified Clifford tower. -/
theorem mat2_noncomm_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A := by
  refine ⟨InfoGeometry.Clifford.Cl11Matrix.Eplus, InfoGeometry.Clifford.Cl11Matrix.Eminus, ?_⟩
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  simp [InfoGeometry.Clifford.Cl11Matrix.Eplus, InfoGeometry.Clifford.Cl11Matrix.Eminus] at h01
  norm_num at h01

end InfoGeometry.Canonical.SplitCliffordTowerUnification
