/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl11GradedTensorUntwist
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CantorCylinderLattice
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# InfoGeometry.Clifford.SplitCl11GradedTensorTower

General `n`-fold split Clifford graded-tensor tower:

  `⊗ᵍ_{k=1}^n Cl(1,1)  ≃ₐ[ℝ]  Cl(q11^{⊕ n})  ≃ₐ[ℝ]  Matrix (Fin (2^n)) (Fin (2^n)) ℝ`

constructed inductively via the native Koszul untwisting isomorphism
`splitCliffordEquivMatrix` (`Cl11GradedTensorUntwist.lean`), together with its
diagonal Cartan Boolean projector subalgebra indexed by `BinaryWord n = Fin n → Bool`
and `Set (BinaryWord n)` (from `CantorCylinderLattice.lean`).
-/

noncomputable section

namespace InfoGeometry.Clifford.SplitCl11GradedTensorTower

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11GradedTensorUntwist
open InfoGeometry.Canonical.CantorCylinderLattice
open scoped TensorProduct

/-! ## 1. Recursive `n`-fold split quadratic carrier `q11^{⊕ n}` -/

/-- Carrier vector space for the `n`-fold orthogonal sum of `Cl(1,1)`. -/
def SplitCarrier : ℕ → Type
  | 0 => PUnit
  | n + 1 => (ℝ × ℝ) × SplitCarrier n

instance splitCarrierAddCommGroup : (n : ℕ) → AddCommGroup (SplitCarrier n)
  | 0 => inferInstanceAs (AddCommGroup PUnit)
  | n + 1 =>
    letI := splitCarrierAddCommGroup n
    inferInstanceAs (AddCommGroup ((ℝ × ℝ) × SplitCarrier n))

instance splitCarrierModule : (n : ℕ) → Module ℝ (SplitCarrier n)
  | 0 => inferInstanceAs (Module ℝ PUnit)
  | n + 1 =>
    letI := splitCarrierAddCommGroup n
    letI := splitCarrierModule n
    inferInstanceAs (Module ℝ ((ℝ × ℝ) × SplitCarrier n))

/-- The `n`-fold split quadratic form `q11^{⊕ n}` on `SplitCarrier n`. -/
def splitQ : (n : ℕ) → QuadraticForm ℝ (SplitCarrier n)
  | 0 => 0
  | n + 1 => q11.prod (splitQ n)

/-- The `n`-fold split Clifford algebra `Cl(q11^{⊕ n}) ≅ ⊗ᵍ^n Cl(1,1)`. -/
abbrev SplitClPower (n : ℕ) := CliffordAlgebra (splitQ n)

/-- Each step `n + 1` splits as a graded tensor product `Cl(1,1) ᵍ⊗ Cl(q11^{⊕ n})`. -/
def splitClPowerStepGradedTensor (n : ℕ) :
    SplitClPower (n + 1) ≃ₐ[ℝ]
      GradedTensorProduct ℝ (CliffordAlgebra.evenOdd q11) (CliffordAlgebra.evenOdd (splitQ n)) :=
  CliffordAlgebra.prodEquiv q11 (splitQ n)

/-! ## 2. Base equivalence `Cl(0 on PUnit) ≃ₐ[ℝ] Matrix (Fin 1) (Fin 1) ℝ` -/

/-- `CliffordAlgebra (0 : QuadraticForm ℝ PUnit) ≃ₐ[ℝ] ℝ`. -/
def clZeroPUnitEquivReal : SplitClPower 0 ≃ₐ[ℝ] ℝ :=
  AlgEquiv.ofAlgHom
    (CliffordAlgebra.lift (0 : QuadraticForm ℝ PUnit)
      ⟨0, fun _ => by simp⟩)
    (Algebra.ofId ℝ (SplitClPower 0))
    (by ext)
    (by
      apply CliffordAlgebra.hom_ext
      ext x
      cases x
      have h0 : (PUnit.unit : PUnit) = (0 : SplitCarrier 0) := rfl
      simp only [h0, map_zero])

/-- `ℝ ≃ₐ[ℝ] Matrix (Fin 1) (Fin 1) ℝ`. -/
def realEquivMat1 : ℝ ≃ₐ[ℝ] Matrix (Fin 1) (Fin 1) ℝ :=
  AlgEquiv.ofBijective (Algebra.ofId ℝ (Matrix (Fin 1) (Fin 1) ℝ))
    ⟨fun a b h => by
      have h00 := congrFun (congrFun h 0) 0
      simpa [Algebra.algebraMap_eq_smul_one] using h00,
     fun M => ⟨M 0 0, by
      ext i j
      fin_cases i
      fin_cases j
      simp [Algebra.algebraMap_eq_smul_one]⟩⟩

/-- Indexing equivalence `Fin (2 ^ n) × Fin 2 ≃ Fin (2 ^ (n + 1))`. -/
def finPowProd2Equiv (n : ℕ) : Fin (2 ^ n) × Fin 2 ≃ Fin (2 ^ (n + 1)) :=
  finProdFinEquiv.trans (finCongr (by ring : 2 ^ n * 2 = 2 ^ (n + 1)))

/-! ## 3. General algebra isomorphism `⊗ᵍ^n Cl(1,1) ≃ₐ[ℝ] Mat_{2^n}(ℝ)` -/

/-- Inductive real algebra isomorphism `SplitClPower n ≃ₐ[ℝ] Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ`. -/
def splitClPowerEquivMat :
    (n : ℕ) → SplitClPower n ≃ₐ[ℝ] Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ
  | 0 => clZeroPUnitEquivReal.trans realEquivMat1
  | n + 1 =>
    (splitCliffordEquivMatrix (splitQ n))
      |>.trans (AlgEquiv.mapMatrix (splitClPowerEquivMat n))
      |>.trans (matrixEquivTensor (Fin 2) ℝ (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ))
      |>.trans (Matrix.kroneckerAlgEquiv (Fin (2 ^ n)) (Fin 2) ℝ)
      |>.trans (Matrix.reindexAlgEquiv ℝ ℝ (finPowProd2Equiv n))

/-- Reindexing `BinaryWord n = (Fin n → Bool)` to `Fin (2 ^ n)`. -/
def binaryWordEquivFinPow (n : ℕ) : BinaryWord n ≃ Fin (2 ^ n) :=
  (Fintype.equivFin (BinaryWord n)).trans
    (finCongr (by simp [BinaryWord]))

/-- The `n`-fold split Clifford algebra is algebra-isomorphic to matrices indexed
directly by level-`n` binary words `BinaryWord n = Fin n → Bool`. -/
def splitClPowerEquivWordMat (n : ℕ) :
    SplitClPower n ≃ₐ[ℝ] Matrix (BinaryWord n) (BinaryWord n) ℝ :=
  (splitClPowerEquivMat n).trans
    (Matrix.reindexAlgEquiv ℝ ℝ (binaryWordEquivFinPow n).symm)

/-! ## 4. Diagonal Cartan Boolean projector subalgebra inside `⊗ᵍ^n Cl(1,1)` -/

/-- Diagonal Cartan projector in `Matrix (BinaryWord n) (BinaryWord n) ℝ`
for any Cantor cylinder-sector set `A : Set (BinaryWord n)`. -/
def wordMatCartanProj {n : ℕ} (A : Set (BinaryWord n)) :
    Matrix (BinaryWord n) (BinaryWord n) ℝ :=
  Matrix.diagonal (setIndicator ℝ A)

/-- The corresponding Boolean projector element inside `SplitClPower n ≅ ⊗ᵍ^n Cl(1,1)`. -/
def splitClCartanProj {n : ℕ} (A : Set (BinaryWord n)) : SplitClPower n :=
  (splitClPowerEquivWordMat n).symm (wordMatCartanProj A)

theorem wordMatCartanProj_inf {n : ℕ} (A B : Set (BinaryWord n)) :
    wordMatCartanProj (A ⊓ B) = wordMatCartanProj A * wordMatCartanProj B := by
  unfold wordMatCartanProj
  rw [setIndicator_inf_eq_mul, Matrix.diagonal_mul_diagonal]
  rfl

theorem wordMatCartanProj_sup {n : ℕ} (A B : Set (BinaryWord n)) :
    wordMatCartanProj (A ⊔ B) =
      wordMatCartanProj A + wordMatCartanProj B -
        wordMatCartanProj A * wordMatCartanProj B := by
  unfold wordMatCartanProj
  rw [setIndicator_sup_eq_add_sub_mul, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j <;> simp [h]

theorem wordMatCartanProj_compl {n : ℕ} (A : Set (BinaryWord n)) :
    wordMatCartanProj Aᶜ = 1 - wordMatCartanProj A := by
  unfold wordMatCartanProj
  rw [setIndicator_compl_eq_one_sub]
  ext i j
  by_cases h : i = j <;> simp [h]

theorem wordMatCartanProj_idempotent {n : ℕ} (A : Set (BinaryWord n)) :
    IsIdempotentElem (wordMatCartanProj A) := by
  rw [IsIdempotentElem, ← wordMatCartanProj_inf, inf_idem]

theorem wordMatCartanProj_comm {n : ℕ} (A B : Set (BinaryWord n)) :
    wordMatCartanProj A * wordMatCartanProj B =
      wordMatCartanProj B * wordMatCartanProj A := by
  rw [← wordMatCartanProj_inf, inf_comm, wordMatCartanProj_inf]

theorem wordMatCartanProj_injective {n : ℕ} :
    Function.Injective (wordMatCartanProj (n := n)) := by
  intro A B h
  ext w
  have hw : wordMatCartanProj A w w = wordMatCartanProj B w w := by rw [h]
  simp only [wordMatCartanProj, Matrix.diagonal_apply_eq] at hw
  by_cases hA : w ∈ A <;> by_cases hB : w ∈ B <;> simp [setIndicator, hA, hB] at hw ⊢

/-- Meet in `Set (BinaryWord n)` maps to multiplication of Cartan projectors
inside `SplitClPower n ≅ ⊗ᵍ^n Cl(1,1)`. -/
theorem splitClCartanProj_inf {n : ℕ} (A B : Set (BinaryWord n)) :
    splitClCartanProj (A ⊓ B) = splitClCartanProj A * splitClCartanProj B := by
  unfold splitClCartanProj
  rw [wordMatCartanProj_inf, map_mul]

/-- Join in `Set (BinaryWord n)` maps to `e + f - e * f` inside `⊗ᵍ^n Cl(1,1)`. -/
theorem splitClCartanProj_sup {n : ℕ} (A B : Set (BinaryWord n)) :
    splitClCartanProj (A ⊔ B) =
      splitClCartanProj A + splitClCartanProj B -
        splitClCartanProj A * splitClCartanProj B := by
  unfold splitClCartanProj
  rw [wordMatCartanProj_sup, map_sub, map_add, map_mul]

/-- Complement maps to `1 - e` inside `⊗ᵍ^n Cl(1,1)`. -/
theorem splitClCartanProj_compl {n : ℕ} (A : Set (BinaryWord n)) :
    splitClCartanProj Aᶜ = 1 - splitClCartanProj A := by
  unfold splitClCartanProj
  rw [wordMatCartanProj_compl, map_sub, map_one]

/-- Every Cartan projector inside `⊗ᵍ^n Cl(1,1)` is idempotent. -/
theorem splitClCartanProj_idempotent {n : ℕ} (A : Set (BinaryWord n)) :
    IsIdempotentElem (splitClCartanProj A) := by
  rw [IsIdempotentElem, ← splitClCartanProj_inf, inf_idem]

/-- All Cartan projectors inside `⊗ᵍ^n Cl(1,1)` pairwise commute. -/
theorem splitClCartanProj_comm {n : ℕ} (A B : Set (BinaryWord n)) :
    splitClCartanProj A * splitClCartanProj B =
      splitClCartanProj B * splitClCartanProj A := by
  rw [← splitClCartanProj_inf, inf_comm, splitClCartanProj_inf]

/-- The Cartan Boolean embedding `Set (BinaryWord n) → SplitClPower n` is injective. -/
theorem splitClCartanProj_injective {n : ℕ} :
    Function.Injective (splitClCartanProj (n := n)) :=
  (splitClPowerEquivWordMat n).symm.injective.comp wordMatCartanProj_injective

/-- Concrete upper-triangular elementary `2 × 2` real matrix. -/
def matE01 : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![0, 1], ![0, 0]]

/-- Concrete lower-triangular elementary `2 × 2` real matrix. -/
def matE10 : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![0, 0], ![1, 0]]

/-- Concrete upper-triangular elementary element in `SplitClPower 1 ≅ Cl(1,1) ≅ Mat₂(ℝ)`. -/
def splitClE01 : SplitClPower 1 :=
  (splitClPowerEquivMat 1).symm matE01

/-- Concrete lower-triangular elementary element in `SplitClPower 1 ≅ Cl(1,1) ≅ Mat₂(ℝ)`. -/
def splitClE10 : SplitClPower 1 :=
  (splitClPowerEquivMat 1).symm matE10

/-- Explicit non-commutativity witness in `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem mat2_noncomm_witness :
    matE01 * matE10 ≠ matE10 * matE01 := by
  intro hmat
  have h00 := congrFun (congrFun hmat 0) 0
  norm_num [matE01, matE10, Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem splitClE01_mul_splitClE10_ne :
    (splitClE01 : CliffordAlgebra (splitQ 1)) * (splitClE10 : CliffordAlgebra (splitQ 1)) ≠
      (splitClE10 : CliffordAlgebra (splitQ 1)) * (splitClE01 : CliffordAlgebra (splitQ 1)) := by
  intro h
  apply mat2_noncomm_witness
  have h' := congrArg (splitClPowerEquivMat 1) h
  simpa [splitClE01, splitClE10, map_mul] using h'

/-- Explicit non-commutativity witness in `Matrix (BinaryWord 1) (BinaryWord 1) ℝ`. -/
theorem wordMat_one_noncomm :
    ((splitClPowerEquivWordMat 1 splitClE01 : Matrix (BinaryWord 1) (BinaryWord 1) ℝ) *
        (splitClPowerEquivWordMat 1 splitClE10 : Matrix (BinaryWord 1) (BinaryWord 1) ℝ)) ≠
      ((splitClPowerEquivWordMat 1 splitClE10 : Matrix (BinaryWord 1) (BinaryWord 1) ℝ) *
        (splitClPowerEquivWordMat 1 splitClE01 : Matrix (BinaryWord 1) (BinaryWord 1) ℝ)) := by
  intro h
  apply splitClE01_mul_splitClE10_ne
  apply (splitClPowerEquivWordMat 1).injective
  simpa [map_mul] using h

theorem splitClPower_one_noncomm :
    ∃ a b : SplitClPower 1, a * b ≠ b * a :=
  ⟨splitClE01, splitClE10, splitClE01_mul_splitClE10_ne⟩

end InfoGeometry.Clifford.SplitCl11GradedTensorTower
