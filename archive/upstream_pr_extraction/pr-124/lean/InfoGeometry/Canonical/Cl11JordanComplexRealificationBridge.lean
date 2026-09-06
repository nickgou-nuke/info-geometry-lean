import InfoGeometry.Clifford.Cl3ComplexMatrixProduct
import InfoGeometry.Quantum.RealKCategory
import InfoGeometry.Quantum.MobiusSL2CRealification
import Mathlib.Tactic

/-!
# Realification of the complex two-by-two matrix stage

This is the finite coefficient bridge used before any analytic Fock
realization.  It records the real matrix representation of `M₂(ℂ)` and its
multiplicative and Jordan-product laws.  No completion or colimit is added.
-/

namespace InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge

open InfoGeometry.Clifford.Cl3ComplexMatrixProduct
open InfoGeometry.Quantum.RealKCategory
open InfoGeometry.Quantum.MobiusSL2CRealification

abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev Mat4R := Matrix (Fin 4) (Fin 4) ℝ
abbrev Block4R := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ

noncomputable def pairBlockComplexRealEquiv :
    (Fin 2 → ℂ) ≃ₗ[ℝ] (Fin 2 × Fin 2 → ℝ) where
  toFun z := fun i => if i.1 = 0 then (z i.2).re else (z i.2).im
  invFun x := fun i => ⟨x (0, i), x (1, i)⟩
  left_inv z := by
    funext i
    apply Complex.ext
    · simp
    · simp
  right_inv x := by
    funext i
    rcases i with ⟨i₁, i₂⟩
    fin_cases i₁ <;> simp
  map_add' z w := by
    funext i
    rcases i with ⟨i₁, i₂⟩
    fin_cases i₁ <;> simp
  map_smul' r z := by
    funext i
    rcases i with ⟨i₁, i₂⟩
    fin_cases i₁ <;> simp [smul_eq_mul]

@[simp] theorem pairBlockComplexRealEquiv_apply
    (z : Fin 2 → ℂ) (i : Fin 2 × Fin 2) :
    pairBlockComplexRealEquiv z i =
      if i.1 = 0 then (z i.2).re else (z i.2).im := rfl

@[simp] theorem pairBlockComplexRealEquiv_symm_apply
    (x : Fin 2 × Fin 2 → ℝ) (i : Fin 2) :
    pairBlockComplexRealEquiv.symm x i =
      ⟨x (0, i), x (1, i)⟩ := rfl

theorem pairBlockComplexRealEquiv_smul
    (z : ℂ) (v : Fin 2 → ℂ) :
    pairBlockComplexRealEquiv (z • v) =
      z.re • pairBlockComplexRealEquiv v +
        z.im • pairBlockComplexRealEquiv (Complex.I • v) := by
  funext i
  rcases i with ⟨i₁, i₂⟩
  fin_cases i₁ <;>
    simp [pairBlockComplexRealEquiv, Complex.mul_re, Complex.mul_im,
      Complex.I_mul, smul_eq_mul] <;> ring

def blockRealify (A : Mat2C) : Block4R := fun i j =>
  match i.1, j.1 with
  | 0, 0 => (A i.2 j.2).re
  | 0, 1 => -(A i.2 j.2).im
  | 1, 0 => (A i.2 j.2).im
  | 1, 1 => (A i.2 j.2).re

noncomputable def reindexBlock : Block4R ≃ₐ[ℝ] Mat4R :=
  Matrix.reindexAlgEquiv ℝ ℝ finProdFinEquiv

noncomputable def realify (A : Mat2C) : Mat4R :=
  reindexBlock (blockRealify A)

@[simp] theorem realify_apply (A : Mat2C) (i j : Fin 4) :
    realify A i j =
      blockRealify A (finProdFinEquiv.symm i) (finProdFinEquiv.symm j) := rfl

theorem blockRealify_mul (A B : Mat2C) :
    blockRealify (A * B) = blockRealify A * blockRealify B := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases j₁ <;> fin_cases i₂ <;> fin_cases j₂ <;>
    simp [blockRealify, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem realify_mul (A B : Mat2C) :
    realify (A * B) = realify A * realify B := by
  change reindexBlock (blockRealify (A * B)) =
    reindexBlock (blockRealify A) * reindexBlock (blockRealify B)
  rw [blockRealify_mul]
  exact (reindexBlock.map_mul _ _)

theorem realify_add (A B : Mat2C) :
    realify (A + B) = realify A + realify B := by
  change reindexBlock (blockRealify (A + B)) =
    reindexBlock (blockRealify A) + reindexBlock (blockRealify B)
  rw [show blockRealify (A + B) = blockRealify A + blockRealify B by
    ext i j
    rcases i with ⟨i₁, i₂⟩
    rcases j with ⟨j₁, j₂⟩
    fin_cases i₁ <;> fin_cases j₁ <;> simp [blockRealify] <;> ring]
  exact reindexBlock.map_add _ _

theorem blockRealify_one :
    blockRealify (1 : Mat2C) = (1 : Block4R) := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases j₁ <;>
    fin_cases i₂ <;> fin_cases j₂ <;>
    simp [blockRealify, Matrix.one_apply]

theorem realify_one : realify (1 : Mat2C) = (1 : Mat4R) := by
  change reindexBlock (blockRealify (1 : Mat2C)) = 1
  rw [blockRealify_one]
  exact reindexBlock.map_one

noncomputable def realifyRingHom : Mat2C →+* Mat4R where
  toFun := realify
  map_one' := realify_one
  map_mul' := realify_mul
  map_zero' := by
    change reindexBlock (blockRealify 0) = 0
    rw [show blockRealify (0 : Mat2C) = 0 by
      ext i j
      rcases i with ⟨i₁, i₂⟩
      rcases j with ⟨j₁, j₂⟩
      fin_cases i₁ <;> fin_cases j₁ <;> simp [blockRealify]]
    exact reindexBlock.map_zero
  map_add' A B := by
    change reindexBlock (blockRealify (A + B)) =
      reindexBlock (blockRealify A) + reindexBlock (blockRealify B)
    rw [show blockRealify (A + B) = blockRealify A + blockRealify B by
    ext i j
    rcases i with ⟨i₁, i₂⟩
    rcases j with ⟨j₁, j₂⟩
    fin_cases i₁ <;> fin_cases j₁ <;> simp [blockRealify] <;> ring]
    exact reindexBlock.map_add _ _

@[simp] theorem realifyRingHom_apply (A : Mat2C) :
    realifyRingHom A = realify A := rfl

theorem realify_injective : Function.Injective realify := by
  intro A B h
  have hblock : blockRealify A = blockRealify B := by
    apply reindexBlock.injective
    exact h
  ext i j
  apply Complex.ext
  · simpa [blockRealify] using
      congrFun (congrFun hblock (0, i)) (0, j)
  · simpa [blockRealify] using
      congrFun (congrFun hblock (1, i)) (0, j)

noncomputable def jordanProduct2 (A B : Mat2C) : Mat2C :=
  (1 / 2 : ℂ) • (A * B + B * A)

noncomputable def jordanProduct4 (A B : Mat4R) : Mat4R :=
  (1 / 2 : ℝ) • (A * B + B * A)

theorem realify_real_smul (r : ℝ) (A : Mat2C) :
    realify ((r : ℂ) • A) = r • realify A := by
  change reindexBlock (blockRealify ((r : ℂ) • A)) =
    r • reindexBlock (blockRealify A)
  rw [show blockRealify ((r : ℂ) • A) = r • blockRealify A by
    ext i j
    rcases i with ⟨i₁, i₂⟩
    rcases j with ⟨j₁, j₂⟩
    fin_cases i₁ <;> fin_cases j₁ <;>
      simp [blockRealify, Matrix.smul_apply, Complex.ofReal_re,
        Complex.ofReal_im]]
  exact reindexBlock.toLinearEquiv.map_smul r (blockRealify A)

theorem realify_jordanProduct (A B : Mat2C) :
    realify (jordanProduct2 A B) =
      jordanProduct4 (realify A) (realify B) := by
  unfold jordanProduct2 jordanProduct4
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [hhalf, realify_real_smul, realify_add, realify_mul, realify_mul]

theorem realify_commutator (A B : Mat2C) :
    realify (A * B - B * A) =
      realify A * realify B - realify B * realify A := by
  calc
    realify (A * B - B * A) =
        realify (A * B) - realify (B * A) :=
      realifyRingHom.map_sub _ _
    _ = realify A * realify B - realify B * realify A := by
      rw [realify_mul, realify_mul]

theorem jordanProduct2_add_half_commutator (A B : Mat2C) :
    jordanProduct2 A B + (1 / 2 : ℂ) • (A * B - B * A) = A * B := by
  unfold jordanProduct2
  module

theorem jordanProduct4_add_half_commutator (A B : Mat4R) :
    jordanProduct4 A B + (1 / 2 : ℝ) • (A * B - B * A) = A * B := by
  unfold jordanProduct4
  module

noncomputable def complexStructure : Mat4R :=
  realify ((Complex.I : ℂ) • (1 : Mat2C))

theorem complexStructure_sq :
    complexStructure * complexStructure = -(1 : Mat4R) := by
  change realify ((Complex.I : ℂ) • (1 : Mat2C)) *
      realify ((Complex.I : ℂ) • (1 : Mat2C)) = -(1 : Mat4R)
  rw [← realify_mul]
  have h : ((Complex.I : ℂ) • (1 : Mat2C)) *
      ((Complex.I : ℂ) • (1 : Mat2C)) = -(1 : Mat2C) := by
    rw [smul_mul_smul]
    simp [Complex.I_mul_I]
  rw [h]
  have hneg : realify (-(1 : Mat2C)) = -(1 : Mat4R) := by
    calc
      realify (-(1 : Mat2C)) = -realify (1 : Mat2C) :=
        realifyRingHom.map_neg (1 : Mat2C)
      _ = -(1 : Mat4R) := by rw [realify_one]
  exact hneg

theorem realify_commutes_complexStructure (A : Mat2C) :
    realify A * complexStructure = complexStructure * realify A := by
  change realify A * realify ((Complex.I : ℂ) • (1 : Mat2C)) =
    realify ((Complex.I : ℂ) • (1 : Mat2C)) * realify A
  rw [← realify_mul, ← realify_mul]
  congr 1
  simp [Matrix.mul_apply, Fin.sum_univ_two]

def complexStructureCommutant : Set Mat4R :=
  {T | T * complexStructure = complexStructure * T}

theorem realify_range_subset_complexStructureCommutant :
    Set.range realify ⊆ complexStructureCommutant := by
  rintro T ⟨A, rfl⟩
  exact realify_commutes_complexStructure A

abbrev RealVec4 := Fin 4 → ℝ

noncomputable def complexVectorRealEquiv4 : (Fin 2 → ℂ) ≃ₗ[ℝ] RealVec4 :=
  complexVectorRealEquiv.trans
    (EuclideanSpace.equiv (Fin 4) ℝ).toLinearEquiv

/- `realify` uses the block order `(re z₀, re z₁, im z₀, im z₁)`,
whereas the existing vector equivalence uses `(re z₀, im z₀, re z₁, im z₁)`. -/
noncomputable def swap12 : RealVec4 ≃ₗ[ℝ] RealVec4 :=
  LinearEquiv.ofLinear
    { toFun := fun x => ![x 0, x 2, x 1, x 3]
      map_add' := by
        intro x y
        funext i
        fin_cases i <;> simp
      map_smul' := by
        intro c x
        funext i
        fin_cases i <;> simp }
    { toFun := fun x => ![x 0, x 2, x 1, x 3]
      map_add' := by
        intro x y
        funext i
        fin_cases i <;> simp
      map_smul' := by
        intro c x
        funext i
        fin_cases i <;> simp }
    (by ext x i; fin_cases i <;> simp)
    (by ext x i; fin_cases i <;> simp)

noncomputable def alignedComplexVectorRealEquiv :
    (Fin 2 → ℂ) ≃ₗ[ℝ] RealVec4 :=
  complexVectorRealEquiv4.trans swap12

@[simp] theorem alignedComplexVectorRealEquiv_apply (z : Fin 2 → ℂ) :
    alignedComplexVectorRealEquiv z =
      ![(z 0).re, (z 1).re, (z 0).im, (z 1).im] := by
  ext i
  fin_cases i <;>
    simp [alignedComplexVectorRealEquiv, swap12,
      complexVectorRealEquiv_apply, complexVectorRealEquiv4]

@[simp] theorem alignedComplexVectorRealEquiv_symm_apply (x : RealVec4) :
    alignedComplexVectorRealEquiv.symm x =
      ![x 0 + x 2 * Complex.I, x 1 + x 3 * Complex.I] := by
  ext i
  fin_cases i <;>
    simp [alignedComplexVectorRealEquiv, swap12,
      complexVectorRealEquiv_symm_apply, complexVectorRealEquiv4]

noncomputable def complexStructureLinear : RealVec4 →ₗ[ℝ] RealVec4 :=
  Matrix.toLin' complexStructure

theorem complexStructure_matrix :
    complexStructure =
      !![0, 0, -1, 0; 0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.divNat, Fin.modNat, complexStructure, realify,
      reindexBlock, Matrix.reindex, blockRealify, finProdFinEquiv,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.kronecker_apply]

theorem alignedComplexVectorRealEquiv_complexI (z : Fin 2 → ℂ) :
    complexStructureLinear (alignedComplexVectorRealEquiv z) =
      alignedComplexVectorRealEquiv ((Complex.I : ℂ) • z) := by
  unfold complexStructureLinear
  rw [complexStructure_matrix]
  ext i
  fin_cases i <;>
    simp [alignedComplexVectorRealEquiv_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, Complex.mul_re, Complex.mul_im]

theorem complexStructureLinear_sq :
    complexStructureLinear.comp complexStructureLinear =
      -(LinearMap.id : RealVec4 →ₗ[ℝ] RealVec4) := by
  have hcomp :
      (Matrix.toLin' complexStructure).comp (Matrix.toLin' complexStructure) =
        Matrix.toLin' (-(1 : Mat4R)) := by
    rw [← Matrix.toLin'_mul, complexStructure_sq]
  simpa [complexStructureLinear] using hcomp

noncomputable def complexStructureRealKVect : RealKVect where
  V := RealVec4
  K := complexStructureLinear
  K_sq := complexStructureLinear_sq

noncomputable def alignedComplexVectorRealEquivComplex :
    (Fin 2 → ℂ) ≃ₗ[ℂ] complexStructureRealKVect.asComplexModule := by
  refine
    { toFun := alignedComplexVectorRealEquiv
      invFun := alignedComplexVectorRealEquiv.symm
      left_inv := fun x => alignedComplexVectorRealEquiv.left_inv x
      right_inv := fun x => alignedComplexVectorRealEquiv.right_inv x
      map_add' := fun x y => alignedComplexVectorRealEquiv.map_add x y
      map_smul' := ?_ }
  intro z x
  rcases z with ⟨a, b⟩
  change alignedComplexVectorRealEquiv (({ re := a, im := b } : ℂ) • x) =
    RealKVect.complexSMul complexStructureRealKVect { re := a, im := b }
      (alignedComplexVectorRealEquiv x)
  rw [show ({ re := a, im := b } : ℂ) = a + b * Complex.I by
    apply Complex.ext <;> simp]
  rw [add_smul, mul_smul]
  simp [RealKVect.complexSMul]
  ext i
  fin_cases i <;>
    simp [alignedComplexVectorRealEquiv_apply, complexStructureRealKVect,
      complexStructureLinear, complexStructure_matrix, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four, Complex.mul_re,
      Complex.mul_im]

theorem realMatrix_commuting_with_J_is_complexLinear
    (T : Mat4R) (hT : T * complexStructure = complexStructure * T) :
    ∃ f : complexStructureRealKVect ⟶ complexStructureRealKVect,
      f.hom = Matrix.toLin' T := by
  let f : complexStructureRealKVect ⟶ complexStructureRealKVect :=
    { hom := Matrix.toLin' T
      comm := by
        have hcomp :
            (Matrix.toLin' T).comp (Matrix.toLin' complexStructure) =
              (Matrix.toLin' complexStructure).comp (Matrix.toLin' T) := by
          rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hT]
        simpa [complexStructureLinear] using hcomp }
  exact ⟨f, rfl⟩

noncomputable def complexLinearMapOfCommuting
    (T : Mat4R) (hT : T * complexStructure = complexStructure * T) :
    complexStructureRealKVect.asComplexModule ⟶
      complexStructureRealKVect.asComplexModule :=
  (realMatrix_commuting_with_J_is_complexLinear T hT).choose.toComplexLinear

/- The complex-linear map above can be transported back to the standard
   coordinate model `Fin 2 → ℂ` without making a new scalar action. -/
noncomputable def standardComplexLinearMapOfCommuting
    (T : Mat4R) (hT : T * complexStructure = complexStructure * T) :
    (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) :=
  alignedComplexVectorRealEquivComplex.symm.toLinearMap.comp
    ((complexLinearMapOfCommuting T hT).hom.comp
      alignedComplexVectorRealEquivComplex.toLinearMap
      )

noncomputable def complexMatrixOfCommuting
    (T : Mat4R) (hT : T * complexStructure = complexStructure * T) : Mat2C :=
  LinearMap.toMatrix (Pi.basisFun ℂ (Fin 2)) (Pi.basisFun ℂ (Fin 2))
    (standardComplexLinearMapOfCommuting T hT)

set_option maxHeartbeats 1000000 in
theorem complexMatrixOfCommuting_toLin
    (T : Mat4R) (hT : T * complexStructure = complexStructure * T) :
    Matrix.toLin' (complexMatrixOfCommuting T hT) =
      standardComplexLinearMapOfCommuting T hT := by
  apply (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℂ (Fin 2))).injective
  simp [complexMatrixOfCommuting]

noncomputable def realMapOfComplexMatrix (A : Mat2C) :
    RealVec4 →ₗ[ℝ] RealVec4 :=
  alignedComplexVectorRealEquiv.toLinearMap.comp
    ((LinearMap.restrictScalars ℝ (Matrix.toLin' A)).comp
      alignedComplexVectorRealEquiv.symm.toLinearMap)

set_option maxHeartbeats 1000000 in
theorem realMapOfComplexMatrix_eq_realify (A : Mat2C) :
    realMapOfComplexMatrix A = Matrix.toLin' (realify A) := by
  ext x i
  fin_cases x <;> fin_cases i <;>
    simp [realMapOfComplexMatrix, alignedComplexVectorRealEquiv_apply,
      alignedComplexVectorRealEquiv_symm_apply, Matrix.toLin'_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, Fin.sum_univ_four, Fin.divNat,
      Fin.modNat, realify_apply, blockRealify, finProdFinEquiv,
      Matrix.reindex, Complex.mul_re, Complex.mul_im] <;>
    ring

theorem standardComplexLinearMapOfCommuting_commuting_square
    (T : Mat4R) (hT : T * complexStructure = complexStructure * T) :
    (alignedComplexVectorRealEquivComplex.toLinearMap).comp
        (standardComplexLinearMapOfCommuting T hT) =
      (complexLinearMapOfCommuting T hT).hom.comp
        alignedComplexVectorRealEquivComplex.toLinearMap := by
  ext z
  simp [standardComplexLinearMapOfCommuting]

theorem standardComplexLinearMapOfCommuting_apply
    (T : Mat4R) (hT : T * complexStructure = complexStructure * T)
    (z : Fin 2 → ℂ) :
    alignedComplexVectorRealEquiv
        (standardComplexLinearMapOfCommuting T hT z) =
      Matrix.toLin' T (alignedComplexVectorRealEquiv z) := by
  have hsq := standardComplexLinearMapOfCommuting_commuting_square T hT
  have hz := congrArg (fun f => f z) hsq
  simp only [LinearMap.comp_apply] at hz
  change alignedComplexVectorRealEquiv
      (standardComplexLinearMapOfCommuting T hT z) =
    (complexLinearMapOfCommuting T hT).hom
      (alignedComplexVectorRealEquiv z) at hz
  have hf (x : RealVec4) :
      (complexLinearMapOfCommuting T hT).hom x = Matrix.toLin' T x := by
    change (realMatrix_commuting_with_J_is_complexLinear T hT).choose.hom x = _
    rw [(realMatrix_commuting_with_J_is_complexLinear T hT).choose_spec]
    rfl
  rw [hf] at hz
  exact hz

set_option maxHeartbeats 1000000 in
theorem realMapOfComplexMatrix_ofCommuting
    (T : Mat4R) (hT : T * complexStructure = complexStructure * T) :
    realMapOfComplexMatrix (complexMatrixOfCommuting T hT) =
      Matrix.toLin' T := by
  apply LinearMap.ext
  intro x
  let z := alignedComplexVectorRealEquiv.symm x
  have hz := standardComplexLinearMapOfCommuting_apply T hT z
  change alignedComplexVectorRealEquiv
      (Matrix.toLin' (complexMatrixOfCommuting T hT)
        (alignedComplexVectorRealEquiv.symm x)) =
    Matrix.toLin' T x
  rw [complexMatrixOfCommuting_toLin T hT]
  simpa [standardComplexLinearMapOfCommuting, z] using hz

set_option maxHeartbeats 1000000 in
theorem complexMatrixOfCommuting_readback
    (T : Mat4R) (hT : T * complexStructure = complexStructure * T) :
    realify (complexMatrixOfCommuting T hT) = T := by
  apply (Matrix.toLin' : Mat4R ≃ₗ[ℝ] _).injective
  rw [← realMapOfComplexMatrix_eq_realify]
  exact realMapOfComplexMatrix_ofCommuting T hT

theorem complexStructureCommutant_eq_range_realify :
    complexStructureCommutant = Set.range realify := by
  apply Set.Subset.antisymm
  · intro T hT
    exact ⟨complexMatrixOfCommuting T hT,
      complexMatrixOfCommuting_readback T hT⟩
  · exact realify_range_subset_complexStructureCommutant

/-! The same finite commutant identification with the API orientation used by
the realification callers.  The substantive inclusions are proved above; this
is only their symmetric presentation. -/
theorem realify_range_eq_complexStructureCommutant :
    Set.range realify = complexStructureCommutant := by
  exact complexStructureCommutant_eq_range_realify.symm

end InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge
