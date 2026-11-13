/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl11GradedUnrolling
import InfoGeometry.Clifford.SplitCliffordMatrixEquiv
import Mathlib.Data.Matrix.Composition
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Native recursive unrolling with the Clifford head on the left

The input matrix indices are binary words, with the first bit naming the
outermost two-by-two block. Each recursive step is the native Clifford
orthogonal-sum equivalence followed by the original-basis graded matrix
equivalence. The source is always the native split Clifford quotient.

This left-head coordinate choice is constructed directly. It is not silently
identified with the pre-existing spinor representation's right-head indexing.
-/

noncomputable section

open scoped Matrix Matrix.Module TensorProduct

namespace InfoGeometry.Clifford.Cl11RecursiveUnrolling

open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11GradedTensorMorita
open InfoGeometry.Clifford.Cl11GradedUnrolling
open InfoGeometry.Clifford.SplitCliffordMatrixEquiv

abbrev Bits (n : ℕ) := Fin n → Fin 2
abbrev RealMatrix (n : ℕ) := Matrix (Bits n) (Bits n) ℝ

/-- The actual recursive quadratic form with its head written as `q11`. -/
def headIsometry (n : ℕ) :
    (Qsplit (n + 1)).IsometryEquiv (q11.prod (Qsplit n)) where
  toLinearEquiv := LinearEquiv.refl ℝ (SplitSpace (n + 1))
  map_app' v := by
    change (q11.prod (Qsplit n)) v = (InfoGeometry.CliffordTower.Q11.prod (Qsplit n)) v
    rw [q11_eq_splitQ11]

/-- The native orthogonal-sum step, without a matrix surrogate carrier. -/
def headTensorEquiv (n : ℕ) :
    Clsplit (n + 1) ≃ₐ[ℝ]
      (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n)) :=
  (CliffordAlgebra.equivOfIsometry (headIsometry n)).trans CliffordAlgebra.prodEquiv

@[simp] theorem headTensorEquiv_ι (n : ℕ) (v : SplitSpace (n + 1)) :
    headTensorEquiv n (CliffordAlgebra.ι (Qsplit (n + 1)) v) =
      (CliffordAlgebra.ι q11 v.1 ᵍ⊗ₜ (1 : Clsplit n)) +
        ((1 : CliffordAlgebra q11) ᵍ⊗ₜ CliffordAlgebra.ι (Qsplit n) v.2) := by
  change CliffordAlgebra.ofProd q11 (Qsplit n)
    (CliffordAlgebra.map (headIsometry n).toIsometry
      (CliffordAlgebra.ι (Qsplit (n + 1)) v)) = _
  rw [CliffordAlgebra.map_apply_ι]
  simpa [headIsometry] using
    (CliffordAlgebra.ofProd_ι_mk (Q₁ := q11) (Q₂ := Qsplit n) v.1 v.2)

abbrev nativeParity (n : ℕ) : Clsplit n ≃ₐ[ℝ] Clsplit n :=
  CliffordAlgebra.involuteEquiv

theorem nativeParity_even (n : ℕ) {a : Clsplit n}
    (ha : a ∈ CliffordAlgebra.evenOdd (Qsplit n) 0) : nativeParity n a = a :=
  CliffordAlgebra.involute_eq_of_mem_even ha

theorem nativeParity_odd (n : ℕ) {a : Clsplit n}
    (ha : a ∈ CliffordAlgebra.evenOdd (Qsplit n) 1) : nativeParity n a = -a :=
  CliffordAlgebra.involute_eq_of_mem_odd ha

/-- The actual one-head algebra equivalence, with the native tail grading. -/
def nativeStepEquiv (n : ℕ) :
    Clsplit (n + 1) ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) (Clsplit n) :=
  (headTensorEquiv n).trans
    (tensorMatrixEquivOriginal (nativeParity n) (CliffordAlgebra.evenOdd (Qsplit n))
      (nativeParity_even n) (nativeParity_odd n))

/-- Flatten two-by-two blocks with the outer bit first. -/
def flatten (B : Type*) [Ring B] [Algebra ℝ B] (n : ℕ) :
    Matrix (Fin 2) (Fin 2) (Matrix (Bits n) (Bits n) B) ≃ₐ[ℝ]
      Matrix (Bits (n + 1)) (Bits (n + 1)) B :=
  (Matrix.compAlgEquiv (Fin 2) (Bits n) B ℝ).trans
    (Matrix.reindexAlgEquiv ℝ B (Fin.consEquiv fun _ : Fin (n + 1) => Fin 2))

@[simp] theorem flatten_apply (B : Type*) [Ring B] [Algebra ℝ B] (n : ℕ)
    (M : Matrix (Fin 2) (Fin 2) (Matrix (Bits n) (Bits n) B))
    (i j : Bits (n + 1)) :
    flatten B n M i j = M (i 0) (j 0) (Fin.tail i) (Fin.tail j) := rfl

@[simp] theorem flatten_symm_apply (B : Type*) [Ring B] [Algebra ℝ B] (n : ℕ)
    (M : Matrix (Bits (n + 1)) (Bits (n + 1)) B)
    (a b : Fin 2) (i j : Bits n) :
    (flatten B n).symm M a b i j = M (Fin.cons a i) (Fin.cons b j) := rfl

/-- Recursion through native graded tensor steps, with a real empty stage. -/
def leftMatrixEquiv : (n : ℕ) → Clsplit n ≃ₐ[ℝ] RealMatrix n
  | 0 =>
      (splitSpinorAlgEquiv 0).trans
        ((Matrix.uniqueAlgEquiv (m := Fin 1) (R := ℝ) (A := ℝ)).trans
          (Matrix.uniqueAlgEquiv (m := Bits 0) (R := ℝ) (A := ℝ)).symm)
  | n + 1 =>
      (nativeStepEquiv n).trans
        ((leftMatrixEquiv n).mapMatrix.trans (flatten ℝ n))

@[simp] theorem leftMatrixEquiv_succ (n : ℕ) (x : Clsplit (n + 1)) :
    leftMatrixEquiv (n + 1) x =
      flatten ℝ n ((nativeStepEquiv n x).map (leftMatrixEquiv n)) := rfl

def unrollNative (n : ℕ) : RealMatrix n ≃ₐ[ℝ] Clsplit n :=
  (leftMatrixEquiv n).symm

@[simp] theorem reconstruct_unrollNative (n : ℕ) (M : RealMatrix n) :
    leftMatrixEquiv n (unrollNative n M) = M :=
  (leftMatrixEquiv n).apply_symm_apply M

@[simp] theorem unrollNative_reconstruct (n : ℕ) (x : Clsplit n) :
    unrollNative n (leftMatrixEquiv n x) = x :=
  (leftMatrixEquiv n).symm_apply_apply x

theorem unrollNative_mul (n : ℕ) (M N : RealMatrix n) :
    unrollNative n (M * N) = unrollNative n M * unrollNative n N :=
  map_mul (unrollNative n) M N

/-- Independently transported native Clifford parity on the matrix carrier. -/
def matrixParity (n : ℕ) : RealMatrix n ≃ₐ[ℝ] RealMatrix n :=
  ((leftMatrixEquiv n).symm.trans (nativeParity n)).trans (leftMatrixEquiv n)

@[simp] theorem matrixParity_represented (n : ℕ) (x : Clsplit n) :
    matrixParity n (leftMatrixEquiv n x) = leftMatrixEquiv n (nativeParity n x) := by
  simp [matrixParity]

theorem matrixParity_involutive (n : ℕ) : Function.Involutive (matrixParity n) := by
  intro M
  simp [matrixParity, nativeParity, CliffordAlgebra.involute_involutive]

/-- The native orthogonal-sum equivalence has the independently specified
factorwise Clifford involution. -/
theorem headTensorEquiv_involute (n : ℕ) (x : Clsplit (n + 1)) :
    headTensorEquiv n (nativeParity (n + 1) x) =
      tensorParity (CliffordAlgebra.evenOdd (Qsplit n)) (nativeParity n)
        (nativeParity_even n) (nativeParity_odd n) (headTensorEquiv n x) := by
  have h :
      (headTensorEquiv n).toAlgHom.comp (nativeParity (n + 1)).toAlgHom =
        (tensorParity (CliffordAlgebra.evenOdd (Qsplit n)) (nativeParity n)
          (nativeParity_even n) (nativeParity_odd n)).toAlgHom.comp
            (headTensorEquiv n).toAlgHom := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    change headTensorEquiv n (CliffordAlgebra.involute
      (CliffordAlgebra.ι (Qsplit (n + 1)) v)) = _
    simp only [CliffordAlgebra.involute_ι, map_neg, headTensorEquiv_ι,
      AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, map_add,
      tensorParity_tmul, map_one]
    simp [nativeParity, GradedTensorProduct.tmul, TensorProduct.neg_tmul,
      TensorProduct.tmul_neg]
  exact AlgHom.congr_fun h x

/-- Native parity exchanges both matrix coordinates and applies tail parity. -/
theorem nativeStepEquiv_involute (n : ℕ) (x : Clsplit (n + 1)) :
    nativeStepEquiv n (nativeParity (n + 1) x) =
      !![nativeParity n (nativeStepEquiv n x 1 1),
         nativeParity n (nativeStepEquiv n x 1 0);
         nativeParity n (nativeStepEquiv n x 0 1),
         nativeParity n (nativeStepEquiv n x 0 0)] := by
  change tensorMatrixEquivOriginal (nativeParity n) _ _ _
    (headTensorEquiv n (nativeParity (n + 1) x)) = _
  rw [headTensorEquiv_involute, tensorMatrixEquivOriginal_parity]
  rfl

theorem matrixParity_succ (n : ℕ)
    (M : Matrix (Fin 2) (Fin 2) (RealMatrix n)) :
    matrixParity (n + 1) (flatten ℝ n M) =
      flatten ℝ n
        !![matrixParity n (M 1 1), matrixParity n (M 1 0);
           matrixParity n (M 0 1), matrixParity n (M 0 0)] := by
  have h : (leftMatrixEquiv (n + 1)).symm (flatten ℝ n M) =
      (nativeStepEquiv n).symm (M.map (unrollNative n)) := by
    apply (leftMatrixEquiv (n + 1)).injective
    simp [leftMatrixEquiv_succ, unrollNative, Matrix.map_map]
  change leftMatrixEquiv (n + 1)
    (nativeParity (n + 1) ((leftMatrixEquiv (n + 1)).symm (flatten ℝ n M))) = _
  rw [h, leftMatrixEquiv_succ, nativeStepEquiv_involute,
    AlgEquiv.apply_symm_apply]
  apply congrArg (flatten ℝ n)
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The explicitly recursive tensor power of the swap matrix `K`. -/
def gamma : (n : ℕ) → RealMatrix n
  | 0 => 1
  | n + 1 => flatten ℝ n !![0, gamma n; gamma n, 0]

theorem gamma_succ_apply (n : ℕ) (a b : Fin 2) (i j : Bits n) :
    gamma (n + 1) (Fin.cons a i) (Fin.cons b j) = J1 a b * gamma n i j := by
  fin_cases a <;> fin_cases b <;> simp [gamma, J1]

theorem gamma_sq (n : ℕ) : gamma n * gamma n = 1 := by
  induction n with
  | zero => simp [gamma]
  | succ n ih =>
      change flatten ℝ n _ * flatten ℝ n _ = 1
      rw [← map_mul]
      have h : (!![0, gamma n; gamma n, 0] :
          Matrix (Fin 2) (Fin 2) (RealMatrix n)) *
            !![0, gamma n; gamma n, 0] = 1 := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, ih]
      rw [h, map_one]

theorem gamma_conj_flatten (n : ℕ) (M : Matrix (Fin 2) (Fin 2) (RealMatrix n)) :
    gamma (n + 1) * flatten ℝ n M * gamma (n + 1) =
      flatten ℝ n
        !![gamma n * M 1 1 * gamma n, gamma n * M 1 0 * gamma n;
           gamma n * M 0 1 * gamma n, gamma n * M 0 0 * gamma n] := by
  change flatten ℝ n _ * flatten ℝ n M * flatten ℝ n _ = _
  rw [← map_mul, ← map_mul]
  apply congrArg (flatten ℝ n)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_assoc]

/-- The actual transported Clifford grading is exactly the matrix conjugation
used by the intake's recursive algorithm. -/
theorem matrixParity_eq_gamma_conj (n : ℕ) (M : RealMatrix n) :
    matrixParity n M = gamma n * M * gamma n := by
  induction n with
  | zero =>
      have hM : M = algebraMap ℝ (RealMatrix 0) (M default default) := by
        ext i j
        simp [Subsingleton.elim i default, Subsingleton.elim j default,
          Algebra.algebraMap_eq_smul_one]
      rw [hM, AlgEquiv.commutes]
      simp [gamma]
  | succ n ih =>
      obtain ⟨N, rfl⟩ := (flatten ℝ n).surjective M
      rw [matrixParity_succ, gamma_conj_flatten]
      simp only [ih]

/-- Unrolling commutes with the two parity projections. -/
theorem unrollNative_evenPart (n : ℕ) (M : RealMatrix n) :
    unrollNative n (evenPart (matrixParity n) M) =
      evenPart (nativeParity n) (unrollNative n M) := by
  simp [evenPart, matrixParity, unrollNative]

theorem unrollNative_oddPart (n : ℕ) (M : RealMatrix n) :
    unrollNative n (oddPart (matrixParity n) M) =
      oddPart (nativeParity n) (unrollNative n M) := by
  simp [oddPart, matrixParity, unrollNative]

/-- Applying the scalar inverse entrywise commutes with the corrected four
blocks, so the correction can be performed before recursing into each tail. -/
theorem unrollNative_correctedCoefficients (n : ℕ)
    (M : Matrix (Fin 2) (Fin 2) (RealMatrix n)) :
    correction (nativeParity n) (coefficients (M.map (unrollNative n))) =
      fun i => unrollNative n (correction (matrixParity n) (coefficients M) i) := by
  funext i
  fin_cases i <;> simp [correction, coefficients, evenPart, oddPart,
    matrixParity, unrollNative, map_smul]

/-- Exact left-peeling inverse, with four corrected matrix tails followed by
four recursive calls. The combination uses the actual native graded product. -/
theorem unrollNative_succ (n : ℕ) (M : RealMatrix (n + 1)) :
    unrollNative (n + 1) M =
      (headTensorEquiv n).symm
        (tensorExpansion (CliffordAlgebra.evenOdd (Qsplit n))
          (fun i => unrollNative n
            (correction (matrixParity n) (coefficients ((flatten ℝ n).symm M)) i))) := by
  change (headTensorEquiv n).symm
    ((tensorMatrixEquivOriginal (nativeParity n) (CliffordAlgebra.evenOdd (Qsplit n))
      (nativeParity_even n) (nativeParity_odd n)).symm
        (((flatten ℝ n).symm M).map (unrollNative n))) = _
  rw [tensorMatrixEquivOriginal_symm_apply, unrollNative_correctedCoefficients]

/-! ## One arbitrary coefficient algebra -/

universe u
variable (B : Type u) [Ring B] [Algebra ℝ B]

abbrev CoefficientMatrix (n : ℕ) := Matrix (Bits n) (Bits n) B

/-- Left multiplication by the single terminal coefficient, entrywise.
Its real linearity uses the central real scalar action, not commutativity of B. -/
def coefficientReadback (n : ℕ) (b : B) : RealMatrix n →ₗ[ℝ] CoefficientMatrix B n :=
  ((LinearMap.mulLeft ℝ b).comp (Algebra.ofId ℝ B).toLinearMap).mapMatrix

@[simp] theorem coefficientReadback_apply (n : ℕ) (b : B) (M : RealMatrix n)
    (i j : Bits n) :
    coefficientReadback B n b M i j = b * algebraMap ℝ B (M i j) := rfl

@[simp] theorem coefficientReadback_one (n : ℕ) (M : RealMatrix n) :
    coefficientReadback B n 1 M = M.map (algebraMap ℝ B) := by
  ext i j
  simp

theorem coefficientReadback_flatten (n : ℕ) (b : B)
    (M : Matrix (Fin 2) (Fin 2) (RealMatrix n)) :
    coefficientReadback B (n + 1) b (flatten ℝ n M) =
      flatten B n (M.map (coefficientReadback B n b)) := by
  ext i j
  rfl

/-- Extend the actual left-head equivalence by one terminal copy of B. -/
def leftCoefficientEquiv (n : ℕ) :
    (Clsplit n ⊗[ℝ] B) ≃ₐ[ℝ] CoefficientMatrix B n :=
  (Algebra.TensorProduct.congr (leftMatrixEquiv n) (AlgEquiv.refl : B ≃ₐ[ℝ] B)).trans
    ((Algebra.TensorProduct.comm ℝ (RealMatrix n) B).trans
      (matrixEquivTensor (Bits n) ℝ B).symm)

@[simp] theorem leftCoefficientEquiv_tmul (n : ℕ) (x : Clsplit n) (b : B) :
    leftCoefficientEquiv B n (x ⊗ₜ[ℝ] b) =
      coefficientReadback B n b (leftMatrixEquiv n x) := by
  ext i j
  simp [leftCoefficientEquiv, coefficientReadback_apply]

def unrollCoefficients (n : ℕ) :
    CoefficientMatrix B n ≃ₐ[ℝ] (Clsplit n ⊗[ℝ] B) :=
  (leftCoefficientEquiv B n).symm

@[simp] theorem reconstruct_unrollCoefficients (n : ℕ) (M : CoefficientMatrix B n) :
    leftCoefficientEquiv B n (unrollCoefficients B n M) = M :=
  (leftCoefficientEquiv B n).apply_symm_apply M

@[simp] theorem unrollCoefficients_reconstruct (n : ℕ) (x : Clsplit n ⊗[ℝ] B) :
    unrollCoefficients B n (leftCoefficientEquiv B n x) = x :=
  (leftCoefficientEquiv B n).symm_apply_apply x

theorem unrollCoefficients_mul (n : ℕ) (M N : CoefficientMatrix B n) :
    unrollCoefficients B n (M * N) =
      unrollCoefficients B n M * unrollCoefficients B n N :=
  map_mul (unrollCoefficients B n) M N

/-- Canonical Clifford parity acts trivially on the retained coefficient leg. -/
def coefficientParity (n : ℕ) : (Clsplit n ⊗[ℝ] B) ≃ₐ[ℝ] (Clsplit n ⊗[ℝ] B) :=
  Algebra.TensorProduct.congr (nativeParity n) (AlgEquiv.refl : B ≃ₐ[ℝ] B)

def coefficientMatrixParity (n : ℕ) : CoefficientMatrix B n ≃ₐ[ℝ] CoefficientMatrix B n :=
  ((leftCoefficientEquiv B n).symm.trans (coefficientParity B n)).trans
    (leftCoefficientEquiv B n)

@[simp] theorem coefficientMatrixParity_represented (n : ℕ) (z : Clsplit n ⊗[ℝ] B) :
    coefficientMatrixParity B n (leftCoefficientEquiv B n z) =
      leftCoefficientEquiv B n (coefficientParity B n z) := by
  simp [coefficientMatrixParity]

private def nativeGamma (n : ℕ) : Clsplit n := unrollNative n (gamma n)

private theorem nativeParity_eq_gamma_conj (n : ℕ) (x : Clsplit n) :
    nativeParity n x = nativeGamma n * x * nativeGamma n := by
  apply (leftMatrixEquiv n).injective
  rw [← matrixParity_represented, matrixParity_eq_gamma_conj]
  simp only [map_mul, nativeGamma, reconstruct_unrollNative]

private theorem coefficientParity_eq_gamma_conj (n : ℕ) (z : Clsplit n ⊗[ℝ] B) :
    coefficientParity B n z =
      (nativeGamma n ⊗ₜ[ℝ] (1 : B)) * z * (nativeGamma n ⊗ₜ[ℝ] (1 : B)) := by
  induction z using TensorProduct.inductionOn with
  | tmul x b =>
      simp only [coefficientParity, Algebra.TensorProduct.congr_apply,
        Algebra.TensorProduct.map_tmul,
        AlgEquiv.refl_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [nativeParity_eq_gamma_conj]
  | add x y hx hy => simp only [map_add, hx, hy, mul_add, add_mul]

/-- The full coefficient-algebra grading is the same known permutation-matrix
conjugation; the construction never imposes a grading on B. -/
theorem coefficientMatrixParity_eq_gamma_conj (n : ℕ) (M : CoefficientMatrix B n) :
    coefficientMatrixParity B n M =
      (gamma n).map (algebraMap ℝ B) * M * (gamma n).map (algebraMap ℝ B) := by
  change leftCoefficientEquiv B n
    (coefficientParity B n ((leftCoefficientEquiv B n).symm M)) = _
  rw [coefficientParity_eq_gamma_conj, map_mul, map_mul, AlgEquiv.apply_symm_apply]
  simp [leftCoefficientEquiv_tmul, nativeGamma, coefficientReadback_apply]

theorem coefficientMatrixParity_tmul (n : ℕ) (x : Clsplit n) (b : B) :
    coefficientMatrixParity B n
      (coefficientReadback B n b (leftMatrixEquiv n x)) =
        coefficientReadback B n b (leftMatrixEquiv n (nativeParity n x)) := by
  rw [← leftCoefficientEquiv_tmul, coefficientMatrixParity_represented]
  simp [coefficientParity]

/-- Consing a scalar Clifford head is a native linear map on the tail.
This map does not duplicate or multiply terminal B coefficients. -/
def consNative (n : ℕ) (a : CliffordAlgebra q11) : Clsplit n →ₗ[ℝ] Clsplit (n + 1) :=
  (headTensorEquiv n).symm.toLinearMap.comp
    ((GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11)
      (CliffordAlgebra.evenOdd (Qsplit n))).toLinearMap.comp
        (TensorProduct.mk ℝ (CliffordAlgebra q11) (Clsplit n) a))

@[simp] theorem consNative_apply (n : ℕ) (a : CliffordAlgebra q11) (x : Clsplit n) :
    consNative n a x = (headTensorEquiv n).symm (a ᵍ⊗ₜ x) := rfl

def consTensor (n : ℕ) (a : CliffordAlgebra q11) :
    (Clsplit n ⊗[ℝ] B) →ₗ[ℝ] (Clsplit (n + 1) ⊗[ℝ] B) :=
  TensorProduct.map (consNative n a) (LinearMap.id : B →ₗ[ℝ] B)

@[simp] theorem consTensor_tmul (n : ℕ) (a : CliffordAlgebra q11) (x : Clsplit n) (b : B) :
    consTensor B n a (x ⊗ₜ[ℝ] b) = consNative n a x ⊗ₜ[ℝ] b := rfl

theorem nativeStepEquiv_consNative (n : ℕ) (a : CliffordAlgebra q11) (x : Clsplit n) :
    nativeStepEquiv n (consNative n a x) =
      tensorMatrixEquivOriginal (nativeParity n) (CliffordAlgebra.evenOdd (Qsplit n))
        (nativeParity_even n) (nativeParity_odd n) (a ᵍ⊗ₜ x) := by
  simp [nativeStepEquiv, consNative_apply]

private def headBlock {A : Type*} [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (a : CliffordAlgebra q11) (x : A) : Matrix (Fin 2) (Fin 2) A :=
  !![cl11EquivMat a 0 0 • evenPart θ x + cl11EquivMat a 0 1 • oddPart θ x,
     cl11EquivMat a 0 0 • oddPart θ x + cl11EquivMat a 0 1 • evenPart θ x;
     cl11EquivMat a 1 0 • evenPart θ x + cl11EquivMat a 1 1 • oddPart θ x,
     cl11EquivMat a 1 0 • oddPart θ x + cl11EquivMat a 1 1 • evenPart θ x]

private theorem headBlock_add {A : Type*} [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (a : CliffordAlgebra q11) (x y : A) :
    headBlock θ a (x + y) = headBlock θ a x + headBlock θ a y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [headBlock, evenPart, oddPart, smul_add, smul_sub, add_sub_add_comm] <;> module

private theorem headBlock_natural {A C : Type*} [Ring A] [Algebra ℝ A]
    [Ring C] [Algebra ℝ C] (θ : A ≃ₐ[ℝ] A) (θ' : C ≃ₐ[ℝ] C)
    (f : A →ₗ[ℝ] C) (hf : ∀ x, f (θ x) = θ' (f x))
    (a : CliffordAlgebra q11) (x : A) :
    (headBlock θ a x).map f = headBlock θ' a (f x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [headBlock, evenPart, oddPart, hf]

/-- The coefficient extension respects the native head operation. -/
theorem leftCoefficientEquiv_consTensor (n : ℕ) (a : CliffordAlgebra q11)
    (z : Clsplit n ⊗[ℝ] B) :
    leftCoefficientEquiv B (n + 1) (consTensor B n a z) =
      flatten B n (headBlock (coefficientMatrixParity B n) a
        (leftCoefficientEquiv B n z)) := by
  induction z using TensorProduct.inductionOn with
  | tmul x b =>
      simp only [consTensor_tmul, leftCoefficientEquiv_tmul, leftMatrixEquiv_succ,
        nativeStepEquiv_consNative, coefficientReadback_flatten]
      rw [tensorMatrixEquivOriginal_tmul_entries]
      apply congrArg (flatten B n)
      change ((headBlock (nativeParity n) a x).map
        ((coefficientReadback B n b).comp (leftMatrixEquiv n).toLinearMap)) = _
      apply headBlock_natural
      intro y
      exact (coefficientMatrixParity_tmul B n y b).symm
  | add x y hx hy =>
      simp only [map_add, hx, hy, headBlock_add]

private theorem headBlock_basis_sum {A : Type*} [Ring A] [Algebra ℝ A]
    (θ : A ≃ₐ[ℝ] A) (c : Fin 4 → A) :
    headBlock θ 1 (c 0) + headBlock θ (CliffordAlgebra.ι q11 (1, 0)) (c 1) +
      headBlock θ J1_cl (c 2) + headBlock θ (CliffordAlgebra.ι q11 (0, 1)) (c 3) =
        synthesize (correction θ c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [headBlock, J1_cl, map_mul, cl11EquivMat_iota_pos,
      cl11EquivMat_iota_neg, Eplus_mul_Eminus, Eplus, Eminus, J1,
      synthesize, correction] <;> abel

theorem coefficientMatrixParity_involutive (n : ℕ) :
    Function.Involutive (coefficientMatrixParity B n) := by
  intro M
  obtain ⟨z, rfl⟩ := (leftCoefficientEquiv B n).surjective M
  rw [coefficientMatrixParity_represented, coefficientMatrixParity_represented]
  apply congrArg (leftCoefficientEquiv B n)
  induction z using TensorProduct.inductionOn with
  | tmul x b => simp [coefficientParity, nativeParity]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The empty chain retains exactly its single terminal B coefficient. -/
theorem unrollCoefficients_zero (M : CoefficientMatrix B 0) :
    unrollCoefficients B 0 M = (1 : Clsplit 0) ⊗ₜ[ℝ] M default default := by
  apply (leftCoefficientEquiv B 0).injective
  rw [reconstruct_unrollCoefficients, leftCoefficientEquiv_tmul, map_one]
  ext i j
  simp [coefficientReadback_apply, Subsingleton.elim i default,
    Subsingleton.elim j default]

/-- The displayed four-tail inverse from the intake, now at every depth and
over one arbitrary noncommutative real coefficient algebra. The tail parity
is identified with known `K`-matrix conjugation above. -/
theorem unrollCoefficients_succ (n : ℕ) (M : CoefficientMatrix B (n + 1)) :
    let V := correction (coefficientMatrixParity B n)
      (coefficients ((flatten B n).symm M))
    unrollCoefficients B (n + 1) M =
      consTensor B n (1 : CliffordAlgebra q11) (unrollCoefficients B n (V 0)) +
      consTensor B n (CliffordAlgebra.ι q11 (1, 0)) (unrollCoefficients B n (V 1)) +
      consTensor B n J1_cl (unrollCoefficients B n (V 2)) +
      consTensor B n (CliffordAlgebra.ι q11 (0, 1)) (unrollCoefficients B n (V 3)) := by
  dsimp only
  apply (leftCoefficientEquiv B (n + 1)).injective
  simp only [reconstruct_unrollCoefficients, map_add, leftCoefficientEquiv_consTensor]
  rw [← map_add, ← map_add, ← map_add, headBlock_basis_sum,
    correction_involutive (coefficientMatrixParity B n)
      (coefficientMatrixParity_involutive B n),
    synthesize_coefficients, AlgEquiv.apply_symm_apply]

/-- Concrete binary indexing: the Clifford head is the most significant bit. -/
def bitsFinEquiv : (n : ℕ) → Bits n ≃ Fin (2 ^ n)
  | 0 =>
      { toFun := fun _ => 0
        invFun := fun _ i => Fin.elim0 i
        left_inv := fun x => by funext i; exact Fin.elim0 i
        right_inv := fun i => by fin_cases i; rfl }
  | n + 1 =>
      (Fin.consEquiv fun _ : Fin (n + 1) => Fin 2).symm.trans
        (((Equiv.refl (Fin 2)).prodCongr (bitsFinEquiv n)).trans
          (finProdFinEquiv.trans (finCongr (by simp [pow_succ, Nat.mul_comm]))))

/-- The explicit matrix reindexing preserves the complete coefficient algebra. -/
def binaryMatrixEquiv (n : ℕ) :
    CoefficientMatrix B n ≃ₐ[ℝ] Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) B :=
  Matrix.reindexAlgEquiv ℝ B (bitsFinEquiv n)

def binaryUnroll (n : ℕ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) B ≃ₐ[ℝ] (Clsplit n ⊗[ℝ] B) :=
  (binaryMatrixEquiv B n).symm.trans (unrollCoefficients B n)

@[simp] theorem binaryUnroll_binaryMatrix (n : ℕ) (M : CoefficientMatrix B n) :
    binaryUnroll B n (binaryMatrixEquiv B n M) = unrollCoefficients B n M := by
  simp [binaryUnroll]

theorem binaryUnroll_mul (n : ℕ) (M N : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) B) :
    binaryUnroll B n (M * N) = binaryUnroll B n M * binaryUnroll B n N :=
  map_mul (binaryUnroll B n) M N

/-- The full finite matrix algorithm: explicit binary block extraction,
four parity corrections, four recursive calls, and native head combination. -/
theorem binaryUnroll_succ (n : ℕ)
    (M : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) B) :
    let V := correction (coefficientMatrixParity B n)
      (coefficients ((flatten B n).symm ((binaryMatrixEquiv B (n + 1)).symm M)))
    binaryUnroll B (n + 1) M =
      consTensor B n (1 : CliffordAlgebra q11)
        (binaryUnroll B n (binaryMatrixEquiv B n (V 0))) +
      consTensor B n (CliffordAlgebra.ι q11 (1, 0))
        (binaryUnroll B n (binaryMatrixEquiv B n (V 1))) +
      consTensor B n J1_cl
        (binaryUnroll B n (binaryMatrixEquiv B n (V 2))) +
      consTensor B n (CliffordAlgebra.ι q11 (0, 1))
        (binaryUnroll B n (binaryMatrixEquiv B n (V 3))) := by
  simp only [binaryUnroll_binaryMatrix]
  exact unrollCoefficients_succ B n ((binaryMatrixEquiv B (n + 1)).symm M)

/-! ## Actual coefficient tensors, ready for matrix-product contraction -/

abbrev Words (n : ℕ) := Fin n → Fin 4

/-- The exact `4^n` coefficient tensor extracted by the corrected block
algorithm. Its structure is real-linear, with the full B-valued last leg. -/
def wordCoefficientEquiv : (n : ℕ) →
    CoefficientMatrix B n ≃ₗ[ℝ] (Words n → B)
  | 0 =>
      (Matrix.uniqueLinearEquiv (m := Bits 0) (n := Bits 0) (R := ℝ) (A := B)).trans
        (LinearEquiv.funUnique (Words 0) ℝ B).symm
  | n + 1 =>
      (flatten B n).symm.toLinearEquiv.trans
        ((gradedCoefficientEquiv (coefficientMatrixParity B n)
          (coefficientMatrixParity_involutive B n)).trans
          ((LinearEquiv.piCongrRight fun _ : Fin 4 => wordCoefficientEquiv B n).trans
            ((LinearEquiv.curry ℝ B (Fin 4) (Words n)).symm.trans
              (LinearEquiv.funCongrLeft ℝ B
                (Fin.consEquiv fun _ : Fin (n + 1) => Fin 4).symm))))

@[simp] theorem wordCoefficientEquiv_zero (M : CoefficientMatrix B 0) (w : Words 0) :
    wordCoefficientEquiv B 0 M w = M default default := rfl

/-- Each coefficient is the recursive tail coefficient selected by the first
Clifford basis label, after the specified parity correction. -/
theorem wordCoefficientEquiv_succ (n : ℕ) (M : CoefficientMatrix B (n + 1))
    (w : Words (n + 1)) :
    wordCoefficientEquiv B (n + 1) M w =
      wordCoefficientEquiv B n
        (correction (coefficientMatrixParity B n)
          (coefficients ((flatten B n).symm M)) (w 0)) (Fin.tail w) := rfl

theorem wordCoefficientEquiv_symm_succ (n : ℕ) (c : Words (n + 1) → B) :
    (wordCoefficientEquiv B (n + 1)).symm c =
      flatten B n (synthesize (correction (coefficientMatrixParity B n)
        (fun a => (wordCoefficientEquiv B n).symm
          (fun w => c (Fin.cons a w))))) := rfl

/-- These coefficient tensors reconstruct the native Clifford carrier;
this is not a pointwise algebra equivalence on the coefficient array. -/
def wordReconstruct (n : ℕ) : (Words n → B) ≃ₗ[ℝ] (Clsplit n ⊗[ℝ] B) :=
  (wordCoefficientEquiv B n).symm.trans (unrollCoefficients B n).toLinearEquiv

@[simp] theorem wordReconstruct_coefficients (n : ℕ) (M : CoefficientMatrix B n) :
    wordReconstruct B n (wordCoefficientEquiv B n M) = unrollCoefficients B n M := by
  simp [wordReconstruct]

theorem wordReconstruct_zero (c : Words 0 → B) :
    wordReconstruct B 0 c = (1 : Clsplit 0) ⊗ₜ[ℝ] c default := by
  change unrollCoefficients B 0 ((wordCoefficientEquiv B 0).symm c) = _
  rw [unrollCoefficients_zero]
  rfl

/-- The coefficient tensor's synthesis follows actual graded Clifford heads
in site order and retains one terminal B coefficient. -/
theorem wordReconstruct_succ (n : ℕ) (c : Words (n + 1) → B) :
    wordReconstruct B (n + 1) c =
      consTensor B n (1 : CliffordAlgebra q11)
        (wordReconstruct B n (fun w => c (Fin.cons 0 w))) +
      consTensor B n (CliffordAlgebra.ι q11 (1, 0))
        (wordReconstruct B n (fun w => c (Fin.cons 1 w))) +
      consTensor B n J1_cl
        (wordReconstruct B n (fun w => c (Fin.cons 2 w))) +
      consTensor B n (CliffordAlgebra.ι q11 (0, 1))
        (wordReconstruct B n (fun w => c (Fin.cons 3 w))) := by
  change unrollCoefficients B (n + 1) ((wordCoefficientEquiv B (n + 1)).symm c) = _
  rw [wordCoefficientEquiv_symm_succ, unrollCoefficients_succ]
  simp only [AlgEquiv.symm_apply_apply, coefficients_synthesize,
    correction_involutive (coefficientMatrixParity B n)
      (coefficientMatrixParity_involutive B n)]
  rfl

end InfoGeometry.Clifford.Cl11RecursiveUnrolling
