import InfoGeometry.Categorical.FibonacciFusionTreeLinearEquiv
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# The finite `R` braiding on the Fibonacci fusion-tree carrier

This owner lifts the diagonal two-channel `R` matrix to a genuine linear
equivalence on the same finite fusion-tree space used by the `F` operator.
It remains a finite representation-level braiding datum; categorical
naturality and hexagon coherence are separate.
-/

namespace InfoGeometry.Categorical.FibonacciFusionTreeBraiding

open InfoGeometry.Categorical.FibonacciFusionTreeLinearEquiv
open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix

noncomputable def rLinearMap (q : Units ℂ) :
    FusionTree →ₗ[ℂ] FusionTree :=
  Matrix.toLin' (fibonacciRMatrix q)

noncomputable def bLinearMap (q : Units ℂ) (τ s : ℂ) :
    FusionTree →ₗ[ℂ] FusionTree :=
  Matrix.toLin' (fibonacciBMatrix q τ s)

theorem rMatrix_mul_inv (q : Units ℂ) :
    fibonacciRMatrix q * fibonacciRMatrix q⁻¹ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fibonacciRMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · exact inv_mul_cancel₀ (pow_ne_zero 4 (Units.ne_zero q))
  · exact mul_inv_cancel₀ (pow_ne_zero 3 (Units.ne_zero q))

theorem rMatrix_inv_mul (q : Units ℂ) :
    fibonacciRMatrix q⁻¹ * fibonacciRMatrix q = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fibonacciRMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · exact mul_inv_cancel₀ (pow_ne_zero 4 (Units.ne_zero q))
  · exact inv_mul_cancel₀ (pow_ne_zero 3 (Units.ne_zero q))

noncomputable def rLinearEquiv (q : Units ℂ) :
    FusionTree ≃ₗ[ℂ] FusionTree := by
  apply LinearEquiv.ofLinear (rLinearMap q) (rLinearMap q⁻¹)
  · rw [show (rLinearMap q).comp (rLinearMap q⁻¹) =
        Matrix.toLin' (fibonacciRMatrix q * fibonacciRMatrix q⁻¹) by
      simp [rLinearMap, Matrix.toLin'_mul]]
    rw [rMatrix_mul_inv]
    ext x i
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  · rw [show (rLinearMap q⁻¹).comp (rLinearMap q) =
        Matrix.toLin' (fibonacciRMatrix q⁻¹ * fibonacciRMatrix q) by
      simp [rLinearMap, Matrix.toLin'_mul]]
    rw [rMatrix_inv_mul]
    ext x i
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

theorem rLinearEquiv_apply (q : Units ℂ) (x : FusionTree) :
    rLinearEquiv q x = Matrix.mulVec (fibonacciRMatrix q) x := by
  rfl

theorem rLinearEquiv_inverse (q : Units ℂ) :
    (rLinearEquiv q).symm = rLinearEquiv q⁻¹ := by
  ext x
  simp [rLinearEquiv]

theorem rLinearEquiv_trans_inverse (q : Units ℂ) :
    (rLinearEquiv q).trans (rLinearEquiv q⁻¹) =
      LinearEquiv.refl ℂ FusionTree := by
  rw [← rLinearEquiv_inverse q]
  exact (rLinearEquiv q).self_trans_symm

theorem bMatrix_mul_inv (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    fibonacciBMatrix q τ s * fibonacciBMatrix q⁻¹ τ s = 1 := by
  rw [fibonacciBMatrix, fibonacciBMatrix]
  calc
    fibonacciFusionMatrix τ s * fibonacciRMatrix q *
        fibonacciFusionMatrix τ s *
        (fibonacciFusionMatrix τ s * fibonacciRMatrix q⁻¹ *
          fibonacciFusionMatrix τ s) =
        fibonacciFusionMatrix τ s *
          (fibonacciRMatrix q *
            (fibonacciFusionMatrix τ s * fibonacciFusionMatrix τ s) *
            fibonacciRMatrix q⁻¹) * fibonacciFusionMatrix τ s := by
              noncomm_ring
    _ = fibonacciFusionMatrix τ s *
          (fibonacciRMatrix q * 1 * fibonacciRMatrix q⁻¹) *
          fibonacciFusionMatrix τ s := by
            rw [fibonacciFusionMatrix_sq hs hτ]
    _ = 1 := by
      rw [mul_one, rMatrix_mul_inv, mul_one, fibonacciFusionMatrix_sq hs hτ]

theorem bMatrix_inv_mul (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    fibonacciBMatrix q⁻¹ τ s * fibonacciBMatrix q τ s = 1 := by
  exact bMatrix_mul_inv q⁻¹ τ s hs hτ

noncomputable def bLinearEquiv (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    FusionTree ≃ₗ[ℂ] FusionTree := by
  apply LinearEquiv.ofLinear (bLinearMap q τ s) (bLinearMap q⁻¹ τ s)
  · rw [show (bLinearMap q τ s).comp (bLinearMap q⁻¹ τ s) =
        Matrix.toLin' (fibonacciBMatrix q τ s * fibonacciBMatrix q⁻¹ τ s) by
      simp [bLinearMap, Matrix.toLin'_mul]]
    rw [bMatrix_mul_inv q τ s hs hτ]
    ext x i
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  · rw [show (bLinearMap q⁻¹ τ s).comp (bLinearMap q τ s) =
        Matrix.toLin' (fibonacciBMatrix q⁻¹ τ s * fibonacciBMatrix q τ s) by
      simp [bLinearMap, Matrix.toLin'_mul]]
    rw [bMatrix_inv_mul q τ s hs hτ]
    ext x i
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

noncomputable def rModuleIso (q : Units ℂ) :
    ModuleCat.of ℂ FusionTree ≅ ModuleCat.of ℂ FusionTree :=
  (rLinearEquiv q).toModuleIso

noncomputable def bModuleIso (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    ModuleCat.of ℂ FusionTree ≅ ModuleCat.of ℂ FusionTree :=
  (bLinearEquiv q τ s hs hτ).toModuleIso

theorem bLinearEquiv_inverse (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    (bLinearEquiv q τ s hs hτ).symm =
      bLinearEquiv q⁻¹ τ s hs hτ := by
  ext x
  simp [bLinearEquiv]

theorem rModuleIso_trans_inverse (q : Units ℂ) :
    rModuleIso q ≪≫ rModuleIso q⁻¹ =
      CategoryTheory.Iso.refl (ModuleCat.of ℂ FusionTree) := by
  apply CategoryTheory.Iso.ext
  apply ModuleCat.hom_ext
  simpa [rModuleIso, CategoryTheory.Iso.trans_hom] using
    congrArg (fun e : FusionTree ≃ₗ[ℂ] FusionTree =>
      (e : FusionTree →ₗ[ℂ] FusionTree)) (rLinearEquiv_trans_inverse q)

theorem bModuleIso_trans_inverse (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    bModuleIso q τ s hs hτ ≪≫ bModuleIso q⁻¹ τ s hs hτ =
      CategoryTheory.Iso.refl (ModuleCat.of ℂ FusionTree) := by
  apply CategoryTheory.Iso.ext
  apply ModuleCat.hom_ext
  have h := (bLinearEquiv q τ s hs hτ).self_trans_symm
  rw [bLinearEquiv_inverse q τ s hs hτ] at h
  simpa [bModuleIso, CategoryTheory.Iso.trans_hom] using
    congrArg (fun e : FusionTree ≃ₗ[ℂ] FusionTree =>
      (e : FusionTree →ₗ[ℂ] FusionTree))
      h

theorem bLinearEquiv_apply (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) (x : FusionTree) :
    bLinearEquiv q τ s hs hτ x =
      Matrix.mulVec (fibonacciBMatrix q τ s) x := by
  rfl

theorem bLinearEquiv_eq_f_trans_r_trans_f
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    bLinearEquiv q τ s hs hτ =
      ((fLinearEquiv τ s hs hτ).trans (rLinearEquiv q)).trans
        (fLinearEquiv τ s hs hτ) := by
  ext x
  simp [bLinearEquiv, bLinearMap, fLinearEquiv, fLinearMap,
    rLinearEquiv, rLinearMap, fibonacciBMatrix,
    Matrix.toLin'_mul, LinearEquiv.trans_apply]

theorem bLinearEquiv_trans_inverse (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    (bLinearEquiv q τ s hs hτ).trans (bLinearEquiv q⁻¹ τ s hs hτ) =
      LinearEquiv.refl ℂ FusionTree := by
  rw [← bLinearEquiv_inverse q τ s hs hτ]
  exact (bLinearEquiv q τ s hs hτ).self_trans_symm

theorem fusionTree_artin
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) :
    ((rLinearMap q).comp (bLinearMap q τ s)).comp (rLinearMap q) =
      ((bLinearMap q τ s).comp (rLinearMap q)).comp (bLinearMap q τ s) := by
  rw [show ((rLinearMap q).comp (bLinearMap q τ s)).comp (rLinearMap q) =
      Matrix.toLin' (fibonacciRMatrix q * fibonacciBMatrix q τ s *
        fibonacciRMatrix q) by
      simp [rLinearMap, bLinearMap, Matrix.toLin'_mul]]
  rw [show ((bLinearMap q τ s).comp (rLinearMap q)).comp (bLinearMap q τ s) =
      Matrix.toLin' (fibonacciBMatrix q τ s * fibonacciRMatrix q *
        fibonacciBMatrix q τ s) by
      simp [rLinearMap, bLinearMap, Matrix.toLin'_mul]]
  rw [fibonacci_fourAnyon_artin q τ s hq_inv hq_pow3 hq5 h_poly hτ hs]

theorem fusionTree_artin_equiv
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) (hτ0 : τ ^ 2 + τ = 1) :
    ((rLinearEquiv q).trans (bLinearEquiv q τ s hs hτ0)).trans
        (rLinearEquiv q) =
      ((bLinearEquiv q τ s hs hτ0).trans (rLinearEquiv q)).trans
        (bLinearEquiv q τ s hs hτ0) := by
  apply LinearEquiv.ext
  intro x
  have h := fusionTree_artin q τ s hq_inv hq_pow3 hq5 h_poly hτ hs
  exact congrArg (fun T => T x) h

end InfoGeometry.Categorical.FibonacciFusionTreeBraiding
