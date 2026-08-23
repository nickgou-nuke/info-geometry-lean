import InfoGeometry.Geometry.PauliParavectorBridge
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases

/-!
# Pauli paravector null boundary and the nontrivial kernel

The existing paravector owner proves that nullness is equivalent to vanishing
of the determinant of the Hermitian `2 × 2` Pauli representative.  This file
closes the next finite-dimensional step: determinant zero is equivalent to a
nontrivial kernel of the associated native mathlib linear endomorphism.

Thus the phrases "zero determinant/volume" and "nontrivial kernel" become
proved equivalent properties for this concrete boundary representative; they
are not identified definitionally.
-/

noncomputable section

namespace InfoGeometry.Geometry.PauliParavectorKernelBoundary

open InfoGeometry.Geometry.PauliParavectorBridge
open InfoGeometry.Canonical.PauliHestenesSpinMomentum
open scoped Matrix

abbrev PauliSpinor := Fin 2 → ℂ

/-- Native linear operator associated to the Pauli matrix. -/
def pauliOperator (v : Minkowski4) : Module.End ℂ PauliSpinor :=
  Matrix.toLin' (pauliMatrix v)

@[simp] theorem pauliOperator_apply (v : Minkowski4) (ψ : PauliSpinor) :
    pauliOperator v ψ = Matrix.mulVec (pauliMatrix v) ψ := by
  simp [pauliOperator, Matrix.toLin'_apply]

/-- For an arbitrary `2 × 2` matrix, the vector perpendicular to its first row
is sent to `(0, det A)`. -/
theorem mulVec_firstRowPerp
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.mulVec A ![-A 0 1, A 0 0] = ![0, Matrix.det A] := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two] <;>
    ring

/-- The Pauli matrix is Hermitian in its off-diagonal entries. -/
theorem pauliMatrix_lowerLeft_eq_star_upperRight (v : Minkowski4) :
    pauliMatrix v 1 0 = star (pauliMatrix v 0 1) := by
  simp [pauliMatrix, toPauliParavector,
    PauliParavector.pauliMatrix]

/-- Explicit kernel witness.  Normally it is the perpendicular vector to the
first matrix row.  If that row vanishes, Hermiticity makes the first standard
basis vector a kernel vector. -/
def pauliKernelWitness (v : Minkowski4) : PauliSpinor :=
  if h : pauliMatrix v 0 0 = 0 ∧ pauliMatrix v 0 1 = 0 then
    ![1, 0]
  else
    ![-pauliMatrix v 0 1, pauliMatrix v 0 0]

/-- The chosen kernel witness is always nonzero. -/
theorem pauliKernelWitness_ne_zero (v : Minkowski4) :
    pauliKernelWitness v ≠ 0 := by
  classical
  by_cases h : pauliMatrix v 0 0 = 0 ∧ pauliMatrix v 0 1 = 0
  · intro hw
    have h0 := congrFun hw (0 : Fin 2)
    simp [pauliKernelWitness, h] at h0
  · intro hw
    have h0raw := congrFun hw (0 : Fin 2)
    have h1raw := congrFun hw (1 : Fin 2)
    have h0 : -pauliMatrix v 0 1 = 0 := by
      simpa [pauliKernelWitness, h] using h0raw
    have h1 : pauliMatrix v 0 0 = 0 := by
      simpa [pauliKernelWitness, h] using h1raw
    have h01 : pauliMatrix v 0 1 = 0 := neg_eq_zero.mp h0
    exact h ⟨h1, h01⟩

/-- Vanishing Pauli determinant gives a concrete nonzero kernel vector. -/
theorem pauliKernelWitness_mem_kernel_of_det_zero
    (v : Minkowski4)
    (hdet : Matrix.det (pauliMatrix v) = 0) :
    pauliOperator v (pauliKernelWitness v) = 0 := by
  classical
  by_cases h : pauliMatrix v 0 0 = 0 ∧ pauliMatrix v 0 1 = 0
  · have h10 : pauliMatrix v 1 0 = 0 := by
      rw [pauliMatrix_lowerLeft_eq_star_upperRight v, h.2]
      simp
    funext i
    fin_cases i <;>
      simp [pauliOperator_apply, pauliKernelWitness, h,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two, h.1, h.2, h10]
  · rw [pauliOperator_apply, pauliKernelWitness, dif_neg h,
      mulVec_firstRowPerp, hdet]
    rfl

/-- A zero determinant therefore produces a nonzero vector in the native
linear-map kernel. -/
theorem exists_nonzero_mem_pauliKernel_of_det_zero
    (v : Minkowski4)
    (hdet : Matrix.det (pauliMatrix v) = 0) :
    ∃ ψ : PauliSpinor, ψ ≠ 0 ∧ ψ ∈ LinearMap.ker (pauliOperator v) := by
  refine ⟨pauliKernelWitness v, pauliKernelWitness_ne_zero v, ?_⟩
  rw [LinearMap.mem_ker]
  exact pauliKernelWitness_mem_kernel_of_det_zero v hdet

/-- Nonzero determinant makes the Pauli operator injective, by the native
nonsingular matrix inverse. -/
theorem pauliOperator_injective_of_det_ne_zero
    (v : Minkowski4)
    (hdet : Matrix.det (pauliMatrix v) ≠ 0) :
    Function.Injective (pauliOperator v) := by
  let A := pauliMatrix v
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  intro ψ φ hψφ
  have hmul : Matrix.mulVec A ψ = Matrix.mulVec A φ := by
    simpa [pauliOperator, A, Matrix.toLin'_apply] using hψφ
  have hback := congrArg (Matrix.mulVec A⁻¹) hmul
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul A hunit, Matrix.one_mulVec, Matrix.one_mulVec] at hback
  exact hback

/-- Exact finite-dimensional equivalence: zero determinant iff the associated
Pauli endomorphism has nontrivial kernel. -/
theorem det_pauliMatrix_eq_zero_iff_ker_ne_bot (v : Minkowski4) :
    Matrix.det (pauliMatrix v) = 0 ↔
      LinearMap.ker (pauliOperator v) ≠ ⊥ := by
  constructor
  · intro hdet hbot
    obtain ⟨ψ, hψ, hψker⟩ := exists_nonzero_mem_pauliKernel_of_det_zero v hdet
    rw [hbot] at hψker
    exact hψ (Submodule.mem_bot.mp hψker)
  · intro hker
    by_contra hdet
    have hinj : Function.Injective (pauliOperator v) :=
      pauliOperator_injective_of_det_ne_zero v hdet
    exact hker (LinearMap.ker_eq_bot.mpr hinj)

/-- Null Minkowski paravectors are exactly those with a nontrivial Pauli
spinor kernel. -/
theorem isNull_iff_pauliKernel_ne_bot (v : Minkowski4) :
    v.IsNull ↔ LinearMap.ker (pauliOperator v) ≠ ⊥ := by
  constructor
  · intro hv
    apply (det_pauliMatrix_eq_zero_iff_ker_ne_bot v).mp
    rw [det_pauliMatrix, hv]
    simp
  · intro hker
    have hdet : Matrix.det (pauliMatrix v) = 0 :=
      (det_pauliMatrix_eq_zero_iff_ker_ne_bot v).mpr hker
    rw [det_pauliMatrix] at hdet
    exact_mod_cast hdet

end InfoGeometry.Geometry.PauliParavectorKernelBoundary
