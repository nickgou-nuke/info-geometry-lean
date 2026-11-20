/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.HestenesPauliSheetBridgeFinite
import InfoGeometry.Canonical.HestenesCliffordDimension

/-! # The real algebra equivalence `Cl⁺(1,3) ≃ M₂(ℂ)` -/

noncomputable section
namespace HestenesEvenPauliEquiv

open scoped DirectSum

open HestenesCl14
open HestenesPauliSheetBridge
open TwoSheetThreeColorWeyl

theorem sheet_finrank : Module.finrank ℝ Sheet = 8 := by
  rw [Module.finrank_matrix, Complex.finrank_real_complex]
  norm_num

def pauli0 : Sheet := 1
def pauli1 : Sheet := !![0, 1; 1, 0]
def pauli2 : Sheet := !![0, -Complex.I; Complex.I, 0]
def pauli3 : Sheet := !![1, 0; 0, -1]

@[simp] theorem clPlusToPauli_sigma0 : clPlusToPauli (sigmaEven 0) = pauli1 := by
  rw [sigmaEven, clPlusToPauli_on_pair]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [paravector, paravectorConj, basisVec, pauli1,
      Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem clPlusToPauli_sigma1 : clPlusToPauli (sigmaEven 1) = pauli2 := by
  rw [sigmaEven, clPlusToPauli_on_pair]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [paravector, paravectorConj, basisVec, pauli2,
      Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem clPlusToPauli_sigma2 : clPlusToPauli (sigmaEven 2) = pauli3 := by
  rw [sigmaEven, clPlusToPauli_on_pair]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [paravector, paravectorConj, basisVec, pauli3,
      Matrix.mul_apply, Fin.sum_univ_two]

def volumeEven : ClPlus14 := sigmaEven 0 * sigmaEven 1 * sigmaEven 2

@[simp] theorem clPlusToPauli_volumeEven :
    clPlusToPauli volumeEven = Complex.I • (1 : Sheet) := by
  simp [volumeEven]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauli1, pauli2, pauli3, Matrix.mul_apply, Fin.sum_univ_two]

def pauliCoeff0 (A : Sheet) : ℂ := (A 0 0 + A 1 1) / 2
def pauliCoeff1 (A : Sheet) : ℂ := (A 0 1 + A 1 0) / 2
def pauliCoeff2 (A : Sheet) : ℂ := (Complex.I / 2) * (A 0 1 - A 1 0)
def pauliCoeff3 (A : Sheet) : ℂ := (A 0 0 - A 1 1) / 2

def liftComplexCoeff (z : ℂ) (x : ClPlus14) : ClPlus14 :=
  z.re • x + z.im • (volumeEven * x)

def pauliPreimage (A : Sheet) : ClPlus14 :=
  liftComplexCoeff (pauliCoeff0 A) 1 +
    liftComplexCoeff (pauliCoeff1 A) (sigmaEven 0) +
    liftComplexCoeff (pauliCoeff2 A) (sigmaEven 1) +
    liftComplexCoeff (pauliCoeff3 A) (sigmaEven 2)

theorem clPlusToPauli_liftComplexCoeff (z : ℂ) (x : ClPlus14) :
    clPlusToPauli (liftComplexCoeff z x) = z • clPlusToPauli x := by
  rw [liftComplexCoeff, map_add, map_smul, map_smul, map_mul,
    clPlusToPauli_volumeEven]
  ext i j
  simp [Complex.ext_iff]
  <;> ring

theorem clPlusToPauli_pauliPreimage (A : Sheet) :
    clPlusToPauli (pauliPreimage A) = A := by
  rw [pauliPreimage, map_add, map_add, map_add]
  simp only [clPlusToPauli_liftComplexCoeff, map_one,
    clPlusToPauli_sigma0, clPlusToPauli_sigma1, clPlusToPauli_sigma2]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliCoeff0, pauliCoeff1, pauliCoeff2, pauliCoeff3,
      pauli1, pauli2, pauli3]
  all_goals ring_nf
  all_goals try rw [Complex.I_sq]
  all_goals ring

theorem clPlusToPauli_surjective : Function.Surjective clPlusToPauli :=
  fun A => ⟨pauliPreimage A, clPlusToPauli_pauliPreimage A⟩

theorem clPlusToPauli_injective : Function.Injective clPlusToPauli := by
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := clPlusToPauli.toLinearMap)
    (by rw [clPlus14_finrank, sheet_finrank])).2
      (by simpa using clPlusToPauli_surjective)

/-- The independently defined native even Clifford algebra is exactly the
real Pauli matrix algebra. -/
noncomputable def clPlusPauliAlgEquiv : ClPlus14 ≃ₐ[ℝ] Sheet :=
  AlgEquiv.ofBijective clPlusToPauli
    ⟨clPlusToPauli_injective, clPlusToPauli_surjective⟩

end HestenesEvenPauliEquiv
end noncomputable section
