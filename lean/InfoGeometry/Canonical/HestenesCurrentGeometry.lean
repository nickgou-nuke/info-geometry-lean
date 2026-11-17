/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.HestenesCurrentAlgebra
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Real spacetime coordinates of the native Clifford current

The current is the actual `Cl14` sandwich from `HestenesCurrentAlgebra`.
The existing faithful equivalence of the entire even algebra identifies its
right paravector with a Hermitian Gram matrix. The inverse paravector formula
therefore produces an actual real vector whose Clifford embedding is the
current, rather than assigning coordinates to an unproved interpretation.

The resulting time coordinate is positive exactly for nonzero even spinors,
and the existing Clifford square proves its nonnegative Minkowski norm. No
arbitrary scalar projection, observer-flux functional, PDE, or global charge
is introduced.
-/

noncomputable section

namespace HestenesCurrentGeometry

open HestenesCl14 HestenesPauliSheetBridge HestenesEvenPauliEquiv
open HestenesHermitianAdjoint HestenesHermitianMatrixBridge
open HestenesCurrentAlgebra

/-- The real inverse coordinates of a Hermitian two-by-two paravector. -/
def hermitianCoordinates (A : HestenesPauliSheetBridge.Sheet) : V14 :=
  ![((A 0 0).re + (A 1 1).re) / 2,
    (A 0 1).re,
    -(A 0 1).im,
    ((A 0 0).re - (A 1 1).re) / 2]

theorem paravector_hermitianCoordinates
    (A : HestenesPauliSheetBridge.Sheet) (hA : A.IsHermitian) :
    paravector (hermitianCoordinates A) = A := by
  have h00 : (A 0 0).im = 0 := by
    have h := congrArg Complex.im (hA.apply 0 0)
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  have h11 : (A 1 1).im = 0 := by
    have h := congrArg Complex.im (hA.apply 1 1)
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  have h10 : A 1 0 = star (A 0 1) := (hA.apply 1 0).symm
  apply Matrix.ext
  intro i j
  apply Complex.ext <;> fin_cases i <;> fin_cases j <;>
    simp [paravector, hermitianCoordinates, h00, h11, h10]
  all_goals ring

/-- The universal even-Clifford map sends `ι(v) γ₀` to its actual
paravector matrix. -/
theorem clPlusToPauli_vector_time (v : V14) :
    clPlusToPauli ((CliffordAlgebra.even.ι Q14).bilin v (basisVec 0)) =
      paravector v := by
  rw [clPlusToPauli_on_pair]
  have htime : paravectorConj (basisVec 0) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [paravectorConj, basisVec]
  rw [htime, mul_one]

/-- Coordinates are read from the entire faithful Gram image, with no
restriction to a diagonal or commuting spinor subspace. -/
def currentCoordinates (ψ : ClPlus14) : V14 :=
  hermitianCoordinates (clPlusToPauli ψ * Matrix.conjTranspose (clPlusToPauli ψ))

theorem paravector_currentCoordinates (ψ : ClPlus14) :
    paravector (currentCoordinates ψ) = clPlusToPauli (ψ * hestenesAdjoint ψ) := by
  rw [map_mul, clPlusToPauli_hestenesAdjoint]
  exact paravector_hermitianCoordinates _
    (Matrix.isHermitian_mul_conjTranspose_self (clPlusToPauli ψ))

/-- Actual grade-one identification of the native Dirac current. -/
theorem iota_currentCoordinates (ψ : ClPlus14) :
    CliffordAlgebra.ι Q14 (currentCoordinates ψ) = diracCurrent ψ := by
  have he : (CliffordAlgebra.even.ι Q14).bilin (currentCoordinates ψ) (basisVec 0) =
      ψ * hestenesAdjoint ψ := by
    apply clPlusToPauli_injective
    rw [clPlusToPauli_vector_time]
    exact paravector_currentCoordinates ψ
  have hv := congrArg Subtype.val he
  change CliffordAlgebra.ι Q14 (currentCoordinates ψ) * gamma 0 =
    (ψ * hestenesAdjoint ψ : ClPlus14) at hv
  rw [← diracCurrent_mul_gamma_zero] at hv
  have h := congrArg (fun a : Cl14 => a * gamma 0) hv
  simpa only [mul_assoc, gamma_zero_sq, mul_one] using h

theorem diracCurrent_mem_vector_range (ψ : ClPlus14) :
    diracCurrent ψ ∈ LinearMap.range (CliffordAlgebra.ι Q14) :=
  ⟨currentCoordinates ψ, iota_currentCoordinates ψ⟩

/-- The positive time component is half the squared Hilbert--Schmidt norm
of the full faithful matrix image. -/
theorem currentCoordinates_time_eq (ψ : ClPlus14) :
    currentCoordinates ψ 0 =
      (Complex.normSq (clPlusToPauli ψ 0 0) +
        Complex.normSq (clPlusToPauli ψ 0 1) +
        Complex.normSq (clPlusToPauli ψ 1 0) +
        Complex.normSq (clPlusToPauli ψ 1 1)) / 2 := by
  simp [currentCoordinates, hermitianCoordinates, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_two,
    Complex.mul_conj, add_assoc]

theorem currentCoordinates_time_nonneg (ψ : ClPlus14) :
    0 ≤ currentCoordinates ψ 0 := by
  rw [currentCoordinates_time_eq]
  exact div_nonneg
    (add_nonneg
      (add_nonneg
        (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
        (Complex.normSq_nonneg _))
      (Complex.normSq_nonneg _)) (by norm_num)

theorem currentCoordinates_time_eq_zero_iff (ψ : ClPlus14) :
    currentCoordinates ψ 0 = 0 ↔ ψ = 0 := by
  constructor
  · intro h
    rw [currentCoordinates_time_eq] at h
    have h00n := Complex.normSq_nonneg (clPlusToPauli ψ 0 0)
    have h01n := Complex.normSq_nonneg (clPlusToPauli ψ 0 1)
    have h10n := Complex.normSq_nonneg (clPlusToPauli ψ 1 0)
    have h11n := Complex.normSq_nonneg (clPlusToPauli ψ 1 1)
    have h00 : Complex.normSq (clPlusToPauli ψ 0 0) = 0 := by linarith
    have h01 : Complex.normSq (clPlusToPauli ψ 0 1) = 0 := by linarith
    have h10 : Complex.normSq (clPlusToPauli ψ 1 0) = 0 := by linarith
    have h11 : Complex.normSq (clPlusToPauli ψ 1 1) = 0 := by linarith
    have hz : ∀ i j : Fin 2, Complex.normSq (clPlusToPauli ψ i j) = 0 := by
      intro i j
      fin_cases i <;> fin_cases j <;> assumption
    apply clPlusToPauli_injective
    rw [map_zero]
    apply Matrix.ext
    intro i j
    exact Complex.normSq_eq_zero.mp (hz i j)
  · rintro rfl
    simp [currentCoordinates, hermitianCoordinates]

theorem currentCoordinates_time_pos_iff (ψ : ClPlus14) :
    0 < currentCoordinates ψ 0 ↔ ψ ≠ 0 := by
  constructor
  · intro hpos hzero
    have htime := (currentCoordinates_time_eq_zero_iff ψ).mpr hzero
    exact (ne_of_gt hpos) htime
  · intro hne
    have ht : currentCoordinates ψ 0 ≠ 0 := by
      intro hzero
      exact hne ((currentCoordinates_time_eq_zero_iff ψ).mp hzero)
    exact lt_of_le_of_ne (currentCoordinates_time_nonneg ψ) (Ne.symm ht)

/-- The vector's actual native quadratic form equals the Fierz coefficient. -/
theorem Q14_currentCoordinates (ψ : ClPlus14) :
    Q14 (currentCoordinates ψ) =
      scalarInvariant ψ ^ 2 + pseudoscalarInvariant ψ ^ 2 := by
  apply (algebraMap ℝ Cl14).injective
  simpa only [← iota_currentCoordinates ψ, CliffordAlgebra.ι_sq_scalar,
    Algebra.algebraMap_eq_smul_one] using diracCurrent_sq ψ

theorem Q14_currentCoordinates_nonneg (ψ : ClPlus14) :
    0 ≤ Q14 (currentCoordinates ψ) := by
  rw [Q14_currentCoordinates]
  exact current_norm_coefficient_nonneg ψ

/-- The current lies in the forward causal cone in the `(+---)` convention,
with strict positive time coordinate for every nonzero even spinor. -/
theorem currentCoordinates_future_causal (ψ : ClPlus14) (hψ : ψ ≠ 0) :
    0 < currentCoordinates ψ 0 ∧ 0 ≤ Q14 (currentCoordinates ψ) :=
  ⟨(currentCoordinates_time_pos_iff ψ).mpr hψ, Q14_currentCoordinates_nonneg ψ⟩

end HestenesCurrentGeometry

end noncomputable section
