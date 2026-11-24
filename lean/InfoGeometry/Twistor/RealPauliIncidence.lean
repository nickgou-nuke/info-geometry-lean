/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RealPauliPfaffianKernel
import InfoGeometry.Twistor.RealTwistorIncidence
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Real Pauli operators on native incidence submodules

The existing real four-by-four Pauli operator acts on `Fin 4 → ℝ`. Its
incidence submodule uses the existing `(ω, π)` convention and has real
dimension four in a real eight-dimensional carrier. The determinant/kernel
criterion gives exactly the existing Lorentzian null-displacement condition.

The existing phase endomorphism preserves these real submodules. This file
does not construct a complex scalar action or identify the submodules with
real two-planes.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealPauliIncidence

open InfoGeometry.Canonical.RealPauliPfaffianKernel
open InfoGeometry.Clifford.GullDoranPseudoscalarBridge
open RealTwistorIncidence

/-- The native incidence graph has the dimension of the full real spinor. -/
theorem finrank_pauli_incidence (x : Fin 4 → ℝ) :
    Module.finrank ℝ
      (incidenceSpace (Matrix.toLin' (pauli (x 0) (x 1) (x 2) (x 3)))) = 4 := by
  rw [← (spinorEquivIncidence
    (Matrix.toLin' (pauli (x 0) (x 1) (x 2) (x 3)))).finrank_eq]
  simp

/-- Distinct real spacetime coordinates give distinct native incidence graphs. -/
theorem pauli_incidence_injective :
    Function.Injective (fun x : Fin 4 → ℝ =>
      incidenceSpace (Matrix.toLin' (pauli (x 0) (x 1) (x 2) (x 3)))) := by
  intro x y h
  have hmat : pauli (x 0) (x 1) (x 2) (x 3) =
      pauli (y 0) (y 1) (y 2) (y 3) :=
    Matrix.toLin'.injective (incidenceSpace_injective h)
  have hp := congrArg (fun M : Matrix4 => M 0 0) hmat
  have hm := congrArg (fun M : Matrix4 => M 2 2) hmat
  have hx := congrArg (fun M : Matrix4 => M 0 2) hmat
  have hy := congrArg (fun M : Matrix4 => M 0 3) hmat
  simp [pauli_explicit] at hp hm hx hy
  funext i
  fin_cases i
  · change x 0 = y 0
    linarith only [hp, hm]
  · exact hx
  · exact hy
  · change x 3 = y 3
    linarith only [hp, hm]

/-- Null displacement is equivalent to nonzero intersection of the actual
real four-dimensional incidence submodules. -/
theorem null_iff_shared_pauli_incidence (x y : Fin 4 → ℝ) :
    intervalSq (x 0 - y 0) (x 1 - y 1) (x 2 - y 2) (x 3 - y 3) = 0 ↔
      ∃ z : (Fin 4 → ℝ) × (Fin 4 → ℝ), z ≠ 0 ∧
        z ∈ incidenceSpace (Matrix.toLin' (pauli (x 0) (x 1) (x 2) (x 3))) ∧
        z ∈ incidenceSpace (Matrix.toLin' (pauli (y 0) (y 1) (y 2) (y 3))) := by
  rw [shared_nonzero_twistor_iff, ← pauli_sub_det_eq_zero_iff]
  have hdet :
      (pauli (x 0) (x 1) (x 2) (x 3) - pauli (y 0) (y 1) (y 2) (y 3)).det = 0 ↔
        ∃ π : Fin 4 → ℝ, π ≠ 0 ∧
          (pauli (x 0) (x 1) (x 2) (x 3) -
            pauli (y 0) (y 1) (y 2) (y 3)).mulVec π = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.symm
  simpa only [Matrix.sub_mulVec, LinearMap.sub_apply, Matrix.toLin'_apply] using hdet

/-- The pair of existing real phase operators preserves each incidence graph. -/
theorem phase_mem_pauli_incidence (x : Fin 4 → ℝ)
    {z : (Fin 4 → ℝ) × (Fin 4 → ℝ)}
    (hz : z ∈ incidenceSpace (Matrix.toLin' (pauli (x 0) (x 1) (x 2) (x 3)))) :
    (realPhaseAxis.mulVec z.1, realPhaseAxis.mulVec z.2) ∈
      incidenceSpace (Matrix.toLin' (pauli (x 0) (x 1) (x 2) (x 3))) := by
  rw [mem_incidenceSpace] at hz ⊢
  simp only [Matrix.toLin'_apply] at hz ⊢
  rw [hz, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, pauli_commutes_phase]

end InfoGeometry.Twistor.RealPauliIncidence
