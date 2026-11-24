/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.GullDoranPseudoscalarBridge
import InfoGeometry.Twistor.RealTwistorIncidence
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Real Lorentz soldering and nonzero graph incidence

The existing real Pauli matrices define a faithful linear soldering map from
four-dimensional real spacetime to endomorphisms of four-dimensional real
spinors. Its determinant is the square of the `(1,3)` quadratic form. Native
matrix kernel theory and the existing graph-incidence owner therefore identify
null displacement with nonzero intersection of the graph submodules.

These graphs are real four-planes in a real eight-dimensional carrier. They
are distinct from the real two-plane Klein construction and the established
split-signature two-spinor soldering equivalence. All new public carriers and
operations here are real. The imported Pauli owner also contains its older
complex-matrix comparison, which is not used to define these maps.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealLorentzTwistorIncidence

open Matrix
open InfoGeometry.Clifford.GullDoranPseudoscalarBridge
open RealTwistorIncidence

abbrev Spacetime := Fin 4 → ℝ
abbrev Spinor := Fin 4 → ℝ

/-- The real Lorentz quadratic form with time coordinate first. -/
def lorentzQuadratic (x : Spacetime) : ℝ :=
  x 0 ^ 2 - x 1 ^ 2 - x 2 ^ 2 - x 3 ^ 2

/-- Linear soldering using the already owned real Pauli generators. -/
def matrixSoldering : Spacetime →ₗ[ℝ] Mat4R :=
  (LinearMap.proj 0).smulRight 1 +
    (LinearMap.proj 1).smulRight realSigma1 +
    (LinearMap.proj 2).smulRight realSigma2 +
    (LinearMap.proj 3).smulRight realSigma3

theorem matrixSoldering_apply (x : Spacetime) :
    matrixSoldering x = x 0 • (1 : Mat4R) + x 1 • realSigma1 +
      x 2 • realSigma2 + x 3 • realSigma3 := rfl

/-- Coordinate normal form of the existing generators' linear combination. -/
theorem matrixSoldering_eq (x : Spacetime) :
    matrixSoldering x =
      !![x 0 + x 3, 0, x 1, x 2;
         0, x 0 + x 3, -x 2, x 1;
         x 1, -x 2, x 0 - x 3, 0;
         x 2, x 1, 0, x 0 - x 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixSoldering_apply, realSigma1, realSigma2, realSigma3, sub_eq_add_neg]

/-- Soldering retains all four spacetime coordinates. -/
theorem matrixSoldering_injective : Function.Injective matrixSoldering := by
  intro x y h
  rw [matrixSoldering_eq, matrixSoldering_eq] at h
  have h00 := congrFun (congrFun h 0) 0
  have h22 := congrFun (congrFun h 2) 2
  have h02 := congrFun (congrFun h 0) 2
  have h03 := congrFun (congrFun h 0) 3
  change x 0 + x 3 = y 0 + y 3 at h00
  change x 0 - x 3 = y 0 - y 3 at h22
  change x 1 = y 1 at h02
  change x 2 = y 2 at h03
  funext i
  fin_cases i <;> simp <;> linarith

/-- The real determinant is the square of the Lorentz quadratic. -/
theorem det_matrixSoldering (x : Spacetime) :
    (matrixSoldering x).det = lorentzQuadratic x ^ 2 := by
  rw [matrixSoldering_eq]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, lorentzQuadratic]
  ring

/-- The image includes genuinely noncommuting operators. -/
theorem matrixSoldering_noncommuting_witness :
    ∃ x y : Spacetime, matrixSoldering x * matrixSoldering y ≠
      matrixSoldering y * matrixSoldering x := by
  refine ⟨![0, 1, 0, 0], ![0, 0, 1, 0], ?_⟩
  intro h
  have h01 := congrFun (congrFun h 0) 1
  norm_num [matrixSoldering_apply, realSigma1, realSigma2, Matrix.mul_apply,
    Fin.sum_univ_succ] at h01

/-- Native real spinor endomorphisms obtained from the faithful matrix map. -/
def operatorSoldering : Spacetime →ₗ[ℝ] Module.End ℝ Spinor :=
  Matrix.toLin'.toLinearMap.comp matrixSoldering

@[simp] theorem operatorSoldering_apply (x : Spacetime) (π : Spinor) :
    operatorSoldering x π = (matrixSoldering x).mulVec π := rfl

theorem operatorSoldering_injective : Function.Injective operatorSoldering :=
  Matrix.toLin'.injective.comp matrixSoldering_injective

/-- The graph of the soldered operator is a native real incidence submodule. -/
def spacetimeIncidenceSpace (x : Spacetime) : Submodule ℝ (Carrier Spinor Spinor) :=
  incidenceSpace (operatorSoldering x)

theorem spacetimeIncidenceSpace_injective : Function.Injective spacetimeIncidenceSpace :=
  incidenceSpace_injective.comp operatorSoldering_injective

/-- Each graph has real dimension four, including at the zero spacetime point. -/
theorem finrank_spacetimeIncidenceSpace (x : Spacetime) :
    Module.finrank ℝ (spacetimeIncidenceSpace x) = 4 := by
  change Module.finrank ℝ (incidenceSpace (operatorSoldering x)) = 4
  rw [← (spinorEquivIncidence (operatorSoldering x)).finrank_eq]
  simp [Spinor]

/-- Null separation is exactly nonzero intersection of the real graph planes.
Coincident spacetime points are included. -/
theorem null_iff_shared_nonzero_twistor (x y : Spacetime) :
    lorentzQuadratic (x - y) = 0 ↔
      ∃ z : Carrier Spinor Spinor, z ≠ 0 ∧
        z ∈ spacetimeIncidenceSpace x ∧ z ∈ spacetimeIncidenceSpace y := by
  change lorentzQuadratic (x - y) = 0 ↔
    ∃ z : Carrier Spinor Spinor, z ≠ 0 ∧
      z ∈ incidenceSpace (operatorSoldering x) ∧
      z ∈ incidenceSpace (operatorSoldering y)
  rw [shared_nonzero_twistor_iff]
  have hdet : (matrixSoldering (x - y)).det = 0 ↔
      ∃ π : Spinor, π ≠ 0 ∧ (matrixSoldering (x - y)).mulVec π = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.symm
  rw [det_matrixSoldering, sq_eq_zero_iff] at hdet
  have heval (π : Spinor) :
      (matrixSoldering (x - y)).mulVec π =
        (operatorSoldering x - operatorSoldering y) π := by
    rw [← map_sub operatorSoldering x y]
    rfl
  simpa only [heval] using hdet

end InfoGeometry.Twistor.RealLorentzTwistorIncidence
