/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.QuaternionicOperatorFrame
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.QuaternionicOperatorComplexStructure

/-!
The pointwise quaternionic two-sphere of complex structures in the existing
Pauli carrier.  This records only finite algebra; no connection or holonomy is
introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.QuaternionicTwistorSphereOperator

open InfoGeometry.Clifford.QuaternionPauliRealForm
open InfoGeometry.Canonical.QuaternionicOperatorFrame

def twistorNormSq (a b c : ℝ) : ℝ := a ^ 2 + b ^ 2 + c ^ 2

def OnTwistorSphere (a b c : ℝ) : Prop := twistorNormSq a b c = 1

def pauliTwistorUnit (a b c : ℝ) : PauliMatrix :=
  (a : ℂ) • qi + (b : ℂ) • qj + (c : ℂ) • qk

theorem pauliTwistorUnit_sq (a b c : ℝ) :
    pauliTwistorUnit a b c * pauliTwistorUnit a b c =
      -((twistorNormSq a b c : ℂ) • (1 : PauliMatrix)) := by
  have hI : (Complex.I : ℂ) ^ 2 = -1 := by norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliTwistorUnit, twistorNormSq, qi, qj, qk,
      sigma1, sigma2, sigma3, Matrix.mul_apply,
      Fin.sum_univ_two, hI, Complex.ext_iff, pow_two] <;>
    norm_num [Complex.ext_iff, pow_two] <;> ring_nf <;> simp

theorem pauliTwistorUnit_sq_of_sphere
    {a b c : ℝ} (h : OnTwistorSphere a b c) :
    pauliTwistorUnit a b c * pauliTwistorUnit a b c =
      -(1 : PauliMatrix) := by
  rw [pauliTwistorUnit_sq]
  simp [OnTwistorSphere] at h
  rw [h]
  simp

section
open InfoGeometry.Canonical.QuaternionicOperatorComplexStructure

/-- The twistor direction acting on the native two-component Pauli spinor. -/
noncomputable def pauliTwistorComplexStructure
    (a b c : ℝ) : PauliSpinorOperator :=
  pauliSpinorAction (pauliTwistorUnit a b c)

/-- Pointwise unit-sphere directions act as genuine complex structures on the
Pauli spinor carrier. -/
theorem pauliTwistorComplexStructure_sq
    {a b c : ℝ} (h : OnTwistorSphere a b c) :
    (pauliTwistorComplexStructure a b c).comp
        (pauliTwistorComplexStructure a b c) =
      -(LinearMap.id : PauliSpinorOperator) := by
  simpa [pauliTwistorComplexStructure] using
    (pauliSpinorAction_sq_of
      (pauliTwistorUnit a b c)
      (pauliTwistorUnit_sq_of_sphere h))

/-- The three coordinate axes recover the previously defined quaternionic
operator complex structures. -/
theorem pauliTwistorComplexStructure_axis_I :
    pauliTwistorComplexStructure 1 0 0 = pauliComplexI := by
  simp [pauliTwistorComplexStructure, pauliTwistorUnit, pauliComplexI]

/-- Second quaternionic coordinate axis. -/
theorem pauliTwistorComplexStructure_axis_J :
    pauliTwistorComplexStructure 0 1 0 = pauliComplexJ := by
  simp [pauliTwistorComplexStructure, pauliTwistorUnit, pauliComplexJ]

/-- Third quaternionic coordinate axis. -/
theorem pauliTwistorComplexStructure_axis_K :
    pauliTwistorComplexStructure 0 0 1 = pauliComplexK := by
  simp [pauliTwistorComplexStructure, pauliTwistorUnit, pauliComplexK]

end

theorem coordinate_axes_on_twistor_sphere :
    OnTwistorSphere 1 0 0 ∧ OnTwistorSphere 0 1 0 ∧ OnTwistorSphere 0 0 1 := by
  norm_num [OnTwistorSphere, twistorNormSq]

end InfoGeometry.Canonical.QuaternionicTwistorSphereOperator
