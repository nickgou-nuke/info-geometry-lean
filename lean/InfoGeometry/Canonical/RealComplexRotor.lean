import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealMirrorComplexStructure

namespace InfoGeometry.Canonical

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def realRotorAction (I : V →ₗ[ℝ] V) (θ : ℝ) (v : V) : V :=
  Real.cos θ • v + Real.sin θ • I v

theorem realRotorAction_zero (I : V →ₗ[ℝ] V) (v : V) :
    realRotorAction I 0 v = v := by
  simp [realRotorAction]

theorem realRotorAction_neg
    (I : V →ₗ[ℝ] V) (θ : ℝ) (v : V) :
    realRotorAction I (-θ) v =
      Real.cos θ • v - Real.sin θ • I v := by
  simp [realRotorAction, Real.cos_neg, Real.sin_neg, sub_eq_add_neg]

theorem realRotorAction_add
    (I : V →ₗ[ℝ] V) (hI : IsRealComplexStructure I)
    (θ φ : ℝ) (v : V) :
    realRotorAction I θ (realRotorAction I φ v) =
      realRotorAction I (θ + φ) v := by
  have hI_apply : ∀ w : V, I (I w) = -w :=
    fun w => realComplexStructure_apply_sq I hI w
  simp only [realRotorAction, map_add, map_smul, smul_add, smul_smul,
    hI_apply]
  rw [Real.cos_add, Real.sin_add]
  module

theorem realRotorAction_add_zero
    (I : V →ₗ[ℝ] V) (_hI : IsRealComplexStructure I)
    (θ : ℝ) (v : V) :
    realRotorAction I θ (realRotorAction I 0 v) =
      realRotorAction I θ v := by
  rw [realRotorAction_zero]

theorem realRotorAction_zero_add
    (I : V →ₗ[ℝ] V) (_hI : IsRealComplexStructure I)
    (θ : ℝ) (v : V) :
    realRotorAction I 0 (realRotorAction I θ v) =
      realRotorAction I θ v := by
  rw [realRotorAction_zero]

theorem realRotorAction_inverse
    (I : V →ₗ[ℝ] V) (hI : IsRealComplexStructure I)
    (θ : ℝ) (v : V) :
    realRotorAction I (-θ) (realRotorAction I θ v) = v := by
  calc
    realRotorAction I (-θ) (realRotorAction I θ v) =
        realRotorAction I (-θ + θ) v :=
      realRotorAction_add I hI (-θ) θ v
    _ = v := by simp [realRotorAction]

end

end InfoGeometry.Canonical
