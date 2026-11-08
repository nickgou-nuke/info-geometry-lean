import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealMirrorComplexStructure

namespace InfoGeometry.Canonical

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def IsRealInvolution (K : V →ₗ[ℝ] V) : Prop :=
  K.comp K = LinearMap.id

def realBoostAction (K : V →ₗ[ℝ] V) (t : ℝ) (v : V) : V :=
  Real.cosh t • v + Real.sinh t • K v

theorem realBoostAction_zero (K : V →ₗ[ℝ] V) (v : V) :
    realBoostAction K 0 v = v := by
  simp [realBoostAction]

theorem realBoostAction_neg
    (K : V →ₗ[ℝ] V) (t : ℝ) (v : V) :
    realBoostAction K (-t) v =
      Real.cosh t • v - Real.sinh t • K v := by
  simp [realBoostAction, Real.cosh_neg, Real.sinh_neg, sub_eq_add_neg]

theorem realBoostAction_add
    (K : V →ₗ[ℝ] V) (hK : IsRealInvolution K)
    (t s : ℝ) (v : V) :
    realBoostAction K t (realBoostAction K s v) =
      realBoostAction K (t + s) v := by
  have hK_apply : ∀ w : V, K (K w) = w :=
    fun w => by
      have h := congrArg (fun f : V →ₗ[ℝ] V => f w) hK
      simpa [IsRealInvolution, LinearMap.comp_apply] using h
  simp only [realBoostAction, map_add, map_smul, smul_add, smul_smul,
    hK_apply]
  rw [Real.cosh_add, Real.sinh_add]
  module

theorem realBoostAction_inverse
    (K : V →ₗ[ℝ] V) (hK : IsRealInvolution K)
    (t : ℝ) (v : V) :
    realBoostAction K (-t) (realBoostAction K t v) = v := by
  calc
    realBoostAction K (-t) (realBoostAction K t v) =
        realBoostAction K (-t + t) v :=
      realBoostAction_add K hK (-t) t v
    _ = v := by simp [realBoostAction]

end

end InfoGeometry.Canonical
