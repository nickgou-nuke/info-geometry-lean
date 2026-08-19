import InfoGeometry.Canonical.HestenesPhaseBoostRotors
import InfoGeometry.Canonical.RealComplexRotor

namespace InfoGeometry.Canonical

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def realLoxodromicAction
    (K I : V →ₗ[ℝ] V) (t θ : ℝ) (v : V) : V :=
  realBoostAction K t (realRotorAction I θ v)

/-! The finite four-channel expansion keeps the boost and elliptic axes real. -/

theorem realLoxodromicAction_four_channel
    (K I : V →ₗ[ℝ] V) (t θ : ℝ) (v : V) :
    realLoxodromicAction K I t θ v =
      (Real.cosh t * Real.cos θ) • v +
        (Real.sinh t * Real.cos θ) • K v +
        (Real.cosh t * Real.sin θ) • I v +
        (Real.sinh t * Real.sin θ) • K (I v) := by
  simp only [realLoxodromicAction, realBoostAction, realRotorAction,
    map_add, map_smul, smul_add, smul_smul]
  module

theorem hyperbolic_weights_reciprocal (a b : ℝ)
    (h : a ^ 2 - b ^ 2 = 1) :
    (a + b) * (a - b) = 1 := by
  nlinarith

theorem realLoxodromicAction_zero
    (K I : V →ₗ[ℝ] V) (v : V) :
    realLoxodromicAction K I 0 0 v = v := by
  simp [realLoxodromicAction, realBoostAction_zero, realRotorAction_zero]

theorem realLoxodromicAction_commute
    (K I : V →ₗ[ℝ] V)
    (hKI : K.comp I = I.comp K) (t θ : ℝ) (v : V) :
    realBoostAction K t (realRotorAction I θ v) =
      realRotorAction I θ (realBoostAction K t v) := by
  have hKI_apply : ∀ w : V, K (I w) = I (K w) :=
    fun w => by
      have h := congrArg (fun f : V →ₗ[ℝ] V => f w) hKI
      simpa [LinearMap.comp_apply] using h
  simp only [realBoostAction, realRotorAction, map_add, map_smul,
    smul_add, smul_smul, hKI_apply]
  module

theorem realLoxodromicAction_add
    (K I : V →ₗ[ℝ] V)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    (t₁ θ₁ t₂ θ₂ : ℝ) (v : V) :
    realLoxodromicAction K I t₁ θ₁
        (realLoxodromicAction K I t₂ θ₂ v) =
      realLoxodromicAction K I (t₁ + t₂) (θ₁ + θ₂) v := by
  unfold realLoxodromicAction
  rw [← realLoxodromicAction_commute K I hKI t₂ θ₁]
  rw [realBoostAction_add K hK]
  rw [realRotorAction_add I hI]

theorem realLoxodromicAction_inverse
    (K I : V →ₗ[ℝ] V)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    (t θ : ℝ) (v : V) :
    realLoxodromicAction K I (-t) (-θ)
        (realLoxodromicAction K I t θ v) = v := by
  unfold realLoxodromicAction
  rw [realLoxodromicAction_commute K I hKI (-t) (-θ)]
  rw [realBoostAction_inverse K hK]
  rw [realRotorAction_inverse I hI]

end

end InfoGeometry.Canonical
