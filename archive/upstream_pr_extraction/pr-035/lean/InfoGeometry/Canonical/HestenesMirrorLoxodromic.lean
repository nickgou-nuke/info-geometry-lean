import InfoGeometry.Canonical.HestenesLoxodromicRotor

namespace InfoGeometry.Canonical

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem mirror_realBoostAction
    (K : V →ₗ[ℝ] V) (J : V ≃ₗ[ℝ] V)
    (hJK : ∀ v : V, J (K v) = -(K (J v)))
    (t : ℝ) (v : V) :
    J (realBoostAction K t v) =
      realBoostAction K (-t) (J v) := by
  unfold realBoostAction
  simp only [map_add, map_smul, Real.cosh_neg, Real.sinh_neg, hJK]
  module

theorem mirror_realRotorAction
    (I : V →ₗ[ℝ] V) (J : V ≃ₗ[ℝ] V)
    (hJI : ∀ v : V, J (I v) = -(I (J v)))
    (θ : ℝ) (v : V) :
    J (realRotorAction I θ v) =
      realRotorAction I (-θ) (J v) := by
  unfold realRotorAction
  simp only [map_add, map_smul, Real.cos_neg, Real.sin_neg, hJI]
  module

theorem mirror_realLoxodromicAction
    (K I : V →ₗ[ℝ] V) (J : V ≃ₗ[ℝ] V)
    (hJK : ∀ v : V, J (K v) = -(K (J v)))
    (hJI : ∀ v : V, J (I v) = -(I (J v)))
    (t θ : ℝ) (v : V) :
    J (realLoxodromicAction K I t θ v) =
      realLoxodromicAction K I (-t) (-θ) (J v) := by
  unfold realLoxodromicAction
  rw [mirror_realBoostAction K J hJK t]
  rw [mirror_realRotorAction I J hJI θ]

end

end InfoGeometry.Canonical
