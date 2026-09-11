import InfoGeometry.Canonical.BeliefDynamics
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.ChiralTorsionBridge

open InfoGeometry.Canonical.BeliefDynamics
open InfoGeometry.Convex

section VolumeRN

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/-- Relative-volume ratio induced by the Radon-Nikodym operator. -/
noncomputable def relativeVacuumVolume
    (H : HessianGeometry E) (x y : E) : ℝ :=
  radonNikodymOp H x y

/-- Boltzmann entropy of relative-volume change: `-log(dμ/dν)`. -/
noncomputable def boltzmannRelativeVolumeEntropy
    (H : HessianGeometry E) (x y : E) : ℝ :=
  -Real.log (relativeVacuumVolume H x y)

omit [FiniteDimensional ℝ E] in
/-- In this model, `-log RN` is exactly the Hessian/Bregman divergence. -/
lemma boltzmannRelativeVolumeEntropy_eq_divergence
    (H : HessianGeometry E) (x y : E) :
    boltzmannRelativeVolumeEntropy H x y = H.divergence x y := by
  unfold boltzmannRelativeVolumeEntropy relativeVacuumVolume radonNikodymOp
  simp

end VolumeRN

end InfoGeometry.Canonical.ChiralTorsionBridge
