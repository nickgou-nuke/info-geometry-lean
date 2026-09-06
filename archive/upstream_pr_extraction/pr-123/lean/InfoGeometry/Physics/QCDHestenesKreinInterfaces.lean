import Mathlib

/-!
# Real Hestenes/Krein complex-structure interfaces

This file records the theorem shape needed to connect two real carriers carrying
internal square-minus-one operators.  It deliberately avoids scalar extension
to `C`.
-/

noncomputable section

namespace InfoGeometry.Physics.QCDHestenesKreinInterfaces

/-- A real-linear carrier equipped with an internal complex structure. -/
structure InternalComplexCarrier (V : Type*) [AddCommGroup V] [Module ℝ V] where
  J : Module.End ℝ V
  J_sq : J * J = -(1 : Module.End ℝ V)

/-- A proof-carrying real-linear intertwiner between internal complex carriers. -/
structure InternalComplexIntertwiner
    (V W : Type*)
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (source : InternalComplexCarrier V)
    (target : InternalComplexCarrier W) where
  toLinearMap : V →ₗ[ℝ] W
  map_J : ∀ v, toLinearMap (source.J v) = target.J (toLinearMap v)

namespace InternalComplexIntertwiner

variable
    {V W : Type*}
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    {source : InternalComplexCarrier V}
    {target : InternalComplexCarrier W}

/-- Intertwining automatically transports the square-minus-one action. -/
theorem map_J_sq (F : InternalComplexIntertwiner V W source target) (v : V) :
    F.toLinearMap (source.J (source.J v)) = -(F.toLinearMap v) := by
  rw [F.map_J, F.map_J]
  have h := LinearMap.congr_fun target.J_sq (F.toLinearMap v)
  simpa [Module.End.mul_apply] using h

end InternalComplexIntertwiner

end InfoGeometry.Physics.QCDHestenesKreinInterfaces

end noncomputable section
