/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib

/-! Extension of an algebraic twisted-cyclicity identity from a dense image.
No state, positivity, analytic continuation, or new carrier is postulated.
-/

namespace InfoGeometry.OperatorAlgebra.DenseTwistedCyclicity

/-- A continuous readout inherits twisted cyclicity from a dense ring image.
In particular, the readout may be an actual continuous linear functional. -/
theorem twisted_cyclicity_of_denseRange
    {A B : Type*} [Ring A] [NormedRing B]
    (f : A →+* B) (hf : DenseRange f)
    (ψ : B → ℂ) (hψ : Continuous ψ) (δ : Aˣ)
    (hboundary : ∀ x y : A,
      ψ (f (x * y)) = ψ (f (y * ((↑δ : A) * x * (↑(δ⁻¹) : A))))) :
    ∀ X Y : B,
      ψ (X * Y) = ψ (Y * (f (↑δ : A) * X * f (↑(δ⁻¹) : A))) := by
  intro X Y
  refine hf.induction_on X
    (isClosed_eq
      (hψ.comp (continuous_id.mul continuous_const))
      (hψ.comp (continuous_const.mul
        ((continuous_const.mul continuous_id).mul continuous_const)))) ?_
  intro x
  refine hf.induction_on Y
    (isClosed_eq
      (hψ.comp (continuous_const.mul continuous_id))
      (hψ.comp (continuous_id.mul continuous_const))) ?_
  intro y
  simpa only [map_mul] using hboundary x y

end InfoGeometry.OperatorAlgebra.DenseTwistedCyclicity
