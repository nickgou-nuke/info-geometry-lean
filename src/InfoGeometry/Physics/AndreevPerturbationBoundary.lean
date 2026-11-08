/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.GeneralFermionicAndreevCarrier

/-! The existing doubled-space rotation is injective. Hence applying it to
both a signal and a perturbed signal cannot erase a nonzero perturbation.
This is not a theorem about denoisers with measurements or extra information. -/
namespace InfoGeometry.Physics.GeneralFermionicAndreevCarrier

variable {V R : Type*} [Fintype V] [DecidableEq V] [CommRing R]

theorem andreevRotation_mulVec_injective :
    Function.Injective (andreevRotation (V := V) (R := R)).mulVec := by
  intro x y h
  funext i
  cases i with
  | inl i =>
      simpa only [andreevRotation_mulVec_inr] using congrFun h (Sum.inr i)
  | inr i =>
      have hi := congrFun h (Sum.inl i)
      simpa only [andreevRotation_mulVec_inl, neg_inj] using hi

/-- Reversible reflection distinguishes every nonzero additive perturbation. -/
theorem andreevRotation_perturbation_eq_iff (x e : V ⊕ V → R) :
    andreevRotation.mulVec (x + e) = andreevRotation.mulVec x ↔ e = 0 := by
  rw [andreevRotation_mulVec_injective.eq_iff, add_eq_left]

end InfoGeometry.Physics.GeneralFermionicAndreevCarrier
