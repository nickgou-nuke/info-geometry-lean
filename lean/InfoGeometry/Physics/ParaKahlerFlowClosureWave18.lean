/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Physics.ParaKahlerBoostMetricClosureWave12

/-!
# Para-Kähler modular-flow closure

The existing para-Kähler owner supplies an involution, an anti-invariant symmetric
form, and the hyperbolic flow.  This file closes the group-action and symplectic
transport laws for that actual carrier.  No Gibbs or modular logarithm is
introduced: those require a separate state carrier and are not inferred here.
-/

noncomputable section

namespace InfoGeometry.Physics.ParaKahler

namespace ParaKahlerStructure

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (pk : ParaKahlerStructure V)

/-- The hyperbolic flow satisfies the one-parameter group law. -/
theorem hyperbolicFlow_add (s t : ℝ) (v : V) :
    pk.hyperbolicFlow (s + t) v =
      pk.hyperbolicFlow s (pk.hyperbolicFlow t v) := by
  dsimp [hyperbolicFlow]
  rw [pk.J.map_add, pk.J.map_smul, pk.J.map_smul, pk.J_sq]
  rw [Real.cosh_add, Real.sinh_add]
  simp only [add_smul]
  ring_nf
  module

/-- Reversing the hyperbolic parameter gives the inverse flow. -/
theorem hyperbolicFlow_inverse (t : ℝ) (v : V) :
    pk.hyperbolicFlow (-t) (pk.hyperbolicFlow t v) = v := by
  rw [← pk.hyperbolicFlow_add, neg_add_cancel]
  simp [hyperbolicFlow]

/-- The flow commutes with the para-complex involution. -/
theorem hyperbolicFlow_commutes_J (t : ℝ) (v : V) :
    pk.J (pk.hyperbolicFlow t v) =
      pk.hyperbolicFlow t (pk.J v) := by
  dsimp [hyperbolicFlow]
  simp only [pk.J.map_add, pk.J.map_smul, pk.J_sq]

/-- The hyperbolic flow preserves the para-Berry form. -/
theorem hyperbolicFlow_preserves_omega (t : ℝ) (u v : V) :
    pk.omega (pk.hyperbolicFlow t u) (pk.hyperbolicFlow t v) = pk.omega u v := by
  rw [pk.omega_apply, pk.hyperbolicFlow_commutes_J]
  exact congrArg (fun w : V => pk.g (pk.hyperbolicFlow t u) w)
    (pk.hyperbolicFlow_commutes_J t v) ▸
    pk.hyperbolicFlow_preserves_bilinear t u (pk.J v)

end ParaKahlerStructure

end InfoGeometry.Physics.ParaKahler
