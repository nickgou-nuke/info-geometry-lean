/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.KleinRealOperatorDescent

noncomputable section

namespace InfoGeometry.Topology.KleinRealOperatorDescent

open KleinBrillouinBase KleinBottleOrbitQuotient

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Descent sends the identity operator on torus fields to the identity
operator on quotient fields. -/
theorem quotientOperator_id_wave38 :
    quotientOperator (LinearMap.id : Module.End ℝ (BrillouinTorus → V)) (by
      intro field
      exact field.property) =
      (LinearMap.id : Module.End ℝ (KleinBrillouinQuotient → V)) := by
  symm
  apply quotientOperator_unique
  intro _field point
  rfl

/-- Descent sends the zero operator on torus fields to the zero operator on
quotient fields. -/
theorem quotientOperator_zero_wave38 :
    quotientOperator (0 : Module.End ℝ (BrillouinTorus → V)) (by
      intro field
      exact (invariantFields (V := V)).zero_mem) =
      (0 : Module.End ℝ (KleinBrillouinQuotient → V)) := by
  symm
  apply quotientOperator_unique
  intro _field point
  rfl

end InfoGeometry.Topology.KleinRealOperatorDescent
