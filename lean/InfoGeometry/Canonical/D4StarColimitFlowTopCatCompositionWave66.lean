/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.D4StarColimitFlowTopCat

namespace InfoGeometry.Topology.ColimitDynamics

open CategoryTheory Limits

variable {J : Type*} [Category J]
variable (D : TopologicalDiscreteFlowSystem (J := J))
variable (C : Cocone D.carrier)
variable (hC : IsColimit C)

theorem colimitEndomorphismTopCatHom_comp_forward (s t : ℤ) :
    colimitEndomorphismTopCatHom D C hC s ≫
        colimitEndomorphismTopCatHom D C hC t =
      colimitEndomorphismTopCatHom D C hC (s + t) := by
  calc
    colimitEndomorphismTopCatHom D C hC s ≫
        colimitEndomorphismTopCatHom D C hC t =
      colimitEndomorphismTopCatHom D C hC (t + s) := by
        exact (colimitEndomorphismTopCatHom_add D C hC t s).symm
    _ = colimitEndomorphismTopCatHom D C hC (s + t) := by
      rw [add_comm]

end InfoGeometry.Topology.ColimitDynamics
