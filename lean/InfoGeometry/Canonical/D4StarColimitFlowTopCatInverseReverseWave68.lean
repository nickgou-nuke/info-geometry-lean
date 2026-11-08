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

theorem colimitEndomorphismTopCatHom_comp_inverse_reverse (t : ℤ) :
    colimitEndomorphismTopCatHom D C hC (-t) ≫
        colimitEndomorphismTopCatHom D C hC t =
      𝟙 C.pt := by
  exact colimitEndomorphism_neg_comp D C hC t

end InfoGeometry.Topology.ColimitDynamics
