/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl11FilteredInductiveInverseColimitBridge

noncomputable section

namespace InfoGeometry.Canonical.Cl11FilteredInductiveInverseColimitBridge

open CategoryTheory CategoryTheory.Limits
open FilteredColimit
open FilteredColimit.Native

/-- Every element of the concrete Cl(1,1) direct limit is the image of a
stage element under the canonical native ModuleCat colimit readout. -/
theorem limitReadout_surjective :
    Function.Surjective limitReadout.hom := by
  intro x
  induction x using DirectLimit.induction with
  | _ n A =>
      exact ⟨(colimit.ι (moduleDiagram directSystem) n).hom A,
        limitReadout_stage_apply n A⟩

end InfoGeometry.Canonical.Cl11FilteredInductiveInverseColimitBridge
