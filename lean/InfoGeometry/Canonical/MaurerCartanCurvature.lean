/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.BogoliubovTransport

/-!
# Doubled-space commutator curvature

This focused owner contains the existing operator curvature and its skew law.
The Berry readout and vielbein owners share these exact declarations without
requiring the rest of the Berry geometry to define exponential transport.
-/

set_option linter.unusedSectionVars false

namespace InfoGeometry.Canonical.BerryPhase

open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Krein
open scoped InnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/--
Operator Maurer-Cartan curvature bracket on doubled real space.
-/
noncomputable def hestenesMaurerCartanCurvature
    (X Y : EndH) : EndH :=
  transportCommutator (E := E) X Y

theorem hestenesMaurerCartanCurvature_skew
    (X Y : EndH) :
    hestenesMaurerCartanCurvature X Y
      =
    -hestenesMaurerCartanCurvature Y X := by
  unfold hestenesMaurerCartanCurvature transportCommutator
  abel

end InfoGeometry.Canonical.BerryPhase
