/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.G2ExportedFlagAction
import InfoGeometry.Canonical.G2ExportedFlagObstruction

/-! Kernel audit for the exported-permutation obstruction and the conditional
incidence-preserving flag action. -/

open InfoGeometry.Algebra.Zorn.G2ExportedFlagAction
open InfoGeometry.Canonical.G2ExportedFlagObstruction
open InfoGeometry.Algebra.Zorn.G2FlagIncidenceAction

#print axioms exported_generator_zero_not_flag_action
#print axioms no_corrected_t_flag_lift
#print axioms PreservesIncidence.mul
#print axioms flagMap_mul
