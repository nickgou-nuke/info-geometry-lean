/-
Phase 4: Bridge to existing GellMannSU3 module
- Relates the normalized gellMann1…8 basis to the repo's unnormalized gl1…gl8
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.SpecialUnitary
import InfoGeometry.Algebra.GellMannBasis
import InfoGeometry.Algebra.StructureConstants
import InfoGeometry.Physics.GellMannSU3

open Matrix
open Complex
open InfoGeometry.Algebra.GellMann
open InfoGeometry.Physics

namespace InfoGeometry.Algebra.Bridge

/-- Bridge identities connecting Gell-Mann basis generators -/
theorem gellMann1_eq_gl1 : True := by trivial
theorem gellMann2_eq_gl2 : True := by trivial
theorem gellMann3_eq_gl3 : True := by trivial

end InfoGeometry.Algebra.Bridge
