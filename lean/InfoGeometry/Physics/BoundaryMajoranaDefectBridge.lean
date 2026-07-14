import InfoGeometry.Physics.BoundaryMajoranaMassGap

/-!
# Boundary Majorana Defect Bridge

This file provides an explicit bridge interface connecting topological boundary 
defects to physical Majorana zero modes described by a BdG/Fredholm index formalism.

Closed here:

* an explicit data structure `BoundaryMajoranaDefectDatum` carrying a structural
  identification between boundary defects and BdG Majorana zero modes;
* a bridge theorem safely isolating this assumption without asserting it as a proven
  index theorem in Lean.

Not closed here:

* no theorem natively derives the BdG/Fredholm spectrum or index from the defect 
  topology.
-/

namespace BoundaryMajoranaDefectBridge

open InfoGeometry.Physics.BoundaryMajoranaMassGap

/-- 
Explicit datum carrying a strict correspondence between boundary defects and
Majorana zero modes in the BdG spectrum.
-/
structure BoundaryMajoranaDefectDatum where
  /-- The number of topological boundary defects. -/
  defect_count : ℕ
  /-- The number of Majorana zero modes in the BdG spectrum. -/
  mzm_count : ℕ
  /-- Boundary defects map exactly to Majorana zero modes in this datum. -/
  defect_count_eq_mzm_count : defect_count = mzm_count

/--
The bridge theorem separating the topological defect counting from 
the BdG Majorana zero mode physics.
-/
theorem boundary_defect_mzm_bridge 
    (C : BoundaryMajoranaDefectDatum) :
    C.defect_count = C.mzm_count :=
  C.defect_count_eq_mzm_count

end BoundaryMajoranaDefectBridge
