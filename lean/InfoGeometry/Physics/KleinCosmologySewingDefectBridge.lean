/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.KleinBottleCosmology
import InfoGeometry.Canonical.KleinSewingDefect

/-! # Klein Cosmology Sewing Defect Bridge

Connects the existing Klein bottle cosmology sewing theorem (chiral index
vanishes on sewn states) to the exact defect trace law. Shows that a sewn
boundary state has zero defect trace, and that the defect is governed by
twice the chiral index.

Reuses existing carriers and theorems; no new carrier or structure.
-/
namespace InfoGeometry.Physics.KleinCosmologySewingDefectBridge

open Matrix Complex
open InfoGeometry.Canonical.KleinSewingDefect
open InfoGeometry.Physics.KleinBottleCosmology

/-- Sewn implies defect zero on the canonical carrier. -/
theorem sewn_implies_defect_zero (s : BoundaryState) (h : isSewn s) :
    Matrix.trace (tilt * (switch * s.rho * switch - s.rho)) = 0 := by
  have hci : chiralIndex s = 0 := sewn_boundary_chiral_index_vanishes s h
  exact boundary_defect_trace_zero_iff s |>.mpr hci

/-- A sewn boundary state has zero defect trace. -/
theorem sewn_zero_defect_trace (s : BoundaryState) (h : isSewn s) :
    Matrix.trace (tilt * (switch * s.rho * switch - s.rho)) = 0 :=
  sewn_implies_defect_zero s h

/-- The defect trace on a sewn state is governed by the chiral index:
    defect = −2 • chiralIndex, and chiralIndex = 0 when sewn. -/
theorem sewn_defect_chiral_link (s : BoundaryState) (h : isSewn s) :
    Matrix.trace (tilt * (switch * s.rho * switch - s.rho)) = - (2 • chiralIndex s) ∧
    chiralIndex s = 0 := by
  constructor
  · exact boundary_defect_trace s
  · exact sewn_boundary_chiral_index_vanishes s h

/-- The cosmology glide-invariant sewing condition implies zero defect. -/
theorem glide_sewn_zero_defect (s : BoundaryState) (h : isSewn s) :
    Matrix.trace (tilt * (switch * s.rho * switch - s.rho)) = 0 ∧
    chiralIndex s = 0 := by
  constructor
  · exact sewn_zero_defect_trace s h
  · exact sewn_boundary_chiral_index_vanishes s h

end InfoGeometry.Physics.KleinCosmologySewingDefectBridge