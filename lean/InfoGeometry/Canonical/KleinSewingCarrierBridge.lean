/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KleinBottleSewing
import InfoGeometry.Physics.KleinBottleSewingExact
import InfoGeometry.Canonical.KleinSewingDefect
import InfoGeometry.Canonical.AndreevKleinChiralBridge

/-! # Klein Sewing Carrier Bridge

Intertwines the two existing Klein sewing carriers:
- Canonical: `tilt`/`switch` (matrix literal)
- Physics: `tilt2`/`switch2` (function match)

Proves carrier equivalence, transfers the defect law and Andreev bridge to the
second carrier, and connects the sewn condition to defect vanishing on both.
No new carrier is introduced; all results reuse existing definitions.
-/
namespace InfoGeometry.Canonical.KleinSewingCarrierBridge

open Matrix Complex
open InfoGeometry.Physics.KleinBottleSewingExact
open InfoGeometry.Canonical.KleinSewingDefect
open InfoGeometry.Canonical.AndreevKleinChiralBridge

/-- The two tilt carriers are definitionally equal. -/
theorem tilt_eq_tilt2 : tilt = tilt2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tilt, tilt2]

/-- The two switch carriers are definitionally equal. -/
theorem switch_eq_switch2 : switch = switch2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [switch, switch2]

/-- Carrier algebra transfers: tilt2²=1 follows from tilt²=1. -/
theorem tilt2_sq_from_canonical : tilt2 * tilt2 = 1 := by
  rw [← tilt_eq_tilt2]
  simpa [sq] using tilt_sq

/-- Carrier algebra transfers: switch2²=1 follows from switch²=1. -/
theorem switch2_sq_from_canonical : switch2 * switch2 = 1 := by
  rw [← switch_eq_switch2]
  simpa [sq] using switch_sq

/-- Anticommutation transfers to the second carrier. -/
theorem tilt2_switch2_anticomm_from_canonical :
    tilt2 * switch2 = - (switch2 * tilt2) := by
  rw [← tilt_eq_tilt2, ← switch_eq_switch2]
  exact tilt_switch_anticomm

/-- A BoundaryState2 can be viewed as a BoundaryState (same fields). -/
def boundaryState2ToBoundaryState (s : BoundaryState2) : BoundaryState where
  rho := s.rho
  is_hermitian := s.is_hermitian
  trace_one := s.trace_one

/-- The sewing condition is preserved under carrier equivalence. -/
theorem isSewn_iff_isSewn2 (s : BoundaryState2) :
    isSewn (boundaryState2ToBoundaryState s) ↔ is_klein_bottle_sewn_2 s := by
  unfold isSewn is_klein_bottle_sewn_2 boundaryState2ToBoundaryState
  rw [switch_eq_switch2]

/-- The chiral index is preserved under carrier equivalence. -/
theorem chiralIndex_eq_chiralIndex2 (s : BoundaryState2) :
    chiralIndex (boundaryState2ToBoundaryState s) = chiral_index_2 s := by
  unfold chiralIndex chiral_index_2 boundaryState2ToBoundaryState
  rw [tilt_eq_tilt2]

/-- Sewn implies defect zero on the canonical carrier. -/
theorem sewn_implies_defect_zero (s : BoundaryState) (h : isSewn s) :
    Matrix.trace (tilt * (switch * s.rho * switch - s.rho)) = 0 := by
  have hci : chiralIndex s = 0 := klein_throat_anomaly_vanishes s h
  exact KleinSewingDefect.boundary_defect_trace_zero_iff s |>.mpr hci

/-- Defect vanishes on sewn states of the second carrier. -/
theorem defect_vanishes_sewn2 (s : BoundaryState2) (h : is_klein_bottle_sewn_2 s) :
    Matrix.trace (tilt2 * (switch2 * s.rho * switch2 - s.rho)) = 0 := by
  rw [← tilt_eq_tilt2, ← switch_eq_switch2]
  exact sewn_implies_defect_zero (boundaryState2ToBoundaryState s) ((isSewn_iff_isSewn2 s).mpr h)

/-- Andreev channel exchange on the second carrier. -/
theorem switch2_tilt2_exchange :
    switch2 * tilt2 * switch2 = - tilt2 := by
  rw [← tilt_eq_tilt2, ← switch_eq_switch2]
  exact concrete_switch_tilt_exchange

end InfoGeometry.Canonical.KleinSewingCarrierBridge