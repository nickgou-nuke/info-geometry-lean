/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.KleinBottleDefects
import InfoGeometry.Canonical.KleinBottleSewing
import InfoGeometry.Canonical.KleinSewingDefect
import InfoGeometry.Physics.KleinBottleCosmology

/-! # Klein Euler Defect–Sewing Bridge

Connects the topological Euler characteristic defect balance (5-7 polygon
pairs on trivalent Klein bottle lattices) with the algebraic sewing
constraints (switch invariance, chiral index vanishing).

Both express topological frustration neutralization:
- Euler: F5 = F7 (pentagon-heptagon balance)
- Algebraic: chiralIndex = 0 (even/odd sector balance)

Reuses existing carriers and theorems; no new carrier or structure.
-/
namespace InfoGeometry.Physics.KleinEulerSewingBridge

open InfoGeometry.Physics
open InfoGeometry.Canonical.KleinSewingDefect
open InfoGeometry.Physics.KleinBottleCosmology

/-- The Euler defect balance: pentagons equal heptagons. -/
theorem euler_defect_balance (V E F F5 F6 F7 : ℕ)
    (h_euler : V + F = E)
    (h_reg : 3 * V = 2 * E)
    (h_faces : F = F5 + F6 + F7)
    (h_edges : 2 * E = 5 * F5 + 6 * F6 + 7 * F7) :
    F5 = F7 :=
  klein_bottle_defects_balance V E F F5 F6 F7 h_euler h_reg h_faces h_edges

/-- On a sewn boundary state, the algebraic chiral index vanishes,
    paralleling the Euler defect balance (F5 = F7). -/
theorem sewn_chiral_balance (s : BoundaryState) (h : isSewn s) :
    chiralIndex s = 0 :=
  sewn_boundary_chiral_index_vanishes s h

/-- The defect trace vanishes on sewn states, paralleling the
    Euler defect balance. -/
theorem sewn_defect_zero (s : BoundaryState) (h : isSewn s) :
    Matrix.trace (tilt * (switch * s.rho * switch - s.rho)) = 0 := by
  have hci : chiralIndex s = 0 := sewn_boundary_chiral_index_vanishes s h
  exact boundary_defect_trace_zero_iff s |>.mpr hci

/-- Synthesis: both topological (Euler) and algebraic (sewing) constraints
    express neutralization of non-orientable frustration. -/
theorem topological_algebraic_neutralization (V E F F5 F6 F7 : ℕ)
    (h_euler : V + F = E)
    (h_reg : 3 * V = 2 * E)
    (h_faces : F = F5 + F6 + F7)
    (h_edges : 2 * E = 5 * F5 + 6 * F6 + 7 * F7)
    (s : BoundaryState) (h_sewn : isSewn s) :
    F5 = F7 ∧ chiralIndex s = 0 ∧
    Matrix.trace (tilt * (switch * s.rho * switch - s.rho)) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact euler_defect_balance V E F F5 F6 F7 h_euler h_reg h_faces h_edges
  · exact sewn_chiral_balance s h_sewn
  · exact sewn_defect_zero s h_sewn

end InfoGeometry.Physics.KleinEulerSewingBridge