/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Finite two-cell Kitaev pairing: bulk and boundary witnesses

A four-coordinate real/integer finite shadow of the tuned two-cell chain.
The bulk couples only coordinates 1 and 2; coordinates 0 and 3 remain
decoupled. These are *exact finite matrix identities*, not a proof of
topological protection, a spectral gap, or arbitrary-chain bulk-edge duality.
-/

namespace InfoGeometry.Canonical.KitaevTwoCellBoundary

open Matrix

abbrev Mat4Z := Matrix (Fin 4) (Fin 4) ℤ

/-- Local inter-cell bond (interior coordinates 1 and 2). -/
def bulkBond : Mat4Z :=
  !![0, 0, 0, 0;
     0, 0, 1, 0;
     0, 1, 0, 0;
     0, 0, 0, 0]

/-- Independent boundary support projections. -/
def leftEdge : Mat4Z :=
  !![1, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

def rightEdge : Mat4Z :=
  !![0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 1]

def interiorSupport : Mat4Z :=
  !![0, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 0]

/-- Exact decomposition of the finite two-cell carrier. -/
theorem support_partition :
    leftEdge + interiorSupport + rightEdge = 1 := by
  decide

theorem edge_idempotents :
    leftEdge * leftEdge = leftEdge ∧
    rightEdge * rightEdge = rightEdge ∧
    leftEdge * rightEdge = 0 ∧
    rightEdge * leftEdge = 0 := by
  decide

/-- Both boundary projections are annihilated on both sides. -/
theorem bulk_annihilates_edges :
    bulkBond * leftEdge = 0 ∧
    leftEdge * bulkBond = 0 ∧
    bulkBond * rightEdge = 0 ∧
    rightEdge * bulkBond = 0 := by
  decide

/-- The bulk bond squares to its two-dimensional interior support. -/
theorem bulk_square : bulkBond * bulkBond = interiorSupport := by
  decide

/-- The edge support is precisely an algebraic zero-mode sector. -/
theorem boundary_support_annihilated :
    bulkBond * (leftEdge + rightEdge) = 0 ∧
    (leftEdge + rightEdge) * bulkBond = 0 := by
  rcases bulk_annihilates_edges with ⟨hl, hll, hr, hrr⟩
  constructor
  · rw [mul_add, hl, hr, add_zero]
  · rw [add_mul, hll, hrr, add_zero]

end InfoGeometry.Canonical.KitaevTwoCellBoundary
