import InfoGeometry.Algebra.OSp12
import InfoGeometry.Canonical.FibonacciParafermionAtoms

noncomputable section

namespace InfoGeometry.Algebra.OSp12BulkBoundaryBridge

open InfoGeometry.Algebra.OSp12

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-!
Thin bulk/boundary readback for the operator-first `osp(1|2)` tripotent lane.

This file does not add a new property model. It only packages the existing
`O^3 = O` projector split from `InfoGeometry.Algebra.OSp12` using the same
bulk/boundary completeness and orthogonality language already owned by
`InfoGeometry.Canonical.FibonacciParafermionAtoms`.

Witness-dependent statements about a concrete `3 × 3` carrier, its compressed
`2 × 2` active sector, or any lower-dimensional/zero-volume/topological
interpretation remain separate obligations in their own lanes.
-/

/-- The vacuum-side projector in the OSp12 tripotent split. -/
def boundaryVacuumProjector (O : Op V) : Op V :=
  projVac O

/-- The active support projector in the OSp12 tripotent split. -/
def activeSupportProjector (O : Op V) : Op V :=
  projUp O + projDown O

/-- The active support projector is exactly the tripotent square `O^2`. -/
theorem activeSupportProjector_eq_sq (O : Op V) :
    activeSupportProjector O = O ^ 2 := by
  simpa [activeSupportProjector] using supportProjector_eq (O := O)

/-- The vacuum-side projector is the complement of the active support projector. -/
theorem boundaryVacuumProjector_eq_complement (O : Op V) :
    boundaryVacuumProjector O = 1 - activeSupportProjector O := by
  simpa [boundaryVacuumProjector, activeSupportProjector] using
    vacuumComplement_eq (O := O)

/-- Bulk-plus-boundary completeness for the OSp12 tripotent split. -/
theorem bulk_boundary_completeness (O : Op V) :
    boundaryVacuumProjector O + activeSupportProjector O = 1 := by
  calc
    boundaryVacuumProjector O + activeSupportProjector O
        = projVac O + (projUp O + projDown O) := by
            simp [boundaryVacuumProjector, activeSupportProjector]
    _ = projVac O + projUp O + projDown O := by abel
    _ = 1 := projVac_add_projUp_add_projDown (O := O)

/-- Vacuum-side followed by active support vanishes under `O^3 = O`. -/
theorem bulk_boundary_orthogonal (O : Op V) (hO3 : O ^ 3 = O) :
    boundaryVacuumProjector O * activeSupportProjector O = 0 := by
  rw [activeSupportProjector_eq_sq]
  change InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_vacancy O * O ^ 2 = 0
  exact InfoGeometry.Canonical.FibonacciParafermionAtoms.bulk_boundary_orthogonal O hO3

/-- Active support followed by vacuum-side vanishes under `O^3 = O`. -/
theorem boundary_bulk_orthogonal (O : Op V) (hO3 : O ^ 3 = O) :
    activeSupportProjector O * boundaryVacuumProjector O = 0 := by
  rw [activeSupportProjector_eq_sq]
  change O ^ 2 * InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_vacancy O = 0
  exact InfoGeometry.Canonical.FibonacciParafermionAtoms.boundary_bulk_orthogonal O hO3

end OSp12BulkBoundaryBridge
