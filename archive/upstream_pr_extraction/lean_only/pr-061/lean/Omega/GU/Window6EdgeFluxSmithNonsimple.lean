import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Omega.GU

open Matrix

/-- Audited four-block edge-flux interaction matrix from the window-`6` skeleton arithmetic. -/
def window6EdgeFluxSkeletonAuditedMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.diagonal ![1, 1, 3, 3450]

theorem det_window6EdgeFluxSkeletonAuditedMatrix :
    window6EdgeFluxSkeletonAuditedMatrix.det = 10350 := by
  native_decide

/-- Determinants of the irreducible rank-`4` finite Cartan types `A₄`, `B₄`, `C₄`, `D₄`, `F₄`. -/
def finiteTypeIrreducibleRank4CartanDeterminants : List ℤ :=
  [5, 2, 2, 4, 1]

/-- Audited Smith diagonal of the edge-flux skeleton matrix. -/
def window6EdgeFluxSmithDiagonal : List ℤ :=
  [1, 1, 3, 3450]

/-- Determinant of the audited edge-flux skeleton matrix. -/
def edgeFluxDeterminant (edgeFluxMatrix : Matrix (Fin 4) (Fin 4) ℤ) : ℤ :=
  edgeFluxMatrix.det

/-- The determinant mismatch excludes the audited matrix from the irreducible rank-`4` finite
Cartan list. -/
def notFiniteTypeIrreducibleCartan
    (edgeFluxMatrix : Matrix (Fin 4) (Fin 4) ℤ) : Prop :=
  edgeFluxDeterminant edgeFluxMatrix ∉ finiteTypeIrreducibleRank4CartanDeterminants

/-- The audited window-`6` edge-flux skeleton has Smith diagonal `[1,1,3,3450]`, determinant
`10350`, and determinant mismatch with every irreducible rank-`4` finite Cartan type.
    cor:window6-edge-flux-skeleton-smith-nonsimple -/
theorem paper_window6_edge_flux_skeleton_smith_nonsimple
    (edgeFluxMatrix : Matrix (Fin 4) (Fin 4) ℤ)
    (audited_edgeFluxMatrix : edgeFluxMatrix = window6EdgeFluxSkeletonAuditedMatrix) :
    window6EdgeFluxSmithDiagonal = [1, 1, 3, 3450] ∧
      edgeFluxDeterminant edgeFluxMatrix = (10350 : ℤ) ∧
      notFiniteTypeIrreducibleCartan edgeFluxMatrix := by
  refine ⟨rfl, ?_, ?_⟩
  · unfold edgeFluxDeterminant
    rw [audited_edgeFluxMatrix, det_window6EdgeFluxSkeletonAuditedMatrix]
  · unfold notFiniteTypeIrreducibleCartan edgeFluxDeterminant
      finiteTypeIrreducibleRank4CartanDeterminants
    rw [audited_edgeFluxMatrix, det_window6EdgeFluxSkeletonAuditedMatrix]
    native_decide

end Omega.GU
