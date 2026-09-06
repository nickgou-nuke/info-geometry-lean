import InfoGeometry.Canonical.CantorCylinderLattice
import InfoGeometry.Canonical.KreinProjectorLattice
import Mathlib.Order.GaloisConnection.Basic

/-!
# Lattice Completion Pathways

This file keeps only the finite completion and refinement/coarse-graining
Galois connection that are actually owned in the repository.
-/

namespace InfoGeometry.Canonical.CompletionPathway

/-- The finite completed projection lattice is complete. -/
noncomputable instance finiteProjectionCompletion_complete (n : ℕ) :
    CompleteLattice
      ((Fin n → Bool) → KreinProjectorLattice.KreinSector) :=
  inferInstance

/-- Every set of finite projection sectors has a canonical least upper bound. -/
theorem finiteProjectionCompletion_sSup_isLUB
    (n : ℕ)
    (S : Set
      ((Fin n → Bool) → KreinProjectorLattice.KreinSector)) :
    IsLUB S (sSup S) :=
  isLUB_sSup S

/-- Every set of finite projection sectors has a canonical greatest lower bound. -/
theorem finiteProjectionCompletion_sInf_isGLB
    (n : ℕ)
    (S : Set
      ((Fin n → Bool) → KreinProjectorLattice.KreinSector)) :
    IsGLB S (sInf S) :=
  isGLB_sInf S

/-- Refinement shifts a projection assignment to the next Cantor level. -/
def refineProjectionAssignment {n : ℕ}
    (P : (Fin n → Bool) → KreinProjectorLattice.KreinSector) :
    (Fin (n + 1) → Bool) → KreinProjectorLattice.KreinSector :=
  fun v => P (CantorCylinderLattice.truncateWord v)

/-- Coarse-graining meets the two child sectors above each parent. -/
def coarseProjectionAssignment {n : ℕ}
    (Q : (Fin (n + 1) → Bool) → KreinProjectorLattice.KreinSector) :
    (Fin n → Bool) → KreinProjectorLattice.KreinSector :=
  fun w => Q (CantorCylinderLattice.leftChild w) ⊓
    Q (CantorCylinderLattice.rightChild w)

/-- Refinement and coarse-graining form a Galois connection. -/
theorem projectionAssignment_galoisConnection (n : ℕ) :
    GaloisConnection (@refineProjectionAssignment n) (@coarseProjectionAssignment n) := by
  intro P Q
  constructor
  · intro h w
    apply le_inf
    · have hleft := h (CantorCylinderLattice.leftChild w)
      simpa [refineProjectionAssignment, coarseProjectionAssignment,
        CantorCylinderLattice.leftChild, CantorCylinderLattice.truncateWord,
        CantorCylinderLattice.extendWord] using hleft
    · have hright := h (CantorCylinderLattice.rightChild w)
      simpa [refineProjectionAssignment, coarseProjectionAssignment,
        CantorCylinderLattice.rightChild, CantorCylinderLattice.truncateWord,
        CantorCylinderLattice.extendWord] using hright
  · intro h v
    have hw := h (CantorCylinderLattice.truncateWord v)
    cases hlast : v (Fin.last n)
    · have hleft : v = CantorCylinderLattice.leftChild (CantorCylinderLattice.truncateWord v) := by
        rw [(Fin.snoc_init_self v).symm]
        simp [CantorCylinderLattice.truncateWord, CantorCylinderLattice.leftChild,
          CantorCylinderLattice.extendWord, hlast]
      have hle : P (CantorCylinderLattice.truncateWord v) ≤
          Q (CantorCylinderLattice.leftChild (CantorCylinderLattice.truncateWord v)) :=
        le_trans hw inf_le_left
      rw [hleft]
      simpa [refineProjectionAssignment, coarseProjectionAssignment,
        CantorCylinderLattice.truncateWord, CantorCylinderLattice.leftChild,
        CantorCylinderLattice.extendWord] using hle
    · have hright : v = CantorCylinderLattice.rightChild (CantorCylinderLattice.truncateWord v) := by
        rw [(Fin.snoc_init_self v).symm]
        simp [CantorCylinderLattice.truncateWord, CantorCylinderLattice.rightChild,
          CantorCylinderLattice.extendWord, hlast]
      have hle : P (CantorCylinderLattice.truncateWord v) ≤
          Q (CantorCylinderLattice.rightChild (CantorCylinderLattice.truncateWord v)) :=
        le_trans hw inf_le_right
      rw [hright]
      simpa [refineProjectionAssignment, coarseProjectionAssignment,
        CantorCylinderLattice.truncateWord, CantorCylinderLattice.rightChild,
        CantorCylinderLattice.extendWord] using hle

/-- Refinement/coarse-graining as a concrete Galois connection between adjacent levels. -/
def refinementCoAdjunction (n : ℕ) :
    Σ lower :
      ((Fin n → Bool) → KreinProjectorLattice.KreinSector) →
        ((Fin (n + 1) → Bool) → KreinProjectorLattice.KreinSector),
      { upper :
          ((Fin (n + 1) → Bool) → KreinProjectorLattice.KreinSector) →
            ((Fin n → Bool) → KreinProjectorLattice.KreinSector) //
        GaloisConnection lower upper } :=
  ⟨refineProjectionAssignment, coarseProjectionAssignment,
    projectionAssignment_galoisConnection n⟩

/-- The concrete refinement/coarse-graining maps form a mathlib Galois connection. -/
theorem refinementCoAdjunction_galoisConnection (n : ℕ) :
    GaloisConnection
      (@refineProjectionAssignment n)
      (@coarseProjectionAssignment n) :=
  projectionAssignment_galoisConnection n

/-- The projection refinement map preserves arbitrary joins. -/
theorem refinementCoAdjunction_lower_iSup
    (n : ℕ) {ι : Sort*}
    (P : ι → (Fin n → Bool) → KreinProjectorLattice.KreinSector) :
    refineProjectionAssignment (⨆ i, P i) =
      ⨆ i, refineProjectionAssignment (P i) :=
  (projectionAssignment_galoisConnection n).l_iSup

/-- The projection coarse-graining map preserves arbitrary meets. -/
theorem refinementCoAdjunction_upper_iInf
    (n : ℕ) {ι : Sort*}
    (Q : ι → (Fin (n + 1) → Bool) → KreinProjectorLattice.KreinSector) :
    coarseProjectionAssignment (⨅ i, Q i) =
      ⨅ i, coarseProjectionAssignment (Q i) :=
  (projectionAssignment_galoisConnection n).u_iInf

end InfoGeometry.Canonical.CompletionPathway
