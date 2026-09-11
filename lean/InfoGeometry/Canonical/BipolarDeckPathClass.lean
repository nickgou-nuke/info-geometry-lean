import InfoGeometry.Canonical.BipolarDeckMonodromy
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.ChiralDirectedGraphHomotopy

/-!
# The finite deck path class

The two sheets form a finite directed graph with one deck edge in each
direction.  A double traversal returns to the initial sheet.  The quotient
statement below is deliberately combinatorial: its homotopy witness is an
explicit directed two-cell, so no topological realization is being asserted.
-/

namespace InfoGeometry.Canonical.BipolarDeckPathClass

noncomputable section

open InfoGeometry.Topology
open InfoGeometry.Topology.Weyl
open InfoGeometry.Canonical.BipolarTwoSheetCore

def deckDigraph : ChiralDigraph where
  Vertex := ChiralSheet
  edge := fun u v => v = u.swap
  edge_decidable := fun u v => inferInstance
  sector := fun _ => ChiralSector.left
  allowedTransition := fun _ _ => True
  transition_decidable := fun _ _ => inferInstance
  edge_allowed := by
    intro u v _
    trivial

@[simp] theorem deck_edge (u : ChiralSheet) :
    deckDigraph.edge u u.swap := rfl

def deckPath (u : ChiralSheet) : DirectedPath deckDigraph u u.swap :=
  .cons (deck_edge u) (DirectedPath.refl (G := deckDigraph) u.swap)

def deckPathTwice (u : ChiralSheet) : DirectedPath deckDigraph u u :=
  (deckPath u).append (by simpa using deckPath u.swap)

/-! The deck action also preserves the canonical finite sheet energy. -/

def deckTransport (ψ : SheetAmplitude) : SheetAmplitude :=
  fun u => ψ u.swap

def sheetEnergy (ψ : SheetAmplitude) : ℝ :=
  ‖ψ ChiralSheet.plus‖ ^ 2 + ‖ψ ChiralSheet.minus‖ ^ 2

@[simp] theorem deckTransport_involutive (ψ : SheetAmplitude) :
    deckTransport (deckTransport ψ) = ψ := by
  funext u
  simp [deckTransport]

theorem deckTransport_energy (ψ : SheetAmplitude) :
    sheetEnergy (deckTransport ψ) = sheetEnergy ψ := by
  simp [sheetEnergy, deckTransport, add_comm]

@[simp] theorem deckPathTwice_length (u : ChiralSheet) :
    (deckPathTwice u).length = 2 := by
  cases u <;> rfl

def deckPathTwiceCell (u : ChiralSheet) :
    DirectedChiralTwoCell deckDigraph u u where
  upper := deckPathTwice u
  lower := DirectedPath.refl (G := deckDigraph) u
  compatible := by
    intro _ _ _
    trivial

theorem deckPathTwice_homotopic_refl (u : ChiralSheet) :
    DirectedChiralHomotopy (G := deckDigraph) (deckPathTwice u)
      (DirectedPath.refl (G := deckDigraph) u) := by
  exact ⟨deckPathTwiceCell u, rfl, rfl⟩

/-- Two deck traversals have the identity directed path class. -/
theorem deckPathClass_invariant (u : ChiralSheet) :
    DirectedPathClass.mk (deckPathTwice u) =
      DirectedPathClass.mk (DirectedPath.refl (G := deckDigraph) u) := by
  apply DirectedPathClass.sound
  exact Relation.EqvGen.rel _ _ (deckPathTwice_homotopic_refl u)

theorem deckPathClass_invariant_swap (u : ChiralSheet) :
    DirectedPathClass.mk (deckPathTwice u.swap) =
      DirectedPathClass.mk (DirectedPath.refl (G := deckDigraph) u.swap) := by
  exact deckPathClass_invariant u.swap

end
end InfoGeometry.Canonical.BipolarDeckPathClass
