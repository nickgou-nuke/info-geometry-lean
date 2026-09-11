import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentBasedLoopHomotopyQuotientConcatenation

namespace InfoGeometry.Topology

/-!
# Reversal readouts for the based-loop homotopy quotient

The endpoint-fiber reversal homeomorphism already exists in the native owner.
This bridge exposes its representative formula and its interaction with the
canonical based-loop quotient map.
-/

theorem symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph_mk
    {X : Type} [TopologicalSpace X] {x : X}
    (γ : SymbolicLatentBasedLoopPath x) :
    symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x
        (basedLoopHomotopyQuotient_mk γ) =
      ⟨symbolicLatentPathHomotopyQuotientMap
          (reverseSymbolicLatentPath γ.1), by
        rw [symbolicLatentPathHomotopyEndpointMap_mk]
        change (reverseSymbolicLatentPath γ.1).endpoints = (x, x)
        apply Prod.ext
        · change (reverseSymbolicLatentPath γ.1).start = x
          rw [reverseSymbolicLatentPath_start]
          exact γ.2.2
        · change (reverseSymbolicLatentPath γ.1).finish = x
          rw [reverseSymbolicLatentPath_finish]
          exact γ.2.1⟩ := by
  apply Subtype.ext
  change reversePathHomotopyQuotientHomeomorph
      (symbolicLatentPathHomotopyQuotientMap γ.1) = _
  rw [reversePathHomotopyQuotientHomeomorph_apply,
    reversePathHomotopyQuotientMap_mk]

theorem symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom_mk
    {X : Type} [TopologicalSpace X] {x : X}
    (γ : SymbolicLatentBasedLoopPath x) :
    symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom x
        (basedLoopHomotopyQuotient_mk γ) =
      symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x
        (basedLoopHomotopyQuotient_mk γ) :=
  rfl

theorem symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph_involutive
    {X : Type} [TopologicalSpace X] {x : X}
    (q : SymbolicLatentBasedLoopHomotopyQuotient x) :
    symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x
        (symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x q) = q := by
  exact (symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x).left_inv q

end InfoGeometry.Topology
