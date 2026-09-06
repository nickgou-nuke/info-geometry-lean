/-
InfoGeometry/Quantum/SouriauFoliation/ClosureInvariantLeaf.lean
-/
import InfoGeometry.OperatorAlgebra.MobiusClosureFixedPoints
import InfoGeometry.Quantum.SouriauFoliation.SymplecticLeaf

noncomputable section

namespace InfoGeometry.Quantum.SouriauFoliation

open InfoGeometry.OperatorAlgebra.MobiusClosureFixedPoints

/--
A closure/Tomita-style involution that preserves a Souriau leaf.

This reuses the existing abstract `ClosureInvolution` and does not introduce a
new modular group.
-/
structure ClosureInvariantLeaf
    {State : Type*}
    (L : SymplecticLeaf State) where
  /-- Supplied closure/Tomita/Möbius involution. -/
  closure : ClosureInvolution State

  /-- The closure sends leaf points to leaf points. -/
  closure_preserves_leaf :
    ∀ ⦃x : State⦄, x ∈ L.carrier → closure.theta x ∈ L.carrier

namespace ClosureInvariantLeaf

variable {State : Type*}
variable {L : SymplecticLeaf State}
variable (C : ClosureInvariantLeaf L)

/-- Entropy survives the supplied closure involution on the leaf. -/
theorem entropy_theta_eq
    {x : State}
    (hx : x ∈ L.carrier) :
    L.entropyReadout (C.closure.theta x) = L.entropyReadout x :=
  L.entropy_eq_of_mem (C.closure_preserves_leaf hx) hx

/-- Weyl scale survives the supplied closure involution on the leaf. -/
theorem weylScale_theta_eq
    {x : State}
    (hx : x ∈ L.carrier) :
    L.weylScaleReadout (C.closure.theta x) = L.weylScaleReadout x :=
  L.weylScale_eq_of_mem (C.closure_preserves_leaf hx) hx

end ClosureInvariantLeaf

end InfoGeometry.Quantum.SouriauFoliation
