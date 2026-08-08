import Mathlib.Analysis.InnerProductSpace.Adjoint
import InfoGeometry.Topology.AmplituhedronBoundary

/-!
# CuntzWeylUHFBridge

Assumption-carrying bridge between a hyperbolic `Z₂` grading and a Cuntz-style
shift operator.

This file is intentionally finite and explicit:

* the hyperbolic cell carries the grading operators `e_plus` and `e_minus`;
* the left shift `S_L` is declared odd with respect to the induced grading;
* the Weyl/Cuntz reflection identity is a direct readout of that oddness;
* the trace corollary is linear, so it needs no proof placeholder.

The file does not claim a derivation of the grading from the conformal null-pair
lane.  That would be a stronger theorem than the current owner surfaces provide.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzWeylUHFBridge

open scoped BigOperators

/-- A minimal hyperbolic cell carrying the chiral grading operators. -/
structure HyperbolicCell (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  e_plus : H →L[ℂ] H
  e_minus : H →L[ℂ] H

/--
Bundle of the finite Weyl/Cuntz reflection data.

The oddness of `S_L` is a property, not a derived theorem.
-/
structure CuntzWeylSystem (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  cell : HyperbolicCell H
  S_L : H →L[ℂ] H
  S_R : H →L[ℂ] H
  J_swap : cell.e_plus ∘L S_L ∘L cell.e_plus = S_R
  SL_odd : (cell.e_plus ∘L cell.e_minus) ∘L S_L =
    - (S_L ∘L (cell.e_plus ∘L cell.e_minus))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (cws : CuntzWeylSystem H)

/--
Weyl-Cuntz reflection invariance.

This is the direct application of the oddness property in the package.
-/
theorem weyl_cuntz_reflection_invariance :
    (cws.cell.e_plus ∘L cws.cell.e_minus) ∘L cws.S_L =
      - (cws.S_L ∘L (cws.cell.e_plus ∘L cws.cell.e_minus)) := cws.SL_odd

/--
Plabic/BCFW-style comparison packet to transport on-shell combinatorics into the
Weyl-Cuntz reflection identity.

`bcfwReadout` is a user-supplied comparison datum (typically obtained from the
amplituhedron/combinatorial lane):
- if the `Amplituhedron3Point` boundary packet closes (or is otherwise shown to
  support plabic square symmetry), then the same sign flip is read as the Weyl
  operator reflection.
-/
structure PlabicReflectionPacket (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (Op : Type*) [Ring Op]
    (amp : InfoGeometry.Topology.AmplituhedronBoundary.AmplituhedronBoundaryPacket Op)
    (cws : CuntzWeylSystem H) where
  bcfwReadout : Op
  bcfwReadout_eq_amplituhedron : bcfwReadout = amp.bcfwReadout
  readoutToOperator : Op → H →L[ℂ] H
  readoutToOperator_eq_reflection :
    readoutToOperator bcfwReadout =
      (cws.cell.e_plus ∘L cws.cell.e_minus) ∘L cws.S_L
  reflection_of_readout :
    readoutToOperator bcfwReadout =
      -(cws.S_L ∘L (cws.cell.e_plus ∘L cws.cell.e_minus))

/--
Conservative transport: given a plabic/BCFW comparison packet, and a readout of the
associated `bcfwReadout`, the Weyl-Cuntz reflection identity follows directly.
-/
theorem weyl_cuntz_reflection_from_bcfw_packet
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Op : Type*} [Ring Op]
    (amp : InfoGeometry.Topology.AmplituhedronBoundary.AmplituhedronBoundaryPacket Op)
    (cws : CuntzWeylSystem H)
    (P : PlabicReflectionPacket H Op amp cws) :
    (cws.cell.e_plus ∘L cws.cell.e_minus) ∘L cws.S_L =
      - (cws.S_L ∘L (cws.cell.e_plus ∘L cws.cell.e_minus)) := by
  calc
    (cws.cell.e_plus ∘L cws.cell.e_minus) ∘L cws.S_L =
        P.readoutToOperator P.bcfwReadout :=
      P.readoutToOperator_eq_reflection.symm
    _ = -(cws.S_L ∘L (cws.cell.e_plus ∘L cws.cell.e_minus)) :=
      P.reflection_of_readout

/--
Trace parity match for the Weyl/Cuntz bridge.

This uses only linearity of the trace functional.
-/
theorem weyl_signum_cuntz_parity_match
    (trace : (H →L[ℂ] H) →ₗ[ℂ] ℂ) :
    trace ((cws.cell.e_plus ∘L cws.cell.e_minus) ∘L cws.S_L) =
      - trace (cws.S_L ∘L (cws.cell.e_plus ∘L cws.cell.e_minus)) := by
  rw [weyl_cuntz_reflection_invariance cws]
  exact trace.map_neg (cws.S_L ∘L (cws.cell.e_plus ∘L cws.cell.e_minus))

end InfoGeometry.Canonical.CuntzWeylUHFBridge
