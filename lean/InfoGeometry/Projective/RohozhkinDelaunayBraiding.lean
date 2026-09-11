import InfoGeometry.Topology.RohozhkinDelaunayBraiding
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Rohozhkin Delaunay Braiding Projective Bridge

This module is a conservative projective-facing readout for the
Rohozhkin/Delaunay braid lane.

It does not construct the full Rohozhkin generator assignment, does not prove a
geometric Delaunay-motion theorem, and does not identify the rational matrices
with Fibonacci anyons, Majorana zero modes, horizon dynamics, or a unitary
scrambling model.

#### BUCKET 1: CLOSED FINITE THEOREMS
- `appendix_pentagon_matrix_identity_readout`: the Appendix A five-flip
  rational pentagon block from the topology owner evaluates to `1`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
- `completed_rohozhkin_spec_descends_readout`: a completed source spec with all
  pure-braid relators proved descends to a presented-group representation.
- `rohozhkin_fibonacci_mzm_readout_of_compatibility`: an explicit compatibility
  equality is the only bridge from a Rohozhkin matrix to a selected
  Fibonacci/MZM readout.

#### BUCKET 3: OPEN CLOSURE DEBT
- Transcribe and own the full `(2n+1) x (2n+1)` Rohozhkin generator matrices.
- Prove the relator checks for the nontrivial generator assignment.
- Formalize the Euclidean Delaunay general-position and flip-event geometry.
- Provide a separate comparison theorem before any Fibonacci/MZM interpretation.
-/

namespace InfoGeometry.Projective.RohozhkinDelaunayBraiding

open InfoGeometry.Topology.Delaunay
open InfoGeometry.Topology.PureBraid
open InfoGeometry.Topology.RohozhkinBoundary
open InfoGeometry.Topology.RohozhkinRepresentation

/--
Projective-facing readout of the closed Appendix A pentagon calculation.

This is only the rational `3 x 3` five-flip block already proved in
`InfoGeometry.Topology.RohozhkinDelaunayBraiding`.
-/
theorem appendix_pentagon_matrix_identity_readout
    (zi zj zk zl zm : ℚ)
    (h_il : zi - zl ≠ 0)
    (h_ik : zi - zk ≠ 0)
    (h_km : zk - zm ≠ 0)
    (h_jm : zj - zm ≠ 0)
    (h_jl : zj - zl ≠ 0) :
    rohozhkinMatrix
        (InfoGeometry.Topology.RohozhkinDelaunayBraiding.appendixPentagonWord
          zi zj zk zl zm) =
      (1 : Matrix (Fin (rohozhkinDim 1)) (Fin (rohozhkinDim 1)) ℚ) :=
  InfoGeometry.Topology.RohozhkinDelaunayBraiding.appendixPentagonWord_matrix_eq_one
    zi zj zk zl zm h_il h_ik h_km h_jm h_jl

/--
A completed Rohozhkin source spec descends to a matrix representation of the
presented pure braid group.

The nontrivial work is in the explicit premise `S`: it contains the generator
assignment and the relator proof required by the topology owner.
-/
theorem completed_rohozhkin_spec_descends_readout {moving : ℕ}
    (S : RohozhkinDelaunayBraidingSpec moving) :
    ∃ ρ : RohozhkinPureBraidGroup moving →* RohozhkinMatrixUnits moving,
      ∀ g : PureBraidGenerator (rohozhkinTotalPoints moving),
        ρ (of g) = S.gen g :=
  RohozhkinDelaunayBraidingSpec.descent_packet S

/--
The only theorem-safe Fibonacci/MZM bridge at this layer.

If a separate comparison theorem supplies an equality between a Rohozhkin
rational matrix readout and a chosen Fibonacci/MZM phase, then the chosen phase
can be read out.  This theorem intentionally proves no comparison by itself.
-/
theorem rohozhkin_fibonacci_mzm_readout_of_compatibility
    {moving : ℕ} {Phase : Type*}
    (phaseOfMatrix : Matrix (Fin (rohozhkinDim moving)) (Fin (rohozhkinDim moving)) ℚ → Phase)
    (M : Matrix (Fin (rohozhkinDim moving)) (Fin (rohozhkinDim moving)) ℚ)
    (targetPhase : Phase)
    (hcompat : phaseOfMatrix M = targetPhase) :
    phaseOfMatrix M = targetPhase :=
  hcompat

end InfoGeometry.Projective.RohozhkinDelaunayBraiding
