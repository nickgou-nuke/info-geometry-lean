# Rohozhkin Delaunay Braiding Spec

This note records the theorem-safe Rohozhkin/Delaunay braid corridor currently
available in the repo.  It is a rational Delaunay flip and pure-braid
presentation boundary, not a WRT/TQFT, Rokhlin, Majorana, or Fibonacci anyon
theorem.

## Closed Surface

- `InfoGeometry.Topology.Delaunay.pentagon_appendix_identity`
  proves the Appendix A five rational `3 x 3` pentagon transport matrices
  multiply to `1` under explicit nonzero denominator hypotheses.
- `InfoGeometry.Topology.Delaunay.rohozhkin_invariant_under_pentagon_move`
  proves that a witnessed five-flip pentagon deletion preserves the
  `rohozhkinMatrix` word evaluation.
- `InfoGeometry.Topology.Delaunay.appendix_pentagon_delaunay_equiv`
  packages the Appendix A five-flip block as a single `DelaunayEquiv` step.
- `InfoGeometry.Topology.Delaunay.tiling_pentagon_braid_readout`
  gives the named tiling-pentagon braid readout: deleting the witnessed
  Appendix A pentagon block preserves the rational transport matrix.
- `InfoGeometry.Topology.RohozhkinBoundary.pureBraidMatrixRepresentationOfRelators`
  descends any generator assignment to a presented pure-braid matrix
  representation once all pure-braid relators evaluate to `1`.
- `InfoGeometry.Topology.RohozhkinRepresentation.RohozhkinDelaunayBraidingSpec`
  records exactly the remaining data for a nontrivial Rohozhkin representation:
  a generator assignment and a relator proof.

## Witnesses

- `tools/sympy/rohozhkin_pentagon_matrices.py`
  checks the inverse flip, far-commuting block readout, symbolic Appendix A
  pentagon product, and one rational example.  It exits nonzero if any check
  fails.
- `tools/sympy/penrose_braid_lorentz_finite_packet.py`
  checks the separate finite five-label pentagrid reflection and `S3` braid
  quotient readout.

## Assumptions Needed For The Next Layer

- Construct the nontrivial Rohozhkin generator assignment
  `PureBraidGenerator (moving + 3) -> MatrixUnits (2 * moving + 1)`.
- Prove that this assignment satisfies every relator in
  `PureBraid.pureBraidRelations`.
- Connect geometric Delaunay motions to witnessed `DelaunayFlipWord`s with
  admissibility data.
- If a TQFT/Rokhlin/Majorana interpretation is desired, separately formalize:
  framed link closure or surgery data, spin structures on the 3-manifold,
  the Rokhlin invariant/mod-2 Dirac index, and an actual functorial comparison
  from the rational Delaunay representation to the chosen TQFT representation.

## Explicit Non-Claims

- No Yang-Baxter theorem is derived from the Rohozhkin matrices here.
- No Markov-move invariant or knot invariant is proved here.
- No completed nontrivial pure-braid homomorphism is constructed here.
- No identification with Witten-Reshetikhin-Turaev, Rokhlin, MZM, black-hole,
  or Fibonacci anyon data is claimed here.
