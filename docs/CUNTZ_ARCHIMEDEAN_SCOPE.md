# Cuntz algebraic relations and split-quaternion checks

The requested `Exceptional.CuntzArchimedeanColimit` filename is retained, but
the module does not construct an Archimedean colimit. It contains only finite
algebraic consequences, using native `Ring`, `StarRing`, additive homomorphisms,
and the existing `Clifford.SplitQuaternion` owner.

Dependencies are separate branches, not the proposed causal chain:

- Two left inverses plus a partition of the identity imply cross orthogonality.
- Those relations plus a cyclic additive real-valued map force its value at
  the identity to differ from one. Thus a normalized trace on the full Cuntz
  algebra is not an available next construction. This does not exclude states
  that are not tracial, or traces on an appropriate subalgebra.
- The existing split norm evaluates `(0,0,scale,scale)` to `-2 * scale^2`;
  it is null only at zero. In contrast `(0,scale,scale,0)` is null and square-zero.
- A centered square vanishes exactly at its center; no continuum statement
  is encoded by that scalar identity.

The split norm has signature `(2,2)`, not the spacetime signature `(1,3)`.
An element whose square is one is involutive, not square-zero.
No map from Cuntz generators to these quaternion coordinates is supplied.
No detector model, Maass eigenfunction, spectral inequality, or RH implication
is established. Such connections need separately typed constructions and proofs.

Any continuum extension must use the repository's existing categorical owners
and an explicit diagram, maps and universal property. A nested union of rational
subsets and a scalar clamp on the real line do not supply that construction.

Verification status: proofs and regression tests supplied; kernel checking is
pending the shared build queue.
