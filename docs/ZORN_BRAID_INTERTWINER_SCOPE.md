# Native Zorn braid transport

The dependency order is mathematical, not a claim of physical causation:

```text
canonical complex Zorn product ──→ coordinate equivalence ──→ operatorEquiv
concrete LeftMulQ / LeftMulR ──→ zornPhi ──→ canonical braidRepresentation
Zorn automorphism subgroup ──→ regular-action covariance ──→ generator covariance
zornPhi + pointwise stage naturality ──→ unit-valued colimit representation
canonical coordinate intertwining + colimit readback ──→ synthesis intertwiner
```

Owners reused directly:

- `Physics/QCDCanonicalComplexZornBridge.lean`: the nonassociative product-preserving coordinate equivalence.
- `Physics/YangBaxterZornBridge.lean`: invertible braid generators and the presented-group representation `zornPhi`.
- `Canonical/CanonicalZornBraidTransport.lean`: the canonical carrier, endomorphism algebra equivalence, and conjugation covariance.
- `Canonical/SplitOctonionAutomorphism.lean`: the existing product-preserving automorphism subgroup, instantiated over `ℂ`.
- `Categorical/ZornColimitStageAction.lean`: natural stage actions and their categorical descent.

The extension in the categorical owner packages the existing stage action as
a monoid homomorphism and then transports `zornPhi` through `Units.map`.
Thus inverses and arbitrary braid words act, not just the two generators.
The synthesis theorem identifies its stage readback with the canonical-carrier
representation for every braid, including inverse braids.

The source's `LeftMulQ` squares to the identity, not zero. Its `LeftMulR`
is unnormalised and is packaged as an invertible matrix, not asserted here to
be unitary. Non-equivalence is to the particular q-scaled tensor-swap pair
specified upstream, not to every quantum-group representation. Covariance is
not invariance of each generator. No knot closure, noise protection, nuclear
shape, anomaly cancellation, or physical mass gap follows from these lemmas.

There are no new replacement carriers or axiom fields. All added declarations
have proof scripts without placeholders; kernel verification is pending the
shared build lane. Run:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Synthesis.ZornBraidIntertwinerTests
```
