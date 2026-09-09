# Upstream reconciliation ledger

This ledger records upstream functionality that has been translated into the
current native owner tree. Upstream files are treated as design evidence; only
the active owner files and kernel-checked builds count as implemented.

## Integrated native owners

| Upstream archetype | Current owner | Verification |
| --- | --- | --- |
| H3(Zorn) Jordan triple, Kantor boundary, inner derivations, native 3-graded TKK bracket, antisymmetry, self-bracket, and `(-1,-1,+1)` Jacobi slice | `Canonical/H3ZornJordanTripleBridge.lean`, `Canonical/H3ZornTKKNative.lean` | `lake build InfoGeometry.Canonical.H3ZornTKKNative` |
| F4/Peirce/triality split | `Canonical/H3ZornF4PeirceTrialitySplit.lean` | `lake build InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit` |
| Freudenthal quartic invariant | `Algebra/H3ZornFreudenthalQuartic.lean` | `lake build InfoGeometry.Algebra.H3ZornFreudenthalQuartic` |
| Peirce-0 split-spin-factor quadratic representation and SO(5,5) homothety | `Canonical/SplitAlbertPeirceZeroQuadraticRepresentation.lean`, `Canonical/SplitSpinFactorHomothetySO55.lean` | `lake build InfoGeometry.Canonical.SplitSpinFactorHomothetySO55` |
| Self-concordant Lyapunov DAG bridge | `Canonical/SelfConcordantLyapunovDAGBridge.lean` | `lake build InfoGeometry.Canonical.SelfConcordantLyapunovDAGBridge` |
| Native Zorn derivation lane and five-graded TKK socket | `Lie/CanonicalZornExceptionalTowerSocket.lean` | `lake build InfoGeometry.Lie.CanonicalZornExceptionalTowerSocket` |
| Native conformal `(6,6)` extension of the split-spin-factor carrier, including `pGen`, `kGen`, `dGen`, `rotGen`, metric bivectors, and the `p`–`k` cross bracket | `Canonical/SplitSpinFactorTKKConformalSO66.lean` | `lake build InfoGeometry.Canonical.SplitSpinFactorTKKConformalSO66` |
| Native conformal TKK parameter carrier, intrinsic `B10`-skew middle grade, test-vector separation, injective generator map, and range equivalence | `Canonical/SplitSpinFactorTKKInjectivityNative.lean` | `lake build InfoGeometry.Canonical.SplitSpinFactorTKKInjectivityNative` |

The native TKK socket contributes the verified Zorn derivation action,
faithfulness, 14-dimensional derivation readout, standard-derivation span, and
a bundled Mathlib Lie homomorphism into an abstract five-graded target. It is
kept as a socket contract, not promoted to a concrete E₇ realization without
the missing target and grade-zero proof data.

The native owners are imported by `InfoGeometry.All` where appropriate. No
compatibility copy of the obsolete upstream namespace is introduced when a
current owner already supplies the same theorem-safe functionality.

The new conformal SO(6,6) owners are also imported by `InfoGeometry.All`.
Their focused builds pass. The latest aggregate `InfoGeometry.All` attempt
reached unrelated pre-existing failures in
`Topology/ProjectiveKleinCompactification.lean` and
`Clifford/PolarizedFourVectorNeutralCarrier.lean`; no error was reported from
the new conformal owners.

## Audited but not promoted

The following upstream chains still require native API work and are not
claimed as implemented:

* `H3ZornPeirce0QuadraticRepresentation` / `H3ZornPeirce0QuadraticHomothety`:
  their proofs target obsolete coordinate constructors and zero/readback
  simp lemmas.
* `H3ZornPeirce0SO55` and `H3ZornPeirce0TKK66`: their mathematical content
  is represented in the current split-spin-factor owners, but the original
  files depend on the obsolete Peirce-0 carrier and incomplete finite-rank
  instances.
* `H3ZornJordanKantorCapstone`: the archived capstone depends on the obsolete
  `H3ZornJordanTripleG2Bridge` import.  Its kernel-relevant content is already
  covered by `H3ZornJordanTripleBridge` and `H3ZornTKKNative`, including the
  native Kantor-operator vanishing, inner-derivation law, TKK antisymmetry,
  self-bracket, and the `(-1,-1,+1)` Jacobi slice.  It is therefore retained
  as evidence rather than imported as a duplicate compatibility namespace.
* The archived Peirce/G2 chain (`SplitAlbertPeirceQuadraticRepresentation`,
  `SplitG2AlbertEntrywiseLift`, and `SplitG2AlbertJordanCompatibility`) was
  compiled directly and still has unsolved goals or type mismatches against
  the current APIs.  Its intended quadratic and derivation content is covered
  by the verified native Peirce-zero, SO(5,5), F4/Peirce, and exceptional-tower
  owners listed above; the raw chain is not promoted.
* The archived operator-Zorn twin/Weyl chain imports an upstream
  `AssociativeOperatorZornCartanPeirce`/twin carrier contract that is not the
  active owner API.  Direct checks either fail at that missing archived module
  boundary or expose proof mismatches in `TwoFourOperatorVectorZorn`; these
  files remain archived evidence rather than active imports.
* `F4LeibnizConstraintSpace` is an evidence-level finite-coordinate proposal,
  not a verified owner: direct elaboration exposes incorrect commutative-ring
  normalization over the noncommutative H3 carrier, residual type mismatches,
  and an explicitly open rank certificate.  The current F4 derivation owners
  remain the authoritative implementation.
* `SplitSpinFactorTKKSO66` remains an audited upstream namespace rather than a
  compatibility import. Its injectivity/range-equivalence functionality is now
  represented by the native conformal owner and
  `SplitSpinFactorTKKInjectivityNative`; the upstream file itself is not copied
  because it targets obsolete generator and carrier names.
* `WeylChiralHodgeCurvatureSplit` remains archived evidence.  Its immediate
  owner `OperatorWeylChiralCurvatureBlocks` is absent from the active source
  tree (both files exist only under the upstream extraction archive), so the
  candidate cannot be promoted or focused-built without importing an entire
  obsolete dependency corridor.  Its finite Weyl/Hodge statements are not
  currently connected to an active native owner.

Archived PR extraction files are evidence only and are not active imports.
Failures reported against an archived extraction must not be used as proof
that a current owner is implemented or verified.

## Aggregate status

The focused native owners above compile independently. The aggregate build has
also passed in earlier cache-complete runs with zero explicit axioms and zero
declarations depending natively on `sorryAx`; after broad aggregate rebuilds,
unrelated archived or legacy extraction targets may still surface errors. Such
errors remain open reconciliation items until their active owner and import
path are identified.

The PR161 polarized-boundary functionality is present as a native rewrite in
the active tree, rather than as a cherry-pick of the upstream branch.  The six
rewritten owners (`PolarizedMinkowski55`, `PolarizedQuadraticExtension55`,
`PolarizedBoundaryInvolutions`, `PolarizedBoundaryBivectors`,
`PolarizedBoundary55PristineChain`, and `PolarizedBoundary55Audit`) were built
together successfully with `lake build`; the audit reports only the expected
Lean foundation axioms (`propext`, `Classical.choice`, and `Quot.sound`) for
the audited declarations.  The source remains staged in the managed worktree
but cannot be restaged because `.git/index` is read-only.

The adjacent Kramers/Klein lane was also repaired against native owners:
`Pin55KramersContactMultigrading` now imports `KleinParityDeck`, and
`KleinAffineOrbitQuotient` is implemented over
`KleinQuotientDeckInvariants` with explicit local group/action instances.
The supporting `KleinDeckNormalForm` readout and affine quotient proofs were
closed without new axioms.  Focused builds of `KleinAffineOrbitQuotient` and
`Pin55KramersKleinFiveGradeClosure` both pass.

## 2026-09-06 reconciliation snapshot

The complete set of `refs/remotes/upstream/*` was inventoried with
`tools/upstream_snapshot_inventory.sh`.  The snapshot contained 336 refs and
22,071 unique upstream Lean paths.  The active tree contains 22,173 Lean paths;
133 real upstream Lean paths were absent and were preserved as source evidence
under `archive/upstream_snapshot_20260906/`, together with provenance tables.
These archived files are not imported automatically: each candidate still
requires a native-owner review and a focused kernel build before promotion.

Two concrete owner repairs from the aggregate gate are now verified:

* `Clifford/PolarizedFourVectorNeutralCarrier.lean` has explicit nested
  product inverse proofs and the sign-corrected coordinate map proof.
* `Topology/ProjectiveKleinCompactification.lean` proves the fourth Möbius
  power using the noncommutative matrix normalization appropriate to matrix
  multiplication.

Focused builds for both owners and the aggregate `InfoGeometry.All` build pass
on the current worktree.  Git staging is currently unavailable because the
managed environment exposes `.git/index` read-only; this affects staging only,
not Lean source verification.

The O(5,5) multigraded audit was repaired against the active native owner names.
Its imports now include the two-boundary readout, the Pin/glide bridge, and the
canonical pristine chain; stale references were replaced by
`contact_grade_count_agrees_with_native_o55` and `native_o55_bridge_packet`.
The focused audit/pristine-chain build completed successfully (8188 jobs).
Its axiom report contains only the expected Lean foundation axioms plus
`Lean.ofReduceBool`/`Lean.trustCompiler` on native-computation-backed
declarations; no `sorryAx` was reported.

The split-octonion associator lane now has a native owner,
`OperatorAlgebra/SplitOctonionOddAssociator.lean`, imported by the operator
algebra aggregate.  It proves the valid odd-sector diagonal readout: the two
diagonal associator entries are opposite sums of upper/lower scalar triple
products.  A proposed theorem asserting that all off-diagonal components vanish
was rejected after kernel expansion produced nonzero symbolic residuals; that
stronger claim is not promoted without additional hypotheses.  The focused
owner build passed (`3103` jobs).

The H3/Kantor upstream lane now has a native capstone owner,
`Canonical/H3ZornJordanKantorCapstone.lean`, wired into `Canonical/All.lean`.
It packages the currently proved Kantor boundary vanishing, native inner
derivation property/skewness, and triple Leibniz law.  It intentionally does
not promote an unsupported dimension or exceptional-Lie identification.
The focused capstone build passed (`8047` jobs).

Two further upstream Peirce PR paths were restored as compatibility owners:
`SplitAlbertPeirceQuadraticRepresentation.lean` delegates to the native
fixed-tripoten quadratic representation, while
`SplitAlbertPeirceZeroQuadraticHomothety.lean` delegates to the native
split-spin-factor homothety.  Their statements preserve the current native
normalization (the homothety scales by `splitInterval10 u ^ 2`), rather than
silently importing the upstream normalization.  Both focused builds passed.

The upstream `SplitG2AlbertEntrywiseLift` path now has a native compatibility
owner delegating to `SplitG2AlbertEntrywiseBridge`.  It proves the three
diagonal-annihilation readouts for the entrywise lift and is wired into the
canonical aggregate.  The separate upstream Jordan-compatibility claims remain
unpromoted because the active bridge explicitly treats product preservation as
a frontier.  The focused lift build passed (`8131` jobs).

The upstream H3 Peirce-zero triple restriction now has a compatibility owner
at `Canonical/H3ZornPeirceZeroJordanTripleRestriction.lean`, delegating to the
native Split-Albert restriction.  Both closure theorem names are restored and
the owner is wired into `Canonical/All.lean`.
The upstream-only `H3ZornJordanTripleG2Bridge` path is now restored as a
compatibility owner.  It re-exports the active Jordan triple outer symmetry
and Kantor-boundary identity.  The upstream G₂-triple derivation declaration
is intentionally not re-exported: the active entrywise G₂ owner does not
prove Jordan-product preservation, so that claim remains a documented
frontier rather than an unsupported theorem promotion.
The upstream-only `F4LeibnizConstraintSpace` path is restored as a native
compatibility owner over `F4LeibnizConstraintSpaceBridge`.  Its readout and
residual-zero theorem compile; the upstream flattened rank certificate remains
explicitly open and is not claimed.
After refreshing the snapshot inventory, the unresolved real upstream-only
Lean path count is 116 (down from 133).  The two latest restored paths are no
longer in the missing set; the remaining set is dominated by speculative
capstones and a small number of explicit mathematical frontiers.
The upstream G₂ exported flag-action pair was inspected but not promoted:
the active `G2ExportedIncidenceGenerator` proves the exported CAS point
permutations fail the parabolic incidence predicate.  Consequently the
upstream `flagPerm` constructions are ill-typed under the native owners; the
cluster remains an explicit contradiction/frontier rather than an axiom-backed
integration.
The top-level `B3PresentedGroup`, `YangBaxterQSwap`, `YangBaxterZornBridge`,
and `ZornScalingFlow` entries are symlinks to unavailable `/media/...`
artifacts.  Their functional implementations already exist under
`InfoGeometry.Physics.*`; the external symlinks were not replaced because
their targets are outside the writable repository and the target provenance
is not available.

PR165 (`Exterior_Cyclotomic_Peirce_PR165.zip`, commit
`ce133f86007fab8ce73c0ddc39a26cbe8138ca60`) was inspected from the supplied
archive.  Its five proposed owners are not currently integrated: the finite
corner reconstruction can be repaired locally, but the fourth-root projector
owner does not elaborate against the pinned Mathlib/API surface (scalar-action
inference timeouts, phase normalization goals, and matrix-literal reduction
goals).  The unverified overlay was removed from live `lean/` after the
focused build failed; the archive remains the authoritative provenance.  No
PR165 declaration is promoted until a native rewrite passes kernel checking.

The archived `Canonical/OperatorPauliLubanskiLift.lean` was tested as a
candidate restoration.  It does not elaborate against current owners: it
references removed `FiniteJonesModel` projector identifiers and leaves
multiple Pauli matrix normalization goals unresolved.  It was not promoted;
the finite Pauli--Lubanski lift remains a native-rewrite frontier.

Preservation record: the rejected overlay's intended functionality is retained
as a rewrite contract rather than discarded.  Its dependency chain is
`FiniteJonesModel`/Jones projectors -> Clifford Pauli generators -> finite
Lorentz generators -> Pauli--Lubanski operator and Casimir identities.  The
mathematical target is a finite, kernel-checked lift of the Pauli--Lubanski
vector with explicit normalization and commutator conventions, using the
current native Clifford/Lorentz owners and the existing finite physics bridge.
The archived source remains available under the upstream snapshot for exact
reference; no theorem from the failed overlay is treated as implemented.
