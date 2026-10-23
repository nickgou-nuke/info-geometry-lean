# Existing constructive replacements: source review

This record classifies three selected inventory candidates. It does not certify
the whole repository or claim that the lexical inventory is exhaustive.

## Ground-truth contracts and dispositions

### Sugawara finite-window obstruction

`Canonical/SugawaraFiveGradingObstruction` proves the mode-shift law
`[L_n, J_m] = -m • J_(n+m)` and its consequence for a proposed five-mode
boundary. Its direct consumer `Canonical/CompletedCurrentRepresentationBridge`
already supplies the constructive replacement: the integer-indexed completed
current mode carrier, its injective indexing, the native Heisenberg Lie
representation on charged Fock space, and
`virasoro_lgen_acts_on_completedCurrent` for every integer pair.

`Canonical/CurrentSugawaraBridge.chargedFockSpaceCurrentHeisenbergRep` constructs
the Heisenberg datum from the universal enveloping algebra action, including
local truncation and the commutator law. This is not merely an assumed datum.
`CurrentHeisenbergRep.currentSugawaraRepresentation` is a native Lie algebra
homomorphism. The central term vanishes at global modes -1, 0, 1; that fact
does not close a mixed five-mode current truncation.

Disposition: reuse the full-mode construction. The completed-current range is
a mode carrier; its readout is not asserted to be an algebra homomorphism from
the locally finite matrix multiplication to the centrally extended algebra.
No finite quotient or five-grading identification is established here.

### Uniform Zorn scaling

`Canonical/ThreeColorZornScalingObstruction` uses upper weight q and lower
weight q inverse. `Physics/ZornScalingFlow` uses a unit parameter p with
effective weight q = p squared. Its
`zornScale_mul_iff_pow_six_eq_one` proves full multiplication preservation
exactly when p to the sixth power is one. These parameter conventions must
not be conflated. General parameters still preserve the composition norm.

The same owner constructs `torusFlow` with three upper weights p, q, and
(pq) inverse and inverse lower weights. `torusFlow_one`, `torusFlow_comp`,
`torusFlow_norm`, and `torusFlow_mul` give the genuine determinant-one torus
alternative on the original complex Zorn carrier. Disposition: reuse these
existing constructions, without introducing a scalar proxy or asserting that
every norm-preserving transformation preserves multiplication.

### Indefinite Hodge kernels

`HodgeCohomology/KreinHodgeObstruction` retains the nonzero exact harmonic
witness on `Plane = DoubledSpace ℝ`. `KreinNullContraction` already constructs
a bounded homotopy h with d h + h d = 1 and h squared zero, decomposes every
state, and proves unique primitives normalized by h y = 0. The homotopy is
not the indefinite adjoint. `nullComplex_exact` and
`nullComplex_homology_zero` establish exactness and zero homology separately.

Disposition: covered by the existing contraction. Positive-adjoint Hodge
results and symmetry-compatible Krein kernel results have different
hypotheses; none identifies all indefinite harmonic states with unique
homology representatives.

## Verification scope

The new `Canonical.ExistingConstructiveReplacementsAudit` imports the existing
owners and requests axiom reports for the full-mode and scaling replacements.
It adds no theorem aliases or alternative carriers. The parent locked build
and independent QA rerun both passed (8,967 jobs). All eight axiom reports
contain only `propext`, `Classical.choice`, and `Quot.sound`. Independent
semantic review passed. Strict screening found zero traps, and scoped diff
checks passed. QA counted 127 warnings: zero from this audit, 125 from
dependency sources, and two package warnings.

The null contraction has its existing `KreinNullContractionAudit`; it is not
duplicated or rerun here. Its disposition above is a source review. Acceptance
of the new audit is scoped to the eight printed declarations and imports,
not a claim of repository-wide coverage.
