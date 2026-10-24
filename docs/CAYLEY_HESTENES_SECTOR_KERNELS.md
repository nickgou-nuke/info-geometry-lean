# Exact Cayley–Hestenes sector kernels

Contract on the existing `CayleyHestenesGradedDatum V`, with native real
linear endomorphisms: the kernel of `CK-KC` equals the `-1` eigenspace of
`M`, and the kernel of `CK+KC` equals its `+1` eigenspace. The product `KC`
is injective because `-(CK)` is a left inverse. It commutes with `M`;
the two brackets factor as `KC*(-M-1)` and `KC*(1-M)`.

Reusing `plain_intertwiner_obstruction`, any map intertwining commuting
source operators with the target pair has range contained in the target
minus eigenspace. This supplies the exact permitted sector instead of only
commutator annihilation. It does not assert existence of every such
intertwiner or a converse from arbitrary range containment.

Source owners inspected: `CayleyHestenesGradedIntertwinerBridge`,
`CayleyHestenesWittGradedConcreteBridge`, and
`CayleyHestenesWittGradedFilteredColimitBridge`. Their existing projector
annihilation statements give inclusions. The new kernel characterization
uses the same datum and therefore applies to both the finite and colimit
instances without redefining either carrier. No exact kernel equality was
found in the inspected maintained references.

Nonvacuity: the existing concrete Witt grading is
`diag(1,-1,-1,-1,1,-1,-1,-1)` on `Fin 8 → ℝ`. The native vectors
`Pi.single 0 1` and `Pi.single 1 1` realize nonzero plus and minus sectors.
No antiunitarity, Hilbert structure, or physical symmetry is claimed.

Eight named lemmas implement the contract in
`Canonical.CayleyHestenesSectorKernels`. The companion audit includes nine
axiom requests (the new results and original obstruction) and four examples:
two nonzero eigenvectors and the two concrete kernel equalities.

Parent locked audit session 98289 exited zero (8933 jobs). Every axiom report
contains exactly `propext`, `Classical.choice`, `Quot.sound`; the new modules
produce zero warnings. Independent semantic review passed. Final independent
kernel QA session 41717 exited zero (8933 jobs), confirming all nine standard
axiom reports, four examples, zero own-source warnings, zero strict-screen
traps, and clean scoped diffs. Fourteen dependency warnings and two package
notices remain outside this addition. Accepted with the scope above.
Session-local evidence: `/tmp/cayley-sector-audit.log`, `/tmp/cayley-sector-qa.log`.
