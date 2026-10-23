# G2 residual classification: ground-truth contract

The carrier remains `SplitOctF2Aut`, with native PC recovery, unipotent
subgroup, flag action, and concrete double cosets. A scalar count or list of
formal cell weights does not replace this carrier.

`G2PCRecoveryFactorization.fullPeel_pcWord_factorization` proves
`pcWord (extractAllBits f) * fullPeel f = f` unconditionally.
`G2TwoBruhatClassification.fullPeel_mem_same_concreteBruhatCell` preserves
known double-coset membership. `fullPeel_bruhat_cover_iff` equates residual
double-coset coverage with ambient coverage. Neither asserts that an arbitrary
residual is a Weyl representative.

The overview of `G2BruhatClassificationMaster` incorrectly called its
classification unconditional. Its actual declarations have these inputs:

- `native_stabilizer_order_eq_64` and `ambient_group_order_eq_12096` require
  all eight residual basis readbacks for every flag stabilizer element.
- `explicitQuotientRepresentativeEquiv` requires residual alignment and
  ambient order 12096.
- `bruhat_covering_is_entire_group` requires quotient-representative
  injectivity and ambient order 12096.
- `residual_injectivity_all_cells` is an unconditional within-cell
  certificate; it does not supply cross-cell quotient alignment.

The edit corrects this owner's prose without changing a theorem statement or
proof. It does not claim that those inputs cannot be proved elsewhere.

`G2NativeFlagStabilizerLastBitClosure` reduces stabilizer closure to final
readbacks. Its sixth-image y0 bit already has an unconditional proof. The
seventh-image identity was initially traced through existing multiplication and
coordinate relations; it is now implemented below without assuming the desired
cardinality. No new contradiction theorem is added.

Independent semantic review and QA accepted the prose-only correction. QA
compared non-comment Lean token sequences against HEAD and confirmed that
declarations and proofs are unchanged. Parent and independent locked builds
passed (9,078 jobs). Strict screening found zero traps and scoped diff checks
passed. QA reported 78 warnings: zero owner warnings, 76 dependency-source
warnings, and two package warnings. No new proof or classification closure
is certified by this correction.

The constructive route proves the two pivot readbacks
`(fullPeel g (basis8 2)).y1 = false` and
`(fullPeel g (basis8 3)).x2 = false` from the existing peel formulas, then
transport the multiplication relations between basis elements to eliminate
the remaining seventh-image coordinates. The five pivot lemmas and two
residual-shape/seventh-image lemmas compiled in a locked build (9,019 jobs,
`/tmp/g2-residual-closure-build.log`). Neither pivot uses the desired
seventh-image identity.

The native multiplication identities used for the final elimination are
`basis8 4 * basis8 7 = basis8 2 * basis8 5`,
`basis8 2 * basis8 7 = zero`, and
`basis8 7 * basis8 5 = basis8 3`. All products are the existing split-octonion
product, transported through the actual automorphism. Four residual Boolean
coordinates are eliminated, not an assumed enumeration of the automorphism
group. Composition retains the repository's reversed function convention.

The implementation adds unconditional consequences in
`G2NativeFlagResidualClosure`: residual identity on the native flag stabilizer,
equality with `unipotentSubgroup`, quotient cardinality 189, and ambient
cardinality 12096. These consume the existing final-readback theorems and the
already proved sixth-image y0 readback. The first 11-declaration axiom audit
exposed inherited native-decision axioms in the two cardinality consequences.
Replacing native evaluation in `G2NativeCandidateSymmetry` and
`G2IntrinsicBaseLineCensus.admissiblePairs_card` with kernel evaluation removed
them: a fresh locked build passed (9,020 jobs), and all eleven declarations
report exactly `propext`, `Classical.choice`, and `Quot.sound`.
Independent semantic review passed the proof, census repair, and final lint
cleanup. Independent QA accepted this bounded result after rerunning the locked
build (9,020 jobs, exit 0, `/tmp/g2-residual-closure-qa.log`). All eleven
transitive axiom reports individually contain exactly the three standard
axioms. Strict screening found zero traps in the five touched Lean files;
scoped staged/worktree diff checks passed and source hashes remained unchanged
during QA. The build had 73 warnings: zero touched-source, 71 dependency-source,
and two package warnings. This is not a repository-wide clean-build claim.
This does not prove cross-cell quotient-representative
alignment or complete the Bruhat classification.

Executed repair contract: preserve every proposition and finite carrier in these
two census owners, replacing their native-decision evaluations with kernel
reduction or structural proofs. The first candidate is `decide` (with `+revert`
for bound finite coordinates), using the exact existing decidable instances.
No external enumeration, new axiom, carrier change, or cardinality assumption
is permitted. The census theorem and symmetry namespace use bounded resource
limits (`maxRecDepth 100000`, `maxHeartbeats 4000000`). The final cleanup makes
three hypothesis reversions explicit and removes two pre-existing linter
warnings. Acceptance requires rerunning the transitive axiom audit after
the downstream build, not merely scanning for tactic names.
