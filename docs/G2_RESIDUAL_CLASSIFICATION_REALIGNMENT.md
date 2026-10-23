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
seventh-image identity is being traced through existing multiplication and
coordinate relations; it is not assumed from the desired cardinality.
Constructive closure remains ongoing. No new contradiction theorem is added.

Independent semantic review and QA accepted the prose-only correction. QA
compared non-comment Lean token sequences against HEAD and confirmed that
declarations and proofs are unchanged. Parent and independent locked builds
passed (9,078 jobs). Strict screening found zero traps and scoped diff checks
passed. QA reported 78 warnings: zero owner warnings, 76 dependency-source
warnings, and two package warnings. No new proof or classification closure
is certified by this correction.

The next constructive route is to prove the two pivot readbacks
`(fullPeel g (basis8 2)).y1 = false` and
`(fullPeel g (basis8 3)).x2 = false` from the existing peel formulas, then
transport the multiplication relations between basis elements to eliminate
the remaining seventh-image coordinates. This route is a source-grounded
proof proposal, not yet kernel checked. It must not use the desired
seventh-image identity to establish either pivot.
