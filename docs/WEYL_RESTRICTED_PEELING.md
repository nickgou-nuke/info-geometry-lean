# Subgroup-restricted peeling with subword witnesses

The existing ambient-anchor `HasPeelingStep` is stronger than the checked
native two-cell law. Add a generic theorem using its existing `InCell` carrier,
but restrict anchors to a subgroup N and require reflection generators in N.
For a word L over those generators, return a sublist K of L with
`L.prod * x ∈ B * (K.prod * n) * B`. This retains actual branch information;
an unrestricted existential ambient anchor would be vacuous.

Instantiate the theorem for the native Weyl subgroup and `{s, correctedT}`
using normal-form coverage and `G2TwoCellTransition`. No change to legacy
length conventions, ambient peeling axioms, or the incomplete `TitsSystem`
bundle is implied. Existing subword owners and `BruhatPeelingTransport` were
searched and read before this construction.

## Acceptance

Parent locked compilation and independent final QA passed (9044 jobs).
Poincare's independent mathematical review confirmed subword orientation and
subgroup scope. Popper accepted the four-declaration scope after the final
rerun. Each transitive axiom report contains exactly `propext`,
`Classical.choice`, and `Quot.sound`. Strict screening found zero traps;
scoped diff checks passed. Zero own-source warnings, 72 dependency-source
warnings, and two package warnings remain in the final QA output.
Evidence: `/tmp/g2-weyl-word-peeling.log` and
`/tmp/g2-weyl-word-peeling-final-qa.log`.

Further tracing identifies a separate length-alignment task: native
`correctedT` has parameter `(5,true)`, while the legacy one-letter second
generator has parameter `(1,true)`. This theorem makes no minimal-length claim.
A constructive continuation must explicitly reindex the parameters and prove
word evaluation and minimality before transferring legacy length claims.
