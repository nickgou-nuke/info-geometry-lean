# Native signature cell separation: theorem contract

Use `G2CorrectedCosetSignature.cosetSignature`, the twelve existing
`G2QuotientOrbitSeparation.orbitWeylRepresentative` anchors, and the 64
`G2TwoSylowSubgroup.PCWordExp` words on the native automorphism carrier.
The finite leaf is: equality of the signature of `pcWord a * W k` with that
of `W l` implies `k=l`. The parent kernel decision check passed. It compares
9216 finite cases, not ambient group elements.

The subgroup property reduces the existing three-word separation premise to
one word. Right-subgroup signature invariance removes the final factor.
The existing quotient-orbit separation theorem then gives disjoint double
cosets. No legacy quotient injectivity, cell disjointness, or cover assumption
is used. Failed computation requires inspecting the conventions, not adding
an inconsistent premise. The parent locked build passed (9045 jobs), with
three standard-only transitive axiom reports and zero screening traps.
Independent semantic review and QA passed. QA reran the locked audit (9045
jobs), confirmed all three standard-only axiom reports, zero own-source
warnings, 75 existing dependency/package warnings and zero screening traps.
Acceptance is scoped to the finite separation and its two structural transports.

Together with `G2CorrectedBruhatCover.concrete_cover`, these results replace
the legacy collided quotient-enumeration route. The old conditional theorem
`G2BruhatClassificationMaster.bruhat_covering_is_entire_group` remains a valid
implication but its legacy injectivity premise is not the route used here.
No claim about BN2 or individual cell cardinalities follows just from these
two new owners.
