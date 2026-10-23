# Corrected native Bruhat cover: theorem contract

The proved inverse-word quotient enumeration replaces the collided legacy
quotient map. Existing GAP witness assembly supplies group factorizations,
independently of legacy quotient injectivity. The corrected and flag word
tables currently coincide definitionally; this bridge must itself compile.

Carrier: native `SplitOctF2Aut`, its unipotent subgroup and existing
`concreteBruhatCell`. Invert each certified factorization, swapping the two
subgroup factors, to obtain cell membership at the inverse Weyl representative.
The existing `weylNF_inv_exists` keeps this anchor in the twelve Weyl forms.
Surjectivity of `correctedCosetEquiv` and right subgroup invariance then give
coverage of every native group element.

Dependencies read: `G2CorrectedCosetSignature`, `G2GAPFlagWitnessAssembly`,
`G2FlagOrbitPartitionCertificate`, `G2TwoBruhatClassification`, and
`G2TwoConcreteWeylG2`. No cell disjointness, BN2, cardinality of individual
cells, or legacy injectivity is assumed or claimed. Parent compilation and
independent QA locked rerun passed (9070 jobs). All four transitive axiom
reports contain exactly `propext`, `Classical.choice`, `Quot.sound`.
Independent semantic review passed; QA accepted coverage only. Zero own-source
warnings, 77 existing dependency/package warnings, and zero screening traps.
