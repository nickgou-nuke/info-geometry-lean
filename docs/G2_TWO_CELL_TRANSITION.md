# Corrected simple-reflection two-cell transition

Target: for `r` in `{s, correctedT}`, a Weyl normal form `w`, and
`g ∈ concreteBruhatCell w`, prove `r*g ∈ concreteBruhatCell w` or
`r*g ∈ concreteBruhatCell (r*w)`. This is the Weyl-restricted BN2 law,
not preservation of the union of all cells and not an ambient-anchor axiom.

Reuse `G2SignatureCompleteness` to lift a finite signature certificate.
The finite inputs are two reflections, twelve Weyl parameters, and 64 left
PC words. The certificate searches a left PC witness for either target cell;
signature equality supplies the right subgroup factor. Then absorb the
arbitrary right subgroup factor of the original cell element.

Owners inspected: `G2CorrectedCosetSignature`, `G2SignatureCompleteness`,
`G2SignatureCellSeparation`, `G2BNPair`, `G2TwoBruhatClassification`,
`G2ConcreteGeneratorInfrastructure`, and `BruhatPeelingTransport`.
Independent source tracing identified no already-proved full two-cell law
in these owners.

## Acceptance

The finite certificate and structural lift compiled successfully in the parent
locked build (9042 jobs; the certificate owner took 62 seconds). Poincare's
independent mathematical review passed. Popper's independent QA reran the
audit successfully (9042 jobs) and accepted the four-declaration scope.
Each transitive axiom report contains exactly `propext`, `Classical.choice`,
and `Quot.sound`, including the kernel `decide` certificate.
No own-source warnings; QA reported 72 dependency-source and two package
warnings. Strict screening found zero traps, and scoped diffs passed.
Logs: `/tmp/g2-two-cell-transition.log` and
`/tmp/g2-two-cell-transition-qa.log`.

This proves the two specified target cells for the corrected reflection pair
and Weyl anchors. It does not instantiate `BruhatPeeling.HasPeelingStep`, whose
anchor quantifier ranges over all ambient elements, or certify a complete
bundled BN-pair structure.
