# Corrected generator word length

Legacy `toReducedWord` uses the second generator at parameter `(1,true)`;
the native corrected generator has parameter `(5,true)`. Preserve that owner
and reindex by `(k,b) ↦ (-k,b)`. Interpret Boolean true as `s` and false as
`correctedT` (opposite to the selector convention in `G2TwoCellTransition`).

Prove evaluation of the reindexed chosen word, then minimality among all
Boolean words with that native evaluation. Use a finite native multiplication
check for left-generator steps and a length-increase bound, followed by list
induction. No classification by bare cardinality or assumed minimality.
Owners inspected: `G2ReducedWords`, `G2WeylGroupEquiv`,
`G2TwoConcreteWeylG2`, and the corrected BN2 generator owner. Recursive search
for corrected length/reduced-word bridges found no duplicate in that search.
## Acceptance

Parent locked verification and independent QA passed (8990 jobs each).
Poincare's mathematical review passed, including the native basis-extensionality
checks. Popper accepted the seven-declaration scope after an independent audit
rerun. All seven transitive axiom reports contain exactly `propext`,
`Classical.choice`, and `Quot.sound`. There are zero own-source warnings,
31 dependency-source warnings, and two package warnings. Strict screening
reported zero traps and scoped diff checks passed.
Evidence: `/tmp/g2-corrected-word-length.log` and
`/tmp/g2-corrected-word-length-qa.log`.

This establishes native word evaluation, a lower bound for every Boolean word,
and attainment. It does not identify cell cardinalities or inversion-root
coordinates with native residual subgroups.
