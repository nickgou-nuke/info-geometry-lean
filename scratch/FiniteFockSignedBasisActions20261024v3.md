# Signed finite Fock basis actions v3

Exact diagnostic read:
/tmp/qa-a-fock-signed-basis-v2-y85og_mg/compile.log.
The sole reported Lean error is line82:46: unresolved disjointness placeholder
in change ({i}).disjUnion S _. Replace it with the explicit existing proof
Finset.disjoint_singleton_left.mpr hi. No mathematical change.

Only that proof argument and the version comment differ from v2. Same exact
permutation sign, native carrier and operators, all theorem statements, imports,
and hypotheses. No new warnings reported in the v2 log; the failed run is not
claimed as acceptance of the whole file. V3 is uncompiled.

New sandbox files only, force-staged. No builds/tests/live edits. V1/v2 and the
AA-passed adjointness candidate remain frozen and preserved. Parent serial QA
must validate v3 before promoting the dependency used by adjointness.
