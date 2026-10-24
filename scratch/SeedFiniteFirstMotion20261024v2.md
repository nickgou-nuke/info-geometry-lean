# Finite-first motion v2: helper API repair

New files only; originals unchanged. No builds/live edits or budget changes.
Terminal evidence: /tmp/qa-a-finite-first-motion-2dduklm9/helper_compile.log.
Consumer was not compiled; helper stopped after the three naturality errors.

Exact helper changes:
1. Use (f.restrictScalars Real).toLinearMap.map_smul for real scalar transport;
   AlgHom has no projected map_smul field in this environment.
2. Install the local NormedAlgebra Rat B via
   NormedAlgebra.restrictScalars Rat Complex B, alongside the existing Rat A.
   This supplies the codomain Algebra Rat B required by NormedSpace.map_exp.

Keep naturality statements, finite carrier and finite witness unchanged.
Retain map_neg/hr/map_smul in the final simp: their unused warnings occurred
while map_exp could not elaborate; do not remove necessary downstream rewrites
on the basis of that cascading failure. No linter suppression.

Consumer v2 changes ONLY its import to scratch.FiniteExponentialMotion20261024v2.
It still imports accepted alignment-v2 and native seed faithfulness, and retains
the exact actual seed map/flow/all-beta nonzero-tilt conclusion. No new assumed
naturality, faithfulness or state. Native owners and older scratch files untouched.

Both v2 files remain uncompiled. QA should compile helper v2 first and only then
consumer v2, with the helper and alignment scratch oleans on its import path.
Budgets stay at existing1M/500k. No claim later helper declarations or consumer
passed, since the previous terminal stopped before those were checked.
