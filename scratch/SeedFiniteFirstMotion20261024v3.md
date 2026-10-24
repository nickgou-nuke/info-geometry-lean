# Finite-first motion v3: notation field access repair

NEW helper/consumer files only. No builds/live edits/budget changes; v1/v2 preserved.
Terminal /tmp/qa-a-finite-first-v2-w76joj0x/helper_compile.log shows naturality
passed its prior failure point, then unknown identifiers E.symm... at79/84.
No candidate warnings were reported; consumer compilation had not started.

Exact change: every field access on local notation E becomes (E).field in BOTH
files, including symm, injective and symm_apply_apply. This makes the notation
expand as an expression before field projection. Consumer import now names
scratch.FiniteExponentialMotion20261024v3. All theorem statements' mathematical
meaning, proof strategy, native state/map/flow, and1M/500k baseline unchanged.

No claim that later helper declarations or the actual seed consumer compile.
Compile helper first, then consumer with helper-v3 and accepted alignment-v2
available on the serial QA import path. No assumed naturality/faithfulness.
