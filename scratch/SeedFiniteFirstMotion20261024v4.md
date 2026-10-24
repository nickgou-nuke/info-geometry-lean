# Finite-first motion v4: explicit star-equivalence map equation

NEW files only; preserve v3 and native owners. No builds, transparency/budget changes.
Log: /tmp/qa-a-finite-first-v3-k_y4dkp2/helper_compile.log line96.
The finite motion proof selected inherited injectivity whose target uses
ofMatrixStarAlgEquiv.toRingEquiv applications; hz retains star-algebra-equivalence
applications. Source evidence reports a coercion mismatch, not a false theorem.
Generic naturality, finite-dimensionality and continuity got past prior failures;
consumer was not run.

Repair ONLY finiteStage_exists_path_move: first prove the explicitly typed
star-equivalence equality E(H*x-x*H)=E(0) by map_sub/map_mul/map_zero and hz.
Apply congrArg with E.symm, then the exact StarAlgEquiv.symm_apply_apply laws.
This avoids inherited .injective selecting a different coercion projection.
No new assumed equality, theorem weakening or alternate carrier.
Consumer v4 changes only helper import to scratch.FiniteExponentialMotion20261024v4.
Everything remains uncompiled until parent serial QA; limits stay1M/500k.
