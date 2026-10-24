# Motion v9: explicit native conjugation carrier

New source-only sandbox; original v8 and all native owners preserved.
Read terminal log /tmp/qa-a-seedfinitefirstmotion20261024v8-ivg4yhdo/compile.log.
V8 progressed beyond the v7 bundled-hom binder timeout. At55:8 the unitary
argument is incorrectly consumed as the explicit Type parameter of
Unitary.conjStarAlgAut. The diagnostic is an API application type mismatch,
not evidence that later proof steps have compiled (maxErrors stops reporting).

Exactly one source-line change from v8:

    Unitary.conjStarAlgAut (S := ℂ) (R := representedCStarClosure Stage sys ω)

This is in haction, identifying the existing matrixRealTimeAut with its native
unitary conjugation. No statements, assumptions, proof steps elsewhere,
imports, instance declarations, budgets or transparency settings change.
All-beta, nonzero-tilt actual represented-switch motion remains the conclusion.
Accepted native faithfulness and finite exponential helper are still reused;
the scratch alignment-v2 dependency is unchanged.

V8 source SHA256:
57228036625707f0994bb68819e529a04485fdf7b4433c6624b9a649a4abc6ce
See SeedFiniteFirstMotion20261024v8.md for the unchanged full contract and
source-grounded abstract-tower boundary repair. The v8 provenance comment is
retained verbatim to keep this source delta minimal.

No builds/tests/live edits. Candidate uncompiled, staged for independent AA
and serial QA. No claim that explicit-R repair resolves later elaboration.
