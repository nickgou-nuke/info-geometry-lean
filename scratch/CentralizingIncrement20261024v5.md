# Centralizing increments v5

V4 kernel all11 PASS reported by parent; strict T16 rejected absence of an
explicit ordered-product noncommutativity statement. Source log:
/tmp/qa-a-centralizingincrement20261024v4-b0oxlxa8/strict.log.

Only addition: boundaryZZ_old_switch_noncommute proves
boundaryZZ * concreteStep 1 switch2 != concreteStep 1 switch2 * boundaryZZ.
It specializes the existing proved actual ZZ/old-switch obstruction at scalar 1.
No fresh surrogate matrices or assumed noncommutativity. Generic criterion and
all v4 proofs unchanged. Scope remains A tensor I, not a universal obstruction
for Fock vacuum embeddings. No gate modifications or bypass.

New sandbox only; preserved v1–v4. No builds/tests/live edits; uncompiled addition.
