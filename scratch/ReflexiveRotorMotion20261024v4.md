# Reflexive rotor motion v4: scalar normalization

Source: ReflexiveRotorMotion20261024v4.lean, new frozen scratch candidate.
Same statements, pair premises, and mathematical contract as v3.
Exact diagnostics: /tmp/qa-a-reflexive-rotor-v3-2thzyk6j/compile.log.

Adds neg_mul to the fixed minus-conjugation simp set, normalizing the
remaining -((-s*s) • (d*B)) to (s*s) • (d*B) with the existing neg_smul
and neg_neg rules. Replaces the reported unnecessary <;> with sequential
simp only and abel in rotor_mul_plus. No other proof changes.

No builds/tests/live-owner edits, added assumptions, or budget changes.
V3 and the separate analytic draft are preserved. AA and serialized QA pending.
