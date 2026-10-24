# Complement-preserving hyperbolic orbit v3

New source only; frozen v1/v2 and live owners unchanged. All existing definitions,
theorem statements, hypotheses and six extracted reusable helper lemmas retained.

Exact diagnostic: /tmp/qa-a-hyperbolic-v2-j4nx7cpk/compile.log.
The sole failed proof distributed the raw sum d+B before absorption lemmas could
match. Capture the four derived support/complement velocity identities and the
native velocity square, unfold only hyperbolicRotor, then generalize d+B to an
opaque Q simultaneously in those five facts and the goal. The multiplication
simplifier now treats Q as an atom. Retain v2 smul_add/smul_smul and smul_neg fixes.
The product proof remains under 20 lines; no budget or linter changes.

No builds/tests/live edits. Uncompiled source candidate for independent AA/QA.
Rational witness contract remains staged separately; witness authoring resumes
only after this repair is frozen and delivered. Fock descent is unchanged.
