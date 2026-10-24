# Rational proper-support hyperbolic witness

New source only: ComplementHyperbolicMat3Q20261024v2.lean.
Intended native import: InfoGeometry.Canonical.ComplementHyperbolicOrbit
(current generic candidate is under independent QA). No changes to that owner,
its frozen scratch candidates, or the Fock pairing candidate.

Carrier is the existing Matrix (Fin 3) (Fin 3) ℚ, with only an abbreviation
Mat3Q. Seeds are actual Matrix.single 0 1 1 and Matrix.single 1 0 1.
Prove the existing IsDualSeedPair predicate from exact matrix arithmetic.
Native support is diag(1,1,0), hence is not full identity (entry 2,2).
Parameters u=5/3, v=4/3 satisfy u*u-v*v=1, with v nonzero.

Use actual generic hyperbolicRotor and hyperbolicPlus, with no replacement
orbit definitions. Establish H=[[5/3,4/3,0],[4/3,5/3,0],[0,0,1]] and
P'=[[25/9,-20/9,0],[20/9,-16/9,0],[0,0,0]]. Obtain P'^2=P' by the generic
hyperbolicPlus_idempotent theorem, not a separately assumed or certified field.
Prove P' differs from dB and transpose(P') differs from P' by exact entries.
Prove H fixes the actual inactive vector ![0,0,1] and both left/right products
with the inactive matrix corner E22. This exhibits a genuinely fixed nonzero
complement in an oblique rational idempotent orbit.

Small independent lemmas; exact rational norm_num/finite-index proofs only.
No native_decide, builds, tests, live edits, positivity/metric/KMS claims.
This replaces a nontrivial integer hyperbola example: integer u²-v²=1 forces
v=0, whereas these rational coefficients give actual nonzero motion.
Source is uncompiled and requires independent AA and serialized QA.

## v2 bounded repair

Prior receipt: /tmp/qa-a-hyperbolic-mat3q-qael7dgi/result.json records successful
compile and axiom audit, stable inputs, and strict-screen failure. Per QA,
T16 needs an explicit recognized noncommutativity witness.
The sole source addition is seed_noncommute : seedD*seedB ≠ seedB*seedD,
derived from the existing seed_plus_matrix/seed_minus_matrix readbacks at entry
(0,0), followed by exact norm_num. All previous statements/proofs are unchanged.
Frozen v1 is preserved. No builds/tests/live edits; new v2 awaits AA/QA.
