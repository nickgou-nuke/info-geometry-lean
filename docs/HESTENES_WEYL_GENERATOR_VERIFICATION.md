# Hestenes–Krein Weyl generator verification

## Implemented

- `lean/InfoGeometry/Core/InnerConjugationJet.lean`: actual units in Mathlib's
  `DualNumber A` for every ring A; exact noncommutative conjugation
  `(1+εG)(X+εY)(1-εG) = X+ε(Y+GX-XG)`.
- `lean/InfoGeometry/Krein/HestenesWeylGenerator.lean`: native operators on
  arbitrary `DoubledSpace E`; rotor Krein-adjoint, unit and isometry laws;
  Clifford inversion reversing both rotor and commutator; exact first jet;
  nonzero action; Clifford-algebra representation compatibility.
- `lean/InfoGeometry/Krein/All.lean`: imports the new owner. It is reachable
  from `InfoGeometry.All` through `AllExhaustive`.

The two new owners contain 12 named theorems and 3 definitions (37 generated
kernel declarations). Existing carriers, adjoints, Clifford representation,
commutator, and real rotor definitions were reused, not replaced.

## Native conventions

The installed doubled metric is ε(x,y)=(x,-y). Its Krein-skew split generator
is G=modular_j, G(x,y)=(y,x). The negative Clifford vector is
W=complex_i, W(x,y)=(-y,x). Thus W²=-1, W⁻¹=-W and WGW⁻¹=-G.
This uses the actual chosen metric; it does not silently declare ε itself
Krein-skew, or identify W with the metric symmetry.

The real rotor is the existing `hyperbolicRotor G c s`, with
`c*c-s*s=1`. The proof derives `R♯=R⁻¹` and Krein isometry. Inversion gives
`WRW⁻¹=R⁻¹`. The exact algebraic infinitesimal is the existing
`kreinCommutator G X`, and its action on ε is `2 • complex_i`.
The nonzero witness uses E=ℝ and the native doubled vector (1,0).

This task does not select a time parametrization, identify a new exponential
series, construct a projective quotient, or establish a full Tomita theory.
W's scalar projective readout is -1/z; the coordinate CAS also checks its
Krein anti-isometry. That last CAS check is supplementary, not a newly named
operator-level anti-isometry theorem in this owner.

## Verification

All builds/replays used the shared build lock and compiler-process checks.
Other agents' jobs were waited for; no job was killed or cache removed.
Dependency pins were unchanged.

- Baseline: PASS, 8,937 jobs (`/tmp/hestenes-weyl-baseline.log`).
- Final narrow build: PASS, 8,939 jobs (`/tmp/hestenes-weyl-build8.log`).
- `InfoGeometry.Krein.All InfoGeometry.All`: PASS, **27,053 jobs**
  (`/tmp/hestenes-weyl-integrated.log`).
- Strict kernel replay with `tools/infra/axiom_check.lean`: **375 declarations
  across eight owners**, all PASS (`/tmp/hestenes-weyl-axioms.log`).
- Allowed transitive axioms only: `propext`, `Classical.choice`, `Quot.sound`.
- Source-aware forbidden-token scan: empty for both new owners.
- Staged-source `proof_proxy_staged_gate.check_text` on both new owners: PASS,
  stable index (`/tmp/hestenes-weyl-source-gate.log`). This is a scoped gate,
  not a verdict on every concurrent staged file.
- New owners emit zero warnings. Pre-existing dependency/root warnings remain;
  the full repository is not claimed warning-free or globally axiom-audited.
- Before/after selected source drift: empty. Selected oleans were fresh.
- Ten exact coordinate CAS checks passed with owner hashes and basis metadata:
  `scripts/check_hestenes_weyl_generator.py`, `/tmp/hestenes-weyl-cas.json`.

| Replayed owner | Declarations |
|---|---:|
| Core/InnerConjugationJet | 7 |
| Krein/HestenesWeylGenerator | 30 |
| Krein/DoubledSpace | 100 |
| Krein/DoubledAdjoint | 23 |
| Krein/Representation | 25 |
| Krein/KreinSpace | 143 |
| OperatorAlgebra/KreinInnerDerivation | 32 |
| Algebra/ChiralRealHyperbolicRotor | 15 |
| **Total** | **375** |

New-source SHA-256:

```
08f85896142195f7f65d20de93e51294e4f4957b880a854b644a5f0c709fbfa6  Core/InnerConjugationJet.lean
2a7752ec952ffd6a8731f0fa647ac811fa648097f0d754a04b36b7917b3ce9c8  Krein/HestenesWeylGenerator.lean
```

The full nine-file snapshot (including umbrella) is
`/tmp/hestenes-weyl-final-hashes.json`. Early elaboration failures are retained
in build logs 1–7; they are not counted as successful verification.
Changes are staged, not committed; unrelated shared work is preserved.
