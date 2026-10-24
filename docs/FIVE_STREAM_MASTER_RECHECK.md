# Five-stream master recheck

## Repair contract

Owner: `lean/InfoGeometry/Canonical/DeBruijnRotorAlternationCycle.lean`,
originally `InfoGeometry.Canonical.DeBruijnRotorAlternationCycle.fubini_study_chordal_metric`.
A concurrent, preserved scope correction renamed it to
`InfoGeometry.Canonical.DeBruijnRotorAlternationCycle.movingPolePlus_chordal_square_and_compression`.

Carrier: `[CommRing R] [Ring A] [Algebra R A]`. Multiplication in `A` is
noncommutative. `h : IsDualSeedPair d B` supplies the two square-zero and two
reflexivity laws. `h_cs : c*c+s*s=1` is a scalar-ring equation.
The existing `movingPolePlus` remains the rotor sandwich, not a new polynomial
definition. The exact conclusions are

```
(movingPolePlus c s d B - polePlus d B) *
  (movingPolePlus c s d B - polePlus d B) = (s*s) • carrierSupport d B
polePlus d B * movingPolePlus c s d B * polePlus d B = (c*c) • polePlus d B
```

Reuse: `movingPolePlus_sub_polePlus`, `chordalDirection_sq`,
`movingPolePlus_eq`, `polePlus_mul_velocity`, `polePlus_idem`, and
`polePlus_mul_poleMinus` in the same owner. The repair only normalizes the
zero-scalar terms left by the compression proof. No theorem type or hypothesis
changes, new wrapper, numeric model, or CAS theorem transport is needed.

Direct consumers: `DeBruijnRotorAlternationCycleAudit.lean` and
`FiveStreamMasterIntertwiner.movingPoles_chordal_compression_and_orthogonality`,
with `FiveStreamMasterIntertwinerAudit.lean` auditing the latter.

The earlier locked build failed at the final `sub_zero` rewrite
(`/tmp/five-stream-master-review-build.log`). Before this repair, a concurrent
edit had already supplied a second `smul_zero` and reordered part of the
rewrite list. Preserve those intervening changes and replace only the final
zero-normalization tail with `simp only`.

## Scope boundaries

- Algebraic displacement squares and compression are not by themselves a
  scalar-valued metric, positivity theorem, or Fubini–Study/Poincaré geometry.
- Rotor inversion does not assert adjoint unitarity without star assumptions.
- The integral `(c,s)=(3,4)` witness gives polynomial trace 145 but is not on
  the unit circle and does not instantiate normalized moving idempotence.
- The modular-center theorem acts by left multiplication, not conjugation.
- External independent A-A/QA-A acceptance is not authenticated by this recheck.

## Verification

- Focused repaired-owner and master-audit build: PASS, **9,304 jobs**
  (`/tmp/five-stream-master-repair-focused.log`).
- `InfoGeometry.All`, all six audit companions, and the existing
  `FiveStreamRotorChordal` consumer: PASS, **27,067 jobs**
  (`/tmp/five-stream-master-repair-integrated2.log`). The earlier integrated
  build also passed but preceded concurrent scope/name changes.
- Final strict kernel replay and transitive axiom collection: **1,114 generated
  declarations in 13 owners**, all PASS; only `propext`, `Classical.choice`,
  `Quot.sound` (`/tmp/five-stream-master-repair-axioms-final.log`).
- The six owners contribute 193/187/184/148/164/91 declarations respectively:
  **967**, including the master. PR #205's three requested core modules add
  **60**; PR #206's four requested modules add **87**.
- No warnings from the repaired owner or master in the checked builds.
  Existing dependency/root warnings remain.
- Forbidden-token scans are empty for all 13 owners. Selected oleans were
  fresh; source drift before/after replay and at final readback was empty.
  All 19 selected owner/companion files matched their staged contents.
- Companion `#print axioms` command counts are **111/91/107/67/80/36 = 492**.
  These are command counts, not generated-declaration totals or a reproduction
  of the reported 476-declaration certification.

### Source-gate qualification

The scoped repaired-theorem check returned no proxy alerts; the master owner
also returned none. The full Stream 5 scan flags the existing concrete
`mat2Z_isDualSeedPair` constructor as bundling Prop fields. Its four explicit
matrix proofs were inspected and kernel-replayed: this is the inhabited
noncommutative seed witness, not an assumed certificate or missing theorem.
It was not rewritten merely to evade the scanner. Therefore this receipt does
**not** claim a clean whole-owner proxy-gate result. Concurrent unrelated Git
staging also prevented a globally stable-index gate; the selected file bytes
were independently checked against the final source hashes and staged bytes.
See `/tmp/five-stream-master-repair-source-final.log`.

### Concurrent work and snapshot scope

The first 17-owner replay passed at 1,156 declarations, but later owner edits
invalidated that snapshot. A second replay passed all modules but detected
subsequent `Cl11FiveStreamColimitTransport` source drift. Neither is the final
current-source certificate. The final replay is deliberately limited to the
six requested streams/master plus the seven PR modules, not active peripheral
colimit/rotor development. Full snapshot binding:
`/tmp/five-stream-master-repair-snapshot-final.json`.

The concurrent author preserved the repaired `simp only` tail while renaming
the algebraic statements and adding both moving idempotences and both zero
products in `movingPoles_complementary_idempotents`. Those changes were read,
preserved and reverified; they are not attributed to this repair.

Verification used the shared-lock build wrapper and process prechecks. One
200-second tool wait timed out while its Lake child continued; the child was
left running and its successful completion was read back rather than restarted
or killed. Another externally launched Lake process was observed during that
interval, so global single-flight operation is not asserted. Final strict
replay ran under the shared lock after compiler-process checks.

This task changes only the compression-proof normalization and this receipt.
No dependency pins, caches, or theorem assumptions changed. Changes are staged,
not committed. Earlier receipts remain evidence of their earlier snapshots.
