# No-Hypothesis Mandate Policy (Hard Gate)

This repository policy is mandatory:

1. No non-honest placeholder proof tokens:
   - `admit`
   - `axiom`
   - `postulate`
   - `sorry` is allowed only as explicit open-debt marker.

2. No witness/certificate/assumption declaration naming for promoted surfaces:
   - `*_of_witness*`
   - `*witness*`
   - `*certificate*`
   - `*certified*`
   - `*hypothesis*`
   - `*assumption*`

3. Every closure claim must be either:
   - fully kernel-proved in Lean, or
   - explicitly tracked as open closure debt.

Enforcement command:

```bash
python3 tools/quality/check_no_hypothesis_mandate.py --root lean/InfoGeometry
```

This policy is intended to be run in CI and pre-merge checks.
