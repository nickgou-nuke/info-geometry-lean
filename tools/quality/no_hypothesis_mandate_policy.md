# No-Hypothesis Mandate Policy (Hard Gate)

This repository policy is mandatory:

1. No non-honest placeholder proof tokens:
   - `admit`
   - `axiom`
   - `postulate`
   - `sorry` is allowed only as explicit open-debt marker.

2. No placeholder-assumption declaration naming for promoted surfaces:
   - `*hypothesis*`
   - `*assumption*`
   - `*axiom*`
   - `*postulate*`
   Concrete `witness` and `certificate` names are allowed when they denote
   kernel-proved constructions; proof-only and semantic-content gates audit
   whether those constructions are substantive.

3. Documentation comments are not source debt.  The checker strips Lean line
   and block comments before looking for proof-hole tokens, while the kernel,
   axiom audit, and proof-only gates remain authoritative for actual code.

4. Every closure claim must be either:
   - fully kernel-proved in Lean, or
   - explicitly tracked as open closure debt.

Enforcement command:

```bash
python3 tools/quality/check_no_hypothesis_mandate.py --root lean/InfoGeometry
```

This policy is intended to be run in CI and pre-merge checks.
