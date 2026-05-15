# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:53.231520+00:00`
Root: `lean/InfoGeometry/Krein/InvolutiveSelfDualCarrier.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **24**
- Hard: **0**
- Soft: **17**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Krein/InvolutiveSelfDualCarrier.lean` | `advisory` | 41 | 0 | 17 | 7 | 24 |

## Findings by file

### `lean/InfoGeometry/Krein/InvolutiveSelfDualCarrier.lean`
- module: `InfoGeometry.Krein.InvolutiveSelfDualCarrier`
- status: `advisory`
- debt_score: `41`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L69 [soft] `skeletal-proof` in `theorem K_sq_of_relations` — proof appears to close via minimal tactic one-liner
  - L90 [soft] `skeletal-proof` in `theorem J_comp_K_of_relations` — proof appears to close via minimal tactic one-liner
  - L102 [soft] `skeletal-proof` in `theorem K_comp_J_of_relations` — proof appears to close via minimal tactic one-liner
  - L165 [soft] `law-field-locker` in `structure-field InvolutiveSelfDualCarrier.J` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L168 [soft] `law-field-locker` in `structure-field InvolutiveSelfDualCarrier.J_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L172 [soft] `law-field-locker` in `structure-field InvolutiveSelfDualCarrier.pairing_symm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L175 [soft] `law-field-locker` in `structure-field InvolutiveSelfDualCarrier.pairing_J_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L189 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L208 [soft] `simp-law-injection` in `simp-declaration K_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L226 [soft] `simp-law-injection` in `simp-declaration J_comp_K` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L235 [soft] `simp-law-injection` in `simp-declaration K_comp_J` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L249 [soft] `simp-law-injection` in `simp-declaration K_comp_` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L252 [advisory] `local-hypothesis-injection` in `def Pminus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L282 [soft] `simp-law-injection` in `simp-declaration Pplus_idempotent` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L289 [soft] `simp-law-injection` in `simp-declaration Pminus_idempotent` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L297 [soft] `simp-law-injection` in `simp-declaration Pplus_add_Pminus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L301 [advisory] `local-hypothesis-injection` in `def Pminus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L303 [soft] `skeletal-proof` in `theorem Pplus_sub_Pminus` — proof appears to close via minimal tactic one-liner
  - L311 [advisory] `local-hypothesis-injection` in `theorem Pplus_sub_Pminus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L321 [soft] `simp-law-injection` in `simp-declaration Pplus_comp_Pminus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L325 [advisory] `local-hypothesis-injection` in `theorem Pplus_sub_Pminus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L329 [soft] `simp-law-injection` in `simp-declaration Pminus_comp_Pplus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L333 [advisory] `local-hypothesis-injection` in `theorem Pplus_sub_Pminus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

