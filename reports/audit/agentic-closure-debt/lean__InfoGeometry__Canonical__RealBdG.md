# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:47.530216+00:00`
Root: `lean/InfoGeometry/Canonical/RealBdG.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **25**
- Hard: **0**
- Soft: **22**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RealBdG.lean` | `advisory` | 47 | 0 | 22 | 3 | 25 |

## Findings by file

### `lean/InfoGeometry/Canonical/RealBdG.lean`
- module: `InfoGeometry.Canonical.RealBdG`
- status: `advisory`
- debt_score: `47`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [soft] `simp-law-injection` in `simp-declaration modularK_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L36 [soft] `skeletal-proof` in `lemma modularK_eq_modularComplexI` — proof appears to close via minimal tactic one-liner
  - L42 [soft] `simp-law-injection` in `simp-declaration modularK_eq_modular_j_comp_spectral_epsilon` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L46 [soft] `simp-law-injection` in `simp-declaration modularK_eq_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L51 [soft] `simp-law-injection` in `simp-declaration modularK_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L59 [soft] `simp-law-injection` in `simp-declaration modularK_apply_modularK` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L62 [advisory] `local-hypothesis-injection` in `lemma modularK_eq_modularComplexI` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L87 [soft] `skeletal-proof` in `lemma KLinearPart_add_KAntilinearPart` — proof appears to close via minimal tactic one-liner
  - L104 [advisory] `local-hypothesis-injection` in `lemma KLinearPart_add_KAntilinearPart` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L106 [soft] `skeletal-proof` in `lemma KConjugate_comp_modularK` — proof appears to close via minimal tactic one-liner
  - L123 [soft] `skeletal-proof` in `lemma modularK_comp_KConjugate` — proof appears to close via minimal tactic one-liner
  - L136 [soft] `skeletal-proof` in `theorem kSplit_linear` — proof appears to close via minimal tactic one-liner
  - L157 [soft] `skeletal-proof` in `theorem kSplit_antilinear` — proof appears to close via minimal tactic one-liner
  - L191 [soft] `law-field-locker` in `structure-field RealBdGDatum.H` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L192 [soft] `law-field-locker` in `structure-field RealBdGDatum.particleHole` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L193 [soft] `law-field-locker` in `structure-field RealBdGDatum.timeReversal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L194 [soft] `law-field-locker` in `structure-field RealBdGDatum.chiral` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L195 [soft] `law-field-locker` in `structure-field RealBdGDatum.H_KLinear` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L197 [soft] `law-field-locker` in `structure-field RealBdGDatum.H_chiral` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L198 [soft] `law-field-locker` in `structure-field RealBdGDatum.PH_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L200 [soft] `law-field-locker` in `structure-field RealBdGDatum.TR_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L201 [soft] `law-field-locker` in `structure-field RealBdGDatum.PH_KAnti` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L203 [soft] `law-field-locker` in `structure-field RealBdGDatum.TR_KAnti` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L211 [soft] `skeletal-proof` in `lemma complexI_action_eq_modularK` — proof appears to close via minimal tactic one-liner

