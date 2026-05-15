# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:48.832306+00:00`
Root: `lean/InfoGeometry/Canonical/RealIncidenceHomology.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **28**
- Hard: **0**
- Soft: **20**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RealIncidenceHomology.lean` | `advisory` | 48 | 0 | 20 | 8 | 28 |

## Findings by file

### `lean/InfoGeometry/Canonical/RealIncidenceHomology.lean`
- module: `InfoGeometry.Canonical.RealIncidenceHomology`
- status: `advisory`
- debt_score: `48`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L40 [soft] `law-field-locker` in `structure-field RealChainComplex.instAdd` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [soft] `law-field-locker` in `structure-field RealChainComplex.instModule` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L42 [soft] `law-field-locker` in `structure-field RealChainComplex.boundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field RealChainComplex.boundary_boundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L64 [advisory] `bridge-shaped-declaration` in `theorem boundary_boundary_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L91 [soft] `law-field-locker` in `structure-field RealCochainComplex.instAdd` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L92 [soft] `law-field-locker` in `structure-field RealCochainComplex.instModule` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L93 [soft] `law-field-locker` in `structure-field RealCochainComplex.coboundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L94 [soft] `law-field-locker` in `structure-field RealCochainComplex.coboundary_coboundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L98 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L115 [advisory] `bridge-shaped-declaration` in `theorem coboundary_coboundary_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L156 [soft] `simp-law-injection` in `simp-declaration map_src` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L160 [soft] `simp-law-injection` in `simp-declaration map_rel` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L164 [soft] `simp-law-injection` in `simp-declaration map_tgt` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L186 [soft] `skeletal-proof` in `theorem zeroCoboundary_apply` — proof appears to close via minimal tactic one-liner
  - L220 [soft] `law-field-locker` in `structure-field HestenesChainComplex.instAdd` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L221 [soft] `law-field-locker` in `structure-field HestenesChainComplex.instModule` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L222 [soft] `law-field-locker` in `structure-field HestenesChainComplex.boundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L223 [soft] `law-field-locker` in `structure-field HestenesChainComplex.boundary_boundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L225 [soft] `law-field-locker` in `structure-field HestenesChainComplex.phase` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L226 [soft] `law-field-locker` in `structure-field HestenesChainComplex.phase_sq_neg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L227 [soft] `law-field-locker` in `structure-field HestenesChainComplex.twist` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L228 [soft] `law-field-locker` in `structure-field HestenesChainComplex.boundary_phase` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L234 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L250 [advisory] `bridge-shaped-declaration` in `theorem phase_sq_neg_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L257 [advisory] `bridge-shaped-declaration` in `theorem boundary_phase_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

