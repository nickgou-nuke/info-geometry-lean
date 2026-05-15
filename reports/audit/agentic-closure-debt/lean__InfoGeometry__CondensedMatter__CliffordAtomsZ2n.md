# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:21.343106+00:00`
Root: `lean/InfoGeometry/CondensedMatter/CliffordAtomsZ2n.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **27**
- Hard: **0**
- Soft: **20**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/CondensedMatter/CliffordAtomsZ2n.lean` | `advisory` | 47 | 0 | 20 | 7 | 27 |

## Findings by file

### `lean/InfoGeometry/CondensedMatter/CliffordAtomsZ2n.lean`
- module: `InfoGeometry.CondensedMatter.CliffordAtomsZ2n`
- status: `advisory`
- debt_score: `47`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L43 [soft] `law-field-locker` in `structure-field SplitCliffordAtomSystem.e` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L45 [soft] `law-field-locker` in `structure-field SplitCliffordAtomSystem.f` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [soft] `law-field-locker` in `structure-field SplitCliffordAtomSystem.e_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [soft] `law-field-locker` in `structure-field SplitCliffordAtomSystem.f_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L56 [soft] `law-field-locker` in `structure-field SplitCliffordAtomSystem.f_mul_e` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [soft] `law-field-locker` in `structure-field SplitCliffordAtomSystem.H_comm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L79 [soft] `skeletal-proof` in `theorem H_sq` — proof appears to close via minimal tactic one-liner
  - L122 [soft] `simp-law-injection` in `simp-declaration flipBit_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L124 [soft] `skeletal-proof` in `theorem flipBit_self` — proof appears to close via minimal tactic one-liner
  - L130 [soft] `simp-law-injection` in `simp-declaration flipBit_other` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L132 [soft] `skeletal-proof` in `theorem flipBit_other` — proof appears to close via minimal tactic one-liner
  - L149 [soft] `law-field-locker` in `structure-field CliffordHypercubeAction.edge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L151 [soft] `law-field-locker` in `structure-field CliffordHypercubeAction.act` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L154 [soft] `law-field-locker` in `structure-field CliffordHypercubeAction.charge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L157 [soft] `law-field-locker` in `structure-field CliffordHypercubeAction.edge_charge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L166 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L207 [soft] `law-field-locker` in `structure-field FourAtomChirality.Gamma_def` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L212 [soft] `law-field-locker` in `structure-field FourAtomChirality.Gamma_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L220 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L256 [soft] `law-field-locker` in `structure-field GlobalAnomalyClass.index_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L283 [soft] `law-field-locker` in `structure-field LocalToGlobalAnomalyDatum.compatibility` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L288 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L290 [soft] `skeletal-proof` in `theorem local_charge_is_four_bit` — proof appears to close via minimal tactic one-liner
  - L295 [advisory] `bridge-shaped-declaration` in `theorem compatibility_is_extra` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L302 [advisory] `existential-packaging` in `def CliffordAtomsZ2nOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

