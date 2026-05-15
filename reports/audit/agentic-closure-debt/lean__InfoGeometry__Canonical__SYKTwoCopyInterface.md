# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:54.562994+00:00`
Root: `lean/InfoGeometry/Canonical/SYKTwoCopyInterface.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **9**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SYKTwoCopyInterface.lean` | `advisory` | 27 | 0 | 9 | 9 | 18 |

## Findings by file

### `lean/InfoGeometry/Canonical/SYKTwoCopyInterface.lean`
- module: `InfoGeometry.Canonical.SYKTwoCopyInterface`
- status: `advisory`
- debt_score: `27`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L41 [soft] `law-field-locker` in `structure-field TaggedClaim.statement` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L92 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L107 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L107 [soft] `section-law-variable` in `variable S` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L159 [soft] `law-field-locker` in `structure-field TFDLikePreparation.normalized` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L169 [soft] `skeletal-proof` in `theorem traversableProtocolTargetClaim_not_repo` — proof appears to close via minimal tactic one-liner
  - L183 [soft] `skeletal-proof` in `theorem erEprInterpretationClaim_not_repo` — proof appears to close via minimal tactic one-liner
  - L195 [soft] `law-field-locker` in `structure-field TraversableProtocolWitness.prep` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L206 [soft] `skeletal-proof` in `theorem traversableProtocolRepoClaim_is_repo` — proof appears to close via minimal tactic one-liner
  - L239 [advisory] `bridge-shaped-declaration` in `def topologicalIndexZ2_append_owner_claim.` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L250 [advisory] `bridge-shaped-declaration` in `theorem topologicalIndexZ2_append_owner_claim_is_repo.` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L250 [soft] `skeletal-proof` in `theorem topologicalIndexZ2_append_owner_claim_is_repo.` — proof appears to close via minimal tactic one-liner
  - L256 [advisory] `bridge-shaped-declaration` in `theorem topologicalIndexZ2_append_owner_claim_holds.` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L281 [advisory] `bridge-shaped-declaration` in `def connesCocycle_state_chain_owner_claim` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L292 [advisory] `bridge-shaped-declaration` in `theorem connesCocycle_state_chain_owner_claim_is_repo` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L292 [soft] `skeletal-proof` in `theorem connesCocycle_state_chain_owner_claim_is_repo` — proof appears to close via minimal tactic one-liner
  - L298 [advisory] `bridge-shaped-declaration` in `theorem connesCocycle_state_chain_owner_claim_holds` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

