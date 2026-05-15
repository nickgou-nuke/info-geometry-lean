# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:35.937659+00:00`
Root: `lean/InfoGeometry/Automorphic/RoelckeSelbergSpectral.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **32**
- Hard: **0**
- Soft: **21**
- Advisory: **11**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Automorphic/RoelckeSelbergSpectral.lean` | `advisory` | 53 | 0 | 21 | 11 | 32 |

## Findings by file

### `lean/InfoGeometry/Automorphic/RoelckeSelbergSpectral.lean`
- module: `InfoGeometry.Automorphic.RoelckeSelbergSpectral`
- status: `advisory`
- debt_score: `53`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L61 [soft] `simp-law-injection` in `simp-declaration mem_eigenspace_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L63 [soft] `skeletal-proof` in `theorem mem_eigenspace_iff` — proof appears to close via minimal tactic one-liner
  - L72 [advisory] `local-hypothesis-injection` in `theorem mem_eigenspace_iff` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L74 [advisory] `local-hypothesis-injection` in `theorem mem_eigenspace_iff` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L94 [soft] `simp-law-injection` in `simp-declaration mem_cuspidalEigenspace_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L96 [soft] `skeletal-proof` in `theorem mem_cuspidalEigenspace_iff` — proof appears to close via minimal tactic one-liner
  - L107 [soft] `skeletal-proof` in `theorem map_mem_pCuspidal_of_commutes` — proof appears to close via minimal tactic one-liner
  - L121 [advisory] `local-hypothesis-injection` in `theorem map_mem_pCuspidal_of_commutes` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L123 [advisory] `local-hypothesis-injection` in `theorem map_mem_pCuspidal_of_commutes` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L132 [advisory] `local-hypothesis-injection` in `theorem map_mem_pCuspidal_of_commutes` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L135 [advisory] `local-hypothesis-injection` in `theorem map_mem_pCuspidal_of_commutes` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L162 [soft] `law-field-locker` in `structure-field RoelckeSelbergSpectralDatum.laplacian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L168 [soft] `law-field-locker` in `structure-field RoelckeSelbergSpectralDatum.hecke` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L171 [soft] `law-field-locker` in `structure-field RoelckeSelbergSpectralDatum.hecke_pairwise_commute` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L176 [soft] `law-field-locker` in `structure-field RoelckeSelbergSpectralDatum.hecke_commutes_laplacian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L181 [soft] `law-field-locker` in `structure-field RoelckeSelbergSpectralDatum.hecke_commutes_cuspidal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L186 [soft] `law-field-locker` in `structure-field RoelckeSelbergSpectralDatum.roelckeSelbergStatement` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L203 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L237 [soft] `law-field-locker` in `structure-field JointEigenvalue.hecke` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L250 [soft] `simp-law-injection` in `simp-declaration mem_jointEigenspace_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L252 [soft] `skeletal-proof` in `theorem mem_jointEigenspace_iff` — proof appears to close via minimal tactic one-liner
  - L333 [soft] `law-field-locker` in `structure-field AutomorphicLFunctionDatum.value` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L336 [soft] `law-field-locker` in `structure-field AutomorphicLFunctionDatum.localFactor` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L340 [soft] `law-field-locker` in `structure-field AutomorphicLFunctionDatum.regular` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L344 [soft] `law-field-locker` in `structure-field AutomorphicLFunctionDatum.value_nonzero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L348 [soft] `law-field-locker` in `structure-field AutomorphicLFunctionDatum.eulerProductStatement` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L364 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L375 [soft] `simp-law-injection` in `simp-declaration potential_eq_zero_of_abs_eq_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L377 [soft] `skeletal-proof` in `theorem potential_eq_zero_of_abs_eq_one` — proof appears to close via minimal tactic one-liner
  - L410 [advisory] `existential-packaging` in `def RoelckeSelbergSpectralOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L421 [advisory] `existential-packaging` in `def AutomorphicLFunctionOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

