# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:22.012827+00:00`
Root: `lean/InfoGeometry/Canonical/KKTCore.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **40**
- Hard: **0**
- Soft: **13**
- Advisory: **27**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/KKTCore.lean` | `advisory` | 53 | 0 | 13 | 27 | 40 |

## Findings by file

### `lean/InfoGeometry/Canonical/KKTCore.lean`
- module: `InfoGeometry.Canonical.KKTCore`
- status: `advisory`
- debt_score: `53`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L31 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L33 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L69 [soft] `simp-law-injection` in `simp-declaration uPlus_eq_gOnePart` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L72 [soft] `skeletal-proof` in `theorem uPlus_eq_gOnePart` — proof appears to close via minimal tactic one-liner
  - L75 [soft] `simp-law-injection` in `simp-declaration uMinus_eq_gNegOnePart` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L78 [soft] `skeletal-proof` in `theorem uMinus_eq_gNegOnePart` — proof appears to close via minimal tactic one-liner
  - L148 [advisory] `local-hypothesis-injection` in `theorem RealSplitCl11Action.eps_is_cartan` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L161 [advisory] `local-hypothesis-injection` in `theorem RealSplitCl11Action.eps_is_cartan` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L174 [advisory] `local-hypothesis-injection` in `theorem RealSplitCl11Action.eps_is_cartan` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L188 [advisory] `local-hypothesis-injection` in `theorem RealSplitCl11Action.eps_is_cartan` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L202 [advisory] `local-hypothesis-injection` in `theorem RealSplitCl11Action.eps_is_cartan` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L221 [advisory] `local-hypothesis-injection` in `theorem RealSplitCl11Action.eps_is_cartan` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L225 [soft] `simp-law-injection` in `simp-declaration gZeroPart_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L230 [soft] `simp-law-injection` in `simp-declaration gZeroPart_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L235 [soft] `simp-law-injection` in `simp-declaration gOnePart_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L240 [soft] `simp-law-injection` in `simp-declaration gOnePart_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L245 [soft] `simp-law-injection` in `simp-declaration gNegOnePart_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L250 [soft] `simp-law-injection` in `simp-declaration gNegOnePart_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L261 [advisory] `local-hypothesis-injection` in `theorem RealSplitCl11Action.eps_is_cartan` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L262 [advisory] `local-hypothesis-injection` in `theorem RealSplitCl11Action.eps_is_cartan` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L368 [soft] `skeletal-proof` in `theorem uPlus_mul_uPlus_eq_zero` — proof appears to close via minimal tactic one-liner
  - L377 [soft] `skeletal-proof` in `theorem uMinus_mul_uMinus_eq_zero` — proof appears to close via minimal tactic one-liner
  - L416 [advisory] `local-hypothesis-injection` in `theorem uMinus_mul_uMinus_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L432 [advisory] `local-hypothesis-injection` in `theorem uMinus_mul_uMinus_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L468 [advisory] `local-hypothesis-injection` in `theorem uMinus_mul_uMinus_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L486 [advisory] `local-hypothesis-injection` in `theorem uMinus_mul_uMinus_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L502 [advisory] `local-hypothesis-injection` in `theorem uMinus_mul_uMinus_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L505 [advisory] `local-hypothesis-injection` in `theorem uMinus_mul_uMinus_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L515 [advisory] `local-hypothesis-injection` in `theorem uMinus_mul_uMinus_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L518 [advisory] `local-hypothesis-injection` in `theorem uMinus_mul_uMinus_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L521 [advisory] `local-hypothesis-injection` in `theorem uMinus_mul_uMinus_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L542 [advisory] `local-hypothesis-injection` in `theorem uMinus_mul_uMinus_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L544 [advisory] `local-hypothesis-injection` in `theorem uMinus_mul_uMinus_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L549 [advisory] `local-hypothesis-injection` in `theorem uMinus_mul_uMinus_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L556 [advisory] `local-hypothesis-injection` in `theorem uMinus_mul_uMinus_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L567 [advisory] `local-hypothesis-injection` in `theorem uMinus_mul_uMinus_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L581 [advisory] `local-hypothesis-injection` in `theorem uMinus_mul_uMinus_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L590 [advisory] `local-hypothesis-injection` in `theorem uMinus_mul_uMinus_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L620 [soft] `skeletal-proof` in `theorem commutator_uPlus_uMinus_isGZero` — proof appears to close via minimal tactic one-liner

