# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:53.077144+00:00`
Root: `lean/InfoGeometry/Krein/HilbertBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **40**
- Hard: **0**
- Soft: **30**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Krein/HilbertBridge.lean` | `advisory` | 70 | 0 | 30 | 10 | 40 |

## Findings by file

### `lean/InfoGeometry/Krein/HilbertBridge.lean`
- module: `InfoGeometry.Krein.HilbertBridge`
- status: `advisory`
- debt_score: `70`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L105 [soft] `skeletal-proof` in `lemma val_ofWithLp` — proof appears to close via minimal tactic one-liner
  - L107 [soft] `skeletal-proof` in `lemma ofWithLp_val` — proof appears to close via minimal tactic one-liner
  - L110 [soft] `simp-law-injection` in `simp-declaration val_toLp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L111 [soft] `simp-law-injection` in `simp-declaration coe_toLp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L112 [soft] `simp-law-injection` in `simp-declaration ofLp_toLp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L113 [soft] `simp-law-injection` in `simp-declaration toLp_ofLp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L116 [soft] `simp-law-injection` in `simp-declaration fst_ofWithLp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L118 [soft] `simp-law-injection` in `simp-declaration snd_ofWithLp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L120 [soft] `simp-law-injection` in `simp-declaration fst_toLp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L121 [soft] `simp-law-injection` in `simp-declaration snd_toLp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L159 [soft] `simp-law-injection` in `simp-declaration ofDoubledLIE_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L162 [soft] `simp-law-injection` in `simp-declaration toDoubledLIE_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L165 [soft] `simp-law-injection` in `simp-declaration ofDoubledContinuousLinearEquiv_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L168 [soft] `simp-law-injection` in `simp-declaration toDoubledContinuousLinearEquiv_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L261 [soft] `skeletal-proof` in `lemma val_ofWithLp` — proof appears to close via minimal tactic one-liner
  - L263 [soft] `skeletal-proof` in `lemma ofWithLp_val` — proof appears to close via minimal tactic one-liner
  - L266 [soft] `simp-law-injection` in `simp-declaration val_toLp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L267 [soft] `skeletal-proof` in `lemma fst_coe` — proof appears to close via minimal tactic one-liner
  - L268 [soft] `skeletal-proof` in `lemma snd_coe` — proof appears to close via minimal tactic one-liner
  - L269 [soft] `skeletal-proof` in `lemma fst_val` — proof appears to close via minimal tactic one-liner
  - L270 [soft] `skeletal-proof` in `lemma snd_val` — proof appears to close via minimal tactic one-liner
  - L271 [soft] `simp-law-injection` in `simp-declaration fst_ofWithLp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L273 [soft] `simp-law-injection` in `simp-declaration snd_ofWithLp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L275 [soft] `simp-law-injection` in `simp-declaration fst_toLp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L276 [soft] `simp-law-injection` in `simp-declaration snd_toLp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L288 [soft] `simp-law-injection` in `simp-declaration neutralJ_eq_J` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L294 [advisory] `local-hypothesis-injection` in `lemma one_div_sqrt_two_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L325 [advisory] `local-hypothesis-injection` in `lemma rotation45_norm` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L328 [advisory] `local-hypothesis-injection` in `lemma rotation45_norm` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L330 [advisory] `local-hypothesis-injection` in `lemma rotation45_norm` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L361 [advisory] `local-hypothesis-injection` in `lemma rotation45_norm` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L380 [advisory] `local-hypothesis-injection` in `def rotation45` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L382 [advisory] `local-hypothesis-injection` in `def rotation45` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L411 [advisory] `local-hypothesis-injection` in `def rotation45` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L413 [advisory] `local-hypothesis-injection` in `def rotation45` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L477 [soft] `simp-law-injection` in `simp-declaration rotation45ToHilbert_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L481 [soft] `simp-law-injection` in `simp-declaration rotation45ToHilbertContinuousLinearEquiv_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L485 [soft] `simp-law-injection` in `simp-declaration rotation45_symm_toLp_pair` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L500 [soft] `simp-law-injection` in `simp-declaration neutralLift_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

