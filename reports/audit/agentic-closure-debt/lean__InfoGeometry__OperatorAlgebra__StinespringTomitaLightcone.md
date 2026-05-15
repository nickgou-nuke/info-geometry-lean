# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:23.521187+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/StinespringTomitaLightcone.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **26**
- Hard: **0**
- Soft: **16**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/StinespringTomitaLightcone.lean` | `advisory` | 42 | 0 | 16 | 10 | 26 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/StinespringTomitaLightcone.lean`
- module: `InfoGeometry.OperatorAlgebra.StinespringTomitaLightcone`
- status: `advisory`
- debt_score: `42`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L42 [soft] `law-field-locker` in `structure-field LocalChannel.map` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L44 [soft] `law-field-locker` in `structure-field LocalChannel.map_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `law-field-locker` in `structure-field LocalChannel.completelyPositive_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L58 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L94 [soft] `law-field-locker` in `structure-field StinespringTomitaDilation.embed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L97 [soft] `law-field-locker` in `structure-field StinespringTomitaDilation.compress` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L100 [soft] `law-field-locker` in `structure-field StinespringTomitaDilation.globalEvolution` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L103 [soft] `law-field-locker` in `structure-field StinespringTomitaDilation.channel_factorization` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L112 [soft] `law-field-locker` in `structure-field StinespringTomitaDilation.embed_mem_observable` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L116 [soft] `law-field-locker` in `structure-field StinespringTomitaDilation.leakage` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L119 [soft] `law-field-locker` in `structure-field StinespringTomitaDilation.leakage_mem_commutant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L123 [soft] `law-field-locker` in `structure-field StinespringTomitaDilation.accounting` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L133 [soft] `law-field-locker` in `structure-field StinespringTomitaDilation.global_reversible_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L154 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L202 [advisory] `existential-packaging` in `structure StinespringTomitaChiralLightconeDilation` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L225 [soft] `law-field-locker` in `structure-field StinespringTomitaChiralLightconeDilation.carrierReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L228 [soft] `law-field-locker` in `structure-field StinespringTomitaChiralLightconeDilation.leakage_hits_chiral_lightcone` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L249 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L261 [advisory] `existential-packaging` in `theorem locally_lost_has_chiral_lightcone_readout` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L272 [advisory] `existential-packaging` in `theorem locally_lost_is_commutant_chiral_lightcone` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L306 [soft] `law-field-locker` in `structure-field TomitaLightconeMirrorCompatibility.carrierReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L312 [soft] `law-field-locker` in `structure-field TomitaLightconeMirrorCompatibility.tomita_readout_compatibility` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L329 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L371 [advisory] `existential-packaging` in `def StinespringTomitaDilationOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L404 [advisory] `existential-packaging` in `def StinespringTomitaChiralLightconeOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

