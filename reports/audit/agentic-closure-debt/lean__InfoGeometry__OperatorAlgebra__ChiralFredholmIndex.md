# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:06.648590+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ChiralFredholmIndex.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **32**
- Hard: **0**
- Soft: **28**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ChiralFredholmIndex.lean` | `advisory` | 60 | 0 | 28 | 4 | 32 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ChiralFredholmIndex.lean`
- module: `InfoGeometry.OperatorAlgebra.ChiralFredholmIndex`
- status: `advisory`
- debt_score: `60`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [soft] `law-field-locker` in `structure-field FredholmIndexDatum.operator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L37 [soft] `law-field-locker` in `structure-field FredholmIndexDatum.isFredholm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field FredholmIndexDatum.kernelFinite` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L46 [soft] `law-field-locker` in `structure-field FredholmIndexDatum.cokernelFinite` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L94 [advisory] `local-hypothesis-injection` in `theorem index_eq_zero_of_mirror_fixed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L117 [soft] `law-field-locker` in `structure-field ChiralFredholmDatum.chi` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L119 [soft] `law-field-locker` in `structure-field ChiralFredholmDatum.D` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L122 [soft] `law-field-locker` in `structure-field ChiralFredholmDatum.chi_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L126 [soft] `law-field-locker` in `structure-field ChiralFredholmDatum.D_odd` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L138 [soft] `law-field-locker` in `structure-field ChiralFredholmDatum.index_eq_kernelCount` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L167 [soft] `law-field-locker` in `structure-field ModularMirrorFredholmCompatibility.J` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L169 [soft] `law-field-locker` in `structure-field ModularMirrorFredholmCompatibility.J_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L173 [soft] `law-field-locker` in `structure-field ModularMirrorFredholmCompatibility.J_flips_chi` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L177 [soft] `law-field-locker` in `structure-field ModularMirrorFredholmCompatibility.J_D_compatibility` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L185 [soft] `law-field-locker` in `structure-field ModularMirrorFredholmCompatibility.mirror_swaps_kernelCount` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L193 [soft] `law-field-locker` in `structure-field ModularMirrorFredholmCompatibility.leftKernel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L194 [soft] `law-field-locker` in `structure-field ModularMirrorFredholmCompatibility.rightKernel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L239 [soft] `law-field-locker` in `structure-field EvenKasparovCycleDatum.rep` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L241 [soft] `law-field-locker` in `structure-field EvenKasparovCycleDatum.chi` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L244 [soft] `law-field-locker` in `structure-field EvenKasparovCycleDatum.F` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L247 [soft] `law-field-locker` in `structure-field EvenKasparovCycleDatum.chi_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L251 [soft] `law-field-locker` in `structure-field EvenKasparovCycleDatum.F_odd` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L255 [soft] `law-field-locker` in `structure-field EvenKasparovCycleDatum.commutators_compact` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L258 [soft] `law-field-locker` in `structure-field EvenKasparovCycleDatum.square_minus_one_compact` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L261 [soft] `law-field-locker` in `structure-field EvenKasparovCycleDatum.self_adjoint_mod_compact` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L264 [soft] `law-field-locker` in `structure-field EvenKasparovCycleDatum.indexPairing` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L278 [soft] `law-field-locker` in `structure-field ChiralIndexFormulaDatum.cocycleReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L280 [soft] `law-field-locker` in `structure-field ChiralIndexFormulaDatum.indexReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L283 [soft] `law-field-locker` in `structure-field ChiralIndexFormulaDatum.index_formula` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L291 [advisory] `existential-packaging` in `def ChiralFredholmIndexOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L298 [advisory] `existential-packaging` in `def EvenKasparovCycleOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

