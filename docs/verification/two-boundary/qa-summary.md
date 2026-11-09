# Independent QA: two-boundary operator geometry

**Verdict: PASS for the scoped native operator extension. The compiler/test lane is released to `/root`.**

The frozen 26-path source/tool set matches independent A-A review and is unchanged after verification. Both fresh, separate source lanes compiled 31 project modules, including the unchanged `KrausInvariantGeometry` consumer. Neither run used incremental artifacts. The nine owners and native audit passed with warnings treated as errors.

The native audit enumerated 284 declarations: 230 theorem constants, 51 definitions, one inductive, one constructor, and one recursor. All are safe and nonpartial, and their transitive axiom union is exactly `Classical.choice`, `Quot.sound`, and `propext`. These counts include existing/promoted owners and generated declarations; they are not counts of newly authored named theorems.

Both raw audits and regenerated dependency DAGs are byte-identical to each other and to the parent final evidence. Independent reachability checks verify all 664 direct edges, 359 Hasse edges, and 10 layers. All 31 source files match across the two lanes. Nine owner mirrors and both exhaustive import-list mirrors match; all seven required new/promoted registrations occur once per lane. The exhaustive entry points were not compiled.

The agreed 35 tooling regressions passed. The five new owners passed strict static refutation with zero findings. The staged proof gate, both shell syntax checks, and staged whitespace check passed. Routing tests use temporary fixtures and subprocess recorders, not native compiler or publication substitutes.

## Retained limitations

Each source lane emits 95 warnings from 12 unchanged dependency modules. These are preserved in the full closure logs and module logs. The nine owned modules and the audit emit zero warnings.

The managed root path preflight returned exit 1 / `ok: false`: Atlas and HomotopyHypothesis lack tracked path-package configuration; GIFT is an uninitialized recorded gitlink with missing configuration. InfoGeometryCore is available. This result is separate from the passing isolated closures. No ordinary root Lake build, pre-push, whole-repository build, or CI completion is certified.

The graph describes expression constants in checked types and values, including opaque values, and excludes structural ConstantInfo metadata. It does not assert physical causation or every kernel reduction dependency.

Lean 4.34.1 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 remain pinned. Existing pinned mathlib caches were reused; project sources were rebuilt fresh. The executable and compatibility helper hashes were checked before/after. The helper only adapts current-process executable readlink lookup. It was not independently rebuilt. An ancillary `ps` monitor was unavailable on the host; direct `/proc` enumeration worked and no compiler was active at lane release.

## Evidence

- Repository/base: `cfbcbca21cf57a4614a9646768ba9356cf3cc6b0`.
- QA receipt: `qa-acceptance.json`; SHA-256: `07877e574553f3932d3600de02cb59a324378664ababdc8d0d90cd892d0bd4db`.
- A-A report SHA-256: `a76ae068c4dd9249054ea773585775a954a0b4bd4736a2ebb4e775c6b427e4f7`.
- Both raw audit SHA-256: `a660268d9350155d3e309d3f7d1d53a0acd3b84e90213951c7dfa32811bb6bfc`.
- Both DAG SHA-256: `45eafd79911832a1a72bba95f7f38377b8e9c641b119b2230f911d84523e834a`.
- Canonical result SHA-256: `34368b0cfa82c5ae1895ce6fac91a0f086a412762e16ba9f9afaeef00ae503da`.
- Src result SHA-256: `1711cb494fd8ca8712008b92859f67c92c92d4bd45cf52e01dece21f451a259b`.

All exact command arguments, exit statuses, source/tool/runtime hashes, native results, graph comparisons, and root preflight data are retained in the JSON receipt and its hashed artifacts under this QA directory. No repository source or index was changed by the reviewer.
