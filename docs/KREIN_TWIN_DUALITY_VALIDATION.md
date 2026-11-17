# Krein twin duality validation record

## Initial source checkpoint — 2026-11-17

Status: **draft; native compilation and axiom acceptance pending**.

Base revision: `08c34e03f610b452e03422037949196dc7d92d6d`.
Toolchain: `leanprover/lean4:v4.34.1`.
Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
The repository pins and existing gate implementations are unchanged.

## Completed source checks

- Independent semantic review of all three owners: passed. Review specifically
  checked noncommutative product order, left/right ideal sidedness, the two
  independent separation assumptions, the finite-dimensional boundary,
  reciprocal flow signs, and the derived reflection `1-2p`.
- Strict placeholder scans of the final three-owner checkpoint: passed with
  zero hard findings. Seven soft notices concerned five section-variable
  declarations and two real scalar polynomial helpers.
- Semantic-vacuity scan of that checkpoint at the maintained `error` threshold:
  passed. Eight soft notices concerned supporting evaluation/linearity lemmas;
  the substantive theorems were inspected separately.
- Installed staged proof gate on the publication sources: passed. Scalar
  polynomial computations have explicit real coefficient lemmas. The finite
  real matrix carrier has a closed noncommutativity witness.
- Whitespace check of all authored code, workflow and documentation: passed.
  A full diff check also flags trailing blank lines in raw input notes 3 and 4;
  those bytes are intentionally preserved and hash-recorded as user source.
- Source closure resolution: all **32** repository modules and **33** native
  import roots resolve. Resolution alone is not compilation.

The first local checker copied a snapshot before the final source clarifications.
While it was still waiting without starting a compiler, that obsolete waiting
process was stopped and the maintained checker restarted on the committed
sources. The canonical shared compiler lock was observed occupied throughout;
its holder was not interrupted and no replacement lock was used.

## Native verification command

From the independent repository checkout:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /workspace/scratch/44e3088154ac/mathlib4 \
  --lean /workspace/scratch/50ddde16aff2/runtime/lean-4.34.1-linux/bin/lean \
  --output /workspace/scratch/0878f2086cff/verification-twin-pairing-current \
  --incremental \
  --target InfoGeometry.Krein.ExchangedProjectionPairing \
  --target InfoGeometry.CliffordWeyl.KreinTwinIdealPairing \
  --target InfoGeometry.Krein.LoxodromicPairingFlow
```

The new `Krein twin duality kernel check` workflow fetches the exact PR head,
checks the same source closure under the same pins, audits all declarations
owned by the three targets, requires zero warnings in the new owners, and
uploads its native report, generated audit source, logs and evidence hashes.
It does not restore precompiled target owners.

Required axiom union is a subset of `propext`, `Classical.choice`, `Quot.sound`.
No axiom-union success is claimed before execution of the native audit.

## Observed remote integration result

The existing [Reviewed PR Integration run 44053258000](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44053258000)
failed during recursive checkout, before invoking Lean:

```text
fatal: No url found for submodule path 'external_refs/auto-ontology' in .gitmodules
```

Its later compilation and audit steps were skipped. This is an observed
repository checkout failure, not a diagnostic from any new Lean declaration.
The dedicated [Krein twin duality run 44053258035](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44053258035)
successfully fetched the exact PR source and pinned Mathlib checkout. On source
commit `69252237b6e1e41879e7127b8ede04a0d986454c`, all 29 pre-existing dependency
owners compiled. The two new generic/flow owners exposed theorem namespace,
endomorphism coercion, scalar-expression normalization and linter issues;
the matrix adapter was blocked by the generic owner. No axiom audit ran.
The subsequent source repair qualifies the native projection theorems,
annotates the reflection's endomorphism type, aligns the real polynomial
helpers with the actual elaborated expressions, and removes the two reported
warning causes. Its acceptance requires a fresh native run.

## Root integration boundary

The fresh checkout is independent, with the tracked pre-commit hook installed.
Source inspection found missing root path dependencies `HomotopyHypothesis`
and `Atlas`, and an uninitialized pinned `GIFT` package configuration. The
isolated source checker does not construct those packages. Root Lake and
repository-wide CI outcomes must therefore be reported separately from
selected-source kernel results. Neither a clean source scan nor this workflow
certifies all tracked historical owners or a physical interpretation.

This draft preserves a reviewable continuation. It does not certify merge
readiness, construct a modular/KMS state or Hardy space, prove a Dirac PDE
conservation law, or establish a physical stability or mass-gap theorem.
