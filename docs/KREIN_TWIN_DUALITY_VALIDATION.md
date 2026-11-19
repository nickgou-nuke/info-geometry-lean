# Krein twin duality validation record

## Current source checkpoint — 2026-11-17

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

## First proof-repair checkpoint

The repaired source checkpoint is remote commit
`2ebcfd88c96c2e3bb0aeaf024e1e538cad04ece6`, corresponding to local commit
`e246d448ab02eb6432802e56f555e448594e0b65`. Their complete source trees both
have Git tree ID `2563e3eeb1cfcd827efe781571587370b0fc01d6`.
The repaired-source placeholder and semantic checks were rerun successfully.

| Owner | Source SHA-256 |
|---|---|
| `Krein.ExchangedProjectionPairing` | `c234bf77c54e5e85d1ef4df5d9c320f5a286675a7ea0839ad69f7c0eaf4149e9` |
| `CliffordWeyl.KreinTwinIdealPairing` | `1baa92eb8838d6ff6d9320600ec4bad087cec6104da2fc602ec9a9e9344a00f0` |
| `Krein.LoxodromicPairingFlow` | `b999ae34d08c8bfa736db6846e724f618aa7a5740da091589f2eac065ded4412` |

The [second native run, 44055290321](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44055290321),
checked that exact remote commit and completed with native compilation errors.
The documentation-only head `9e876c7e33d9086df3c9dc88d78bc50236a654f7`
had byte-identical Lean owners and reproduced those diagnostics in
[run 44062639425](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44062639425).

The generic `ExchangedProjectionPairing` owner now compiled with zero warnings.
All 29 pre-existing dependency owners also compiled. The matrix adapter exposed
five elaboration/simplification failures and four unused-section-variable
warnings; the flow owner exposed one scalar-linearity failure and one unused
simp argument. Neither failed run reached the declaration axiom audit.

## Second proof repair

The present repair makes the linearity goals explicit before simplification,
removes only the typeclass assumptions reported unused by Lean, and calculates
the real matrix witness through separately established star/idempotence/adjoint
identities. The flow scalar proof likewise states its actual real-linear goal
before normalization. No theorem conclusion, noncommutative product order,
carrier, dependency pin, or acceptance rule is weakened.

The candidates were independently proposed and parent-reviewed against the
complete native goal states. The exact remote repair commit
`6d1af173f79dcbd8af1e56e461ba4079492d8409` was checked by
[run 44087804066](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44087804066).
Both `ExchangedProjectionPairing` and `KreinTwinIdealPairing` compiled with zero
warnings. The flow owner had zero warnings and one remaining scalar-linearity
error; the audit was not reached. All 29 unchanged dependency owners compiled.
The prior local waiting attempt produced no environment, compiler log, or
report, and its process session is no longer registered; it is not verification
evidence. A fresh local attempt must use the current source snapshot and the
same occupied shared lock.

| Second-repair owner | Source SHA-256 |
|---|---|
| `Krein.ExchangedProjectionPairing` | `c234bf77c54e5e85d1ef4df5d9c320f5a286675a7ea0839ad69f7c0eaf4149e9` |
| `CliffordWeyl.KreinTwinIdealPairing` | `826ea74e4f30788d6c37ccd276dad7c498418aec5e00c204b05cbf2cf221e674` |
| `Krein.LoxodromicPairingFlow` | `41804fce487d282c6e05deb1a36a721c29770b7bb8622fd887fb76d697f776b5` |

## Third proof repair

The remaining flow proof now identifies the boost and rotor as native real
endomorphisms, and proves scalar preservation using `LinearMap.map_smul` on
their composition. The preceding simplification had left an addition inside
the outer endomorphism opaque to module normalization. No declaration type
or mathematical hypothesis is changed. This source repair still requires
native compilation and the complete declaration audit.

The second-repair local attempt acquired the canonical lock but failed with
`No space left on device` before compiling any module. Its own later retry
remained waiting, with no compiler process or native artifacts, and was stopped
once the remote diagnostic made that snapshot obsolete. The occupied lock's
other holder was not interrupted. Task-owned clean source worktrees were made
sparse to recover storage; no dependency cache was removed.

## Native verification command

From the independent repository checkout:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /workspace/scratch/44e3088154ac/mathlib4 \
  --lean /workspace/scratch/50ddde16aff2/runtime/lean-4.34.1-linux/bin/lean \
  --output /workspace/scratch/0878f2086cff/verification-twin-pairing-repair3 \
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

Other repository-wide jobs on the same initial PR checkpoint had independent
baseline failures:

| Job | Observed result |
|---|---|
| [Post-Build Quality Gate 44053257933](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44053257933) | The maintained locked `lake build` command failed because `external_refs/homotopy-hypothesis-lean4` is absent. The later quality-gate step was skipped. |
| [Lean style lint 44053257743](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44053257743) | Case-sensitivity checking found the existing `lean/docs` and `lean/Docs` directory collision before Lean style lint ran. |
| [Sorry Gate 44053257758](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44053257758) | The tracked-source audit reported 878 findings in 91 files, all classified as archive/fixture material. None is one of the three new owners. |

Independent comparison verified that all 91 listed debt files have identical
Git object IDs at the base revision and repair checkpoint, and that both
case-colliding directory trees and the root package configurations are
unchanged. These runs checked merge revision
`d9c2c4afe44b24827694930957de75db9227c9b5`, containing the initial task head;
they are not represented as executions of a later repair revision.

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
