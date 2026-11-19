# Spectral-table validation

## Result and scope

The focused mathematical and numerical checks pass. Root-package integration
remains blocked by the checkout's missing
`external_refs/homotopy-hypothesis-lean4` path dependency.

| Check | Observed result |
|---|---|
| Native source compilation | 15 declaration-bearing owners pass. |
| Native declaration audit | All 555 owned declarations, including private and generated declarations, pass. |
| Axiom dependencies | Only `propext`, `Classical.choice`, and `Quot.sound`. |
| Focused import-only umbrella | `InfoGeometry.Spectrometry.SpectralTableFactorization` passes with zero warnings. |
| Both strict OpenGauss source screens | All 16 files pass; zero findings. |
| Numerical reproduction | All three jobs pass; prior rounded interval endpoints reproduce exactly. |
| Root Lake target build | Exit 1 during package initialization, before target elaboration: missing `HomotopyHypothesis`. |

The selected Lean closure has 44 nonfatal linter warnings, itemized in
`lean_verification.json`; 11 occur in the existing `BipartiteLogCoupling` owner.
These differ from the strict source-screen results, which have no warnings or
errors. The audit source and umbrella have no warnings.

Lean is 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`.
Mathlib is `d13f23b723b8a846827a245b89c10fc7d3f11612`.
The toolchain, manifest, Lake configurations and maintained checkers are unchanged.

## Proof evidence

`lean_verification.json` contains the final source hashes, dependency
fingerprints, per-owner compilation results, exact declaration counts and
verification-tool hashes. `lean_axioms.log` lists every audited declaration.
The native checker inspects the actual imported environment and rejects unsafe
or partial owned declarations and axioms outside its maintained whitelist.
The three permitted dependencies are the standard logical foundations used by
Mathlib. The owners explicitly use noncomputable real mathematics; this audit
does not claim constructive executable real arithmetic.

Every selected owner was compiled successfully during this QA session.
The final pass compiled three owners and reused twelve compilation records only
after validating their source and dependency fingerprints. The final audit
revisited all 555 declarations. Source hashes, rather than the unchanged base
checkout revision in the report, identify the reviewed uncommitted source.

An independent source reviewer inspected the actual statements, assumptions,
proof bodies, existing owners, numerical input mapping and publication content.
A separate acceptance reviewer executed the compiler, native audit, source
screens, numerical reproduction and root-package attempt. The source reviewer
did not run those checks. `independent_source_review.json` records that separate
scope; `qa_acceptance.json` records acceptance limited to the focused checks.

## Reproduction

In an initialized root checkout, the ordinary focused target command is:

```bash
python3 tools/infra/run_locked_lake_build.py \
  --wait-for-build-lock \
  InfoGeometry.Spectrometry.SpectralTableFactorization
```

That is the actual command which encountered the missing path dependency here.
Its output and unchanged configuration fingerprints are preserved in
`root_lake_build.log` and `root_lake_build_execution.json`. Lake ran in the
normal network environment and initialized its manifest-pinned Mathlib and
LeanCopilot packages before finding the missing dependency.

The maintained generic target override in
`tools/quality/check_clifford_dirac.py` checked the selected source closure using
an already initialized checkout of the identical Mathlib pin. Set these three
task-specific variables to the initialized Mathlib directory, pinned Lean
executable, and a separate output directory, respectively:

```bash
mapfile -t spectral_targets < <(python3 -c \
  'import json; print("\n".join(json.load(open("artifacts/spectral_table_bridge/verification/lean_verification.json"))["targets"]))')
spectral_args=()
for spectral_target in "${spectral_targets[@]}"; do
  spectral_args+=(--target "$spectral_target")
done
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root "$SPECTRAL_MATHLIB_ROOT" \
  --lean "$SPECTRAL_LEAN_BIN" \
  --output "$SPECTRAL_QA_OUTPUT" \
  "${spectral_args[@]}"
```

The checker uses the repository's shared build lock. The import-only umbrella
was separately compiled through `run_locked_lean.py`, with a scratch Lake
adapter using the same pinned runtime and freshly verified owner artifacts.
`lean_execution.json`, `umbrella_execution.json` and
`source_screen_executions.json` preserve the command records. Local execution
paths in published receipts are replaced with `.` for this checkout,
`$SPECTRAL_QA_OUTPUT` for the isolated validation directory, and
`$PINNED_RUNTIME` for the restored runtime. These are portable path labels,
not claims that those shell variables were set in the original execution.

Run the numerical analysis with:

```bash
python3 tools/spectral_table_bridge/reproduce.py
```

The [numerical README](../../../tools/spectral_table_bridge/README.md)
describes the fixtures, commands and normalization conventions.
`numerical_verification.json` records versions, exit codes, source stability
and output fingerprints. The rational interval kernel is unchanged. Its
numerical enclosures are Python certificates, not Lean-kernel verification of
the entered numbers or experimental uncertainty intervals.

## Limits

This is neither whole-repository certification nor a passing root build. It
does not prove general rectangular Sinkhorn convergence, construct a complete
Aitchison metric-space interface, or identify a physical source of the measured
residuals. Close agreement between normalizations, small spectral interaction
and agreement with a spatial exponential remain separately evaluated questions.
