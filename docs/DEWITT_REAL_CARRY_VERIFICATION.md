# DeWitt real carry: independent verification record

## Result and source snapshot

**PASS, scoped to the selected source package.** Independent acceptance completed
on 2026-11-08 at 05:28:24 UTC. The build, imported-environment audit, source
screening, staged proof gate, and staged whitespace check passed. The five Lean
files below matched their staged bytes before and after acceptance; their
SHA-256 hashes did not change. The reviewer made no production-source edits.

- Repository base: `3d7eb6d9b0af5636ab12b3d0b91b82740507e49e`.
- Lean: `leanprover/lean4:v4.34.1`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- The repository's dependency pins and root Lake configuration were unchanged.
- The publication gate was **not run as part of this acceptance**.

The selected package compiled the repository's actual `lean` directory through
`srcDir`; it did not copy, replace, or weaken the production sources.

## Locked build

The following command was executed from the repository checkout after sourcing
the prepared native runtime:

```bash
source /workspace/scratch/2771a9ff6f38/parafermion-runtime/development-environment.sh
cd /workspace/scratch/87f585b3ae15/info-geometry-lean
python3 tools/infra/run_locked_lake_build.py \
  --wait-for-build-lock --wfail \
  InfoGeometry.Canonical.RealCarryAudit \
  -- --dir /workspace/scratch/87f585b3ae15/verification/dewitt
```

The maintained wrapper acquired `/tmp/info-geometry-build.lock`, executed the
selected Lake build, and released the lock. The build exited **0**, completed
**8,932 jobs**, and produced no selected-package compiler warnings. This was a
normal incremental Lake build; the job count is not a count of newly proved
theorems or freshly rebuilt modules.

### Reproduction package

Use an independent directory with an ordinary, nonsymlinked `.lake` directory.
Its `lean-toolchain` contains `leanprover/lean4:v4.34.1`. Its `lakefile.toml` is:

```toml
name = "dewitt_verification"
version = "0.1.0"

[[require]]
name = "mathlib"
path = "/ABSOLUTE/PATH/TO/MATHLIB-AT-d13f23b723b8a846827a245b89c10fc7d3f11612"

[[lean_lib]]
name = "InfoGeometry"
srcDir = "/ABSOLUTE/PATH/TO/INFO-GEOMETRY-LEAN/lean"
```

The uppercase paths are **placeholders**, not literal tested paths. Replace
them with the pinned Mathlib checkout and the unchanged production checkout.
Run the maintained repository wrapper above with `--dir` set to this package.
Use the repository build lock for every compiler invocation. This recipe does
not require changing the production Lake configuration or dependency pins.
The tested selected-package manifest used local paths to this exact Mathlib
checkout and the dependency checkouts recorded by its pinned manifest; it did
not resolve newer dependency revisions.

## Imported-environment audit

`InfoGeometry.Canonical.RealCarryAudit` enumerates declarations belonging to
the four exact imported owners, including private and compiler-generated
declarations. It rejects introduced axioms, unsafe or partial declarations,
and every collected axiom dependency outside `propext`, `Classical.choice`,
and `Quot.sound`. It also fails if an expected owner is absent or empty.

| Owner below `InfoGeometry` | Audited declarations |
|---|---:|
| `OperatorAlgebra.PeirceSpine.BinaryCarry` | 33 |
| `Algebra.QuarticRotor` | 29 |
| `OperatorAlgebra.PeirceSpine.BinaryCarryStar` | 7 |
| `Canonical.RealCarryMatrix` | 31 |
| **Total** | **100** |

The total contains **86 theorem declarations**, including private/generated
theorems. The observed axiom union was exactly:

```text
[propext, Classical.choice, Quot.sound]
```

### Per-theorem axiom probe

A fresh scratch `FinalAxiomProbe.lean` imported `BinaryCarryStar` and
`RealCarryMatrix` and issued `#print axioms` for the 18 declarations identified
below. It was elaborated by the maintained
`tools.infra.run_locked_lean.execute_locked_lean` helper with the selected
package as `root` and `wait=True`. The resulting compiler command was
`lake env lean FinalAxiomProbe.lean`, under the same shared build lock; exit **0**.

All eight ring-only results in `InfoGeometry.Algebra.QuarticRotor` had exactly
`[propext]`:

```text
pow_eight_eq_one
quadratic_gauss_identity
quartic_gauss_sum
parity_factors_mul_zero
parity_channel_mul_zero
rotorNumerator_commute_inverseNumerator
rotorNumerator_mul_inverseNumerator
inverseNumerator_mul_rotorNumerator
```

These six results in `InfoGeometry.OperatorAlgebra.PeirceSpine` also had exactly
`[propext]`:

```text
binaryCarry_sq
binaryCarry_pow_four
binaryCarry_pow_eight
binaryCarry_mul_inverse
binaryCarry_inverse_mul
carryReflection_conjugates
```

The following four results had the full permitted union
`[propext, Classical.choice, Quot.sound]`:

```text
InfoGeometry.Algebra.QuarticRotor.normalizedRotor_mem_unitary
InfoGeometry.OperatorAlgebra.PeirceSpine.binaryCarry_orderOf_eight
InfoGeometry.OperatorAlgebra.PeirceSpine.binaryCarry_normalizedRotor_mem_unitary
InfoGeometry.Canonical.RealCarryMatrix.phi8Companion_orderOf_eight
```

Thus `[propext]` alone describes the listed ring identities, not the entire
delivery. No custom axiom or proof-hole axiom was accepted by the native audit.

## Source and staged checks

These checks ran after the successful build and all exited **0**:

```bash
python3 tools/infra/opengauss_screener.py --strict --json \
  lean/InfoGeometry/OperatorAlgebra/PeirceSpine/BinaryCarry.lean \
  lean/InfoGeometry/Algebra/QuarticRotor.lean \
  lean/InfoGeometry/OperatorAlgebra/PeirceSpine/BinaryCarryStar.lean \
  lean/InfoGeometry/Canonical/RealCarryMatrix.lean \
  lean/InfoGeometry/Canonical/RealCarryAudit.lean
python3 scripts/vacuity-linter.py --json lean/InfoGeometry/OperatorAlgebra/PeirceSpine/BinaryCarry.lean
python3 scripts/vacuity-linter.py --json lean/InfoGeometry/Algebra/QuarticRotor.lean
python3 scripts/vacuity-linter.py --json lean/InfoGeometry/OperatorAlgebra/PeirceSpine/BinaryCarryStar.lean
python3 scripts/vacuity-linter.py --json lean/InfoGeometry/Canonical/RealCarryMatrix.lean
python3 tools/quality/proof_proxy_staged_gate.py
git diff --cached --check
```

The strict OpenGauss screener reported no violations. The staged proof gate
reported `proof_proxy_staged_gate: ok`. The whitespace check was clean.

The heuristic vacuity linter had two findings, independently classified:

| File | Finding | Review |
|---|---|---|
| `BinaryCarry.lean` | `no_hyp_use`, `hPhi` | False positive. `hPhi` is used in `.symm.trans hPhi`, helper applications, and explicit rewrites in the normalized bridge proofs. |
| `QuarticRotor.lean` | `no_hyp_use`, `ζ` | False positive. `ζ` occurs in calculation expressions, local commutation lemmas, and helper applications. The line-oriented regex does not analyze Lean free-variable use. |
| `BinaryCarryStar.lean` | None | No linter findings. |
| `RealCarryMatrix.lean` | None | No linter findings. |

Independent semantic review also passed: local `Commute` hypotheses preserve
the noncommutative ambient ring; primitive star laws yield the carry adjoint;
normalized unitarity explicitly requires invertible `2`; exact order requires
`-1 != 1`; and the integral matrix witness realizes the construction. No braid
relation, Clifford/Lie dimension theorem, or physical interpretation is
certified by these checks.

## Root-package boundary

Before the successful selected-package build, the wrapper attempted root-package
cache hydration with `lake exe cache get`. That operation reported the existing
missing dependency:

```text
HomotopyHypothesis: package directory not found:
  external_refs/homotopy-hypothesis-lean4
```

The failed root-package hydration and the successful selected-package build
are separate outcomes. This record does **not** certify a root-package build
or unrelated repository modules. No dependency repair or pin change was made.

## Accepted source hashes

Paths are relative to `lean/InfoGeometry/`. These SHA-256 hashes identify the
exact staged and compiled source bytes accepted by the reviewer.

| Source | SHA-256 |
|---|---|
| `OperatorAlgebra/PeirceSpine/BinaryCarry.lean` | `3e726ba6007b9525dad0b3fc77dd3424a9c46ae2adb788d0d6ae80ec9ed3f152` |
| `Algebra/QuarticRotor.lean` | `a7631e1ca7d728867ac464e6f2eb26a668d8d0a58455189b22c2396c70374e27` |
| `OperatorAlgebra/PeirceSpine/BinaryCarryStar.lean` | `f5dbce8addfd383a29918a619de678c25903b2e3b67991e4dc18d3ad2dbcadfc` |
| `Canonical/RealCarryMatrix.lean` | `9db3a6780491db2b992473a322261bf0e52d1daf0d4bec97efd8c2902451daf5` |
| `Canonical/RealCarryAudit.lean` | `1c73c42fccbb22156e3ef6b526e03a5be617b6ec0ee139bf31880abadc39409d` |

Full run evidence was retained outside the production repository as
`verification/final-qa.json`, `verification/final-build.log`,
`verification/final-axioms.log`, and `verification/final-checks.json` in the
acceptance workspace. This record retains the reproducible commands, observed
results, and source hashes without embedding the host-specific JSON reports.
