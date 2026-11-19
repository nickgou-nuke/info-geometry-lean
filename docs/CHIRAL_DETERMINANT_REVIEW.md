# Chiral determinant contribution: review and verification record

## Scope and source checkpoint

This record accompanies [the corrected theorem contract](CHIRAL_DETERMINANT_CONTRACT.md).
The implementation is based directly on upstream
`08c34e03f610b452e03422037949196dc7d92d6d`, with no dependency or toolchain changes.
It does not require the unmerged lattice-projector or Hilbert-Gram PRs.

| New owner | Source declarations | SHA-256 |
| --- | --- | --- |
| `InfoGeometry.LinearAlgebra.ExteriorDeterminantLine` | 15 theorem statements, 4 definitions, 1 abbreviation | `4ad3285fcfcfa0e7b93beb6bf0315aff8698e397644a2506cbd114e1a97e86a9` |
| `InfoGeometry.OperatorAlgebra.RectangularDeterminantOverlap` | 25 theorem statements, 3 definitions | `ab8e3903997ebe0ec85923880ea2c475dd1e2946843857a0abd22b69c6777460` |
| `InfoGeometry.OperatorAlgebra.SlaterDeterminantPairing` | 5 theorem statements, 3 definitions | `f57dd28764a274f63afb2c01ec03cf1263c7d15b37d7e4c23d11adecd81981ec` |
| `InfoGeometry.Clifford.Cl55ChiralDeterminantLine` | 2 theorem statements | `bcdfe6ab7753c326b00d2b70800440f0d98f682a4b9b523b65d9f5472e2160f1` |

There are **47 written theorem statements, 10 definitions, and one abbreviation**.
These are source counts, not a compiled declaration/axiom receipt. Generated
declarations are included by the native audit when it executes.

## Independent source review

Separate reviews inspected the native exterior/tensor carrier, coefficient
orientation, basis covariance, nonvanishing criteria, ordered matrix products,
range-support hypotheses, Slater dual pairing, and empty-rank case. They also
checked the relevant APIs in the pinned Mathlib source. No mathematical or
concrete source-API defect remained in the reviewed candidates.

The two real chiral-sector ranks and the exchange bijection come from actual
existing constructions. The positive generator squares to the identity and
provides inverse sector maps; the rank statement discharges the existing
conditional flip contract using that bijection. The consumer does not assume
its desired determinant nonvanishing in a structure field.

A bounded scan covered all **122 existing modules** imported by that concrete
chiral consumer. No executable custom axioms, proof holes, unsafe proof
shortcuts, or declaration-manufacturing bypasses were found. The only `axiom`
word match was a docstring; its theorem projects a relation from an explicitly
supplied algebraic structure. Two metaprogramming commands inspect architecture
metadata and do not construct mathematical axioms. This source inspection is
not a substitute for the compiled axiom audit.

The complete four-owner closure contains **126 repository modules**. The new
workflow's path triggers cover all of them. A separate workflow review checked
the exact target list, unchanged pins, source-head provenance, fresh repository
outputs, mandatory native axiom audit, and rejection of any compiler warning
in a new owner.

## Source-gate results

The following commands were run for the four new files:

```bash
python3 tools/quality/placeholder_audit.py --strict --root FILE --json-out REPORT
python3 tools/quality/semantic_vacuity_gate.py FILE1 FILE2 FILE3 FILE4 \
  --fail-on warning --json-out REPORT
```

The strict placeholder scan returned **0 for each file**, with **zero hard
findings**. It retained five soft skeletal-proof notices: four matrix helper
lemmas and `slaterPairing_star_mul_self`. These are direct uses of native
conjugate-transpose, product-associativity, and the proved determinant readback.

The warning-strict semantic gate returned **1**, with four `trivial_surface`
warnings:

| Declaration | Reviewed mathematical content |
| --- | --- |
| `frameRange_conjTranspose` | `FFᴴ` is self-adjoint, using the native reversal law and involutivity. |
| `compression_one` | Compression of the identity is the actual frame-overlap matrix. |
| `compression_frameChange` | The rectangular compression transforms by the ordered left adjoint and right frame factors. |
| `overlap_frameChange` | The occupied-frame overlap has the corresponding ordered covariance. |

These are reusable structural lemmas consumed by substantive determinant and
modulus results. Their proofs were retained. The heuristic, its thresholds,
and its findings were not changed or hidden; **the warning-strict semantic
gate is not reported as passing**.

The exact required Lean header is present in all four files. The workflow YAML
and its three embedded Python blocks were parsed successfully. This checks
configuration syntax, not a GitHub Actions execution.

## Native and integration verification

The first local native check was invoked with the maintained checker:

```bash
python3 -u tools/quality/check_clifford_dirac.py \
  --mathlib-root /workspace/scratch/50ddde16aff2/runtime/mathlib-4.34.1 \
  --lean /workspace/scratch/50ddde16aff2/runtime/lean-4.34.1-linux/bin/lean \
  --output /workspace/scratch/50ddde16aff2/determinant-verification/native-core \
  --target InfoGeometry.LinearAlgebra.ExteriorDeterminantLine
```

At this source checkpoint it is **waiting for the shared build lock**, with no
completed compiler or axiom report. The lock is not removed or bypassed. Hook
and publication outcomes are recorded in the PR as they become available.

The added `chiral-determinant-lines.yml` workflow checks all four targets with
the same maintained checker. It fetches the exact PR source head, verifies
Lean `4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, checks the Lean archive checksum,
hydrates only discovered native import roots under the shared lock, and
compiles the repository closure into fresh outputs. No repository `.olean`
cache is restored and no incremental/skip-audit option is used. It rejects
owner warnings and verifies native declaration axiom dependencies against the
allowed foundational axioms `propext`, `Classical.choice`, and `Quot.sound`.

The artifact contains source snapshots, hashes, logs, and reports for that
attempt. A passing result certifies those selected owners and their source
closure. It does **not** certify the full root Lake package, every tracked
historical file, the external Craig archive, or a continuum field theory.

## Mathematical boundaries retained

The finite result constructs a determinant amplitude and proves its frame and
projector identities. It supplies neither a smooth family nor a global
trivialization. The analytic obligations and corrected zero-mode/eta claims
are in the contract. In particular, a finite scalar frame law is not itself
an anomaly, a primed spectral determinant does not vanish merely because zero
modes exist, and a unit fermion-measure section is distinct from the determinant
amplitude it evaluates.
