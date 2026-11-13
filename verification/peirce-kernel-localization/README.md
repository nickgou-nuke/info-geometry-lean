# Focused Peirce kernel localization validation

This package checks nine mathematical owners against the repository's exact
Lean and Mathlib pins. It provides an isolated Lake target for these owners and
their actual imports; it does not replace the repository's default-target
build or its other quality gates.

## Mathematical scope

- `CentralPowerLocalization`: the genuine noncommutative Mathlib Ore quotient
  at powers of a central element, ordered representative multiplication,
  eventual equality, the exact power-torsion kernel, regularity-based
  injectivity, an internal denominator inverse, and unique ring factorization.
- `CentralPowerLocalizationStar`: well-defined quotient star for a
  self-adjoint denominator, a star-ring instance, and internal Cayley unitarity
  derived from polynomial numerator identities.
- `CentralPowerLocalizationColimit`: constructed stage maps and full
  existence-and-uniqueness universal properties for arbitrary additive groups
  and native integer modules. The same carrier retains the ordered
  convolution multiplication. Multiplication by the denominator is not treated
  as a ring homomorphism. No categorical `DayConvolution` API instance is claimed.
- `OnShellKernel`: centrality in the generated Peirce subring, idempotent
  support/kernel decomposition, and a star-ring structure on the generated
  subring under the stated hypotheses.
- `CayleyKernelRegularity`: regularity of the shifted denominator from explicit
  star-square faithfulness, on-shell Moore–Penrose relations, and the
  polynomial partial-flip identity.
- `CayleyKernelLocalization`: the actual internal unitary and conjugated
  projection, singular kernel erasure, shifted kernel preservation and
  faithful localization, including its real Hilbert-space application.
- `RealStarSquareFaithfulness`: the requisite star-square faithfulness is
  proved for bounded operators on a complete real inner-product space.
- `RealSupportCoercivity`: an actual support projection and spectral-gap
  equivalence for arbitrary finite-dimensional positive real operators,
  together with a kernel obstruction and a sequence with no uniform gap.
  The latter is a sequence theorem, not a claim about an unspecified
  compatible inductive-limit element.
- `KernelMatrixWitness`: explicit noncommuting full real matrix examples
  retaining a nonzero zero mode and two independent residual kernel corners.
  These do not claim a general rank classification.

The source contract is
[`../../docs/PEIRCE_KERNEL_LOCALIZATION_CONTRACT.md`](../../docs/PEIRCE_KERNEL_LOCALIZATION_CONTRACT.md).

## Commands

Run these commands from the repository root with the pinned `lake` executable
available on `PATH`. `check.py` acquires the repository's shared build lock and
rejects linked worktrees and symlinked Lake roots. It preserves dependency and
build caches. Run compilation and other validation serially.

After a mathematical declaration changes, regenerate and check the explicit
source inventory:

```bash
python3 verification/peirce-kernel-localization/audit.py --write
python3 verification/peirce-kernel-localization/audit.py
```

When the pinned dependency artifacts need restoration, use the focused
package's native cache command:

```bash
python3 verification/peirce-kernel-localization/check.py exe cache get
```

Build the aggregate and audit targets, then execute a fresh audit invocation.
The audit execution is required even if Lake reports a cached target.
`pipefail` preserves the actual Lean exit status when saving logs.

```bash
set -euo pipefail
python3 verification/peirce-kernel-localization/check.py build 2>&1 | tee peirce-kernel-build.log
python3 verification/peirce-kernel-localization/check.py env lean lean/InfoGeometry/OperatorAlgebra/PeirceSpine/KernelLocalizationAudit.lean 2>&1 | tee peirce-kernel-axioms.log
python3 verification/peirce-kernel-localization/audit.py --log peirce-kernel-axioms.log
```

Screen all nine mathematical owners:

```bash
python3 tools/infra/opengauss_screener.py --strict \
  lean/InfoGeometry/Algebra/CentralPowerLocalization.lean \
  lean/InfoGeometry/Algebra/CentralPowerLocalizationStar.lean \
  lean/InfoGeometry/Algebra/CentralPowerLocalizationColimit.lean \
  lean/InfoGeometry/Analysis/RealStarSquareFaithfulness.lean \
  lean/InfoGeometry/Analysis/RealSupportCoercivity.lean \
  lean/InfoGeometry/OperatorAlgebra/PeirceSpine/OnShellKernel.lean \
  lean/InfoGeometry/OperatorAlgebra/PeirceSpine/CayleyKernelRegularity.lean \
  lean/InfoGeometry/OperatorAlgebra/PeirceSpine/CayleyKernelLocalization.lean \
  lean/InfoGeometry/OperatorAlgebra/PeirceSpine/KernelMatrixWitness.lean
```

## Evidence and limits

`audit.py` checks exact toolchain equality with the root; the nine focused Git
dependencies' URLs, revisions and subdirectories against the root manifest;
and the focused lakefile's pinned Mathlib requirement. It does not update pins.
The focused dependency list is an intentional subset of the root workspace,
which has additional unrelated dependencies.

The inventory is a bounded line-oriented extractor for the declaration forms
used by these nine files. It includes explicitly named public instances,
definitions and theorems, and rejects anonymous or unsupported declaration
heads. It is not a Lean parser or a complete enumeration of automatically
generated declarations. Private helpers are not independently listed; Lean's
axiom reports traverse the audited heads' dependencies. The script rejects
prohibited proof constructs in the selected owner source and checks that one
fresh audit log contains exactly one record for each inventoried name, with
only `propext`, `Classical.choice` and `Quot.sound` as foundational axioms.

Source inventory, successful kernel compilation, the transitive axiom check,
strict screening, independent semantic review and distinct acceptance review
are separate pieces of evidence. These commands do not, by themselves,
certify the prose interpretation or the whole repository.

The `Peirce kernel localization` workflow repeats these focused checks and
saves build, fresh axiom and checkout-identity logs. Its revision log records
the checkout commit followed by its full Git tree; a pull-request workflow
can test GitHub's merge checkout rather than the branch head. Report the
observed revision and tree, toolchain, results, independent review scope and
any failures when publishing. This README is not a claim that a particular
execution has already passed.
