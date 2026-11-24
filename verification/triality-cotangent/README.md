# Triality and cotangent native verification

Run from the repository root:

```bash
python3 -B verification/triality-cotangent/check.py
```

An installed exact-pin package provider may be supplied with Lake's official
package-location override format:

```bash
python3 -B verification/triality-cotangent/check.py --packages /absolute/packages.json
```

The wrapper selects seven owners and eleven reused declarations. It delegates
to the same locked transaction used by the Zorn/Souriau intake, whose original
defaults remain unchanged. It uses the existing focused package at
`verification/real-matrix-split`, the repository's Lean 4.34.1 toolchain, and
the exact nine pinned package revisions. No replacement package, weakened
axiom policy, symlinked Lake tree, or dependency update is involved.

The transaction builds the selected targets, freshly elaborates each with
warnings treated as errors, enumerates all declarations owned by those modules
from the native environment, and checks their transitive axiom dependencies.
Its receipts distinguish source inventory from native ownership. The only
permitted foundational axioms are `propext`, `Classical.choice`, and
`Quot.sound`.

The source snapshot includes tracked Lean sources, verification controls,
the new wrapper, intake contract, preserved proposal, review record, and
workflow. Each explicitly requested extra file must exist and be tracked;
an untracked/missing extra file causes failure rather than disappearing from
the fingerprint. HEAD, source hashes, override contents, and actual package
revisions/cleanliness are checked again before success is reported.

Receipts and command logs go to `artifacts/triality-cotangent/native` unless
`--output` selects another directory. A queued receipt is not a compiler
result. A source review is not native acceptance.

## The moved synthesis consumer

The elementary matrix declarations are moved, with their original names and
proof bodies, from the large synthesis owner to `TrialityCartanMatrixCore`.
The focused seven-owner check does not certify the entire large synthesis.
Its separate compatibility build is:

```bash
python3 -B verification/real-matrix-split/check.py build InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis
```

The hosted workflow runs that build after the focused native transaction.
Its result must be reported separately; a failure in that consumer does not
erase a completed focused receipt, and a focused pass does not certify the
consumer. The ordinary root publication gate is also a separate requirement.

## Mathematical coverage

The selected owners contain a native coadjoint action groupoid equivalence,
the actual restricted fixed-group action and faithful inclusion, bilinear
cotangent transport and nondegeneracy, a shear counterexample to the general
fixed-symplectic claim, an order-three sufficient condition, the exact change
of triality coordinate convention, native fixed-plane basis/dimension, and
the concrete matrix cycle's nondegenerate alternating cotangent fixed form.

No check in this directory establishes a smooth cotangent bundle, closed
multiplicative differential form, fixed Lie subgroup theorem, Killing-form
identification, full outer-triality action on a Lie group, or physical model.
