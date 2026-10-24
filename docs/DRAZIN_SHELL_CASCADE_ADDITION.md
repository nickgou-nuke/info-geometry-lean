# Addition to PR #193: one-step shell cascade

Base: `97fb2a606362bc09fa1f6681baa9d7b68c9599a0` on
`feat/drazin-shell-resolution`. This PR is additive and does not change the
existing inverse definitions or dependency pins.

## Ground-truth theorem contract

Carrier: a ring with a star-ring structure. Assume the existing canonical
`IsDrazinInverse a d k` and a genuine Moore-Penrose witness `g m` for each
actual power of `nilpotent a d`. Reuse `dressedRange` and `dressedShell` from
`Canonical.DrazinObliqueShellResolution`; no replacement predicate is added.

That owner proves nested compressed supports, shell idempotence, zero cross
products, telescoping, extinction, and recovery. This addition derives the
one-step consequence requested in the source summary: `S_m*a` equals its
projection onto the sum of the preceding shells; the leading map from shell
m+1 to shell m is faithful; and the entire operator is its regular part plus
these strictly lowering blocks. The regular recovery equations hold for
all natural powers, including zero.

The proof order is: right complement support -> partial telescope -> power
recovery representation -> strictly lower-shell action -> surviving leading
block -> faithful leading step -> full operator formula. It uses no spectral
basis, self-adjointness of the Drazin complement, or extra commutation of the
shells with the original operator.

A shell can be zero. Faithfulness is an implication about components, not a
claim that every index has a nonzero vector. `k` remains a witness bound,
not an asserted minimal Drazin index. The word isomorphism in the summary
names the two inverse identities on the regular summand; this file does not
introduce a new bundled Hilbert-space isometry or diagonalization.

## Verification

The dedicated workflow compiles the exact full transitive repository source
closure against the pinned Mathlib revision and audits every named declaration
in the new module. Its artifact records the checked commit, toolchain, source
hashes, compiler output, and axiom audit. A successful workflow, not this
candidate documentation, establishes compilation. This is not a full build.

Local repository command:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.DrazinShellCascade
```
