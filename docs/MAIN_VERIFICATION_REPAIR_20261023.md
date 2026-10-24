# Main verification bootstrap repair — 23 October 2026

Source reviewed: `ecccb38da69539e1ced7172f6d44cb1da0d97291`.
This is an infrastructure and verification-target change, not a mathematical
proof addition and not a bulk merge of the open PR stack.

## Concrete repairs

- Both host and optional-container version checks read `lean-toolchain` through
  `ci_bootstrap.py`. Exact version comparison replaces the stale 4.28.1 regexes;
  prefix collisions (4.34.10) and release candidates are rejected for a stable pin.
- Restore the missing `.gitmodules` URL for the already-recorded
  `sandbox/Grassmann.jl` gitlink. Its unchanged commit is
  `4f79a7fdb2d569bf6c13751fad3c078b6c135283`, verified at the upstream
  `chakravala/Grassmann.jl`. No gitlink is moved and submodules are not recursively
  initialized by this change.
- The root build performs a read-only preflight of direct `type=path` Lake
  dependencies and retains the JSON even on failure. A directory without a
  configured Lake file or a tracked source/initialized gitlink does not pass.
- The existing reviewed integration union gains nine explicit October owners.
  It retains every September target and its existing combined native axiom audit.
  Cache namespaces now name the actual Mathlib pin; source fingerprints and the
  allowed axiom set are not relaxed.

## Unresolved root-build prerequisites

`lake-manifest.json` names `Atlas` at `external_refs/atlas-lean`; that path is
not represented in the reviewed Git tree. The June inventory records a local
short SHA, not a complete reproducible dependency specification. No upstream
HEAD, stub, replacement package, or guessed revision is substituted.

`GIFT` at `external_refs/gift-framework-core` and `InfoGeometryCore` at
`lib/InfoGeometryCore` are also path dependencies. Checkout availability is
reported for all of them. The recorded InfoGeometryCore submodule URL is an
absolute local workstation path; this change does not invent a public mirror.

This preflight does not prove dependency correctness. It intentionally fails
closed when root-build sources are unavailable. It does not modify
`lakefile.lean`, `lake-manifest.json`, `lean-toolchain`, dependency source, or
proofs. No Lake cache is removed.

## Verification boundary

Seventeen isolated Python tests passed locally before submission. They test
version parsing and temporary Git fixtures, including missing/untracked local
packages, dirty or mismatched gitlinks, and path escape rejection. They are not
Lean proofs. Fresh CI outcomes and any mathematical compilation failures must
be recorded separately; a successful bootstrap test is not a green root build.

The reviewed integration lane compiles unchanged source against pinned Mathlib
and checks its combined environment. It is not the root Lake package build.
Unresolved external imports remain errors, rather than being stripped or stubbed.

## Reconciliation after infrastructure

1. Reuse `MajoranaCoefficientAction`'s `Fintype.linearCombination`,
   `linearCombination_injective`, and `quadraticElement` when adapting #198's
   summed quadratic action. Keep the real/skew normalization and the distinction
   between a conserved operator and a many-body state kernel.
2. Transport shell corners to the adjoint operator, not within a self-adjoint
   triangular operator. The unconditional identity is
   `star (S_m * a * S_r) = star S_r * star a * star S_m`.
   The adjoint of a range-shell filtration corresponds to the co-range
   construction for `star a`, not automatically its canonical range filtration.
   Prove that correspondence and test a nonzero nilpotent example.
3. Reconcile the corrected conjugate-linear Cuntz star before transporting any
   positive state, GNS representation, or colimit comparison. Finite readout
   equality alone is not equality of limit carriers.

No training-loop, Autograd, or uploaded block-causal attention code is changed.
