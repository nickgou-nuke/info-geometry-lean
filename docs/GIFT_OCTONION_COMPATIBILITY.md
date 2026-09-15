# GIFT octonion compatibility with Lean 4.28.1

## Source pin

The GIFT submodule now uses `https://github.com/Arithmon/K7-Lean.git`,
the renamed upstream of `gift-framework/core`.
The user approved replacing the unavailable commit
`e6f3c3ac2140c2324fb2ae029c32233e73aa5e92` with the latest upstream revision.
On 2026-09-15, upstream `main` resolved to
`0a1252cda1f63cb1054918d19471e86031843449`; the parent repository pins this
exact commit rather than following a moving branch.

No upstream proof files were copied, rewritten, or duplicated. The submodule
worktree is unchanged from that commit. The root Lean toolchain remains
`leanprover/lean4:v4.28.1`, and its Mathlib revision is unchanged.

## Verified scope

The following source files compiled successfully with Lean 4.28.1
(`978f81d363eabdc49c5720726faa53a6007fcee8`):

- `GIFT/Algebraic/Octonions.lean`, from the pinned submodule, with the package's
  `autoImplicit=false` and `relaxedAutoImplicit=false` settings.
- `lean/InfoGeometry/Canonical/HopfTest.lean`, the existing repository consumer.

These were sequential source checks under `/tmp/info-geometry-build.lock`,
using the separately rebuilt, pinned 4.28.1 dependency artifacts in
`/tmp/isnp-rebuilt-4.28.1`. They were not a successful full `lake build -R`.
The octonion module required no source changes to compile on 4.28.1.

The upstream project itself targets Lean 4.33.1. The checks above establish
compatibility of the imported octonion module and its current consumer only,
not a port of every upstream GIFT module. Run builds from this repository's
root to retain its toolchain and dependency selection.

## Mathematical boundary

The imported module defines an eight-coordinate carrier, imaginary units,
componentwise addition, negation, subtraction, scalar multiplication,
conjugation, and a list of Fano triples. It does not implement octonion
multiplication or prove alternativity or norm multiplicativity. Several
finite counting proofs use `native_decide`; compilation is not a claim that
all proofs avoid native computation.

The existing `HopfTest` defines a coordinate norm and proves a real polynomial
identity under an explicit sphere equation. Its successful compilation does
not establish an octonionic Hopf fibration. The repository's existing Zorn
and split-octonion multiplication owners remain separate and unchanged.
