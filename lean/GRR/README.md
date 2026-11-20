# Grothendieck–Riemann–Roch port

This library ports the Lean development from
`grothendiecklabs/grothendieck-riemann-roch` at source commit
`2287b558a9c535ed2247e27577508cb67f2dfc72` into this repository's `lean/`
tree. The source notices and Apache-2.0 attribution are in `NOTICE`.

The principal theorem is `GRR.grothendieck_riemann_roch` in `GRR.Theorem`;
the Hirzebruch–Riemann–Roch corollary is
`GRR.hirzebruch_riemann_roch`. Their carrier and hypotheses are the external
project's scheme, coherent K-group, rational Chow group, smoothness, and
projectivity definitions. This port does not identify them with the local
operator-algebra or abstract GRR structures.

The root Lake project exposes these modules through the separate `GRR` library
target. That target is not a default build target because it imports the pinned
Stacks development, whose build surface is much larger than the GRR sources.
The root Lean toolchain and Mathlib revision remain the repository's existing
`v4.34.1` pins. Stacks is pinned to its `012108f61` commit, whose source and
dependency manifest target Lean/Mathlib 4.34.0-rc2; all 127 Stacks modules
directly imported by this GRR port are present at that revision.

Build status: the upstream Stacks head declares Lean/Mathlib `v4.35.0` and does
not work with this checkout's fixed `v4.34.1` environment. The 4.34-era Stacks
pin above contains all 127 direct GRR imports, but the locked `GRR.Theorem`
build still fails in Stacks prerequisites due to Mathlib API mismatches (for
example, missing `MvPolynomial.coeff` and `mem_specToProj_iff`). Therefore the
ported theorem source has not been kernel-checked in this repository. The root
Mathlib pin remains unchanged.
