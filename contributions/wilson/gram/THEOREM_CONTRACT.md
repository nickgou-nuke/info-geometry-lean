# Positive complex kernels and finite Gram quotient colimits

## Current destination verification — 2026-11-25

The unchanged Lean sources passed the destination-pin build and fresh audit
in [run 45571203500](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45571203500),
job `139058006871`, at preparation source
`ff8e1632b45569d88da1c73c0ec160c913fe55f9`, on upstream
`c25e77e9654a54fc5e4a04bfb637b7144defacc0`. All 29 expected reports passed
the foundational-axiom check; source hashes and dependency pins matched.
Earlier validation records below retain their original scope and provenance.


## Destination and source provenance

Add `PositiveKernelFiniteColimit.lean`, `PositiveKernelLimit.lean`, and the opt-in
`PositiveKernelFiniteColimitAudit.lean` under the existing `LEAN/CoreLean/CoreLean/`.
Place `LICENSE-InfoGeometry-Apache-2.0` at the `LEAN/CoreLean/` project root.
Import the two substantive modules from the existing `CoreLean.lean` umbrella;
keep audit output out of the umbrella. Retain all existing pins and owners.

This contribution implements the finite-stage/Hilbert-completion pattern from
`nickgou-nuke/info-geometry-lean` at
`5e6396f87f8d4d0959c88896975b1aaaf3979009`, in particular
`lean/InfoGeometry/Canonical/FilteredIsometricInnerProductDirectLimit.lean` and
`lean/InfoGeometry/Canonical/FilteredIsometricHilbertCompletion.lean`.
It uses native Mathlib owners instead of importing that project's framework.
The short scalar pre-inner-product construction adapts Mathlib's
`Analysis/InnerProductSpace/Reproducing.lean`; its Apache attribution to Hampus
Nyberg and Yaël Dillies is retained in the source.

## Input and exact carriers

Fix an arbitrary test-label type `X` and an arbitrary complex kernel
`K : Matrix X X ℂ`. The construction takes `Fact K.PosSemidef`. Native
`Matrix.PosSemidef` includes Hermitian symmetry and positivity of the quadratic
form for every finitely supported complex coefficient family. It neither
assumes a Hilbert-space realization nor replaces the kernel by a scalar norm.

1. `PreHilbert K` is a kernel-tagged copy of `X →₀ ℂ`. Its sesquilinear form is
   `Σ x,y, conj (c x) * K x y * d y`, retaining complex values. The explicit
   linear equivalence `coefficients` transports raw coefficient families while
   keeping the kernel-dependent norm on the tagged carrier.
2. `Hilbert K` is its native separated uniform completion. Zero Gram seminorm
   is therefore factored out by the native completion construction.
3. For `F : Finset X`, `finiteEval K F : (F → ℂ) →ₗ[ℂ] Hilbert K` takes finite
   linear combinations of kernel feature vectors. `finiteGram` is the full
   complex double sum, and `inner_finiteEval` is its exact readback.
4. `stage K F` is `LinearMap.range (finiteEval K F)`, with the inherited complex
   inner product. `quotientEquivStage` is Mathlib's first-isomorphism equivalence
   from the actual algebraic quotient `(F → ℂ) ⧸ ker (finiteEval K F)` to this
   stage. The kernel is proved equal both to zero Gram quadratic norm and to
   the radical of the finite form. The quotient is therefore realized with
   the Gram geometry, rather than the unrelated quotient of a coefficient
   sup norm.
5. `Colimit K` is an actual `Module.DirectLimit` of these stages, over the
   directed partial order of finite test families. The structure maps preserve
   complex inner products and satisfy identity and composition exactly.
6. `completionEquiv K` is a complex linear isometric equivalence
   `Completion (Colimit K) ≃ₗᵢ[ℂ] Hilbert K`, with exact stage readback.

## Maps and theorem contract

`zeroExtend h` inserts zero coefficients for new labels along `F ⊆ G`.
`finiteEval_zeroExtend` proves that finite realizations commute with this map;
`finiteGram_zeroExtend` preserves the entire sesquilinear form. The induced
`quotientMap` is injective, has an exact representative formula, and commutes
with the concrete quotient embeddings.

`colimitToHilbert` is the native direct-limit lift of the stage inclusions.
Its injectivity is proved, rather than assumed. Its range is exactly the union
of finite stages, and that union is dense in the constructed Hilbert space.
The colimit norm and inner product are pulled back along this injective map.
`stageToColimitIsometry` and `colimitIsometry` expose the resulting isometries.

`existsUnique_lift` proves the algebraic universal property for every compatible
family of linear maps to an arbitrary complex module. It does not assert that
an arbitrary unbounded compatible family extends continuously to the Hilbert
completion. The completion equivalence uses the native extension of a linear
isometry and its dense, closed range.

`posSemidef_of_tendsto` in the separate limit module takes an arbitrary
nontrivial filter, eventual positive semidefiniteness of cutoff kernels, and
entrywise convergence. Native `MatrixOrder` order-closed topology yields Hermitian
positive semidefiniteness of the limiting kernel, even for infinite label sets.
This result supplies the positivity input to the finite-family construction.

## Wilson-loop interface and remaining mathematical inputs

For the proposed reflection-positive application, admissible half-space loop
ensembles are the labels, and the candidate kernel has the form
`K(D,E) = W(D ∪ θ(conj E))`, after fixing reflection, normalization, and coupling.
The present files do not define those target-specific operations. Their
admissibility, exact kernel formula, cutoff convergence, and reflection
positivity must be supplied by the Wilson-loop project.

There are two independent indices: the analytic cutoff and the finite test
family. Positivity passes to a limiting kernel through the first; the exact
isometric directed system then uses that single fixed kernel and the second.
The result does not identify different cutoff forms by exact isometries, or
assert a full C*-state, continuum Yang–Mills construction, mass gap, or GRH.

## Validation status

All three sources passed exact destination Lean 4.36.0 with Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, run `45458690593`,
job `138674999974`, preparation commit `0d848bd531f595d8cac0e06b13dad2e48fca8132`.
The warning-as-error build, separate fresh audit, source hashes and frozen
dependency checks passed. All 29 reports (27 public theorems and two main
isometry/completion definitions) use only `propext`, `Classical.choice`, and
`Quot.sound`. The parent matched the current source hashes to the successful
artifact in `validation/evidence/exact-gram-0d848bd`.

Native module visibility, complete Apache attribution and proof-local
classical choices resolved the earlier compatibility warnings. The header
linter remains enabled and expects the separately retained Apache notice.
An independent review confirmed that these changes preserve the full
complex Gram form, actual quotient/direct-limit carriers, maps and completion.
No linter suppression or unproved mathematical assumption was introduced.
