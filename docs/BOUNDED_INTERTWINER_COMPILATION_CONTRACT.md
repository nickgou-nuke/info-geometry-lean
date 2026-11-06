# Bounded intertwiners, cyclic vectors, and typed operator products

## Intake and formal intent

This task compiles the operator claims in the supplied reference-lineage essay.
The source was preserved without modification:

- Uploaded filename: `Pasted text(10).txt`.
- Size: 23,364 bytes.
- SHA256: `6634f7c5192be4f0be55b5dfb684236908c1849cb2c6fee5fb1bda60049705ba`.
- Starting repository revision: `3d7eb6d9b0af5636ab12b3d0b91b82740507e49e`.
- Branch: `codex/bounded-intertwiner-linking`.

The intended outputs are theorems about actual bounded operators on possibly
different, possibly infinite-dimensional spaces. The proposed conflation of a
map between representations with a nilpotent endomorphism is repaired by an
explicit map into a product-space endomorphism algebra. Cyclicity and Hilbert
adjoints are handled on their own native carriers. No conformal-net structure,
Connes fusion, covariance lift, or categorical balance is supplied as a proof
field and then reported as constructed.

## Primary sources and bibliography repair

1. [Marín-Salvador, arXiv:2605.18446v2](https://arxiv.org/html/2605.18446v2),
   especially Definitions 3.1–3.2, Theorems 3.5 and 4.4–4.5, and References.
2. [D'Antoni–Fredenhagen–Köster, math-ph/0312017](https://arxiv.org/abs/math-ph/0312017).
3. [Henriques, arXiv:1706.08471](https://arxiv.org/abs/1706.08471),
   *Loop groups and diffeomorphism groups of the circle as colimits*,
   Communications in Mathematical Physics 366 (2019), 537–565.
4. [Henriques–Nivedita–Penneys, arXiv:2411.01678](https://arxiv.org/abs/2411.01678),
   *Complete W\*-categories* (2024).
5. [Gui, Categorical Extensions of Conformal Nets](https://doi.org/10.1007/s00220-020-03860-8),
   Communications in Mathematical Physics 383 (2021), 763–839.
6. [Fixed-points extension, arXiv:2606.06402v2](https://arxiv.org/abs/2606.06402v2).
7. [Heisenberg extension, arXiv:2608.02574](https://arxiv.org/abs/2608.02574).

The checked v2 bibliography has **23 numbered references**, not the asserted
20. The intake combines DHR I and II, omits Fredenhagen–Rehren–Schroer II
(1992) and Takesaki's *Theory of Operator Algebras II* (2003), and mixes the
paper being read with later companion papers. Its `[Hen19]` and `[HNP24]`
titles are inaccurate; items 3 and 4 above give their actual titles and authors.
The fixed-points paper assumes a faithful finite-group action; the Heisenberg
paper is a separate concrete crossed-category computation. Publication dates
and citations establish provenance, not Lean dependency edges.

## Atomic claim ledger

| ID | Intake claim | Disposition and exact correction |
|---|---|---|
| C01 | The bibliography is a complete 20-paper proof DAG. | Incorrect inventory; v2 has 23 numbered entries. A bibliography is not a formal dependency DAG. |
| C02 | DHR endomorphisms require rationality. | Overstrong. Keep the DHR description distinct from finite statistical dimension, dualizability, and rationality of the net. |
| C03 | Nonrational means every sector has infinite dimension or logarithmic Jordan form. | False implication; neither follows merely from nonrationality. |
| C04 | A bounded intertwiner `T : H₀ → H` is already square-zero. | Ill-typed when the two spaces differ. Construct an endomorphism `creation T` on `E × F`. |
| C05 | Nonzero intertwiners give nonzero square-zero blocks. | Candidate: prove faithfulness and zero products for the explicit bounded block embedding. |
| C06 | The block commutes with the complementary corner. | False in general. Intertwining corresponds to commutation with a diagonal pair of actions. Commutation with the target-coordinate projection forces the block to vanish. |
| C07 | The vacuum vector is the projection `P`. | Different types. Evaluation at `(Ω, 0)` gives `(0, T Ω)`; no identification of a vector with an idempotent is made. |
| C08 | `T Ω` determines an intertwiner. | Candidate under dense linear span of the source orbit; prove equality by continuity and linearity. |
| C09 | Every target vector has a bounded intertwiner. | Not implied by uniqueness. The bounded-vector subspace is defined using an existence condition. |
| C10 | Cyclicity can be supplied by an existing completed carrier. | Candidate specialization to native `PositiveLinearMap.GNS`, using the existing dense orbit theorem. |
| C11 | `Tξ Tη Ω` is the fused vector. | Generally ill-typed: both maps start at the vacuum space and have different targets. Products of the same oriented linking blocks are zero. |
| C12 | Products `S† T` give source-space operators. | Candidate for Hilbert spaces: prove the adjoint intertwines in reverse and `S† ∘ T` commutes with the source representation. |
| C13 | This Gram commutation constructs Connes fusion. | Open debt: relative tensor product, positive form, null quotient, completion, and localization maps are additional constructions. |
| C14 | The product block construction is a Hilbert/C\*-linking algebra. | Not asserted. Native `E × F` has the maximum norm here; no product Hilbert inner product or adjoint is installed. |
| C15 | Type III alone makes arbitrary representations locally equivalent. | Missing representation hypotheses. Keep nonzero, normality, and the relevant Hilbert-space size assumptions explicit in any future formalization. |
| C16 | Diffeomorphism covariance gives the required sector covariance. | External theorem with its locally normal representation hypotheses; no Lean construction is claimed here. |
| C17 | A bare Möbius-covariant theory cannot have a twist because its fundamental group is nontrivial. | Overstrong. An already supplied universal-cover representation has a central deck operator; automatic existence for all sectors is a separate issue. |
| C18 | The lifted full rotation is a noncontractible loop in the universal cover. | Incorrect: its endpoints differ by a deck transformation. It is not a loop there. |
| C19 | `exp(-2πit)` rotates counterclockwise and a half-turn swaps arbitrary intervals. | The displayed sign is clockwise in the usual complex-plane orientation; arbitrary intervals need not be exchanged by a rigid half-turn. |
| C20 | The balance is ordinary operator multiplication. | Requires the actual tensor functor, braiding, naturality, and support continuation. These cannot be replaced by unrelated block products. |
| C21 | All bibliography arrows are proved implications. | Rejected. Only actual theorem dependencies enter the formal dependency table below. |

## Source ownership and search boundary

Searches covered tracked `lean`, `proofs`, the relevant tooling/entrypoints,
explicitly filtered `external_refs`, and the pinned native Mathlib source.
Queries included `Connes fusion`, `bounded intertwiner`, `cyclic vector`,
`linking algebra`, `adjoint`, `intertwin`, block maps, and alternate products.
The context preflight and follow-up searches are navigation evidence. Local
declaration/InfoTree/LeanSearch indexes were absent; no remote graph was
assumed complete or refreshed to manufacture evidence.

| Existing owner | Actual reusable surface | Boundary |
|---|---|---|
| `Core.OperatorCliffordDouble` | Algebraic block operators on `M × M`. | Does not provide the heterogeneous bounded `E →L F` embedding. |
| `OperatorAlgebra.ChiralBlockSpectralGap` | Bounded same-space blocks on `E × E`. | Its spectral assumptions and same-space carrier are unnecessary here. |
| `SuperGrassmannian.ProjectorGraphChart` | Algebraic graph projectors and a diagonal intertwining criterion. | No operator norm or continuity assertion for the heterogeneous bounded block. |
| `Clifford.TwistedChiralLinking` | Peirce corner subtypes and a supplied twist. | No constructed conformal representation, fusion, or Hilbert linking completion. |
| `OperatorAlgebra.CommutantIntertwine` | Ring equivalence and `SheetConnection` data with an intertwining field. | Not a bounded Hilbert-space intertwiner theorem. |
| Native `ContinuousLinearMap` product API | `inr`, `fst`, `prodMap`, bounded composition, operator norm. | Used directly for the new embedding. |
| Native `ContinuousLinearMap.ext_on` | Equality from agreement on a set with dense linear span. | Cyclic intertwiner uniqueness is derived using the ordered intertwining equations. |
| `PositiveLinearMapGNSVacuum` and `GNSMathlibBridge` | Native completed GNS carrier, vacuum, representation, and `gnsOrbitMap_denseRange`. | No identification with a conformal-net vacuum is assumed. |
| Native Hilbert adjoint API | `adjoint_comp`, `adjoint_adjoint`, `star_eq_adjoint`. | Applied to actual maps between two complete inner-product spaces. |
| Native `BraidedCategory.braiding_naturality` | Reorders tensor morphisms through a braiding, with typed domains and codomains. | Already native; not duplicated or reported as a construction of a conformal-net balance. |
| `Canonical.MonoidalRibbonPentagonHexagonCapstone.RibbonTwist` | Supplied objectwise isomorphisms and tensor-balance fields. | These fields do not construct the analytic or categorical structures in the intake. |

The nearby owners' definitions, hypotheses, imports, and relevant consumers
were inspected before adding focused files. The absence conclusion is limited
to the searched declarations: no existing heterogeneous bounded creation API
or cyclic-intertwiner uniqueness theorem was found there.

## Exact theorem contracts

### 1. Bounded linking block

Let `𝕜` be a nontrivially normed field, and let `E`, `F` be normed spaces.
For `T : E →L[𝕜] F`, construct

```text
creation T = inr ∘L T ∘L fst
creation T (x, y) = (0, T x)
```

All products of endomorphisms mean composition, with the right factor acting
first. Let `D(A,B) = A.prodMap B`, `P = 1.prodMap 0`, and `Q = 0.prodMap 1`.
The target identities are:

```text
‖creation T‖ = ‖T‖
creation T = 0 ↔ T = 0
creation T * creation S = 0
Q * creation T * P = creation T
D(A,B) * creation T - creation T * D(A,B)
  = creation (B ∘L T - T ∘L A)
Commute D(A,B) (creation T) ↔ B ∘L T = T ∘L A
Commute Q (creation T) ↔ T = 0
```

The diagonal pair retains arbitrary source and target operator actions. The
blocks are not scalar or commuting substitutes. Norm preservation certifies
that the construction does not discard the original bounded operator.

### 2. Cyclic-vector uniqueness

For indexed bounded families `A i : E →L[𝕜] E`, `B i : F →L[𝕜] F`, assume
`Dense (span 𝕜 (range (fun i => A i Ω)))`. If

```text
T ∘L A i = B i ∘L T
S ∘L A i = B i ∘L S
T Ω = S Ω
```

for every `i`, prove `T = S`, and derive the zero criterion. Neither family is
assumed commutative. No existence or surjectivity of vacuum evaluation follows.

### 3. Completed GNS specialization

For a unital complex C\*-algebra `A` with the native order assumptions and any
positive linear map `φ : A →ₚ[ℂ] ℂ`, use the actual native Hilbert completion
`φ.GNS` and `φ.gnsStarAlgHom`. The existing owner proves that the orbit of
`gnsVacuum φ = Λ(1)` is dense. Apply contract 2 to obtain bounded-intertwiner
uniqueness without assuming cyclicity again. Faithfulness and normalization of
`φ`, and finite dimensionality of the algebra or spaces, are not required.

### 4. Adjoint and Gram operators

Let `E`, `F` be complete complex inner-product spaces and let
`π : A →⋆ₐ[ℂ] (E →L[ℂ] E)`, `ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)` be native
star-algebra homomorphisms. From `T ∘L π(a) = ρ(a) ∘L T` for every `a`, prove

```text
T† ∘L ρ(a) = π(a) ∘L T†.
```

For a second intertwiner `S`, derive

```text
Commute (S† ∘L T) (π a).
```

The proof reverses order when taking adjoints and uses intertwining at
`star a`; it does not assume the representation image commutative or the
individual operators normal. An arbitrary cross-Gram operator `S† ∘ T` is not
asserted positive. This produces a source-space Gram operator,
not a relative tensor product or Haag-duality identification.

## Structural synthesis and sharpness

The fundamental distinction is the type of an arrow `E →L F` versus the type
of an endomorphism of `E × F`. The four relevant relations are concrete:

| Role | Construction and law |
|---|---|
| Ambient carrier | Native bounded endomorphisms of the maximum-norm product. |
| Embedding | `N(T) = creation T`; it preserves norm and detects zero. |
| Recovery | `R(Z) = snd ∘L Z ∘L inl`; the original arrow is recovered from `N(T)`. |
| Corner support | `N(R(Z)) = Q Z P`; this equals `Z` exactly on the supported corner. |

The round trip in the ambient algebra is a corner compression, not the
identity on arbitrary endomorphisms. Source and target actions transport this
corner by the ordered defect `BT - TA`. The existing normed product supplies
continuity; the completed GNS branch supplies density; the separate Hilbert
branch supplies actual adjoints. None is inferred from nilpotency alone.

The hypotheses have concrete mathematical witnesses and failure cases:

- On `E = F = ℂ²`, take both actions to be the full matrix algebra and
  `Ω = e₁`. Its orbit spans `E`; the identity is a nonzero intertwiner whose
  creation block is nonzero and square-zero. The representation image is
  noncommutative.
- With only the identity action, `Ω = e₁`, `T = diag(0,1)`, and `S = 0`,
  agreement at `Ω` does not imply equality. The missing hypothesis is
  cyclicity.
- For the full matrix action, no intertwiner can take `e₁` to `e₂`:
  intertwining with `E₁₁` would give `0 = e₂`. Uniqueness does not imply
  existence for every target vector.
- `S = 1`, `T = -1` gives the cross-Gram operator `-1`, illustrating why
  arbitrary cross-Gram positivity is not claimed.

These are semantic witnesses and counterexamples, not additional claimed
Lean declarations or a substitute for the module checks below.

## Dependency order

| Result | Actual dependencies |
|---|---|
| Bounded block and recovery of `T` | Native product injections, projections, and bounded composition. |
| Nilpotency and corner obstruction | Block evaluation and the zero composite `fst ∘ inr`. |
| Diagonal intertwining criterion | Ordered commutator calculation and `creation_eq_zero_iff` zero detection. |
| Cyclic uniqueness | Native dense-span extensionality and both intertwining equations. |
| Completed GNS uniqueness | Cyclic uniqueness plus the existing completed GNS orbit density. |
| Adjoint reverse intertwining | Star preservation, intertwining at `star a`, and reversal of adjoint composition. |
| Gram commutation | Reverse intertwining for `S†`, forward intertwining for `T`, and associativity. |

The product-block, cyclicity, and Hilbert-adjoint branches have different
hypotheses. No chronological or metaphorical edge between them is inserted.

## Verification record

Disposition: **`[accepted_limited_scope]`**. All 19 stated theorems and the
single new definition compiled with Lean `4.34.1` (compiler commit
`5045d0056413266e57c625dcd7c365b10e377c52`) and pinned Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

| Check | Result and coverage |
|---|---|
| Independent semantic review | PASS for all four modules, the exact carriers/hypotheses, and the contract. |
| Fresh selected source closure | PASS: all seven project modules freshly compiled, including three unchanged GNS dependencies. No project artifacts were borrowed for this run. |
| Independent owner rebuild | PASS: four new owners recompiled into a disjoint artifact root; only the three unchanged dependency artifacts were reused after matching source, logs, pins, and baseline Git blobs. |
| Native declaration audit | PASS: all 24 owned declarations, including generated helpers; counts 18 / 2 / 2 / 2 in the module order below. |
| Observed foundational axioms | Exactly `propext`, `Classical.choice`, `Quot.sound`; no custom axiom, proof hole, unsafe or partial declaration accepted. |
| New-owner and audit warnings | Zero. |
| Existing dependency diagnostic | One `unnecessarySimpa` warning in unchanged `PositiveLinearMapGNSVacuum` at line 83; not attributed to a new owner. |
| Staged proof gate and whitespace | PASS. The installed pre-commit hook repeats the staged gate when committing. |
| Root Lake integration | Not certified by these source checks. The actual unchanged pre-push hook result is recorded separately in the PR; the known missing pinned GIFT configuration is outside this mathematical change. |

The first development attempt exposed a missing explicit native
`NormedSpace` import in `CyclicIntertwiner`. Adding
`Mathlib.Analysis.Normed.Module.Basic` repaired the import surface without
changing any theorem statement or proof. The complete final source closure
was then compiled afresh in `development-2` and independently rebuilt.

Exact development invocation, from the checkout root:

```bash
source /workspace/scratch/2e3cbf77ee2a/runtime/environment.sh
set -o pipefail
python3 tools/quality/check_operator_geometry.py \
  --repo /workspace/scratch/2771a9ff6f38/info-geometry-lean \
  --mathlib /workspace/scratch/2e3cbf77ee2a/runtime/mathlib \
  --work-dir /workspace/scratch/2771a9ff6f38/verification/bounded-intertwiner/development-2 \
  --target InfoGeometry.OperatorAlgebra.BoundedIntertwinerLinking \
  --target InfoGeometry.OperatorAlgebra.CyclicIntertwiner \
  --target InfoGeometry.OperatorAlgebra.GNSCyclicIntertwiner \
  --target InfoGeometry.OperatorAlgebra.IntertwinerAdjointGram \
  2>&1 | tee /workspace/scratch/2771a9ff6f38/verification/bounded-intertwiner/development-2.log
```

Exact independent QA invocation, from the task workspace:

```bash
source /workspace/scratch/2e3cbf77ee2a/runtime/environment.sh
python3 /workspace/scratch/2771a9ff6f38/verification/bounded-intertwiner/qa/run_qa.py \
  --repo /workspace/scratch/2771a9ff6f38/info-geometry-lean \
  --reference /workspace/scratch/2771a9ff6f38/verification/bounded-intertwiner/development-2 \
  --mathlib /workspace/scratch/2e3cbf77ee2a/runtime/mathlib \
  --lean /workspace/scratch/2e3cbf77ee2a/runtime/lean-4.34.1-linux/bin/lean \
  --development-log /workspace/scratch/2771a9ff6f38/verification/bounded-intertwiner/development-2.log \
  --work /workspace/scratch/2771a9ff6f38/verification/bounded-intertwiner/qa/final
```

Both runners acquired and released the repository's shared build lock. The
QA runner uses the unchanged native `tools/quality/reviewed_audit_source.py`
and checks verification-tool integrity as well as source hashes.

| Verified source / receipt | SHA256 |
|---|---|
| `BoundedIntertwinerLinking.lean` | `26470c1e97cf1caa67493c8abf969ace7790c7bbce155bb2fec84e1bbaa1db20` |
| `CyclicIntertwiner.lean` | `c06fb1ad29e2b42db717e6fa326b4aee5a4a2c0e44cbea35aa35aea07fbb06c8` |
| `GNSCyclicIntertwiner.lean` | `e1b9ff77cb2f830a28c28969d408bd5533d56c420f573843306895785bdfd583` |
| `IntertwinerAdjointGram.lean` | `bdf5244bedb64206af9dccab5e02b34bc8d8b100870638742ab286ca1e4b83f0` |
| Development `result.json` | `91d6e286ef65b28bbb52c4196de3e3eadc33149173d971b273bb9fad9d4f6c3c` |
| Independent `qa-result.json` | `cec65bcbccf728f7934a8a2f9ea12de5a62e580983b75ea774a22b988265df86` |
| Native `declaration-audit.log` | `3362af3ac745415a5aa78d5f18314b14578ba473773fc9cb78bb901c2c0f7ede` |
| Independent `qa/run_qa.py` | `882790ce4a87f5d8287b0c56e13b2773255e6e79bc5118d9427535e1110a0bbc` |

Source-closure compilation, declaration-axiom checking, semantic review,
and whole-package integration are separate claims. This record certifies the
first three at the stated scope, without promoting the intake's analytic
conformal-net conclusions.
