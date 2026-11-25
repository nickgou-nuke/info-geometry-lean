# Summable approximate state compatibility

## Current destination verification — 2026-11-25

The unchanged Lean sources passed the destination-pin build and fresh audit
in [run 45571203500](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45571203500),
job `139058006920`, at preparation source
`ff8e1632b45569d88da1c73c0ec160c913fe55f9`, on upstream
`c25e77e9654a54fc5e4a04bfb637b7144defacc0`. All 11 expected reports passed
the foundational-axiom check; source hashes and dependency pins matched.
Earlier validation records below retain their original scope and provenance.


## Provenance and correction of the intake

The intake is `Pasted text(20261124-150457).txt`, supplied on 2026-11-24.
Its proposed recursion and telescoping argument concern arbitrary real-valued
functions on seminormed groups. They can establish pointwise convergence and
exact compatibility of functions, but do not establish a state: additivity,
scalar linearity, positivity, normalization, and star-algebra transitions are
absent from that theorem's hypotheses. For example, identity transitions and
the constant family `ω(a) = a²` on the real numbers have zero compatibility
error, while their limit is not linear.

The replacement keeps that useful general limit result and adds the missing
state proof under genuine C-star hypotheses.

## Carriers and exact statements

### Portable native Mathlib layer

`CoreLean.ApproximateCompatibility` uses a dependent sequence `A n` of
seminormed additive groups, arbitrary norm-contracting functions
`ι n : A n → A (n+1)`, and functions into an arbitrary complete metric space.
Given nonnegative summable errors and

```
dist (ω n a) (ω (n+1) (ι n a)) ≤ ε n * ‖a‖,
```

it constructs pointwise limits, proves exact adjacent compatibility, and proves
the full quantitative tail estimate at every finite horizon `k`:

```
dist (evaluationSequence ι ω n a k) (ωLimit n a)
  ≤ (∑' j, ε (n+k+j)) * ‖a‖.
```

The real-valued intake is a specialization. The complex case does not discard
imaginary components.

`CoreLean.ApproximateStateLimits` uses genuine, possibly noncommutative complex
C-star algebras; unital star-algebra homomorphisms; and native positive linear
maps `A n →ₚ[ℂ] ℂ`, normalized at one. It derives transition contractivity from
Mathlib. The pointwise limit is constructed as a native positive linear map:
additivity and complex homogeneity pass through limits; positivity passes
through the closed native complex order; normalization passes through unital
transitions. No continuity or positivity of the desired limit is assumed.

### Existing repository consumer

`InfoGeometry.Canonical.ApproximateStateColimit` imports the actual
`CStarAlgebraStateColimit` owner. On an existing sequential
`ContinuousStarInductiveSystem`, it constructs that owner's actual
`CompatibleStateFamily`, with native `State` values and compatibility for
**all** transitions `i ≤ j`, proved from adjacent compatibility and the system's
composition law. The result can therefore supply the state-family input to
the existing filtered GNS constructions.

This adapter belongs to the InfoGeometry integration layer. The portable
CoreLean owners require only Mathlib and one another; they do not import
InfoGeometry or construct a second state wrapper.

The existing repository system uses one universe for both its index type and
its stage types. Consequently this natural-indexed adapter uses `A : ℕ → Type`,
matching that owner's actual API. This is not a finite-dimensionality
restriction. The portable convergence and positive-functional theorems remain
polymorphic in the universe of the stages. The adapter also retains the legacy
module convention required to import the unchanged repository owner; only the
portable upstream modules use Lean's modern `module` form.

## Native owners and declarations reused

- `cauchySeq_of_dist_le_of_summable` and
  `dist_le_tsum_of_dist_le_of_tendsto` from
  `Mathlib.Topology.Algebra.InfiniteSum.Real`.
- `cauchySeq_tendsto_of_complete`, `tendsto_nhds_unique`, and the natural-index
  shift theorem.
- `PositiveLinearMap.mk₀`, native complex order and `ge_of_tendsto`.
- `NonUnitalStarAlgHom.norm_apply_le`, so a redundant contractivity assumption
  is not required for the C-star theorem.
- The native `StarRingHomClass.instOrderHomClass` and `map_nonneg`, preserving
  positivity on the full algebra without diagonal or commuting reductions.
- Existing repository `State`, `State.restrict`,
  `ContinuousStarInductiveSystem`, and `CompatibleStateFamily`.

## Boundaries

The analytic compatibility estimate and summability are inputs. This module
does not derive them for Wilson-loop observables or extend estimates proved
only on a selected collection of loops to an entire C-star algebra. The
refinement maps must actually be unital star-algebra homomorphisms; a general
Markov averaging operator cannot be silently substituted. No injectivity or
finite-dimensionality hypothesis is imposed. No full continuum theorem,
reflection positivity, mass gap, or construction of the underlying physical
observable algebra is asserted.

## Verification

### Exact upstream portable check: passed

The three portable CoreLean files passed the unchanged upstream Lean **4.36.0**
and Mathlib **`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`** in
[CI run 45460909233](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45460909233),
job **138682887362**, preparation source commit
**`4e0e4add51d44649cb232d9c8f540f26d34a709d`**. The focused
`lake --wfail build CoreLean.ApproximateStateLimitsAudit` gate and a separate
fresh `lake env lean CoreLean/ApproximateStateLimitsAudit.lean` audit passed.
The exact declaration inventory contains **10 public theorems and one recursive
definition**, giving **11 axiom reports**. The final three Lean source hashes
match the saved destination artifact. Toolchain, lakefile, manifest, and resolved
dependency revisions were checked without changing the existing pins.

The source inventory, build log, fresh axiom log, checker output, dependency
revisions, and artifact receipt are in the preparation repository
`nickgou-nuke/info-geometry-lean`, directory
`contributions/wilson/validation/evidence/exact-states-4e0e4ad/`.

### Actual InfoGeometry state-family adapter: passed locally

The portable owners and the two InfoGeometry-facing adapter files also passed
the available Lean **4.34.1** and Mathlib
**`d13f23b723b8a846827a245b89c10fc7d3f11612`**, using the maintained exclusive
compilation lock and standard linters. All **five new files have zero warnings
and zero errors**. The shared transcript checker accepted the 11 portable
reports plus the adapter's **one fresh report**. Every report is either
axiom-free or uses only `propext`, `Classical.choice`, and `Quot.sound`.

The actual existing repository dependencies compiled successfully, with
**14 inherited style warnings** in unchanged owner files. These are distinct
from the warning-free new sources. The adapter validation is a focused
dependency-closure check, not a whole-repository build certificate.

The final focused command was:

```bash
python3 wilson-contributions/check_candidate.py cutoff \
  InfoGeometry.Canonical.ApproximateStateColimitAudit \
  --source-root wilson-contributions/followup/states \
  --output-name states-followup --standard-linters --wait-for-build-lock
```

This reused only source-hash- and command-matching successful dependencies;
the changed adapter and its audit were compiled fresh. The portable audit was
compiled fresh in the initial combined check and its sources remained unchanged.
The final source scan found no proof holes, custom axioms, unsafe proofs, or
native-decide shortcuts. The saved compiler inventories and final source hashes
reconcile both checks.

Local evidence is in the preparation repository directory
`contributions/wilson/validation/evidence/preliminary-states-followup/`:
`summary.json`, `portable-results.json`, `preliminary-results.json`, the two
axiom-audit JSON files, and raw logs. The three upstream portable files are
verified under the exact CoreLean pin; the existing-owner adapter is verified
under InfoGeometry's separate local pin and is not part of the upstream patch.
