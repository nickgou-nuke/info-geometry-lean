# Extant DNA, recorded ancestry and Hodge structure

This document states what the repository-evolution tools measure, how to supply observations,
and which claims its outputs support. Source inspection is pinned to repository
revision `b143075bbf27e75860a1011e04423a0f227b7c41`.

## Three separate objects

| Object | Vertices and relations | What it establishes |
|---|---|---|
| Recorded Git genealogy | Commit vertices; parent→child edges | Recorded revision ancestry, including every merge parent |
| Declaration dependency graph | Declarations and type/proof references | Which declarations use which other declarations |
| Inferred DNA affinity | Observed taxa with aligned character states | Similarity represented by an unrooted descriptive tree |

A Git merge is not itself evidence of which theorem inherited which subterm.
A dependency reference is not an evolutionary parent. Similarity can arise
through reuse, common requirements, convergence, or refactoring. A historical
claim requires evidence beyond a descriptive affinity tree.

The motivating paper, [Ragan (2009), Trees and networks before and after
Darwin](https://link.springer.com/article/10.1186/1745-6150-4-43), distinguishes
historical representations of affinity, descent and networks. Its treatment of
lateral transfer motivates retaining network relationships when a tree loses
information; it does not prescribe a Git or Lean inference algorithm.

## Inference from extant observations requires no Git mapping

Choose a consistent taxon unit. A taxon can be an observed repository snapshot,
or an individual declaration supplied with its own explicitly aligned character
profile. Do not mix these units in one matrix.

The native snapshot adapter treats an entire observed generation as a taxon;
markers are exact qualified declaration names, with type and value separate.
The generic profile schema allows declaration-level taxa when a producer has
defined comparable markers across those declarations.

### Generic profile input

```json
{
  "schema": "repo-character-profiles/v1",
  "provenance": {"source": "ACTUAL_EXPORTED_OBSERVATIONS"},
  "taxa": [
    {"id": "sample-a", "characters": {
      "conserved-marker": {"state": "ACTUAL_A_STATE", "algorithm_version": "RECORDED_VERSION"}
    }},
    {"id": "sample-b", "characters": {
      "conserved-marker": {"state": "ACTUAL_B_STATE", "algorithm_version": "RECORDED_VERSION"}
    }},
    {"id": "sample-c", "characters": {
      "conserved-marker": {"state": "ACTUAL_C_STATE", "algorithm_version": "RECORDED_VERSION"}
    }}
  ]
}
```

This is a schema illustration, not measured DNA or a supplied input dataset.
Replace placeholders with observed values. A state is a categorical allele
label. It can be a structural digest, but hexadecimal, bit and numeric distances
between cryptographic digests are never used.

### Native observation adapter

The tool also accepts `repo-dna-snapshots/v1` with a `snapshots` array and actual
native `declarations` rows. Each observation needs `sample_id`, `generation`,
`commit`, or `id`, in that preference order. A Git SHA is optional. Any supplied
historical identifier is preserved as an unverified assertion.

Each declaration has its exact `name` and `typeDigest`, with optional
`valueDigest`. Each non-null digest must contain `algorithmVersion`, a 64-hex
`digest`, boolean `openTerm`, and optionally nonnegative integer `nodeCount`.
Null values are unobserved; open terms are excluded. Name-only and known
metadata-proxy rows are rejected.

```bash
python3 tools/repository_evolution/dna_character_tree.py \
  --input observed_profiles.json --out artifacts/repository-evolution/affinity.json
```

Open `tools/repository_evolution/dna-affinity-viewer.html` and import the resulting `affinity.json`. No server or network
connection is needed. Equal-angle display lengths are uniform and explicitly
not to scale; selecting an edge exposes the exact inferred branch length.
The center chosen for drawing is not a root or ancestor.

### Statistical and computational contract

1. Require 3–128 unique taxa. Exact marker IDs are an alignment assumption,
   not demonstrated homology. The snapshot adapter does not infer renames.
2. Retain a marker only if it is observed in every taxon and all observations
   use the same algorithm version. Missing/open terms are unknown, never an
   observed absence allele. Report coverage and every excluded column. Reject
   an empty comparable intersection instead of inferring zero distances.
3. Measure the fraction of retained columns with unequal categorical states:

   `d(i,j) = mismatching retained markers / all retained markers.`

   Every retained marker has equal weight. Native type and proof digests are
   separate markers. A one-bit and a many-bit hash change each count as one
   mismatch. Whole-term digest mismatch is not a count of AST edits.
4. Apply the neighbor-joining Q criterion with exact rational arithmetic and
   deterministic tie breaking. The output is **unrooted structural affinity**.
   Internal vertices have no observed ancestor identity. Branch lengths use
   mismatch-distance units, not years or counts of mutations.
5. Preserve and report negative branch lengths. Report all-pair tree-path RMSE
   and four-point additivity residuals. Evaluate every quartet up to 4,096;
   otherwise evaluate a deterministic sample of 4,096, explicitly labeled.

The original algorithm is [Saitou and Nei
(1987)](https://academic.oup.com/mbe/article/4/4/406/1029664). Applying it to
software characters is a modeling choice, not a biological theorem about code.

A binary drawing can reflect deterministic tie breaking, including zero-length
branches; it does not establish support for that split. This tool does not
estimate a mutation model, bootstrap confidence, or a molecular clock.
Complete-case filtering can discard many observations, while type/proof markers
and shared subterms can be correlated. Identical retained profiles imply zero
distance only on those observations. Poor fit calls for inspecting alignment
and a similarity network, not promoting tree edges to historical facts.

The tools do not query a live Arango instance. Supply actual exported observations;
no real DNA tree is preloaded. Synthetic fixtures exist only in tests. Observation-to-commit binding is needed for a later comparison to Git
history; it is unnecessary for the inference itself.

## Actual Hodge–Dirac calculation on the captured Git graph

A capture made on 27 October 2026 used all **13,461 vertices and 13,687 ordered parent edges**,
not the compressed display. The carrier is the **unfilled graph 1-complex**
over the rationals or reals. No triangular faces are filled.

For an edge u→v, its incidence column is −δu+δv:

```text
B : C¹ → C⁰              shape 13,461 × 13,687
d = Bᵀ : C⁰ → C¹        (df)(u→v) = f(v) − f(u)
D = [[0, B], [Bᵀ, 0]]   shape 27,148 × 27,148
Γ = diag(+I_vertices, −I_edges)
```

Exact sparse integer checks establish:

- `D = Dᵀ`;
- `Γ² = I`;
- `ΓD + DΓ = 0`;
- `D² = diag(BBᵀ, BᵀB)`;
- the actual commutator `[Γ,D]` is nonzero.

The calculation uses the actual incidence operator, with no diagonal substitute,
numerical eigensolver or dense matrix.

| Full graph invariant | Value |
|---|---:|
| Connected components / β₀ | 1 |
| Independent unfilled cycles / β₁ | 227 |
| Rank of B | 13,460 |
| Dimension of D | 27,148 |
| Rank of D | 26,920 |
| Dimension of ker D | 228 |
| Even zero modes | 1 |
| Odd zero modes | 227 |
| Even-to-odd index / Euler characteristic | −226 |
| Recorded roots minus terminal tips | −10 |

The rank certificate combines a signed forest minor with diagonal entries ±1
and independent component indicators in ker(Bᵀ). The cycle certificate has
227 independent columns Z, each with a unique nonforest-edge pivot, and
verifies BZ=0 exactly. The witness file records every signed coefficient and
the ordered vertices/edges needed to reconstruct the operators.

The actual root `7d5bcb3a51bb835e17d8816bd5536a2993a1ef35` has six incident
edges. Its vertex delta satisfies `||Dδroot||²=6` and is **not a zero mode**.
Zero modes are vectors across cells: constant vertex values on connected
components and balanced edge flows on unfilled cycles. They are not individual
theorem or commit vertices designated as logically complete.

The first three recorded commits already provide a concrete witness:

```text
e0: 7d5bcb3a51 → f3bc385a50   coefficient +1
e1: 7d5bcb3a51 → 66b66e10b0   coefficient −1
e2: f3bc385a50 → 66b66e10b0   coefficient +1
```

All other edge coefficients are zero. This vector has Bz=0 in the **full**
graph. The triangle has no directed cycle and is not filled by a 2-cell.

### Cones, parity and index

Directed cones are computed by reachability in the full parent graph, excluding
the seed. Counts are independent of compression/date focus, and the viewer
highlights each cone separately. Degree-changing d and d* are not past/future
traversals. Γ is cell-degree parity, not temporal orientation.

Directed and undirected cycles do not invalidate this parity anticommutation.
Changing selected edge orientations multiplies those columns of B by −1 and
orthogonally conjugates D. Its spectrum therefore cannot determine time
direction. No conclusion that low energy means foundational theorems or high
energy means peripheral theorems is justified by these identities.

The even-to-odd index is β₀−β₁=n−m here. It is not roots minus leaves.
Adding 2-cells changes the complex and its Betti numbers. For a 0⊕1⊕2 operator,
parity anticommutation still follows from odd degree, but degree-diagonal D²
requires the chain condition B₁B₂=0. A dependency triangle does not itself prove
that two Lean derivations are equal.

## Source audit: what is already implemented in Lean

All links refer to inspected revision
`b143075bbf27e75860a1011e04423a0f227b7c41`. Source proof bodies were read;
**no fresh Lean compilation was performed**.

- [ChiralDiracAnticommutation.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/b143075bbf27e75860a1011e04423a0f227b7c41/lean/DAG/ChiralDiracAnticommutation.lean):
  `DAG.ChiralDiracAnticommutation.dirac_anticommutes_gamma` is stated for
  arbitrary real B₁ and B₂ matrices, with no acyclicity hypothesis.
- [EckmannHodge.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/b143075bbf27e75860a1011e04423a0f227b7c41/lean/DAG/EckmannHodge.lean):
  `eckmann_hodge_nullity` over rational matrices assumes `del2 * del1 = 0`
  and identifies nullity with the appropriate rank difference.
- [TermDigest.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/b143075bbf27e75860a1011e04423a0f227b7c41/lean/DAG/TermDigest.lean):
  v4 hashes syntax subterms and erases local binder names. However, `Expr.const`
  still encodes the **global constant name and universe levels**. It does not
  replace each referenced declaration by a recursive type/proof digest.
  This is not dependency-closure identity, beta normalization or proof of
  mathematical equivalence. Open-term identifier erasure requires the closed
  term gate.
- [ExprFingerprint.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/b143075bbf27e75860a1011e04423a0f227b7c41/lean/DAG/ExprFingerprint.lean):
  v3 constructor/count features differ from v4. Its hash still includes binder
  names; its unique-node bound-index histogram is not occurrence frequency.
- [Basic.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/b143075bbf27e75860a1011e04423a0f227b7c41/lean/DAG/Basic.lean)
  extracts declaration→dependency edges, semantically opposite to Git
  parent→child. [Hydrate.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/b143075bbf27e75860a1011e04423a0f227b7c41/lean/DAG/Hydrate.lean)
  condenses SCCs. A recursive dependency-hash layer must handle cyclic blocks.
- [ExprArangoExport.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/b143075bbf27e75860a1011e04423a0f227b7c41/lean/DAG/ExprArangoExport.lean):
  term nodes are globally shared. Use declaration type/value roots and scoped
  edges to attribute subterms; a node's first-emitted `decl` field is not
  exhaustive ownership. Its occurrence-specific `deBruijnHash` is distinct
  from a shared structural allele.
- [extract_expr_fingerprints.py](https://github.com/nickgou-nuke/info-geometry-lean/blob/b143075bbf27e75860a1011e04423a0f227b7c41/tools/infra/extract_expr_fingerprints.py)
  declares a metadata proxy, excluded by the native inference adapter.

In Lean, propositions inhabit Prop, and any two proofs of the same proposition
are definitionally interchangeable. Structural proof fingerprints therefore
measure implementation structure, not proposition identity. See the
[official Lean reference](https://lean-lang.org/doc/reference/latest/The-Type-System/Propositions/).
Bound variables already use de Bruijn indices in
[Lean.Expr](https://lean-lang.org/doc/api/Lean/Expr.html).

Other repository gradings, such as representation-depth parity, have different
contracts. Their defects must not be conflated with universal cell parity.
Python mod-2 ranks for complexes with faces must likewise not be reported as
rational or real Hodge dimensions without a justified bridge.

## Validation and limits

The focused suites cover exporter history, categorical inference, sparse Hodge
operators and renderer integration. Reproducible commands are in
[the usage guide](REPOSITORY_EVOLUTION.md). The dated capture above passed every
exact operator/rank/cycle check. Run reports and browser evidence are archived
artifacts, not committed source. Lean proof bodies were source-inspected only;
no new compiler validation is claimed.

These are offline source tools. It does not modify ArangoDB, publish a
GitHub branch, recover unreachable Git objects, or obtain missing historical
DNA. Actual fingerprint observations are the remaining input needed for a
source-backed DNA affinity result.
