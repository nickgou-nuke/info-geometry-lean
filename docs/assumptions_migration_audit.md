# Assumptions/Axioms Migration Audit

## Scope

This audit explains the second-pass extraction of nonconstructive content into:

- `lean/InfoGeometry/Assumptions.lean`
- `lean/InfoGeometry/Axioms.lean`

and the resulting reductions in:

- `lean/InfoGeometry/New.lean`
- `lean/InfoGeometry/Degree.lean`
- `lean/InfoGeometry/Projective/LogSum.lean`

Archived pre-extraction drafts are preserved in:

- `lean/InfoGeometry/Archive/Drafts/New_pre_assumptions_extraction.lean`
- `lean/InfoGeometry/Archive/Drafts/Degree_pre_assumptions_extraction.lean`
- `lean/InfoGeometry/Archive/Drafts/Projective_LogSum_pre_assumptions_extraction.lean`

## Why file sizes dropped sharply

`InfoGeometry/New.lean` previously mixed:

- duplicate declarations already present in canonical modules,
- exploratory drafts,
- non-code prose injected into the source,
- and unfinished proof placeholders.

Measured on the previous `HEAD` version:

- `New.lean` contained `35` `sorry/admit` placeholders.
- `New.lean` had `109` unique declaration names.
- Of those, `35` are declared elsewhere in `lean/InfoGeometry` today.
- `74` names had no current declaration elsewhere and were draft-only.

`Degree.lean` kept its four theorem names, but now delegates bodies to explicit assumptions.

`Projective/LogSum.lean` now exposes the same theorem name through the assumptions layer because
the old proof script was incomplete and warning-failing.

## Deletion/retention criteria used

Content was reduced only when at least one of these held:

1. The declaration duplicated an existing canonical declaration.
2. The declaration lived in a draft file with unresolved placeholders.
3. The file contained non-Lean prose that made maintenance/nonregression unsafe.
4. The declaration was outside canonical reach and not imported by production modules.

Content was retained when:

1. It is part of the constructive canonical surface, or
2. it is required for legacy API names and could be represented as explicit assumptions.

## What was preserved (by API intent)

Preserved via canonical modules (examples):

- finite probability/KL primitives now in `EntropicInference` and `Basic`
- transformation-group invariance/uniformity lemmas in `TransformationGroups`
- analytic primitives such as `logSumExp` in `Analytic/LogSumExp`

Preserved via explicit assumptions:

- manifold-degree bridge theorems (4 names) through `Degree` + `Axioms`
- projective finite log-sum inequality through `Projective/LogSum` + `Axioms`

## Current assumptions surface

`InfoGeometry.Assumptions` currently contains:

- `ManifoldDegree.exists_isolating_nhds_of_nondegenerate`
- `ManifoldDegree.preimage_finite_of_regular_value`
- `ManifoldDegree.exists_local_chart_homotopy_to_linear`
- `ManifoldDegree.local_degree_eq_sign_jacDet`
- `Projective.logSum_inequality`
- `IB.*` (IB pipeline draft interface)
- `ManifoldHomology.*` (mapping-degree/top-homology draft interface)
- `Determinant.*` (determinant/group-wrapper draft interface)
- `DualConnections.*` (Fisher/α-connection draft interface)
- `LLN.*` (empirical/SLLN draft interface)

`InfoGeometry.Axioms` re-exports these names for compatibility.

## Domain-by-domain reintegration status

The largest unresolved bucket from old `New.lean` has now been reintroduced as
dedicated noncanonical research modules:

- `lean/InfoGeometry/Research/IB.lean`
- `lean/InfoGeometry/Research/ManifoldHomology.lean`
- `lean/InfoGeometry/Research/Determinant.lean`
- `lean/InfoGeometry/Research/DualConnections.lean`
- `lean/InfoGeometry/Research/LLN.lean`
- umbrella: `lean/InfoGeometry/Research/All.lean` and `lean/InfoGeometry/Research.lean`

Each domain module has an explicit import boundary and re-exports only the
relevant research API, instead of centralizing this surface in `New.lean`.

## Remaining constructive backlog

The major exploratory buckets are now split by domain, but some declarations are
still scaffold-level and need constructive replacement over time:

- IB pipeline drafts (`IBProblem`, `ibLagrangian`, `ibIteration`, `ib_convergence`, etc.)
- manifold/homology scaffolds (`mappingDegree`, `topHomologyIso`, `degree_formula_via_jacobian`)
- determinant/group wrappers (`GL`, `SL`, `detHom`, `logAbsDet`, etc.)
- dual-connection geometry drafts (`alphaConnection`, `amariChentsovTensor`, etc.)
- LLN/empirical bridge drafts (`fixed_partition_slln`, `empirical_to_theoretical_slln`)

Also, two manifold-degree declarations remain as true axioms in
`lean/InfoGeometry/Assumptions.lean`:

- `exists_isolating_nhds_of_nondegenerate`
- `preimage_finite_of_regular_value`
