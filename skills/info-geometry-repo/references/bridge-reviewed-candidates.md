# Reviewed Bridge Candidates

This note is a manually curated quarantine packet for non-debt bridge runs.

Unlike `bridge-candidates.md`, this file is allowed to carry concrete,
critique-approved materialization sketches that the proof driver may insert into
quarantine.

It is still not a proof artifact.

## Candidate 1

`name`

`ReviewedCandidate.index_bridge_spectral_constant_family`

`review verdict`

`accept`

`review reason`

The existing theorem `InfoGeometry.KK.index_bridge_spectral` is already a
substantive invariant-theory bridge in the trusted surface. For the purpose of
exercising the quarantine proof-attempt loop on non-placeholder input, a small
reviewed wrapper around that theorem is concrete, buildable, and low risk.

`Lean-style signature sketch`

```lean
def reviewed_index_bridge_spectral_constant_family
    {A B H : Type*}
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H]
    [FiniteDimensional ℝ H]
    (X : InfoGeometry.KK.KasparovCycle A B H)
    (hF : X.F * X.F = 1) :=
  InfoGeometry.KK.index_bridge_spectral (X := X) hF
```

`Lean-ready materialization sketch`

```lean
def reviewed_index_bridge_spectral_constant_family
    {A B H : Type*}
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H]
    [FiniteDimensional ℝ H]
    (X : InfoGeometry.KK.KasparovCycle A B H)
    (hF : X.F * X.F = 1) :=
  InfoGeometry.KK.index_bridge_spectral (X := X) hF
```

`why this closes a real frontier edge`

This reviewed candidate lands directly on the live frontier theorem
`InfoGeometry.KK.index_bridge_spectral` and turns the report-only bridge packet
into a concrete quarantine exercise. It does not claim new mathematics; it
exercises the reviewed-sketch materialization path on a real frontier target.

`proof ingredients already present in repo`

- `InfoGeometry.KK.index_bridge_spectral`
- `lean/InfoGeometry/KK/KasparovCycle.lean`
- `InfoGeometry.Canonical.AnalyticalIndex.IndexInvariantAlong`

`risk level`

`low`

`quarantine recommendation`

`yes`