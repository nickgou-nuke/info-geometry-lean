# Bridge Candidates

This note is a report-only frontier packet derived from the current trusted
`Skynet v2` reverse/bi-directional semantic frontier.

It is not a proof artifact.

The purpose is to pin the first small bridge lemmas suggested by the current
frontier:

- `InfoGeometry.KK.KasparovCycle.analyticalIndex`
- `InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex`
- `InfoGeometry.Canonical.AnalyticalIndex.IndexInvariantAlong`
- `InfoGeometry.Canonical.GrandSynthesis.*`

The design rule is strict:

- candidate bridge statements only
- small insertable lemmas
- no new framework unless unavoidable

## Trusted Graph Context

Current trusted semantic graph facts:

- `Skynet v2` graph:
  - `128` nodes
  - `647` edges
  - `319` cross-module edges
- direct bridge:
  - `InfoGeometry.KK.KasparovCycle.analyticalIndex`
    depends on
  - `InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex`
- reverse frontier reaches:
  - `InfoGeometry.KK.index_bridge_spectral`
  - `InfoGeometry.Canonical.AnalyticalIndex.chiralSliceIsoAlong_of_noZeroEigenCrossing`
  - `InfoGeometry.Canonical.AnalyticalIndex.indexInvariantAlong_of_conjugacy`
  - `InfoGeometry.Canonical.GrandSynthesis.information_wheeler_dewitt_equivalence_of_state_capstone_hypotheses`
  - `InfoGeometry.Canonical.GrandSynthesis.information_wheeler_dewitt_equivalence_of_fullCapstone`
  - `InfoGeometry.Canonical.GrandSynthesis.information_wheeler_dewitt_implication_of_fully_derived_hypotheses`
  - `InfoGeometry.Canonical.GrandSynthesis.thermodynamic_and_geometricAlgebraic_of_fullCapstone`

## Candidate 1

`name`

`InfoGeometry.KK.kasparovIndex_eq_analyticalIndex_zero_of_indexInvariant`

`Lean-style signature sketch`

```lean
theorem kasparovIndex_eq_analyticalIndex_zero_of_indexInvariant
    {A B H : Type*}
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H]
    [FiniteDimensional ℝ H]
    (X : KasparovCycle A B H)
    (hF : X.F * X.F = 1)
    (D Γ : ℝ → Endomorphism H)
    (hD0 : D 0 = X.F.toLinearMap)
    (hΓ0 : Γ 0 = (KreinGradedModule.gradeCLM (H := H)).toLinearMap)
    (hInv : InfoGeometry.Canonical.AnalyticalIndex.IndexInvariantAlong D Γ) :
    ∀ s : ℝ,
      InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex (D s) (Γ s) =
        X.analyticalIndex
```

`why this closes a real frontier edge`

This is the smallest transport lemma from the KK-side anchor into the pathwise
`AnalyticalIndex` invariance regime. It closes the exact edge
`KasparovCycle.analyticalIndex -> AnalyticalIndex.analyticalIndex`, then lifts
that equality along `IndexInvariantAlong`.

`likely proof ingredients already present in repo`

- `InfoGeometry.KK.index_bridge_spectral`
- `InfoGeometry.Canonical.AnalyticalIndex.IndexInvariantAlong`
- rewriting with `hD0`, `hΓ0`

`risk level`

`low`

## Candidate 2

`name`

`InfoGeometry.KK.kasparovIndex_eq_analyticalIndex_of_conjugacy`

`Lean-style signature sketch`

```lean
theorem kasparovIndex_eq_analyticalIndex_of_conjugacy
    {A B H : Type*}
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H]
    [FiniteDimensional ℝ H]
    (X : KasparovCycle A B H)
    (hF : X.F * X.F = 1)
    (D Γ : ℝ → Endomorphism H)
    (eFlow : ℝ → H ≃ₗ[ℝ] H)
    (hD0 : D 0 = X.F.toLinearMap)
    (hΓ0 : Γ 0 = (KreinGradedModule.gradeCLM (H := H)).toLinearMap)
    (hConj : InfoGeometry.Canonical.AnalyticalIndex.ChiralConjugacyAlong D Γ eFlow) :
    ∀ s : ℝ,
      InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex (D s) (Γ s) =
        X.analyticalIndex
```

`why this closes a real frontier edge`

This specializes the previous bridge to the exact frontier theorem already
highlighted by the graph: `indexInvariantAlong_of_conjugacy`. It gives the KK
core a direct entry into the `GrandSynthesis` conjugacy branch.

`likely proof ingredients already present in repo`

- Candidate 1
- `InfoGeometry.Canonical.AnalyticalIndex.indexInvariantAlong_of_conjugacy`

`risk level`

`low`

## Candidate 3

`name`

`InfoGeometry.KK.kasparovIndex_eq_analyticalIndex_of_modularCliffordTransport`

`Lean-style signature sketch`

```lean
theorem kasparovIndex_eq_analyticalIndex_of_modularCliffordTransport
    {A B H : Type*} {ι : Type*}
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H]
    [FiniteDimensional ℝ H]
    (X : KasparovCycle A B H)
    (hF : X.F * X.F = 1)
    (D Γ : ℝ → Endomorphism H)
    (σ : ℝ → Endomorphism H)
    (clAct : ι → Endomorphism H)
    (unit : ι)
    (hD0 : D 0 = X.F.toLinearMap)
    (hΓ0 : Γ 0 = (KreinGradedModule.gradeCLM (H := H)).toLinearMap)
    (hTrans :
      InfoGeometry.Canonical.AnalyticalIndex.ChiralSliceModularCliffordTransportAlong
        (D := D) (Γ := Γ) σ clAct unit) :
    ∀ s : ℝ,
      InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex (D s) (Γ s) =
        X.analyticalIndex
```

`why this closes a real frontier edge`

This is the modular/Clifford twin of Candidate 2. It lands directly on the
branch consumed by
`information_wheeler_dewitt_equivalence_of_ibDynamics_and_modularCliffordTransport_state_hypotheses`.

`likely proof ingredients already present in repo`

- Candidate 1
- `InfoGeometry.Canonical.AnalyticalIndex.indexInvariantAlong_of_modularCliffordTransport`

`risk level`

`low`

## Candidate 4

`name`

`InfoGeometry.Canonical.GrandSynthesis.fullCapstone_of_conjugacy_index_anchor`

`Lean-style signature sketch`

```lean
theorem fullCapstone_of_conjugacy_index_anchor
    (n : Nat)
    {X V F : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hGeoAlg : GeometricAlgebraicState n T flow D Γ)
    (hClosure : SinkhornKMSClosure n T.traj K ω β)
    (hConj : InfoGeometry.Canonical.AnalyticalIndex.ChiralConjugacyAlong D Γ eFlow)
    (hAnchor :
      InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex (D 0) (Γ 0) = kkIndex) :
    FullThermoGeoIndexCapstone n T flow D Γ K ω β
```

`why this closes a real frontier edge`

This candidate makes explicit the bridge from a KK-anchored analytical index to
the already existing capstone bundling route. The theorem
`fullThermoGeoIndexCapstone_of_states` already packages `hGeoAlg + hClosure`;
the added index anchor would expose the KK provenance of that capstone package.

`likely proof ingredients already present in repo`

- `InfoGeometry.Canonical.AnalyticalIndex.fullThermoGeoIndexCapstone_of_states`
- `InfoGeometry.Canonical.AnalyticalIndex.sinkhornRicciIndexInvariant_of_conjugacy_state_hypotheses`
- Candidates 1 or 2

`risk level`

`medium`

## Candidate 5

`name`

`InfoGeometry.Canonical.GrandSynthesis.wheelerDeWitt_equivalence_of_kk_conjugacy_anchor`

`Lean-style signature sketch`

```lean
theorem wheelerDeWitt_equivalence_of_kk_conjugacy_anchor
    (n : Nat)
    {X V F : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hFull : FullThermoGeoIndexCapstone n T flow D Γ K ω β)
    (hIndexAnchor :
      InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex (D 0) (Γ 0) = kkIndex) :
    ThermodynamicKMSState n T K ω β ↔ GeometricAlgebraicState n T flow D Γ
```

`why this closes a real frontier edge`

This does not strengthen the Wheeler-DeWitt equivalence itself; it strengthens
its provenance. The point is to make the KK index anchor explicit on the exact
consumer branch discovered by `Skynet v2`, rather than leaving the connection as
an implicit upstream dependency.

`likely proof ingredients already present in repo`

- `InfoGeometry.Canonical.GrandSynthesis.information_wheeler_dewitt_equivalence_of_fullCapstone`
- Candidate 4

`risk level`

`medium`

## Recommended Order

Best execution order:

1. Candidate 1
2. Candidate 2
3. Candidate 3
4. Candidate 4
5. Candidate 5

The first three are the true bridge lemmas.

The last two are capstone/provenance packaging lemmas and should only be
attempted after the KK-to-`IndexInvariantAlong` bridge is explicit in Lean.
