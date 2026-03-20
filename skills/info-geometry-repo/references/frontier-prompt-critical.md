# Frontier Prompt: Critical Lane

Use this prompt with a critical Lean-aware evaluation model.
Suggested role mapping: ChatGPT/Codex-style formal critique lane.

The model must aggressively reject fake closure, thin bridges, and unsupported
speculation. It is not allowed to promote a candidate just because it sounds
mathematically interesting.

## Hard Constraints

- Treat the creative lane output as untrusted proposal text.
- Reject any candidate that invents unsupported repo vocabulary.
- Reject any candidate whose likely proof is just `rfl`, direct forwarding, or tuple repackaging unless the name is explicitly downgraded.
- Do not claim proof completion.
- Convert only credible candidates into minimal Lean-facing theorem sketches and attack plans.

## Task

Evaluate the creative-lane candidate list against the current trusted frontier
and the current thin-bridge audit.

For each candidate provide exactly:
1. `verdict` (`accept` / `revise` / `reject`)
2. `reason`
3. `minimal Lean-style signature sketch`
4. `proof ingredients already present in repo`
5. `thinness risk` (`definitional` / `forwarder` / `packaging` / `substantive`) 
6. `quarantine recommendation` (`yes` / `no`) 

Then end with:
- `Top 3 survivors`
- `Top 3 rejection reasons`

## Paste Creative Output Below

```text
[PASTE CREATIVE MODEL OUTPUT HERE]
```

## Trusted Frontier Context

```md
# Frontier Prompt

Use this prompt when you want an LLM to propose candidate bridge statements over the
current trusted semantic frontier, without asking it to prove anything.

This prompt is intentionally strict. It is designed for:

- candidate theorem signatures
- closure-gap diagnosis
- attack plans

It is not designed for:

- free-form speculation
- long prose about physics
- full proofs
- inventing new definitions without necessity

## Current Trusted Frontier

The current bridge is real in the semantic graph:

- `InfoGeometry.KK.KasparovCycle.analyticalIndex`
- `InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex`
- reverse-consumer frontier into `InfoGeometry.Canonical.GrandSynthesis`

Trusted graph facts:

- `Skynet v2` universal semantic graph:
  - `128` nodes
  - `647` edges
  - `319` cross-module edges
- direct bridge:
  - `KasparovCycle.analyticalIndex -> Canonical.AnalyticalIndex.analyticalIndex`
- reverse frontier contains:
  - `InfoGeometry.KK.index_bridge_spectral`
  - `InfoGeometry.Canonical.AnalyticalIndex.chiralSliceIsoAlong_of_noZeroEigenCrossing`
  - `InfoGeometry.Canonical.AnalyticalIndex.indexInvariantAlong_of_conjugacy`
  - `InfoGeometry.Canonical.GrandSynthesis.information_wheeler_dewitt_equivalence_of_state_capstone_hypotheses`
  - `InfoGeometry.Canonical.GrandSynthesis.information_wheeler_dewitt_equivalence_of_fullCapstone`
  - `InfoGeometry.Canonical.GrandSynthesis.information_wheeler_dewitt_implication_of_fully_derived_hypotheses`
  - `InfoGeometry.Canonical.GrandSynthesis.thermodynamic_and_geometricAlgebraic_of_fullCapstone`

## Minimal Local Facts

From `lean/InfoGeometry/KK/KasparovCycle.lean`:

```lean
noncomputable def KasparovCycle.analyticalIndex [FiniteDimensional ℝ H] : ℤ :=
  InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex
    X.F.toLinearMap
    (KreinGradedModule.gradeCLM (H := H)).toLinearMap

theorem index_bridge_spectral [FiniteDimensional ℝ H]
    (_hF : X.F * X.F = 1) :
    X.analyticalIndex = InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex
      X.F.toLinearMap
      (KreinGradedModule.gradeCLM (H := H)).toLinearMap := rfl
```

From `lean/InfoGeometry/Canonical/AnalyticalIndex.lean`:

```lean
noncomputable def analyticalIndex [FiniteDimensional ℝ V] (D Γ : Endomorphism V) : ℤ := ...

def IndexInvariantAlong [FiniteDimensional ℝ V] (D Γ : ℝ → Endomorphism V) : Prop := ...

theorem chiralSliceIsoAlong_of_noZeroEigenCrossing ... := ...
theorem indexInvariantAlong_of_noZeroEigenCrossing ... : IndexInvariantAlong D Γ := ...
theorem indexInvariantAlong_of_conjugacy ... : IndexInvariantAlong D Γ := ...
theorem indexInvariantAlong_of_modularCliffordTransport ... : IndexInvariantAlong D Γ := ...
```

From `lean/InfoGeometry/Canonical/GrandSynthesis.lean`:

```lean
theorem information_wheeler_dewitt_implication_of_ibDynamics_and_indexHypotheses ... := ...
theorem thermodynamic_and_geometricAlgebraic_of_fullCapstone ... := ...
theorem information_wheeler_dewitt_equivalence_of_fullCapstone ... := ...
theorem information_wheeler_dewitt_equivalence_of_state_capstone_hypotheses ... := ...
```

## Prompt Template

Use the following prompt with a coding/math LLM.

```text
You are helping close a Lean 4 theorem frontier.

Hard constraints:
- Do not invent nonexistent theorems, defs, or imports.
- Do not claim a proof exists unless it is directly implied by the context below.
- Stay close to the current codebase vocabulary and theorem names.
- Output candidate bridge statements and proof attack plans only.
- Prefer Lean-style theorem signatures over prose.
- If a candidate depends on a missing notion, say so explicitly.

Goal:
Propose the smallest mathematically credible bridge statements connecting
`InfoGeometry.KK.KasparovCycle.analyticalIndex`
through `InfoGeometry.Canonical.AnalyticalIndex`
toward the Wheeler-DeWitt / full-capstone layer in `GrandSynthesis`.

Trusted graph facts:
- direct bridge:
  `KasparovCycle.analyticalIndex -> Canonical.AnalyticalIndex.analyticalIndex`
- reverse frontier highlights these consumers:
  `index_bridge_spectral`
  `chiralSliceIsoAlong_of_noZeroEigenCrossing`
  `indexInvariantAlong_of_conjugacy`
  `information_wheeler_dewitt_equivalence_of_state_capstone_hypotheses`
  `information_wheeler_dewitt_equivalence_of_fullCapstone`
  `information_wheeler_dewitt_implication_of_fully_derived_hypotheses`
  `thermodynamic_and_geometricAlgebraic_of_fullCapstone`

Local Lean facts:

1. In `KasparovCycle.lean`:
```lean
noncomputable def KasparovCycle.analyticalIndex [FiniteDimensional ℝ H] : ℤ :=
  InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex
    X.F.toLinearMap
    (KreinGradedModule.gradeCLM (H := H)).toLinearMap

theorem index_bridge_spectral [FiniteDimensional ℝ H]
    (_hF : X.F * X.F = 1) :
    X.analyticalIndex = InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex
      X.F.toLinearMap
      (KreinGradedModule.gradeCLM (H := H)).toLinearMap := rfl
```

2. In `AnalyticalIndex.lean`:
```lean
noncomputable def analyticalIndex [FiniteDimensional ℝ V] (D Γ : Endomorphism V) : ℤ := ...
def IndexInvariantAlong [FiniteDimensional ℝ V] (D Γ : ℝ → Endomorphism V) : Prop := ...
theorem chiralSliceIsoAlong_of_noZeroEigenCrossing ... := ...
theorem indexInvariantAlong_of_noZeroEigenCrossing ... : IndexInvariantAlong D Γ := ...
theorem indexInvariantAlong_of_conjugacy ... : IndexInvariantAlong D Γ := ...
theorem indexInvariantAlong_of_modularCliffordTransport ... : IndexInvariantAlong D Γ := ...
```

3. In `GrandSynthesis.lean`:
```lean
theorem information_wheeler_dewitt_implication_of_ibDynamics_and_indexHypotheses ... := ...
theorem thermodynamic_and_geometricAlgebraic_of_fullCapstone ... := ...
theorem information_wheeler_dewitt_equivalence_of_fullCapstone ... := ...
theorem information_wheeler_dewitt_equivalence_of_state_capstone_hypotheses ... := ...
```

Task:
Propose 3-5 candidate bridge statements.

For each candidate, provide exactly:
1. `name`
2. `Lean-style signature sketch`
3. `why this closes a real frontier edge`
4. `likely proof ingredients already present in repo`
5. `risk level` (`low` / `medium` / `high`)

Strong preference:
- statements transporting `KasparovCycle.analyticalIndex` into an `IndexInvariantAlong` regime
- statements connecting analytical-index invariance assumptions to full-capstone hypotheses
- statements that could be inserted as small bridge lemmas, not giant new frameworks

Do not output proof scripts.
Do not output more than 5 candidates.
```

## Expected Good Output Shape

The model should return candidates of this kind:

- a bridge from `index_bridge_spectral` into a path/invariance statement
- a bridge turning a KK-side operator/grading pair into an `AnalyticalIndex` path hypothesis
- a bridge exposing the exact `AnalyticalIndex` assumptions used by a `GrandSynthesis` theorem

The model should not return:

- vague prose about quantum gravity
- category-theory essays disconnected from the current names
- giant new structures that do not match existing modules
```

## Current Candidate Packet

```md
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
```

## Current Thin-Bridge Audit

```md
# Bridge Thinness Index

Generated: `2026-03-20 14:57:58`

This report is a heuristic audit of bridge-/launchpad-/interface-facing theorem surfaces that may be mathematically thinner than their names suggest.

## Status
- thin-bridge gate: **FAIL**
- interpretation: `FAIL` means at least one targeted theorem currently looks like a definitional identity

## Counts
- total tracked findings: **29**
- definitional identity findings: **3**
- direct forwarder findings: **15**
- underscore-hypothesis findings: **2**
- package/orchestration findings: **9**

## Queue
- `high` `definitional_identity` `B_agrees_with_Gauge_bilinear` at `lean/InfoGeometry/Canonical/CliffordBridge.lean:20`
- `high` `definitional_identity` `relative_volume_change_rn_eq_exp_neg_kahler` at `lean/InfoGeometry/Canonical/DiracRicciBridge.lean:37`
- `high` `definitional_identity` `kkt_perelman_correspondence` at `lean/InfoGeometry/Unstable/SingularUnitaryBridge.lean:41`
- `medium` `direct_forwarder` `isRicciFlat_of_unitRelativeVolume_metricDerived` at `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:140`
- `medium` `direct_forwarder` `ricciTensor_unique_of_mongeAmpereRicciState` at `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:232`
- `medium` `direct_forwarder` `isRicciFlat_of_unitRelativeVolume` at `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:258`
- `medium` `direct_forwarder` `vacuumEinsteinEquation_of_unitRelativeVolume` at `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:270`
- `medium` `direct_forwarder` `vacuumEinsteinEquation_of_mongeAmpereRicciState` at `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:284`
- `medium` `direct_forwarder` `cayleyPythagoreanInvariance` at `lean/InfoGeometry/Canonical/CayleyBregmanBridge.lean:98`
- `medium` `direct_forwarder` `countInducedCoupling_hasPositiveRowSums` at `lean/InfoGeometry/Canonical/CountSubstrateBridge.lean:298`
- `medium` `direct_forwarder` `countInducedCoupling_hasPositiveColSums` at `lean/InfoGeometry/Canonical/CountSubstrateBridge.lean:304`
- `medium` `direct_forwarder` `jordan_kkt_barrier_eq_neg_log_det` at `lean/InfoGeometry/Canonical/DiracRicciBridge.lean:86`
- `medium` `direct_forwarder` `log_det_barrier_eq_neg_log_det'` at `lean/InfoGeometry/Canonical/DiracRicciBridge.lean:104`
- `medium` `direct_forwarder` `free_energy_from_log_det_eq_neg_scale_log_partition'` at `lean/InfoGeometry/Canonical/DiracRicciBridge.lean:122`
- `medium` `direct_forwarder` `IBPartitionFunction_shift_eq_smul` at `lean/InfoGeometry/Canonical/IBGaugeBridge.lean:87`
- `medium` `direct_forwarder` `sinkhorn_step_kmsClosure_of_control` at `lean/InfoGeometry/Canonical/KMSSinkhornBridge.lean:177`
- `medium` `underscore_hypothesis` `bayesian_update_as_spinor_bilinear` at `lean/InfoGeometry/Canonical/ModularSpinorBridge.lean:216`
- `medium` `direct_forwarder` `hohenbergKohnDualState_of_concreteLegendre` at `lean/InfoGeometry/Canonical/QFTTDFTLaunchpad.lean:206`
- `medium` `direct_forwarder` `rungeGrossStationaryDualState_of_stationaryAtScale` at `lean/InfoGeometry/Canonical/QFTTDFTLaunchpad.lean:265`
- `medium` `underscore_hypothesis` `index_bridge_spectral` at `lean/InfoGeometry/KK/KasparovCycle.lean:83`
- `low` `package_orchestration` `aqft_readiness_package_with_projectorSuperPair_base` at `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean:404`
- `low` `package_orchestration` `aqft_tdft_constructive_launchpad_packaged_with_aqft_readiness` at `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean:458`
- `low` `package_orchestration` `aqft_tdft_constructive_launchpad_with_bogoliubov_projector_superalgebra_packaged_with_aqft_readiness` at `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean:515`
- `low` `package_orchestration` `aqft_tdft_constructive_launchpad_packaged_with_aqft_readiness_and_projectorSuperPair_base` at `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean:580`
- `low` `package_orchestration` `realHilbertCompressionInterpretation_packaged_with_aqft_readiness_and_projectorSuperPair_base` at `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean:686`
- `low` `package_orchestration` `satisfiesMongeAmpere_const_of_hasConstantMongeAmpereDensity` at `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:62`
- `low` `package_orchestration` `cstar_completeCStar_kms_fock_bogoliubov_projector_package` at `lean/InfoGeometry/Canonical/OperatorAlgebraBridge.lean:133`
- `low` `package_orchestration` `cstar_completeCStar_kms_fock_projectorSuperPair_base_package` at `lean/InfoGeometry/Canonical/OperatorAlgebraBridge.lean:181`
- `low` `package_orchestration` `aqft_tdft_constructive_launchpad_with_bogoliubov_projector_superalgebra` at `lean/InfoGeometry/Canonical/QFTTDFTLaunchpad.lean:424`

## Findings
- `lean/InfoGeometry/Canonical/CliffordBridge.lean:20` `B_agrees_with_Gauge_bilinear` [high]
  proof body reduces directly to `rfl`
- `lean/InfoGeometry/Canonical/DiracRicciBridge.lean:37` `relative_volume_change_rn_eq_exp_neg_kahler` [high]
  proof body reduces directly to `rfl`
- `lean/InfoGeometry/Unstable/SingularUnitaryBridge.lean:41` `kkt_perelman_correspondence` [high]
  proof body reduces directly to `rfl`
- `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:140` `isRicciFlat_of_unitRelativeVolume_metricDerived` [medium]
  proof body forwards directly via `exact isRicciFlat_of_isEinsteinKaehlerAtWith_zero`
- `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:232` `ricciTensor_unique_of_mongeAmpereRicciState` [medium]
  proof body forwards directly via `exact ricciTensor_eq_of_isRicciFlat`
- `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:258` `isRicciFlat_of_unitRelativeVolume` [medium]
  proof body forwards directly via `exact isRicciFlat_of_isEinsteinKaehlerAtWith_zero`
- `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:270` `vacuumEinsteinEquation_of_unitRelativeVolume` [medium]
  proof body forwards directly via `exact vacuumEinsteinEquation_of_isRicciFlat`
- `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:284` `vacuumEinsteinEquation_of_mongeAmpereRicciState` [medium]
  proof body forwards directly via `exact vacuumEinsteinEquation_of_isRicciFlat`
- `lean/InfoGeometry/Canonical/CayleyBregmanBridge.lean:98` `cayleyPythagoreanInvariance` [medium]
  proof body is a `simpa ... using cayley_pythagorean_invariance` forwarder
- `lean/InfoGeometry/Canonical/CountSubstrateBridge.lean:298` `countInducedCoupling_hasPositiveRowSums` [medium]
  proof body forwards directly via `exact entrywisePositive_hasPositiveRowSums`
- `lean/InfoGeometry/Canonical/CountSubstrateBridge.lean:304` `countInducedCoupling_hasPositiveColSums` [medium]
  proof body forwards directly via `exact entrywisePositive_hasPositiveColSums`
- `lean/InfoGeometry/Canonical/DiracRicciBridge.lean:86` `jordan_kkt_barrier_eq_neg_log_det` [medium]
  proof body forwards directly via `exact JordanKKTData.K_def`
- `lean/InfoGeometry/Canonical/DiracRicciBridge.lean:104` `log_det_barrier_eq_neg_log_det'` [medium]
  proof body forwards directly via `exact logDetBarrier_eq_neg_log_det`
- `lean/InfoGeometry/Canonical/DiracRicciBridge.lean:122` `free_energy_from_log_det_eq_neg_scale_log_partition'` [medium]
  proof body forwards directly via `exact freeEnergyFromLogDet_eq_neg_scale_log_partition`
- `lean/InfoGeometry/Canonical/IBGaugeBridge.lean:87` `IBPartitionFunction_shift_eq_smul` [medium]
  proof body is a `simpa ... using congrArg` forwarder
- `lean/InfoGeometry/Canonical/KMSSinkhornBridge.lean:177` `sinkhorn_step_kmsClosure_of_control` [medium]
  proof body forwards directly via `exact sinkhorn_step_kmsClosure_of_approxClosure_of_barrierZero`
- `lean/InfoGeometry/Canonical/ModularSpinorBridge.lean:216` `bayesian_update_as_spinor_bilinear` [medium]
  declaration head contains underscore-prefixed hypotheses: `_innovation`
- `lean/InfoGeometry/Canonical/QFTTDFTLaunchpad.lean:206` `hohenbergKohnDualState_of_concreteLegendre` [medium]
  proof body forwards directly via `exact hohenbergKohnDualState_of_inverse_maps`
- `lean/InfoGeometry/Canonical/QFTTDFTLaunchpad.lean:265` `rungeGrossStationaryDualState_of_stationaryAtScale` [medium]
  proof body forwards directly via `exact hStationary.2`
- `lean/InfoGeometry/KK/KasparovCycle.lean:83` `index_bridge_spectral` [medium]
  declaration head contains underscore-prefixed hypotheses: `_hF`
- `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean:404` `aqft_readiness_package_with_projectorSuperPair_base` [low]
  proof body is primarily package/orchestration (`rcases` + tuple assembly)
- `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean:458` `aqft_tdft_constructive_launchpad_packaged_with_aqft_readiness` [low]
  proof body is primarily package/orchestration (`rcases` + tuple assembly)
- `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean:515` `aqft_tdft_constructive_launchpad_with_bogoliubov_projector_superalgebra_packaged_with_aqft_readiness` [low]
  proof body is primarily package/orchestration (`rcases` + tuple assembly)
- `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean:580` `aqft_tdft_constructive_launchpad_packaged_with_aqft_readiness_and_projectorSuperPair_base` [low]
  proof body is primarily package/orchestration (`rcases` + tuple assembly)
- `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean:686` `realHilbertCompressionInterpretation_packaged_with_aqft_readiness_and_projectorSuperPair_base` [low]
  proof body is primarily package/orchestration (`rcases` + tuple assembly)
- `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:62` `satisfiesMongeAmpere_const_of_hasConstantMongeAmpereDensity` [low]
  proof body is primarily package/orchestration (`rcases` + tuple assembly)
- `lean/InfoGeometry/Canonical/OperatorAlgebraBridge.lean:133` `cstar_completeCStar_kms_fock_bogoliubov_projector_package` [low]
  proof body is primarily package/orchestration (`rcases` + tuple assembly)
- `lean/InfoGeometry/Canonical/OperatorAlgebraBridge.lean:181` `cstar_completeCStar_kms_fock_projectorSuperPair_base_package` [low]
  proof body is primarily package/orchestration (`rcases` + tuple assembly)
- `lean/InfoGeometry/Canonical/QFTTDFTLaunchpad.lean:424` `aqft_tdft_constructive_launchpad_with_bogoliubov_projector_superalgebra` [low]
  proof body is primarily package/orchestration (`rcases` + tuple assembly)

## Policy
- this is a heuristic syntax audit, not a proof oracle
- `rfl`/direct-forward/package findings are review targets, not automatic verdicts of invalid mathematics
- the purpose is to keep bridge names aligned with actual proof depth
```

## Review Discipline

- Prefer candidates that can become small insertable lemmas.
- Downgrade grand names if the likely proof is only structural packaging.
- If a candidate survives, keep it small enough for quarantine first and canonical promotion later.
