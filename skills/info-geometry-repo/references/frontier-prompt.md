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
    (hF : X.F * X.F = 1) :
    InfoGeometry.Canonical.AnalyticalIndex.IndexInvariantAlong
      (fun _ : ℝ => X.F.toLinearMap)
      (fun _ : ℝ => (KreinGradedModule.gradeCLM (H := H)).toLinearMap) := ...
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
    (hF : X.F * X.F = 1) :
    InfoGeometry.Canonical.AnalyticalIndex.IndexInvariantAlong
      (fun _ : ℝ => X.F.toLinearMap)
      (fun _ : ℝ => (KreinGradedModule.gradeCLM (H := H)).toLinearMap) := ...
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
