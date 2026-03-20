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
- Convert only credible candidates into minimal Lean-facing theorem sketches, attack plans, and quarantine-ready concrete sketches when justified.

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
7. `Lean-ready materialization sketch` (`none` unless the candidate is concrete and recommended for quarantine) 

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
```

## Current Candidate Packet

```md
# Bridge Candidates

This note is a report-only frontier packet derived from the current trusted
`Skynet v2` semantic frontier.

It is not a proof artifact.

The purpose is to pin the first small bridge lemmas suggested by the current
frontier, ranked with debt-aware scheduling signals.

## Trusted Graph Context

Current trusted semantic graph facts:

- `Skynet v2` graph:
  - `143` nodes
  - `753` edges
  - `378` cross-module edges
- walk mode: `reverse`
- audit signals:
  - thinness findings: `0`
  - vacuity findings: `0`
  - surrogate findings: `0`
  - unification modules tracked: `15`
- seed declarations:
  - `KasparovCycle.analyticalIndex`

## Candidate 1

`name`

`AutoCandidate.index_bridge_spectral_from_analyticalIndex_1`

`Lean-style signature sketch`

```lean
theorem auto_index_bridge_spectral_from_seed_1
    -- seed anchor: `KasparovCycle.analyticalIndex`
    -- frontier target: `InfoGeometry.KK.index_bridge_spectral`
    -- intended role: bridge theorem
    (... local hypotheses specialized to the target declaration ...)
    : (... direct transport / invariance / closure statement feeding the frontier ...) := by
  -- quarantine sketch only
```

`why this closes a real frontier edge`

This candidate is generated directly from the frontier row `InfoGeometry.KK.index_bridge_spectral` in `lean/InfoGeometry/KK/KasparovCycle.lean`. It is intended to insert a small bridge theorem feeding the frontier declaration. The seed-to-frontier link kinds currently visible are `primaryDep`. The current raw/priority scores are `0.043428` / `0.058428`, with module status `classical_adjacent_model` and adjustments `unification_status_adjustment +0.015`.

`likely proof ingredients already present in repo`

- `InfoGeometry.KK.KasparovCycle.analyticalIndex`
- `InfoGeometry.KK.index_bridge_spectral`
- `lean/InfoGeometry/KK/KasparovCycle.lean`
- `frontier rawScore: 0.043428`
- `frontier score: 0.058428`

`risk level`

`low`

## Candidate 2

`name`

`AutoCandidate.kk_analyticalIndex_eq_of_modularCliffordTransport_state_hypotheses_from_analyticalIndex_2`

`Lean-style signature sketch`

```lean
theorem auto_kk_analyticalIndex_eq_of_modularCliffordTransport_state_hypotheses_from_seed_2
    -- seed anchor: `KasparovCycle.analyticalIndex`
    -- frontier target: `InfoGeometry.Canonical.GrandSynthesis.kk_analyticalIndex_eq_of_modularCliffordTransport_state_hypotheses`
    -- intended role: transport equality theorem
    (... local hypotheses specialized to the target declaration ...)
    : (... direct transport / invariance / closure statement feeding the frontier ...) := by
  -- quarantine sketch only
```

`why this closes a real frontier edge`

This candidate is generated directly from the frontier row `InfoGeometry.Canonical.GrandSynthesis.kk_analyticalIndex_eq_of_modularCliffordTransport_state_hypotheses` in `lean/InfoGeometry/Canonical/GrandSynthesis.lean`. It is intended to derive a nontrivial equality that feeds the frontier declaration. The seed-to-frontier link kinds currently visible are `primaryDep`. The current raw/priority scores are `0.066003` / `0.051003`, with module status `mixed_capstone_surface` and adjustments `unification_status_adjustment -0.015`.

`likely proof ingredients already present in repo`

- `InfoGeometry.KK.KasparovCycle.analyticalIndex`
- `InfoGeometry.Canonical.GrandSynthesis.kk_analyticalIndex_eq_of_modularCliffordTransport_state_hypotheses`
- `lean/InfoGeometry/Canonical/GrandSynthesis.lean`
- `frontier rawScore: 0.066003`
- `frontier score: 0.051003`

`risk level`

`medium`

## Candidate 3

`name`

`AutoCandidate.kk_analyticalIndex_eq_of_conjugacy_state_hypotheses_from_analyticalIndex_3`

`Lean-style signature sketch`

```lean
theorem auto_kk_analyticalIndex_eq_of_conjugacy_state_hypotheses_from_seed_3
    -- seed anchor: `KasparovCycle.analyticalIndex`
    -- frontier target: `InfoGeometry.Canonical.GrandSynthesis.kk_analyticalIndex_eq_of_conjugacy_state_hypotheses`
    -- intended role: transport equality theorem
    (... local hypotheses specialized to the target declaration ...)
    : (... direct transport / invariance / closure statement feeding the frontier ...) := by
  -- quarantine sketch only
```

`why this closes a real frontier edge`

This candidate is generated directly from the frontier row `InfoGeometry.Canonical.GrandSynthesis.kk_analyticalIndex_eq_of_conjugacy_state_hypotheses` in `lean/InfoGeometry/Canonical/GrandSynthesis.lean`. It is intended to derive a nontrivial equality that feeds the frontier declaration. The seed-to-frontier link kinds currently visible are `primaryDep`. The current raw/priority scores are `0.063047` / `0.048047`, with module status `mixed_capstone_surface` and adjustments `unification_status_adjustment -0.015`.

`likely proof ingredients already present in repo`

- `InfoGeometry.KK.KasparovCycle.analyticalIndex`
- `InfoGeometry.Canonical.GrandSynthesis.kk_analyticalIndex_eq_of_conjugacy_state_hypotheses`
- `lean/InfoGeometry/Canonical/GrandSynthesis.lean`
- `frontier rawScore: 0.063047`
- `frontier score: 0.048047`

`risk level`

`medium`

## Candidate 4

`name`

`AutoCandidate.chiralSliceIsoAlong_of_noZeroEigenCrossing_from_analyticalIndex_4`

`Lean-style signature sketch`

```lean
theorem auto_chiralSliceIsoAlong_of_noZeroEigenCrossing_from_seed_4
    -- seed anchor: `KasparovCycle.analyticalIndex`
    -- frontier target: `InfoGeometry.Canonical.AnalyticalIndex.chiralSliceIsoAlong_of_noZeroEigenCrossing`
    -- intended role: bridge theorem
    (... local hypotheses specialized to the target declaration ...)
    : (... direct transport / invariance / closure statement feeding the frontier ...) := by
  -- quarantine sketch only
```

`why this closes a real frontier edge`

This candidate is generated directly from the frontier row `InfoGeometry.Canonical.AnalyticalIndex.chiralSliceIsoAlong_of_noZeroEigenCrossing` in `lean/InfoGeometry/Canonical/AnalyticalIndex.lean`. It is intended to insert a small bridge theorem feeding the frontier declaration. The seed-to-frontier link kinds currently visible are `-`. The current raw/priority scores are `0.015689` / `0.030689`, with module status `classical_adjacent_model` and adjustments `unification_status_adjustment +0.015`.

`likely proof ingredients already present in repo`

- `InfoGeometry.Canonical.AnalyticalIndex.chiralSliceIsoAlong_of_noZeroEigenCrossing`
- `lean/InfoGeometry/Canonical/AnalyticalIndex.lean`
- `frontier rawScore: 0.015689`
- `frontier score: 0.030689`
- `module status: classical_adjacent_model`

`risk level`

`low`

## Candidate 5

`name`

`AutoCandidate.sinkhornRicciIndexInvariant_of_conjugacy_state_hypotheses_from_analyticalIndex_5`

`Lean-style signature sketch`

```lean
theorem auto_sinkhornRicciIndexInvariant_of_conjugacy_state_hypotheses_from_seed_5
    -- seed anchor: `KasparovCycle.analyticalIndex`
    -- frontier target: `InfoGeometry.Canonical.AnalyticalIndex.sinkhornRicciIndexInvariant_of_conjugacy_state_hypotheses`
    -- intended role: transport / invariance theorem
    (... local hypotheses specialized to the target declaration ...)
    : (... direct transport / invariance / closure statement feeding the frontier ...) := by
  -- quarantine sketch only
```

`why this closes a real frontier edge`

This candidate is generated directly from the frontier row `InfoGeometry.Canonical.AnalyticalIndex.sinkhornRicciIndexInvariant_of_conjugacy_state_hypotheses` in `lean/InfoGeometry/Canonical/AnalyticalIndex.lean`. It is intended to close an invariance step feeding the frontier declaration. The seed-to-frontier link kinds currently visible are `-`. The current raw/priority scores are `0.014499` / `0.029499`, with module status `classical_adjacent_model` and adjustments `unification_status_adjustment +0.015`.

`likely proof ingredients already present in repo`

- `InfoGeometry.Canonical.AnalyticalIndex.sinkhornRicciIndexInvariant_of_conjugacy_state_hypotheses`
- `lean/InfoGeometry/Canonical/AnalyticalIndex.lean`
- `frontier rawScore: 0.014499`
- `frontier score: 0.029499`
- `module status: classical_adjacent_model`

`risk level`

`low`
```

## Current Thin-Bridge Audit

```md
# Bridge Thinness Index

Generated: `2026-03-20 18:54:35`

This report is a heuristic audit of bridge-/launchpad-/interface-facing theorem surfaces that may be mathematically thinner than their names suggest.

## Status
- thin-bridge gate: **PASS**
- interpretation: `FAIL` means at least one targeted theorem currently looks like a definitional identity

## Counts
- total tracked findings: **0**
- definitional identity findings: **0**
- direct forwarder findings: **0**
- underscore-hypothesis findings: **0**
- package/orchestration findings: **0**

## Queue
- none

## Findings
- none

## Policy
- this is a heuristic syntax audit, not a proof oracle
- `rfl`/direct-forward/package findings are review targets, not automatic verdicts of invalid mathematics
- the purpose is to keep bridge names aligned with actual proof depth
```

## Review Discipline

- Prefer candidates that can become small insertable lemmas.
- Downgrade grand names if the likely proof is only structural packaging.
- If a candidate survives, keep it small enough for quarantine first and canonical promotion later.
- A materialization sketch must be compilable Lean syntax in the current repo vocabulary; it may be a small quarantine wrapper over already existing theorems.
