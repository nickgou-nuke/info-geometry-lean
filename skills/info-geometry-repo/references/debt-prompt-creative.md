# Debt Prompt: Creative Lane

Use this prompt with a proposal-oriented model that is trying to replace real
tracked debt items, not invent new frontier prose.

The model is allowed to suggest helper lemmas, proof decompositions, and local
refactors, but it is not allowed to claim proof completion.

## Hard Constraints

- Do not claim that a theorem is proved.
- Do not invent nonexistent repo vocabulary, imports, or helper lemmas.
- Stay anchored to the exact debt targets in the packet below.
- Prefer small helper lemmas and proof decomposition over giant rewrites.
- If a target should be rejected as not worth automating, say so explicitly.
- Treat the packet as a replacement queue, not a proof artifact.

## Task

For each candidate in the debt packet, propose the smallest constructive
replacement path that could plausibly survive Lean validation.

For each candidate provide exactly:
1. `candidate name`
2. `target theorem to repair`
3. `proposed helper lemmas`
4. `constructive attack plan`
5. `likely existing repo ingredients`
6. `risk level` (`low` / `medium` / `high`)

Do not output full Lean proofs.
Do not propose more than 3 helper lemmas per candidate.

## Debt Packet

```md
# Debt Candidates

This note is a report-only constructive replacement queue derived from the tracked
surrogate, vacuity, and thin-bridge audits.

It is not a proof artifact.

The purpose is to pin exact debt targets that can be attacked by a creative lane,
shrunk by a critical lane, and then materialized into quarantine for Lean validation.

## Audit Context

- surrogate findings: `0`
- vacuity findings: `0`
- thin-bridge findings: `0`
- aggregated replacement targets: `0`

## Selection Rule

- Prefer canonical/stable declarations over unstable/archive surfaces.
- Prefer critical/high findings over medium/low findings.
- Aggregate duplicate targets when multiple audits point at the same declaration.
- Keep every candidate tied to a real file:line surface already tracked by the audits.

## Current Replacement Queue

- none

The current tracked audits do not expose any replacement targets. Regenerate the packet after new debt findings appear.
```

## Surrogate Index

```md
# Surrogate Index

Generated: `2026-03-20 18:54:35`

This report tracks explicit proof gaps, assumption-bearing theorem surfaces, and named contract interfaces so surrogate debt can be replaced aggressively with real proofs.

## Hard Gate
- `scripts/audit_surrogates.sh`: **PASS**
- last gate output:
  - `[surrogate-audit] checking for direct open/namespace references to InfoGeometry.Unstable`
  - `[surrogate-audit] checking for placeholder/surrogate keywords outside allowed paths`
  - `[surrogate-audit] checking for banned surrogate declarations in stable modules`
  - `[surrogate-audit] checking canonical modules for reflexive Prop wrappers (heuristic)`
  - `[surrogate-audit] checking canonical surface for forbidden Canonical tactic usage`
  - `[surrogate-audit] OK`

## Counts
- total tracked findings: **0**
- proof holes: **0**
- explicit axiom declarations: **0**
- conditional theorem wrappers (`_of_axioms/_of_hypotheses/_of_assumptions`): **0**
- named contract declarations (`Axioms/Hypotheses/Assumptions`): **0**
- contract constructors (`to...Assumptions`, `..._of_concrete`, `..._of_finiteSupport`): **0**
- stable surrogate/placeholder markers: **0**
- canonical findings: **0**
- other stable findings: **0**
- unstable/archive findings: **0**

## Aggressive Replacement Queue

## Explicit Proof Holes

- none

## Explicit Axiom Declarations

- none

## Conditional Theorem Surface

- none

## Named Contract Declarations

- none

## Contract Constructors

- none

## Stable Surrogate/Placeholder Markers

- none

## Policy
- explicit proof holes and explicit axioms are not acceptable end-state theory surface
- conditional wrappers are tolerated only when the missing obligation is explicit and scheduled for replacement
- contract declarations must not be confused with completed proofs
- contract constructors are lower-risk adapters from concrete data into contract surfaces; they should not dominate the replacement queue
- replacement priority is: canonical proof holes -> stable axioms -> canonical conditional wrappers -> open contract interfaces
```

## Vacuity Index

```md
# Vacuity Index

Generated: `2026-03-20 18:54:35`

This report tracks alias-driven and definitional-identity surfaces that can make a bridge look mathematically deeper than it currently is.

## Status
- vacuity gate: **PASS**
- interpretation: `FAIL` means at least one high-priority alias/identity transport surface still sits on the active theory path

## Counts
- total tracked findings: **0**
- high-priority carrier/identity findings: **0**
- medium-priority explicit marker findings: **0**
- low-priority findings: **0**

## Aggressive Replacement Queue
- none

## Findings
- none

## Policy
- absence of `sorry` is not enough if a bridge is true only by aliasing or identity transport
- carrier aliases on bridge boundaries count as real mathematical debt, even when Lean accepts them
- replacement priority is: carrier aliases -> identity transports -> explicit alias-model compatibility layers
```

## Thin-Bridge Index

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

## Output Discipline

- If the packet is empty, say there is currently no tracked debt target to repair.
- If a candidate only needs renaming or deletion, say so instead of inventing proof work.
- If a helper lemma would create a larger abstraction leak, reject it.
