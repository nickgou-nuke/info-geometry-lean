# Surrogate Index

Generated: `2026-03-22 22:53:31`

This report tracks explicit proof gaps, assumption-bearing theorem surfaces, and named contract interfaces so surrogate debt can be replaced aggressively with real proofs.

## Hard Gate
- `scripts/audit_surrogates.sh`: **PASS**
- last gate output:
  - `Constructivity audit (stable surface)`
  - `No exact constructivity violations found.`
  - `[surrogate-audit] checking stable surface for uninstantiated bridge assumptions and vacuous bridge debt`
  - `[generate-vacuity-index] wrote /home/goutev/LEAN4/info-geometry-lean/VACUITY_INDEX.md`
  - `[generate-vacuity-index] findings=0 gate=PASS`
  - `[surrogate-audit] OK`

## Counts
- total tracked findings: **0**
- proof holes: **0**
- explicit axiom declarations: **0**
- quarantine manifest drift findings: **0**
- vacuous `trivial` theorems: **0**
- constant `Prop := True/False` surfaces: **0**
- universal `∀ _, True` fields: **0**
- zero quadratic-form surrogates: **0**
- scaled-zero quadratic-form surrogates: **0**
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

## Quarantine Manifest Drift

- none

## Vacuous `trivial` Theorems

- none

## Constant `Prop := True/False` Surfaces

- none

## Universal `∀ _, True` Fields

- none

## Zero Quadratic-Form Surrogates

- none

## Scaled-Zero Quadratic-Form Surrogates

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
- explicit proof holes, explicit axioms, and quarantine-manifest drift are not acceptable end-state theory surface
- vacuous closed proofs (`trivial`, `Prop := True/False`, universal-True fields) count as surrogate debt even when Lean accepts them
- zero-valued surrogate constructions count as debt when they stand in for real mathematical content
- conditional wrappers are tolerated only when the missing obligation is explicit and scheduled for replacement
- contract declarations must not be confused with completed proofs
- contract constructors are lower-risk adapters from concrete data into contract surfaces; they should not dominate the replacement queue
- replacement priority is: canonical proof holes/vacuous proofs -> manifest drift and stable axioms -> canonical conditional wrappers -> open contract interfaces
