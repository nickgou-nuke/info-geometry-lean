# Formalization Discipline

> Status: `current authority`
> Audited: 2026-05-05
> Scope: Lean formalization, external-corpus bridges, generated theorem packets.

This repository follows a strict anti-vacuity standard.  The useful lesson from
`lean-dojo/LeanMillenniumPrizeProblems` is not that every ambitious theorem
should be stated immediately; it is that every unavailable foundation must be
made explicit, named, and quarantined as data or hypothesis.

## Core Rule

Do not encode a mathematical story as a fake theorem.

If the repo does not yet contain the foundations needed to construct an object,
prove an existence theorem, or justify an equivalence, the code must say so in
one of three precise ways:

- `data package`: a structure carrying the missing objects and compatibility
  laws as fields.
- `calibration witness`: an explicit model-specific law connecting two already
  defined readouts.
- `context packet`: a non-authoritative record used for retrieval, planning, or
  audit, never as proof authority.

## Forbidden Patterns

- `axiom` or `constant` to assert a major theorem or missing construction.
- `sorry`, `admit`, or equivalent proof holes in committed theorem surfaces.
- A theorem whose conclusion is true only because a field states the same
  conclusion verbatim.
- A structure that hides all mathematical content behind `Prop` fields named
  `valid`, `law`, or `witness` without exposing the objects being related.
- A diagonal, finite, scalar, or toy model presented as the owner of a genuinely
  noncommutative/infinite/analytic construction.
- External repository records treated as if they were local Lean proof
  authority.

## Required Patterns

### 1. Data package for missing foundations

Use a package when Mathlib or this repository does not yet construct the needed
objects.

Good shape:

```lean
structure SomeData (X : Type*) where
  carrier : Type*
  map : carrier → X
  compatibility : ∀ x, PropAbout (map x)
```

The package is not a theorem that such data exist.  It is a vocabulary for
stating later claims without cheating.

### 2. Derived theorem when structure already exists

If two fields make a third field derivable, remove the third field and prove it.

Good pattern:

```lean
objective_eq_weight :
  objective state = weight

entropy_eq_objective :
  entropy state = objective state
```

Then derive:

```lean
theorem entropy_eq_weight :
  entropy state = weight := by
  rw [entropy_eq_objective, objective_eq_weight]
```

### 3. Identity instance for zero-hypothesis smoke tests

When an abstract calibration is legitimate only because `State` is arbitrary,
also provide a concrete identity model when possible:

```lean
def identityCalibration : Calibration (Finset ℕ) where
  stateOfFinset := id
  readout := canonicalReadout
  readout_eq := by intro A; rfl
```

This proves that the interface is not merely decorative.

### 4. External context is not proof

Bridges such as `millennium_problem_bridge.py`, `leandojo_v2_bridge.py`, and
`real_prover_trace_bridge.py` emit retrieval/training/context records.  These
records may guide Hive, LeanSearch, or LLM prompts, but they do not increase
proof authority.

Every such artifact should carry an authority guard such as:

```json
{
  "external_record_is_retrieval_context": true,
  "not_a_proof_in_current_repo": true,
  "lean_remains_proof_authority": true
}
```

## Standard Form for Ambitious Statements

When stating a large theorem-like target, use this order:

1. Define the canonical objects already owned by the repo.
2. Import the owner modules, not a parallel abstraction.
3. Bundle missing foundations as a named data package.
4. Prove easy directions constructively.
5. State the hard direction as the conjectural target only if it is clearly
   marked as a `Prop`, not as a solved theorem.
6. Add a concrete identity or finite smoke model if available.

## Review Checklist

Before accepting a new bridge or theorem surface, check:

- Does every field relate named objects, or is it just an opaque `Prop`?
- Can any field be derived from earlier fields?
- Is any external source being treated as local proof?
- Is a finite diagonal model being promoted beyond a chart/readout role?
- Are hard analytic/geometric constructions packaged honestly as data?
- Is there at least one constructive lemma or identity instance?
- Does the module avoid `sorry`, `admit`, and user `axiom`s?

The guiding sentence is:

```text
Parameterize missing foundations; prove everything else.
```
