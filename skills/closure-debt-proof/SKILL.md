---
name: closure-debt-proof
description: >
  Eliminate _True/_sorryProof certificate patterns by either proving the
  property as a theorem or replacing it with an honest sorry. Never keep
  a _True : Prop := True default. This skill is the closure-debt half of the
  production evolution system documented in docs/PRODUCTION_EVOLUTION_SYSTEM.md.
---

## Constructive Closure Mandate

This skill is part of the repository's executed autonomous evolution pipeline.
Implementation-level architecture lives in:
- `docs/PRODUCTION_EVOLUTION_SYSTEM.md`
- `tools/infra/evolution_worker.py`
- `tools/infra/gepa_evolver.py`
- `tools/infra/gepa_real_eval.py`
- `tools/infra/proof_seeker.py`
- `tools/infra/vacuity_critic.py`

The `_True : Prop := by sorry` and `_sorryProof` patterns are the **prima materia**
of obfuscation. Every such field that defaults to `True` or `by sorry` hides
a real proof obligation behind a certificate wrapper.

**Rule:** Every mathematical property is either:
- A `theorem` with a kernel-checked proof, OR
- An explicit `sorry` at the theorem level, NOT hidden inside a `Prop` field.

No `_True` wrappers. No `_sorryProof` certificates. No `: Prop := True`.

## How to Fix

### Pattern 1: `_True : Prop := by sorry`

Before:
```lean
structure Foo where
  someProperty_True : Prop := by
    sorry
```

After (provable case):
```lean
structure Foo where
  -- property removed from structure

theorem someProperty (x : Foo) : ... := by
  -- real proof using existing fields
```

After (unprovable case):
```lean
structure Foo where
  -- property removed from structure

theorem someProperty (x : Foo) : ... := by
  sorry  -- honest tracked debt
```

### Pattern 2: `_True : Prop := True`

Before:
```lean
structure Bar where
  prop_True : Prop := True
  prop_sorryProof : prop_True
```

After:
```lean
structure Bar where
  -- prop_True and prop_sorryProof removed

-- If the property holds:
theorem prop (x : Bar) : ... := by
  -- real proof

-- If not:
-- theorem prop (x : Bar) : ... := by
--   sorry
```

### Pattern 3: `_sorryProof` fields

Before:
```lean
structure Baz where
  result_sorryProof : resultType
```

After:
```lean
-- result_sorryProof removed from structure

-- If provable:
theorem result (x : Baz) : resultType := by
  -- real proof using existing fields

-- If not:
-- theorem result (x : Baz) : resultType := by
--   sorry
```

## Verification

After the change:
1. The file must still compile with `lake build`
2. No `_True : Prop := by` fields remain
3. No `_sorryProof` fields remain
4. Every property is a visible `theorem` or `def`, not a field of a structure
5. The owner file should pass the staged proof gate if the repository uses it

## Anti-patterns

### Critic Discoveries

- `_surety` — certificate/assurance synonym, detected by Vacuity Critic
- `_indemnity` — certificate/assurance synonym, detected by Vacuity Critic
- `_attestation` — certificate/assurance synonym, detected by Vacuity Critic
- `_covenant` — certificate/assurance synonym, detected by Vacuity Critic
- `_verity` — certificate/assurance synonym, detected by Vacuity Critic
- `_testimony` — certificate/assurance synonym, detected by Vacuity Critic
- `_accreditation` — certificate/assurance synonym, detected by Vacuity Critic
- `_bond` — certificate/assurance synonym, detected by Vacuity Critic
- `_seal` — certificate/assurance synonym, detected by Vacuity Critic
- `_voucher` — certificate/assurance synonym, detected by Vacuity Critic
- `_nexus` — certificate/assurance synonym, detected by Vacuity Critic
- `_guaranty` — certificate/assurance synonym, detected by Vacuity Critic

## Evolution Pipeline
This skill is dynamically integrated into the autonomous evolution pipeline. Proposers (GEPA/DSPy) mutate this skill to improve Pareto performance during real evaluation. For details on queue commands and worker operations, refer to [PRODUCTION_EVOLUTION_SYSTEM.md](file:///home/goutev/repos/info-geometry-lean/docs/PRODUCTION_EVOLUTION_SYSTEM.md).
