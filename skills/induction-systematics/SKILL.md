---
name: induction-systematics
description: Use when formalizing, reviewing, or debugging induction-heavy Lean 4 proofs in InfoGeometry: Nat induction, generalizing/strong induction, recursive trajectories, finite-stage transport, tensor-algebra induction, or algebraic direct limits.
---

## Constructive Closure Mandate

Replacing witness-gated and external-certificate leftovers with native Lean 4
proofs is the highest mandate. Treat witness packets, certificate fields,
external certificates, assumption interfaces, and proof-carrying wrappers as
closure debt until discharged by kernel-checked Lean or imported mathlib
theorems.

# Induction Systematics Skill

Use this skill when the proof shape is induction, recursion, or staged
transport in the InfoGeometry codebase.

## Read first

1. `README.md`
2. `docs/README.md`
3. `docs/InductionSystematics.md`
4. `docs/InductionHowTo.md`
5. `lean/InfoGeometry/Meta/EssenceOfInductiveProof.lean`
6. `lean/InfoGeometry/Meta/InductionHandbook.lean`
7. `lean/InfoGeometry/Meta/FiniteToInfiniteTransitionSOP.lean`
8. `lean/InfoGeometry/Algebra/InductiveSuperClosureLemmas.lean`
9. `lean/InfoGeometry/Algebra/InfiniteSuperClosureLemmas.lean`
10. `lean/InfoGeometry/Algebra/DirectLimitSuperClosureLemmas.lean`
11. `lean/InfoGeometry/Algebra/TensorAlgebraInduction.lean`
12. `lean/InfoGeometry/Algebra/TensorAlgebraCanonical.lean`
13. `lean/InfoGeometry/Algebra/IterativeExponentiation.lean`
14. `lean/InfoGeometry/Algebra/NilpotentFiniteProductLimit.lean`
15. `lean/InfoGeometry/Clifford/SplitQuaternionNilpotentFlow.lean`
16. `lean/InfoGeometry/Clifford/SplitQuaternionFlowCoordinates.lean`
17. `lean/InfoGeometry/Algebra/FormalSeriesCalculus.lean`
18. `lean/InfoGeometry/Clifford/Cl11TensorTowerIteration.lean`

## What this skill covers

- ordinary `Nat` induction;
- generalized induction with extra parameters;
- strong induction;
- structural induction on lists, trees, and custom datatypes;
- recursive trajectories and seed/step proofs;
- finite-stage algebraic transport;
- image-local infinite target theorems;
- algebraic direct limits and compatible cones;
- tensor-algebra induction via universal properties;
- primitive-recursive finite powers, finite products, and finite orbits;
- nilpotent finite-product induction and eventually-constant `Tendsto` limits;
- formal `PowerSeries` exp/log only when the theorem is genuinely coefficientwise/formal.

## Core workflow

1. Classify the theorem.
   - `P n` only → ordinary induction.
   - recursive datatype → structural induction.
   - all smaller cases → strong induction.
   - bonding maps / stage tower → finite-stage transport or direct limit.
   - tensor powers / tensor algebras → tensor-algebra induction.
   - finite powers/products/orbits → primitive recursion, not Taylor series.
   - formal `exp`/`log` symbols → `PowerSeries` only for formal/coefficientwise algebra.

2. Prove the one-step lemma first.
   - For a tower, isolate the successor preservation statement.
   - For a recursive object, isolate the defining equation.
   - For a direct limit, prove stage compatibility.

3. Package the finite iteration.
   - `induction n with`
   - `induction n generalizing ... with`
   - `Nat.strong_induction_on`
   - `Nat.rec` / `List.rec` / custom recursors

4. If the target is infinite, decide which honest mechanism applies.
   - `Stage n →ₐ` or `→+*` into a target: image-local theorem.
   - `DirectLimit`: actual algebraic colimit.
   - `Finsupp`: finite-support infinite-mode algebra.
   - formal exp/log/geometric series: algebraic `PowerSeries` coefficientwise lane, not analytic completion.
   - topology/continuity/convergence: separate owner file.

5. Distinguish the four lanes explicitly before writing the theorem statement.
   - finite-stage inductive transport: base case + step case + theorem for each finite `n`.
   - primitive-recursive exponentiation/iteration: `x^0 = 1`, `x^(n+1) = x^n * x`; finite `k`-fold products/orbits/stage advances, not Taylor series.
   - nilpotent normalized product limit: prove finite product collapse first, then `Tendsto` only when the sequence is eventually constant or convergence is otherwise formalized; for split quaternions use explicit coordinatewise convergence (`sq_tendsto`) until a topological Clifford algebra owner exists, and keep norm-one coordinate-curve examples separate from subgroup-classification claims.
   - formal-series lane: definitional/algebraic identity in `PowerSeries`; coefficientwise theorems are finite at each degree and do not imply evaluation or convergence.
   - analytic lane: only claim completion, continuity, functional equality, or operator convergence when those hypotheses are formalized in the owner file.
   - Never let Taylor-style rhetoric smuggle an analytic conclusion into a theorem whose proof is only recursive, coefficientwise, or stagewise.

6. Validate immediately.
   - `lake env lean <file.lean>`
   - `lake build <Module.Name>`
   - run the proof-only gate.

## Lean proof patterns

### Ordinary finite induction

```lean
intro n
induction n with
| zero =>
    exact h0
| succ n ih =>
    exact hstep n ih
```

### Strengthened induction

```lean
induction n generalizing m k with
| zero =>
    ...
| succ n ih =>
    ...
```

### Strong induction

```lean
refine Nat.strong_induction_on n ?_
intro n ih
...
```

### Recursive trajectory

```lean
induction n with
| zero => simpa using h0
| succ n ih => simpa using hstep n ih
```

### Stage-to-stage transport

```lean
rw [hstep n]
exact map_anticommutator (φ n) _ _
```

### Direct limit

Use `bondMap`, `directLimitOf`, `CompatibleCone`, and `directLimitLift`.

### Primitive-recursive exponentiation / iteration

Use `inductivePower`, `iterativeProduct`, and `iterativeOrbit` for finite
recursive processes.  In a staged algebra tower, use the owned finite iterate
(e.g. `iteratedStageEmbed`) rather than introducing a Taylor/power-series
encoding.

```lean
induction n with
| zero => simp [inductivePower]
| succ n ih => simp [inductivePower, ih]
```

### Formal series

Use `PowerSeries` only for formal/coefficientwise statements.  Prove identities
by coefficient extensionality; do not infer evaluation or convergence.

```lean
ext n
simp [formalExp, formalLogOnePlus]
```

## Category-language translation

Read a tower proof as a diagram:

- `Stage : ℕ → Type*` = objects of a thin `ℕ`-indexed diagram;
- `bond n` = the transition arrow;
- `DirectedSystem` = functorial coherence;
- `DirectLimit` = colimit;
- `CompatibleCone` = cone into a target;
- `directLimitLift` = universal arrow out of the colimit.

This is the repository’s category-language formalization of induction over
finite stages.

## Anti-patterns

- Do not claim an infinite result from finite-stage induction alone.
- Do not hide the missing step in a witness, certificate, or wrapper field.
- Do not use `rfl` unless the theorem is definitional.
- Do not convert a direct-limit theorem into a prose note.
- Do not treat `Finsupp` as a completion.
- Do not confuse finite recursive exponentiation with Taylor/power series.
- Do not use `PowerSeries` when the intended construction is finite iteration by recursion.
- Do not evaluate a formal series at a non-formal element without explicit substitution/evaluation hypotheses.

## Acceptance criteria

A theorem is handled correctly when:

- the base case is explicit;
- the step case is explicit;
- the induction hypothesis is used honestly;
- the result matches the carrier that the mathematics really requires;
- the file builds with no new proof debt.
