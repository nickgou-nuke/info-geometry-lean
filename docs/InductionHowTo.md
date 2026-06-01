# Induction How-To

> Status: maintained local guide
> Audited: 2026-05-30
> See: [InductionSystematics.md](InductionSystematics.md), [README.md](../README.md), [../skills/induction-systematics/SKILL.md](../skills/induction-systematics/SKILL.md)

This is the practical companion to `InductionSystematics.md`.

## Quick recipe

When a theorem looks inductive, do this:

1. Identify the carrier: `Nat`, a recursive datatype, a stage tower, or a
   direct-limit diagram.
2. Prove the base case.
3. Prove the one-step preservation lemma.
4. Package the finite iteration with `induction`.
5. If the object is staged, transport the result through the stage maps.
6. If the result is supposed to live in a limit, use `DirectLimit` and a
   compatible cone.
7. Validate the file with `lake env lean` before broadening scope.

## Pattern chooser

### A. Plain `Nat` induction

Use this when the statement is just about `n : ℕ`.

```lean
intro n
induction n with
| zero =>
    -- base case
    ...
| succ n ih =>
    -- use `ih`
    ...
```

Typical use: finite-stage closure, monotonicity, invariant transport.

### B. Generalized induction

Use this when the induction hypothesis needs extra parameters.

```lean
induction n generalizing m k with
| zero => ...
| succ n ih => ...
```

Typical use: associativity-style or permutation-style proofs.

### C. Strong induction

Use this when each case may depend on all smaller cases.

```lean
refine Nat.strong_induction_on n ?_
```

Typical use: well-founded recursion, minimal-counterexample arguments.

### D. Structural induction

Use this for lists, trees, and other inductive datatypes.

```lean
induction xs with
| nil => ...
| cons x xs ih => ...
```

Typical use: recursive syntax, combinatorial carriers, canonical forms.

### E. Recursive trajectories

Use this when the object is defined by seed + step.

- `recursiveTrajectory` in `EssenceOfInductiveProof.lean`
- `coneTrajectory` / `stageTrajectory` in `InductionHandbook.lean`

The proof usually says: the trajectory satisfies the same seed/step equations,
so the invariant follows by ordinary induction.

### F. Finite-stage algebraic transport

Use this when each stage maps to the next by a homomorphism.

Target pattern:

- prove a one-step lemma like `superClosure_step`;
- use `induction n` to get `superClosure_all`;
- transport the result with `map_anticommutator`, `map_mul`, or the relevant
  homomorphism lemma.

Owner files:

- `lean/InfoGeometry/Algebra/InductiveSuperClosureLemmas.lean`
- `lean/InfoGeometry/Algebra/FiniteInductiveSUSY.lean`

### G. Image-local infinite transport

Use this when the theorem lives in an explicit target algebra, not in a limit.

Pattern:

- stagewise theorem first;
- then `toLimit n` transports it into `Limit`;
- if a compatibility law exists, derive stage-independence.

Owner files:

- `lean/InfoGeometry/Algebra/InfiniteSuperClosureLemmas.lean`
- `lean/InfoGeometry/Meta/FiniteToInfiniteTransitionSOP.lean`

### H. Algebraic direct limit

Use this when the object is a genuine tower and you need the colimit.

Pattern:

- define `bondMap`;
- prove `DirectedSystem` laws;
- define `directLimitOf`;
- prove `directLimitOf_bondMap`;
- use `directLimitLift` for the universal property.

Owner file:

- `lean/InfoGeometry/Algebra/DirectLimitSuperClosureLemmas.lean`

### I. Tensor algebra induction

Use this when a chain of linear maps induces a chain of tensor-algebra maps.

Owner file:

- `lean/InfoGeometry/Algebra/TensorAlgebraInduction.lean`

This is the preferred route for tensor towers, because it reuses the existing
`TensorAlgebra` universal property rather than inventing a new completion.

### J. Formal PowerSeries lanes

Use this when exp/log/geometric objects are defined as formal power series.

Owner file:

- `lean/InfoGeometry/Algebra/FormalSeriesCalculus.lean`

Rule:

- coefficient identities are proved algebraically, coefficientwise;
- `PowerSeries.map` lemmas are naturality theorems;
- no analytic convergence or completion is claimed unless a separate theorem
  proves it;
- historically, the underlying exp/log laws can be handled by iteration and
  inversion without appealing to Taylor-series as the defining presentation.

## Category-language translation

A staged induction proof can be read as a diagram in the thin category of
natural-number stages:

- objects are stages `Stage n`;
- arrows are bonding maps `bond n`;
- commutativity is the compatibility equation;
- the colimit is `DirectLimit`;
- the cone is a family of maps into a target;
- the universal map is `directLimitLift`.

If you cannot build the cone, do not claim the limit theorem.

## Lean code habits

- Keep the theorem statement minimal and explicit.
- Prove the one-step lemma before the `∀ n` theorem.
- Use `rw` / `simp` to expose the recursive equation before induction.
- Use `generalizing` when the induction hypothesis is too weak.
- Prefer `rfl` only when the object is definitional.
- Avoid storing proof content in fields or witnesses.

## Validation checklist

After writing the theorem, run:

```bash
lake env lean <file.lean>
lake build <Module.Name>
python3 tools/quality/proof_only_mandate_gate.py
python3 tools/lean4-skills/sorry_analyzer.py lean --format=summary
```

For a new finite-to-infinite bridge, also check the relevant SOP:

- `docs/VIRASORO_FINITE_TO_INFINITE_SOP.md`
- `.agents/workflows/virasoro_finite_to_infinite_sop.md`

## Fast decision rule

If the statement is:

- a property of `n` only → ordinary induction;
- a property of a recursive datatype → structural induction;
- a property of all smaller cases → strong induction;
- a property along a homomorphic chain → finite-stage transport;
- a property in a target algebra → image-local theorem;
- a property of a genuine tower → `DirectLimit`;
- a property of tensor powers → tensor-algebra transport.

If none of these fit, stop and classify the theorem before coding.
