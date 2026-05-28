# Finite-to-Infinite Algebraic Transition Skill

Use this skill when formalizing or reviewing Lean code that claims to pass from
finite/local algebraic data to an infinite-indexed, infinite-dimensional,
local-to-global, or finite-stage-to-global theorem.

Typical triggers:

- Virasoro/Witt/Heisenberg/affine Kac--Moody/Sugawara mode algebras;
- N=2 supercharge or central-charge closure over infinite mode families;
- finite-support direct sums, central extensions, cocycles, anomalies;
- locally finite operator sums;
- claimed analytic limits, colimits, or completions.

## Required SOP

Read and follow:

- `.agents/workflows/virasoro_finite_to_infinite_sop.md`
- `.agents/workflows/proof_only_sop.md`
- `.agents/workflows/honest_proof_policy.md`
- `skills/proof-only-mandate/SKILL.md`

## Exemplar references

The external Virasoro package is the model for the algebraic cases:

- `lean/InfoGeometry/External/Virasoro/WittAlgebra.lean`
- `lean/InfoGeometry/External/Virasoro/VirasoroCocycle.lean`
- `lean/InfoGeometry/External/Virasoro/VirasoroAlgebra.lean`
- `lean/InfoGeometry/External/Virasoro/HeisenbergAlgebra.lean`
- `lean/InfoGeometry/External/Virasoro/AffineKacMoody.lean`
- `lean/InfoGeometry/External/Virasoro/Sugawara.lean`
- `lean/InfoGeometry/External/Virasoro/CentralExtension.lean`

## Core policy

Never close an infinite theorem by hiding the missing proof in a law,
certificate, witness, guard, readback, or structure field.

A valid finite-to-infinite theorem must use one of these mechanisms:

1. algebraic direct sum / finite support, preferably `ι →₀ A`;
2. mode families with proved finite-support preservation;
3. explicit central extension by a cocycle;
4. locally finite/truncated sums with support proof before summing;
5. genuine analytic completion with topology, convergence, and continuity
   formalized.

If none is available, leave an honest `sorry` or keep the artifact data-only.

## Preferred theorem shape

For direct-sum carriers, prefer object equality in the carrier:

```lean
operationMode X Y = structuralMode + centralMode
```

over pointwise-only closure:

```lean
∀ i, operation (X i) (Y i) = structural i + central i
```

Pointwise closure is useful as a lemma, but direct-sum equality is the stronger
Virasoro-style endpoint when feasible.

## Implementation procedure

1. Classify the carrier:
   - `Finsupp`/direct sum;
   - flexible mode family plus finite-support theorem;
   - central extension;
   - local finite sum;
   - analytic completion.
2. Write the carrier choice in the module docstring.
3. Prove generator/local laws first.
4. Define cocycles/central obstructions explicitly.
5. For direct sums, define operations as `Finsupp` objects and prove support
   control.
6. For sums, prove local truncation/finite support before using the sum.
7. For finite iterates, do not call the result an infinite limit unless a real
   colimit/completion is built.
8. Reject any `*_law`, `*_certificate`, `*_witness`, `*_guard`, or pure reexport
   theorem that carries the missing proof.

## Allowed examples

```lean
-- finitely supported infinite mode algebra
def WittAlgebra := ℤ →₀ 𝕜
abbrev ModeFamily (ι A : Type*) [Zero A] := ι →₀ A

-- object equality in the direct-sum carrier
anticommutatorMode Q R = H + Z

-- explicit cocycle support
γ (basis m) (basis n) = if m + n = 0 then ... else 0

-- Sugawara/local operator sums require truncation
heiTrunc : ∀ v, atTop.Eventually (fun l => heiOper l v = 0)
```

## Forbidden examples

```lean
finite_to_infinite_limit_law : Prop
finite_to_infinite_limit_certificate : finite_to_infinite_limit_law

sugawara_closure_law : Prop
sugawara_closure_witness : sugawara_closure_law

centrality_guard : Type
convergence_certificate : claimed_convergence
```

Also forbidden: a theorem whose proof is only `P.some_law`,
`P.some_certificate`, or equivalent readback.

## Validation commands

Run after each edit:

```bash
lake env lean <file>
ulam checkpoint <file> --lean-project . --strict --no-allow-axioms
python3 tools/lean4-skills/sorry_analyzer.py lean --format=summary
```

For Canonical/vacuity cleanup also run:

```bash
python3 tools/quality/proof_heartbeat.py lean/InfoGeometry/Canonical --top 30
```

Do not commit generated UlamAI reports unless explicitly requested.

## Acceptance criteria

A finite-to-infinite bridge is acceptable only if one of these is true:

- it is a kernel-checked theorem derived from direct sums, finite support,
  local truncation, explicit cocycles, or proved convergence;
- it is data-only and makes no theorem claim;
- the missing theorem is marked by an honest visible `sorry`.
