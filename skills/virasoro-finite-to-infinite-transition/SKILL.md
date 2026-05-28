# Virasoro Finite-to-Infinite Transition Skill

Use this skill when formalizing or reviewing any Lean code that claims to pass from finite/local current, supercharge, Kac--Moody, Heisenberg, Witt, Virasoro, or Sugawara data to an infinite-mode theorem.

## Required SOP

Read and follow:

- `.agents/workflows/virasoro_finite_to_infinite_sop.md`
- `.agents/workflows/proof_only_sop.md`
- `.agents/workflows/honest_proof_policy.md`
- `skills/proof-only-mandate/SKILL.md`

## External Virasoro reference files

Before implementing or refactoring, inspect the relevant external modules:

- `lean/InfoGeometry/External/Virasoro/WittAlgebra.lean`
- `lean/InfoGeometry/External/Virasoro/VirasoroCocycle.lean`
- `lean/InfoGeometry/External/Virasoro/VirasoroAlgebra.lean`
- `lean/InfoGeometry/External/Virasoro/HeisenbergAlgebra.lean`
- `lean/InfoGeometry/External/Virasoro/AffineKacMoody.lean`
- `lean/InfoGeometry/External/Virasoro/Sugawara.lean`
- `lean/InfoGeometry/External/Virasoro/CentralExtension.lean`

## Core pattern

The external Virasoro library does **not** prove infinite-dimensional claims by hiding an analytic limit in a field.  It uses:

1. finitely supported mode algebras, such as `ℤ →₀ 𝕜`;
2. explicit basis-mode brackets;
3. explicit Lie 2-cocycles;
4. central extensions;
5. local truncation before any Sugawara-style infinite-index sum.

The invariant theorem shape is:

```text
bracket/current closure = shifted structural mode + central cocycle
```

## Implementation procedure

1. Identify the carrier:
   - finitely supported modes/direct sum;
   - central extension;
   - locally finite operator sum;
   - or genuine analytic limit.
2. If the carrier is infinite, prove finite support or local truncation before summing.
3. Define the bracket/cocycle on basis generators first.
4. Extend by linearity/finsupp induction only after the generator theorem is closed.
5. State central terms as cocycles or central-extension coordinates.
6. Reject any `*_law`, `*_certificate`, `*_witness`, `*_guard`, or reexport theorem that carries the missing proof.
7. If the needed analytic convergence/local truncation theorem is unavailable, leave a visible `sorry` or remove the theorem surface.

## Allowed examples

```lean
-- finitely supported infinite mode algebra
def WittAlgebra := ℤ →₀ 𝕜

-- explicit cocycle support
γ (lgen n) (lgen m) = if n + m = 0 then ... else 0

-- Sugawara requires local truncation
heiTrunc : ∀ v, atTop.Eventually (fun l => heiOper l v = 0)
```

## Forbidden examples

```lean
finite_to_infinite_limit_law : Prop
finite_to_infinite_limit_certificate : finite_to_infinite_limit_law

sugawara_closure_law : Prop
sugawara_closure_witness : sugawara_closure_law

centrality_guard : Type
```

Also forbidden: a theorem whose proof is only `P.some_law` or `P.some_certificate`.

## Validation commands

Run after each edit:

```bash
lake env lean <file>
ulam checkpoint <file> --lean-project . --strict --no-allow-axioms
python3 tools/quality/proof_heartbeat.py lean/InfoGeometry/Canonical --top 30
python3 tools/lean4-skills/sorry_analyzer.py lean --format=summary
```

Do not commit generated UlamAI reports unless explicitly requested.

## Acceptance criteria

A finite-to-infinite bridge is acceptable only if one of these is true:

- it is a kernel-checked theorem derived from explicit mode algebra, cocycle, finite support, or local truncation;
- it is data-only and makes no theorem claim;
- the missing theorem is marked by an honest visible `sorry`.
