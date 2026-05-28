# SOP: External Virasoro Finite-to-Infinite Transition Pattern

## Purpose

Use the external Virasoro library as the canonical model for converting finite/local algebraic closure laws into honest infinite-mode Lean formalizations without analytic hand-waving or proof proxies.

This SOP applies when formalizing bridges from finite current/supercharge/Kac--Moody data to infinite indexed Virasoro, Witt, Heisenberg, affine Kac--Moody, or Sugawara-style structures.

## Core rule

Do **not** encode an infinite-dimensional theorem as a finite theorem plus an assumed limit/certificate.  The external Virasoro library uses one of two honest mechanisms:

1. **Algebraic direct sum over infinitely many modes** via finitely supported functions, e.g. `ℤ →₀ 𝕜`.
2. **Locally finite/truncated infinite sums** where every vector sees only finitely many nonzero summands.

If neither finite support nor local truncation is proved, the theorem must remain visible debt (`sorry`) or be refactored into data-only definitions.

## Reference files

Inspect these files before implementing a finite-to-infinite bridge:

- `lean/InfoGeometry/External/Virasoro/WittAlgebra.lean`
- `lean/InfoGeometry/External/Virasoro/VirasoroCocycle.lean`
- `lean/InfoGeometry/External/Virasoro/VirasoroAlgebra.lean`
- `lean/InfoGeometry/External/Virasoro/HeisenbergAlgebra.lean`
- `lean/InfoGeometry/External/Virasoro/AffineKacMoody.lean`
- `lean/InfoGeometry/External/Virasoro/Sugawara.lean`
- `lean/InfoGeometry/External/Virasoro/CentralExtension.lean`
- `lean/InfoGeometry/External/Virasoro/BosonizationConstructiveCurrent.lean`

## Standard transition pattern

The implemented pattern is:

```text
finite/local generator law
→ infinitely indexed basis with finite support
→ bracket/cocycle defined on basis modes
→ bilinear extension
→ central extension
→ mode-generator bracket theorem
→ locally finite Sugawara/representation construction, if needed
```

The shared invariant shape is:

```text
bracket/current closure = shifted structural mode + central cocycle
```

Examples:

- Witt:
  ```text
  [ℓ_n, ℓ_m] = (n - m) • ℓ_{n+m}
  ```
- Virasoro:
  ```text
  [L_n, L_m] = (n - m) • L_{n+m} + cocycle(n,m) • c
  ```
- Heisenberg:
  ```text
  [J_k, J_l] = if k + l = 0 then k • central else 0
  ```
- Affine Kac--Moody:
  ```text
  [J_m^x, J_n^y] = J_{m+n}^{[x,y]} + residue cocycle
  ```
- Sugawara:
  ```text
  Heisenberg commutator + local truncation
  → normal-ordered quadratic modes L_n
  → Virasoro commutator
  ```

## Implementation checklist

### 1. Classify the intended infinite object

Before writing Lean code, decide which construction is actually justified:

- **Finitely supported mode algebra**: use a direct-sum/finsupp representation such as `ℤ →₀ 𝕜`.
- **Central extension**: define an explicit Lie 2-cocycle on basis modes and extend it bilinearly.
- **Sugawara/normal-ordered sum**: prove local truncation/finite support before defining any mode sum.
- **Analytic Hilbert-space limit**: do not assert unless a real analytic convergence theorem is available.

### 2. Encode basis-mode laws first

Prove generator-level laws before proving arbitrary-element laws:

```lean
-- mode theorem first
[J m, J n] = structuralTerm (m+n) + centralTerm m n
```

Then extend by linearity/finsupp induction if needed.

### 3. Make the central obstruction explicit

Central charges must be cocycles or central-extension coordinates, not hidden fields.

Allowed:

```lean
γ basis_m basis_n = if m + n = 0 then ... else 0
CentralExtension γ
```

Disallowed:

```lean
central_law : Prop
central_certificate : central_law
```

### 4. For Sugawara, prove local finiteness before summing

A formal sum such as

```text
L_n v = 1/2 • ∑ᶠ k, :J_{n-k} J_k: v
```

is only acceptable after proving the summand is finitely supported for each `v`, typically from a truncation hypothesis like:

```lean
∀ v, atTop.Eventually (fun l => J l v = 0)
```

Do not replace this with a convergence assumption/certificate.

### 5. Map finite induction to infinite modes carefully

Finite supercharge or central-charge induction lemmas correspond only to the algebraic skeleton:

```text
anticommutator/bracket closure = structural term + central cocycle
```

To upgrade to Virasoro-style infinite modes, add:

- an integer mode index;
- finite support or local truncation;
- explicit shifted mode arithmetic (`m+n`, `n-k`);
- explicit cocycle support (`m+n=0`).

### 6. Validation gates

For each touched file run:

```bash
lake env lean <file>
ulam checkpoint <file> --lean-project . --strict --no-allow-axioms
python3 tools/quality/proof_heartbeat.py lean/InfoGeometry/Canonical --top 30
python3 tools/lean4-skills/sorry_analyzer.py lean --format=summary
```

Do not stage generated UlamAI JSON unless explicitly requested.

## Anti-patterns

Reject these patterns during review:

- `finite_to_infinite_limit_law : Prop` plus certificate field.
- `centrality_witness`, `closure_law`, `sugawara_certificate`, or similar proof-payload fields.
- Theorems that merely re-export a structure field.
- Infinite sums without a finite-support/local-truncation proof.
- Analytic convergence claimed by a datum field.
- A finite theorem renamed as an infinite theorem without mode-indexed construction.

## Review questions

Ask before accepting a finite-to-infinite theorem:

1. What is the infinite carrier? Is it finitely supported?
2. Where is the basis-mode bracket proved?
3. Where is the central cocycle defined?
4. Is the cocycle support explicit (`m+n=0`, residue, etc.)?
5. If a sum over modes appears, where is local truncation proved?
6. Does the theorem prove closure from definitions, or re-export a stored law?
7. Would UlamAI report placeholders or axioms?
8. Does the heartbeat count decrease without introducing new proxy fields?

## Output standard

A compliant bridge should leave one of these outcomes:

- a kernel-checked theorem built from finite support/local truncation and explicit cocycles;
- a data-only structure with no theorem claims; or
- an honest visible `sorry` at the exact missing analytic theorem.
