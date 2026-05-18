# Formula and Function Policy

> Status: `current policy`
> Effective: 2026-05-18
> Scope: repo docs, Lean sources, skills, and generated guidance that names formulas or functions.

## Policy

Formulas are Lean definitions. Functions are functions. Natural-language labels are not authority.

If a quantity is used in derivations, it must be available as a plain `def` with explicit arguments and direct downstream use.

Do not encode a definitional formula as:
- a structure field when a direct `def` is the real owner surface
- a renamed theorem whose only job is to restate the same expression
- a prose label that is later interpreted as code

## Required Shape

- Raw inputs may live in structures.
- Derived formulas must live in `def`s.
- Non-definitional facts must live in theorems.
- If a formula is needed immediately, define it immediately.
- If the formula is used by later code, the later code must call the function directly.

## Naming Rule

Prefer the semantic name of the actual quantity:
- `massieu`
- `force`
- `entropy`
- `energy`
- `partition`

Do not hide a formula behind a `Formula` suffix if the quantity is itself the function being used.

## Prohibited Pattern

This is not acceptable:

```lean
structure S where
  massieu : ℂ → ℂ
```

when `massieu` is a definitional formula rather than stored data.

This is acceptable:

```lean
def massieu (zetaPartition : ℂ → ℂ) : ℂ → ℂ := ...
```

with raw inputs kept separate.

## Enforcement

1. Read the formula as a function, not as prose.
2. Put the formula in a `def`.
3. Use that `def` directly in downstream derivations.
4. Keep socket fields for raw data and proof obligations only.
5. Remove alias-only theorem wrappers unless they discharge a real mathematical burden.

