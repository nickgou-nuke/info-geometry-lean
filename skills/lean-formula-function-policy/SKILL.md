---
name: lean-formula-function-policy
description: Use when editing Lean code or repo policy so definitional formulas are plain defs/functions, not prose labels, structure fields, or alias-only theorem wrappers.
---

# Lean Formula and Function Policy

Use this skill when a Lean declaration is really a formula, and the job is to
make it behave like one in the repository.

## Core rule

Formulas are definitions. Functions are functions. Natural-language labels are
not authority.

If a quantity is used in derivations, expose it as a plain Lean `def` with
explicit arguments and use that `def` directly downstream.

## Required shape

- Raw inputs may live in structures.
- Derived formulas must live in `def`s.
- Non-definitional facts belong in theorems.
- If the formula is needed immediately, define it immediately.
- Downstream code must call the function directly.

## Do not do this

- store a definitional formula as a structure field
- rename the same formula into `massieuFormula`, `forceFormula`, or similar
- keep a prose label and call it authority
- expose an alias-only theorem whose proof is just `rfl` or unfold-and-rename

## Do this

- define the formula as `massieu`, `force`, `partition`, `energy`, or the
  actual semantic name of the quantity
- keep structures for raw analytic or thermodynamic inputs
- let theorem wrappers state the real non-definitional consequence, not the
  same formula with a new name

## Repo policy alignment

Follow:
- `docs/CONSTRUCTIVE_CLOSURE_MANDATE.md`
- `docs/FORMULA_FUNCTION_POLICY.md`

If a formula still appears as a field label, move it to a `def` and use that
function directly in the derivation chain.
