---
name: sympy-lean-handoff
description: Use when algebra, matrix, or group identities should be checked in SymPy first and then translated into Lean 4 in this repo. Use for exact symbolic verification, structure-constant tables, sign conventions, basis computations, and Lean-ready theorem statements.
---

# SymPy to Lean Handoff

Use this skill when the right workflow is:
1. verify the algebra in SymPy,
2. normalize the result into exact symbolic data,
3. translate the verified statement into Lean 4,
4. prove it against the repo's Lean owner surface.

## Core rule

SymPy is an algebra checker and statement shaper. Lean is the truth authority.
Do not treat a SymPy result as final until it is re-expressed as a Lean theorem
and kernel-checked.

## When to use

Use this skill for:
- finite group or Lie algebra tables
- matrix identities, commutators, determinants, traces, eigen-structure
- structure constants, basis expansions, parity/sign conventions
- exact symbolic reductions that should become Lean theorems

Do not use this skill for:
- numerical approximation work
- informal analogy without a concrete algebraic model
- proofs that are already best handled directly in Lean

## Workflow

### 1. Fix the symbolic model in SymPy

- choose the basis order and keep it explicit
- use exact constants only: `Rational`, radicals, symbolic parameters
- write the algebra table or matrix identities so every sign is explicit
- check the identities that matter: skew/symmetry, Jacobi, commutators,
  determinants, powers, and invariants

### 2. Extract Lean-shaped facts

Translate the SymPy output into:
- concrete Lean types
- explicit assumptions
- named lemmas and theorems
- the minimal owner file that should contain the statement

Prefer statements that mirror the SymPy algebra exactly. Do not strengthen the
claim during translation.

### 3. Translate conservatively into Lean 4

- use existing repo owners and mathlib structures
- preserve the exact basis, indexing, and sign conventions
- keep every assumption visible in the theorem statement
- if the SymPy model uses a convention choice, state it in the Lean docstring

LLMs are useful here as translators and normalizers. They are not reliable as
theorem inventors. Use them to turn verified symbolic work into Lean syntax, not
to guess the mathematics.

### 4. Verify in Lean

- search for existing lemmas before proving anything new
- compile the target file
- if the Lean proof needs a missing lemma, add the lemma, not a shortcut
- if the symbolic claim is unstable or convention-dependent, stop and tighten
  the statement before translating

## Failure rules

Stop and revise if:
- SymPy only proves the claim after floating-point or numeric substitution
- the Lean statement would need a hidden axiom or wrapper proof
- the translation changes the algebraic content
- the statement is not invariant under the chosen basis/sign conventions

## Good output shape

The best end state is:
- a SymPy verification artifact that records the exact algebra
- a Lean theorem with the same content
- a small helper lemma set if needed
- a compile-checked Lean file in the repo owner surface
