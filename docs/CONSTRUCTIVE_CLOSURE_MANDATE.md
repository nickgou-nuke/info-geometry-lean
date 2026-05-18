# Constructive Closure Mandate

> Status: `current policy`
> Effective: 2026-05-16
> Scope: all repo agents, skills, proof workflows, closure-debt audits, and promoted Lean surfaces.

## Utmost Mandate

Replacing witness-gated and external-certificate leftovers with native Lean 4
proofs is the top-priority mandate of this repository.

Witness packets, certificate field (Native Closure Mandated: Closure Debt)s, external certificates, assumption
interfaces, and literature-owner placeholders are allowed only as temporary
closure-debt temporary scaffolding (Native Closure Mandated: Closure Debt). They are not final mathematical closure and they are
not promotion authority.

Definitional formulas are not witness packets. If a quantity is a formula, it
must be exposed as a plain Lean `def` and used as a function immediately
downstream. Do not hide formulas behind prose labels, structure fields, or
alias-only theorem wrappers.

## Required Agent Behavior

Every agent working in this repository must:

1. Prefer native Lean proofs over witness/certificate temporary scaffolding (Native Closure Mandated: Closure Debt).
2. Search for existing mathlib and repo lemmas before introducing a new witness.
3. Replace any tractable witness, certificate, or hypothesis field with a
   kernel-checked Lean derivation.
4. Mark unimplemented mathematical content as explicit closure debt when it is
   not currently formalizable.
5. Never present a witness-gated theorem, external certificate, physics analogy,
   literature citation, Arango graph edge, or generated proof sketch as a closed
   Lean proof.

## Ownership Rule

Every witness/certificate surface must have exactly one owner class:

- `closed_by_kernel`
- `closed_by_mathlib`
- `closed_by_repo_owner`
- `literature_owned_unformalized`
- `open_problem_socket`
- `invalid_or_overclaimed_socket`

Anonymous witnesses are forbidden. If the owner is not a native Lean proof, the
surface remains closure debt.

## Promotion Rule

A theorem or interface may be promoted only when its mathematical payload is
discharged by native Lean derivation chains in this repository or by imported
mathlib theorems. Literature references may guide the port, but they do not
close the socket until formalized.

## Audit Rule

Closure audits must prioritize replacing easy witness/certificate leftovers
first. Do not start by claiming progress on RH-level, Hilbert-Polya-level,
Lee-Yang convergence, Jordan-normal-form growth, or operator trace identities
when nearby finite algebra, spectrum, matrix, order, topology, or continuity
lemmas remain packet-gated.

## Standing Goal Loop Rule

Long closure-debt runs should use the repo-local mission loop in
`tools/infra/goal_loop.py`; see `docs/MISSION_LOOP_SOP.md`.

The loop is operational support only. It may persist a goal, render continuation
prompts, track subgoals, parse strict judge JSON, fail open on transient judge
errors, and auto-pause on repeated bad judge output or budget exhaustion. It
must never mutate system prompts, swap toolsets, or count as mathematical
closure.

Lean proof authority remains exactly where this mandate places it: native
kernel-checked proofs and imported mathlib theorems.
