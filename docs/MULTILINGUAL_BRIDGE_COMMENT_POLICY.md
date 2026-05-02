# Multilingual Bridge Comment Policy

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This repository formalizes the physics of information in Lean 4. Its language
intentionally borrows terms from information geometry, statistical mechanics,
operator algebra, quantum mechanics, and thermodynamics: curved spaces, flows,
free energy, Boltzmann entropy, modular Hamiltonians, and related structures.

That language is not decorative by default. Introducing a completely new
vocabulary would make the formalization less intelligible, not more rigorous.
The audit standard is therefore semantic fidelity, not prose minimization.

## Comments Are Transport Substrate

Comments and docstrings may carry the mapping between:

- Lean 4 declarations and proofs
- SymPy or Python prototypes
- LaTeX notation
- natural-language mathematical intent
- physics and information-geometry terminology

When a comment performs that mapping, it is part of the representation layer.
It should be preserved or expanded for accuracy, not shortened by default.

## Forbidden Heuristics

Agents must not judge value by crude structural measures such as:

- comment-to-code ratio
- prose length alone
- presence of physically loaded words alone
- script-level density metrics detached from theorem role

These heuristics confuse explanatory transport with symbolic inflation.

## Correct Audit Standard

Assess comments and docstrings by asking:

- Does the prose faithfully identify the Lean object it describes?
- Does it explain a real bridge between representations?
- Does it distinguish analogy, interpretation, definition, and theorem?
- Does it point toward a load-bearing declaration, proof, or dependency path?
- Does it avoid claiming physical closure before the Lean theorem exists?

Rich prose is acceptable when it clarifies a real transport map. It becomes a
problem only when it asserts more than the formal object proves.

## Edit Policy

When editing explanatory text:

- preserve bridge-bearing comments
- expand comments when needed to remove ambiguity
- correct terminology that misstates the formal object
- mark unproved interpretation as conjectural or motivational
- do not compress comments merely to make files look more code-dense

Deletion is appropriate only for stale, false, duplicative, or non-bridge prose.

## Relation To Pauli Audit

The Pauli Mandate still rejects Total Symbolic Inflation. The distinction is:

- valid bridge prose explains a formal transport already present or being built
- symbolic inflation uses impressive language to mask missing derivation

The auditor must separate those cases semantically. The Lean kernel decides
truth; comments carry the map by which humans and agents find the truth.
