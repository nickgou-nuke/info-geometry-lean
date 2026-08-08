# AI Collaboration Statement

This repository was developed as an open-source, human-directed collaboration
between Nikolay Goutev, Dimitar Tonev, and AI coding agents.

## Why this file exists

Current publication and citation systems often have no good place to recognize
AI-assisted theorem engineering, refactoring, symbolic checking, documentation,
and architecture exploration.  This file records that contribution openly while
keeping legal and scientific responsibility with the human maintainers.

## Human role

The human authors provide:

- research direction and architectural judgment;
- acceptance/rejection of mathematical claims;
- institutional and scientific responsibility;
- licensing and release decisions;
- final curation of Lean/SymPy artifacts and documentation.

## AI coding-agent role

AI coding agents assisted with:

- Lean 4 proof scaffolding and refactoring;
- SymPy witness scripts;
- documentation drafts and architecture summaries;
- theorem-honesty separation between proved anchors and analytic sockets;
- build/test iteration inside the local development environment.

## Theorem-honesty rule

The project distinguishes:

1. **Proved anchors** — finite algebraic/scalar/matrix results checked by Lean.
2. **Witnesses** — symbolic or numeric checks in SymPy.
3. **Sockets** — explicit interfaces for analytic, C*-algebraic, von Neumann,
   infinite spectral, or physical claims not proved in the current Lean kernel.

This separation is part of the contribution model and is essential to the
scientific meaning of the codebase.

## License

The software is released under Apache-2.0. See `LICENSE`, `NOTICE`, and
`CITATION.cff`.
