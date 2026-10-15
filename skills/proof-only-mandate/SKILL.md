<!-- repository-context-rule -->
## Repository context rule

For repository work, the current checked-out codebase is the context. Search
existing implementation and trace actual carriers, definitions, imports,
instances, theorem statements, and uses before claiming a structure is missing
or incorrect. A local absence is not a repository-wide absence. Names,
heuristics, summaries, and documentation guide discovery but do not override
source. Follow `docs/REPO_DEEP_SEARCH_PROTOCOL.md` before repo-wide gap claims.

# Proof-Only Mandate (Hard Policy Skill)

## Policy (non-optional)

1. No new `axiom` or `postulate` declarations.
2. No `sorry` or `admit` terms.
3. No witness-pack debt (`*_statement : Prop` + `*_witness`, or bare `*_witness : Prop`).
4. Every new theorem corridor must be closed with kernel-checked proofs.
5. Do not add wrapper structures/packets to bypass proof obligations.
6. Existing Prop-typed hypothesis/socket/certificate/witness fields must be
   replaced by explicit proved theorems (mathlib/repo-derived), not carried as
   declarative assumptions.
7. In touched modules, hypothesis debt replacement is mandatory before merge.
8. STALE DOC & DOCSTRING PROHIBITION: Never read, resurrect, or use stale documentation,
   historical transcript summaries, abandoned representation taxonomies, or dead markdown
   theories in program or proof design. Lean owner source files and kernel-checked proofs
   are the sole authority. Docstrings and comments must describe only live code verified
   by the current Lean compiler.
9. TRAP T16 PERMANENT PROHIBITION (Zero Scalar Toy Proxies): Non-commutative operator
   algebras ($\mathcal{M}$), infinite-dimensional spectral triples, and spacetime soldering
   forms must never be replaced by coordinate/scalar surrogates.
10. OPERATOR WAVEFRONT DUALITY (OpenGauss Protocol QMS-SOP-IAA-001): Retarded/Advanced
    waves are operator wavefront shells $\mathcal{O}_{\text{foc}}(\tau) = \sigma_{-\tau}(\mathcal{O}_0)$
    and $\mathcal{O}_{\text{defoc}}(\tau) = \sigma_{+\tau}(\mathcal{O}_0')$ in von Neumann
    algebras $\mathcal{M}$ intertwined by Tomita modular conjugation $J \mathcal{O}_{\text{foc}}(\tau) J = \mathcal{O}_{\text{defoc}}(-\tau)$,
    Klein bottle glide reflection $\mathcal{G}_{\text{Klein}}(\mathcal{O}_{\text{foc}}(\tau)) = \mathcal{O}_{\text{defoc}}(-\tau)$,
    KMS thermal boundary periodicity $\tau \to \tau + i\beta$, and chiral ideal splits $P_L \leftrightarrow P_R$.

## Required gate before merge

Run:

```bash
python3 tools/quality/proof_only_mandate_gate.py
```

This gate fails if any forbidden declaration/token is present in
`lean/InfoGeometry`, if witness-pack patterns are found, or if Prop-typed
hypothesis/socket/certificate/witness fields remain.

## Operational workflow

1. Select one owner file.
2. Replace one debt surface with a concrete lemma/proof.
3. Build that file (`lake build <module>`).
4. Run `proof_only_mandate_gate.py`.
5. Repeat.

## Violation handling

- Any violation is blocking.
- Do not claim closure until gate passes.
- Do not bypass this mandate with wrappers, sockets, or theorem-free packets.
