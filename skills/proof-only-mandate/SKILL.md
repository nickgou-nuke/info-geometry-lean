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
