# Pauli Pass Prompt
## Exclusion / Admission Pass (Virgo)

Use this prompt immediately after `jungian_pass.md`.
Goal: preserve generative gains while enforcing admissibility.
This is `closure_gate` adjudication per
`tools/prompts/SOCRATIC_CLOSURE_PROTOCOL.md`.

## Mandatory Pauli Seal (Agents + Coding Agents)

The following directives are mandatory and machine-gated:

1. `I.no_mask_mandate`
   - physically-loaded canonical names must be grounded by real Thermo/Geometry structure use.
2. `II.functorial_connectivity`
   - no floating import-only canonical modules.
3. `III.axiom_surface_seal`
   - no `sorry`/`admit`/`axiom` holes on stable canonical surface.
4. `IV.semantic_weight_ratio`
   - comment-heavy narrative without proof/definition density is disallowed.
5. `V.identity_via_reflexivity`
   - grand unification claims cannot close by trivial `rfl` identity engineering.

Enforcement command:

```bash
python3 tools/quality/functorial_invariance_audit.py --json-out reports/dag/functorial-invariance-audit.json --md-out reports/dag/functorial-invariance-audit.md
python3 tools/quality/pauli_seal_audit.py --root lean/InfoGeometry --json-out reports/pauli-seal-audit.json
```

Any failure is a closure blocker.

```text
You are running the Pauli pass for InfoGeometry.

Scope:
- Evaluate a Jungian symbol-first generation packet.
- Reject unearned closure.
- Keep productive hypotheses alive as structured backlog items.
- Enforce tools/prompts/SYMBOL_FIRST_PROTOCOL.md.

Required outputs:
1) Claim partition
   - proven (with exact theorem/file anchors)
   - bridge-drafted (owner and bridge named)
   - obstructed (precise blocker)
   - decorative (remove)
2) Definitional inflation audit
   - list any "bridge by rename" claims
   - list any theorem weakened to force progress
3) Formalization readiness
   - mark each surviving claim as:
     - symbolic-incomplete (missing relations or lemma chain)
     - pre-formal (ready for translator pass)
     - formalizable-now (safe to encode in Lean)
4) Symbolic completeness audit
   - for each surviving claim verify:
     - operator tuple present
     - relation type present
     - target theorem/file present
     - compile probe or expected first-goal shape present
5) Admission decision
   - admit / stabilize / quarantine
6) Minimal repair plan
   - smallest patch set to move one claim forward

Mandatory constraints:
- Kernel-first: no claim is closed without compiled anchor.
- Distinguish analogy from theorem in every item.
- Preserve unresolved high-value motifs as backlog; do not sterilize.
- Reject language-only packets.

Style:
- Direct, technical, exclusion-driven.
- No motivational prose.
```
