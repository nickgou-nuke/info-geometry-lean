# Mathlib Rules SOP for This Repository

Downloaded references are stored under `external_refs/mathlib_docs/`:

- `README.md` — mathlib4 repository overview and build commands.
- `contribute_index.md` — contribution workflow and PR lifecycle.
- `contribute_style.md` — library style guide.
- `contribute_naming.md` — naming conventions.

## Required practices adopted here

### Before implementing

- Search Mathlib first; do not duplicate existing definitions/theorems.
- Discuss nontrivial library-shaped additions on Lean Zulip/mathlib channels when intended for upstreaming.
- Prefer small, self-contained changes over large bundled rewrites.

### File and documentation style

- Follow the Lean 4 mathlib header shape when creating new library-style files:
  copyright header, optional `module`, grouped imports, then a module docstring.
- Keep imports one per line and alphabetized within public/private import blocks when practical.
- Module docstrings use `/-!` and `-/` delimiters on their own lines, an ATX `#` title,
  a concise summary, and relevant `## Main definitions`, `## Main statements`,
  `## Notation`, `## Implementation notes`, `## References`, and `## Tags` sections
  when those sections add information.
- Every definition and major theorem should have a `/-- ... -/` docstring describing
  the mathematical meaning, not an inflated interpretation of future bridge work.
- Raw URLs in documentation should be written as `<https://...>`.
- Sectioning comments intended for generated docs should use module-doc delimiters,
  e.g. `/-! ### Section title -/`.
- Keep lines at or below 100 characters when practical.
- Use spaces around `:`, `:=`, and infix operators; put them before line breaks.
- Top-level commands and declarations remain flush-left inside namespaces/sections.
- Multiline declaration continuations are indented by 4 spaces; proofs are indented by
  2 spaces after `:= by`.
- Use `where` syntax for structures/classes/instances and docstring structure fields.
- Avoid orphaned parentheses and unclear long proof terms.
- Prefer `fun` or `↦`; never use `λ`. Prefer `<|`/`|>` over `$`.
- Do not squeeze terminal `simp` calls unless there is a demonstrated performance or
  stability reason.
- Avoid `nonrec` unless unavoidable; qualify names instead when possible.
- Avoid empty lines inside declarations; use a short comment if separation is needed.

### Naming

- Use descriptive lower-case theorem names with underscores.
- Name conclusions directly where possible (`map_zero`, `mul_assoc`, `foo_eq_bar`).
- Use `_of_` to encode essential hypotheses only when mathematically meaningful.
- Do not use names that suggest proof closure when the declaration is only a proxy (`*_valid`, `*_readback`, `*_certificate`, `*_witness`, `*_law`).

### Proof discipline

- Prefer theorem/lemma chains over large tactic blobs.
- Add reusable helper lemmas when a proof is repeated or conceptually meaningful.
- Keep proofs local and minimal, but never at the cost of hiding mathematical debt.
- `simp` lemmas and instances require extra care: add only when they are canonical and unlikely to loop or cause global regressions.

### Build and validation

For a touched file:

```bash
lake env lean path/to/File.lean
```

For dependency cache guidance from mathlib4:

```bash
lake exe cache get
lake build Mathlib.Import.Path
lake test
```

For this repo's proof-only and style/documentation gates:

```bash
python3 tools/lean4-skills/sorry_analyzer.py lean --format=summary
python3 tools/quality/check_no_hypothesis_mandate.py --root lean/InfoGeometry
python3 tools/quality/proof_only_mandate_gate.py
python3 tools/quality/audit_style.py lean/InfoGeometry/Canonical
python3 tools/quality/audit_docstrings.py lean/InfoGeometry/Canonical
```

## Upstreaming posture

When code is intended to become a Mathlib contribution, make it independent of repository-specific physics/geometry naming and split it into the smallest reusable mathematical lemmas first.
