# Academic Research Skills Audit

> Status: `external reference`
> Audited: 2026-06-06
> Scope: `Imbad0202/academic-research-skills` and the Codex sibling package.
> Authority: Lean source, `lake env lean`, and local repository publication
> policy remain authority. Academic Research Skills is workflow evidence and
> prompt/process reference only.

## Summary

`Imbad0202/academic-research-skills` is a mature academic-writing workflow
suite for Claude Code. It covers the full research-to-publication pipeline:
research, writing, review, revision, integrity checks, and final formatting.

The repository is directly relevant to this project's publication lane. It is
not a proof dependency and should not be vendored into `lean/` or treated as a
theorem authority.

The most useful discovery is that a Codex-native sibling distribution exists:

```text
https://github.com/Imbad0202/academic-research-skills-codex
```

That package wraps the ARS workflow content as one Codex skill named
`academic-research-suite`, with routes for deep research, academic paper
planning/writing, paper review, full academic pipeline, and experiment-agent
workflows.

## License Boundary

Both audited repositories use Creative Commons Attribution-NonCommercial 4.0
International.

This means:

- do not copy workflow text, agents, hooks, or skill content into this
  repository without a separate license decision;
- do not vendor it into an institute runtime by default;
- do not mix its prompt text into our own maintained skills;
- do use it as an external architecture reference with attribution.

If we later install the Codex package locally for personal experimentation, it
should remain outside the repo source tree and outside proof authority.

## What Is Useful

The ARS architecture has several design patterns worth importing as ideas:

- staged research-to-paper pipeline;
- explicit human checkpoints after every material stage;
- integrity gates before review and before finalization;
- source provenance through a Material Passport concept;
- citation existence and claim-support auditing;
- simulated peer review with separated reviewer roles;
- revision traceability matrix;
- final format/disclosure gate;
- process summary artifact after completion.

These are useful because they match the missing outer shell around our Lean
proof work:

```text
kernel-checked theorem work
  -> theorem/debt manifest
  -> source provenance packet
  -> draft paper skeleton
  -> review/refutation lane
  -> revision trace
  -> final disclosure and submission packet
```

## What Must Not Be Imported Blindly

Do not import:

- its agent prompts as-is;
- Claude-specific slash commands;
- hooks or background runtime behavior;
- cross-model API assumptions;
- automatic external source fetching;
- writing automation that bypasses human checkpoints;
- any claim that AI review replaces Lean verification.

The repo's own security policy treats prompt injection, credential leakage,
data exfiltration, and integrity-gate bypass as in-scope vulnerabilities. Those
same risks apply here.

## Safe Local Mapping

For this repository, the equivalent publication pipeline should be:

```text
1. SELECT
   Choose theorem owner modules and paper target.

2. VERIFY
   Run focused Lean builds and sorry/debt audits.

3. MATERIAL PASSPORT
   Build a local JSON/Markdown packet:
   theorem declarations, definitions, imports, build commands, proof status,
   closure debt, source citations, oracle reviews, and generated artifacts.

4. OUTLINE
   Produce a paper outline from verified material only.

5. REVIEW
   Use aiClaw/oracle review or human review for criticism.

6. REVISE
   Record response-to-review and source changes.

7. FINALIZE
   Produce Markdown/LaTeX/PDF plus AI disclosure and provenance appendix.
```

This preserves the core law:

```text
Lean proves.
Agents draft and criticize.
Humans decide.
External publication systems distribute.
```

## Relation To P2PCLAW

ARS is the stronger model for local publication preparation.
P2PCLAW is the stronger model for external publication/discovery gateway
architecture.

Together they suggest this split:

```text
ARS-like local pipeline:
  prepare, verify, review, revise, package

P2PCLAW-like external gateway:
  publish, discover, peer-review, coordinate
```

Neither layer changes theorem authority.

## Candidate Local Artifacts

Add these later if we decide to implement the publication lane:

```text
tools/publication/build_theorem_passport.py
tools/publication/build_paper_outline.py
tools/publication/check_claim_support.py
tools/publication/render_publication_packet.py
docs/PUBLICATION_PIPELINE_RUNBOOK.md
schemas/publication_packet.schema.json
```

The first implementation should be dry-run only. It should read Lean and build
artifacts, generate packets under `artifacts/publication/`, and never submit
externally.

## Current Recommendation

Do not install or vendor ARS automatically. Keep it as a documented reference.
If the user explicitly wants to experiment with it, prefer the Codex-native
package in a separate local skill installation, with no repo source mutation and
with the CC BY-NC license boundary acknowledged.
