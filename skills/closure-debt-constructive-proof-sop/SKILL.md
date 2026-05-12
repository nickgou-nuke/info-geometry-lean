---
name: closure-debt-constructive-proof-sop
description: Use when reducing closure debt in Lean modules under strict mathlib-rooted constructive-proof policy.
version: 1.0.0
author: Hermes Agent
license: MIT
metadata:
  hermes:
    tags: [lean4, closure-debt, constructive-proofs, mathlib, verification]
    related_skills: [lean4, pauli-auditor, info-geometry-repo]
---

# Closure-Debt Constructive-Proof SOP

## Overview

This skill standardizes closure-debt reduction in info-geometry-lean when proof authority must remain fully Lean/mathlib-grounded.

Core rule: no non-authoritative witness placeholders for final claims. A green compile is necessary but not sufficient. Any promoted proposition must be backed by an explicit derivation chain (owner lemmas -> translator/coherence lemmas -> target theorem) that traces to mathlib-rooted facts without vacuous packaging.

## When to Use

Use this skill when:
- A user asks to eliminate closure debt with explicit constructive proofs.
- A module has owner-target propositions that need theorem-backed realization.
- Audits report hard/soft findings and you need a deterministic burn-down workflow.

Do not use this skill for:
- Purely exploratory generation-first drafts that are explicitly non-authoritative.
- Report-only passes with no Lean edits.

## Standard Operating Procedure

1) Deterministic discovery first

Run scanners before touching Lean:

```bash
# Smoke first to avoid long blind runs
python3 tools/quality/closure_debt_crawler.py \
  --root lean \
  --limit 50 \
  --print-progress \
  --json-out reports/audit/repo-closure-debt-crawler.smoke.json \
  --md-out reports/audit/repo-closure-debt-crawler.smoke.md \
  --print-summary

# Full pass with watchdog timeout
timeout 300 python3 tools/quality/closure_debt_crawler.py \
  --root lean \
  --print-progress \
  --json-out reports/audit/repo-closure-debt-crawler.json \
  --md-out reports/audit/repo-closure-debt-crawler.md \
  --print-summary

python3 tools/quality/placeholder_audit.py \
  --root lean/InfoGeometry \
  --json-out reports/audit/repo-placeholder-audit.json \
  --md-out reports/audit/repo-placeholder-audit.md \
  --signals-out reports/audit/repo-placeholder-signals.json
```

Optional advisory lane:

```bash
python3 tools/quality/llm_closure_debt_auditor.py \
  --root lean/InfoGeometry \
  --limit 20 \
  --max-context-tokens 2048 \
  --max-tokens 600 \
  --print-progress \
  --print-budget \
  --json-out reports/audit/repo-llm-closure-debt-audit-sampled.json \
  --md-out reports/audit/repo-llm-closure-debt-audit-sampled.md
```

2) Prioritize in strict order
- P0 hard findings (`sorry`, `admit`, unsafe proof holes)
- P1 propositions lacking theorem-backed constructive chains
- P2 soft/advisory debt (skeletal proof shape, packaging debt)

3) Constructive proof policy
- Prefer existing mathlib lemmas first.
- If a lemma path is missing, add minimal intermediate lemmas in-repo with full proofs.
- External references (AFP, arXiv, papers) may guide statement design only; final authority is Lean-checked proof terms.
- Avoid introducing opaque witness placeholders as final closure for promoted claims.
- Treat compile success as kernel hygiene only; do not equate it with semantic closure.
- For each promoted proposition, write and verify an explicit dependency chain section in review notes:
  - terminal target theorem
  - immediate supporting lemmas (same module)
  - upstream owner lemmas/modules
  - first mathlib-rooted lemmas/constants used
- Reject/avoid vacuous packaging as closure evidence (`Nonempty`, `Exists`, `_valid` projection-only readbacks, interface/witness shells) unless they are only intermediate and fully discharged by downstream theorem derivation.

4) Verify each touched module immediately

```bash
lake env lean lean/<Path/To/Module>.lean
lake build <Module.Name>
```

5) Re-scan after each batch
- Re-run deterministic scanners and compare hard/soft/advisory deltas.
- Keep JSON/MD artifacts under `reports/audit/`.
- For promotion candidates, run targeted `#print axioms` checks and record outputs to ensure no custom/repo admissions are in the chain.

6) Commit discipline
- Keep commits surgical.
- Include only touched modules and directly related tests/scripts.
- If user asks to push, push both remotes (`origin` + `upstream`).

## Common Pitfalls

1. Treating heuristic scanner strings as proof holes without source inspection.
2. Shipping a proposition with existence packaging but no theorem-level constructive chain for the intended promoted claim.
3. Skipping immediate `lake env lean` checks and discovering breakage late.
4. Letting advisory LLM findings override deterministic scanner/build evidence.

## Verification Checklist

- [ ] Deterministic scanners run and artifacts saved.
- [ ] Every changed proposition has a theorem proof chain compiling in Lean.
- [ ] For each promoted proposition, explicit dependency chain to mathlib-rooted lemmas is documented.
- [ ] No vacuous packaging is used as final closure evidence (`Nonempty`/`Exists`/`_valid` projection-only/interface shells).
- [ ] `lake env lean` passes for each changed module.
- [ ] Targeted `lake build` passes.
- [ ] Targeted `#print axioms` outputs recorded for promoted theorems.
- [ ] Post-change scanner rerun recorded.
- [ ] Commit scope is surgical and policy-compliant.

## Runtime Notes (anti-hang)

- Never start with a full crawler run blind; use `--limit` smoke first.
- For full deterministic crawler passes, use a watchdog timeout (`timeout 300 ...`) and `--print-progress`.
- For LLM auditor on local GGUF lanes, always pin context (`--max-context-tokens`) and keep token headroom (`--max-tokens 600` or lower) unless benchmarked otherwise.
- Use `--print-budget` on sampled runs to verify prompt/excerpt sizing before scaling.
