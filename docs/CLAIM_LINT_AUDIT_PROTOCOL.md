# Claim-Lint Audit Protocol

**Status:** `current authority`
**Scope:** every mathematical law asserted in a manuscript document.

## Law

> No law enters a manuscript without a resolvable `repo-owned` owner, an
> explicit `[partial: …]` gap statement, or an explicit `[unformalized]`
> marker. A missing theorem is stated as missing — never as prose, never as a
> wrapper.

This implements `AGENTS.md`, *The Colimit Continuum Mandate*:

> **Prohibition**: Do NOT hallucinate analytical continuations. Do NOT use
> physical rhetoric … to justify missing proofs.

## Two stages. The script does not replace the audit.

| Stage | Tool | Establishes | Does NOT establish |
|---|---|---|---|
| 1. Screen | `tools/quality/claim_linter.py` | Every law **names** an owner that resolves in `lean/` | That the owner proves the stated claim |
| 2. Audit | Independent agent, per `docs/CANONICAL_AGENT_PIPELINE.md` | That each named owner's **statement** entails the manuscript's claim | — |

A clean screen is **not** certification. It only proves the document is not
missing an owner entirely.

## What the screen provably cannot catch

Every substantive error found in the Section 5 audit cited a *real, resolvable*
owner. The screen was silent on all of them:

| Error | Owner resolves? | Screen | Actually caught by |
|---|---|---|---|
| §5.3 $\omega(u,v)=g(Ku,v)$ sign error | yes — `omega_eq_g_comp_K` | **silent** | reading `compatibility : g v w = omega v (K w)` |
| $U_1U_2U_1 = 2U_1$ wrong factor | yes — `e0_mul_e1_mul_e0` | **silent** | reading the right-hand side |
| "twin *Lagrangian* null sheets" | yes — isotropy theorems | **silent** | the maximality disclaimer at `SplitOctonionClifford33Soldering.lean:95` |
| "Direct $\mathrm{Cl}(3,3)$ Representation" | yes — `zorn_leftActFin8_clifford33` | **silent** | the module's own scope disclaimer |
| 5 theorems presented as complete | names resolve; module does not compile | **silent** | the Lean kernel |

This table is the reason stage 2 is mandatory and is not delegable to code.

## Stage 2 checklist (per law)

1. **Statement-level match.** Read the owner's actual Lean statement. Does it
   entail the manuscript's sentence, term for term? Not merely "related".
2. **Sign and convention.** Check every sign and every `ω`/`g`/`K` convention
   against the owner's `structure` fields, not against prose.
3. **Factors and constants.** Check coefficients ($2U$ vs $U$, $\frac12$, $g$
   vs $2g$).
4. **Hypothesis match.** Does the manuscript claim it for *all* $V$, or only
   where an `IsSheetSwapInvolution` / `ParaKahlerStructure` witness exists?
5. **Non-vacuity.** Is a witness supplied? An unsatisfiable hypothesis makes
   any conclusion true.
6. **Scope vs. docstring.** Does the manuscript's framing exceed the owner's
   own explicit disclaimer? Owner disclaimers win.
7. **Chain completeness.** If the manuscript asserts $A = B = C$ across
   modules, every link needs its own owner in the tag.

## Recording the audit

Findings and verdicts go in the work log. Verdicts are:

- `confirmed` — claim overstates; fix the document
- `false-positive` — screen was wrong; fix the screen
- `needs-owner` — no owner exists; either formalise or mark `[unformalized]`

An audit is complete only when every stage-1 finding has a verdict **and** every
law has been through all seven checklist items.

## Running the screen

```bash
python3 tools/quality/claim_linter.py docs/<doc>.md          # human-readable
python3 tools/quality/claim_linter.py docs/<doc>.md --json   # for the audit step
```

Exit `0` = screen clean. Exit `1` = findings emitted, audit required. Exit
`2` = usage or IO error. There is no warn mode: a claim gate that can be talked
out of failing is not a gate.
