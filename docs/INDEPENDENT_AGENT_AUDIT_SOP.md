# QMS-SOP-IAA-001 — Independent Agent Audit and Acceptance SOP

Status: proposed controlled SOP
Document ID: QMS-SOP-IAA-001
Version: 1.1
Effective date: 2026-07-04
Scope: agent-authored theorem-bearing or theorem-adjacent changes in `info-geometry-lean`, including Lean files, controlled mathematical documentation, debt packets, and verification-facing workflow artifacts.

## 0. Purpose

This SOP formalizes mandatory role separation for agent-authored work in this repository.

It exists to control a specific failure mode:
- an authoring agent writes code or mathematical packaging,
- then effectively accepts its own work,
- while confabulations, wrapper inflation, scope drift, or stale-repo assumptions survive into the reported result.

This SOP does not replace repo proof authority. It adds an independence requirement for acceptance of agent-authored theorem-bearing and theorem-adjacent work.

## 1. Parent standards

This SOP is subordinate to and must be used together with:

- `docs/ALCHEMICAL_QMS_SOP.md`
- `docs/AUTONOMOUS_PROOF_SOP.md`
- `docs/GOAL_LOOP_SOP.md`
- `docs/MISSION_LOOP_SOP.md`
- `FORMALIZATION_PROTOCOL.md`
- `ASTAQLHASH-HOWTO.md`

If this SOP conflicts with current Lean code, kernel-checked owner files, or repo safety policy, those higher authorities win.

## 2. Authority inheritance

This SOP inherits theorem-authority ordering, BUCKET use, and owner-first proof discipline from:
- `docs/ALCHEMICAL_QMS_SOP.md`
- `docs/AUTONOMOUS_PROOF_SOP.md`
- `FORMALIZATION_PROTOCOL.md`

It adds one primary additional control: agent independence is mandatory for acceptance of agent-authored theorem-bearing or theorem-adjacent work.

## 3. Mandatory role separation

This SOP uses the role taxonomy already established by `docs/ALCHEMICAL_QMS_SOP.md`.
Every covered work item must pass through three non-overlapping roles.

### 3.1 Generation / drafting agent (G-A)

Allowed:
- read repo files and supporting controlled docs;
- draft Lean or controlled-doc changes;
- run narrow local checks before handoff;
- report exact files touched and commands run.

Forbidden:
- declaring its own output accepted;
- suppressing known scope limits;
- describing wrapper packaging as stronger mathematics than the file proves;
- serving as the only audit voice.

Required output:
- changed file list;
- exact claim scope;
- exact commands run;
- unresolved doubts or suspected weak points.

### 3.2 Audit agent (A-A)

Allowed:
- re-read the changed files and relevant owner/context files independently;
- search for stronger existing owner surfaces or contradictory evidence;
- classify nonconformities in theorem scope, naming, docstrings, wrappers, vacuity, or proof posture;
- request correction.

Forbidden:
- authoring the original draft under audit;
- accepting the result;
- relying only on the drafter’s summary.

Required output:
- `PASS`, `REQUEST_CHANGES`, or `REJECT`;
- exact file:line findings;
- concrete corrective actions.

### 3.3 Acceptance quality agent (QA-A)

Allowed:
- rerun decisive checks;
- verify that audit-requested changes were actually applied;
- confirm final scope wording and controlled-document placement;
- classify result as `ACCEPTED`, `ACCEPTED_WITH_LIMITED_SCOPE`, or `REJECTED`.

Forbidden:
- writing fresh theorem content to rescue a failing artifact;
- accepting from summaries without rerunning checks;
- widening scope labels to make the result look complete.

Required output:
- disposition;
- exact checks rerun;
- residual open debt list.

## 4. Non-overlap rule

The same agent instance, session, or authoring context may not occupy more than one of `G-A`, `A-A`, or `QA-A` across the full artifact acceptance cycle for one work item.

If the orchestrator authors a theorem-bearing artifact, it must obtain both:
- an independent audit subagent result from an `A-A` distinct from the drafter;
- an independent acceptance subagent result from a `QA-A` distinct from both the drafter and the audit agent;
before reporting the artifact as verified.

## 5. When this SOP is mandatory

Use this SOP whenever any of the following are true:
- Lean theorem or definition edits are made;
- theorem-adjacent packets, wrappers, closure sockets, or hypothesis records are added or renamed;
- docstrings make mathematical interpretation claims;
- a controlled SOP/QMS/process supplement is drafted for agent-authored proof or review workflow;
- a user explicitly requests subagent separation because self-audit is unreliable.

This SOP does not replace repo-wide process control. It adds independent-audit requirements for the specific agent-authored artifact classes above.

## 6. Minimum process delta

This section is intentionally a supplement to the parent standards. Search order, owner-first proof discipline, BUCKET usage, and broad QMS gates are inherited from the parent standards; the clauses below add only the extra independence, handoff, and packaging-control requirements needed for agent-separated execution.

### Gate 0 — Existing-standard check
Before drafting a new process artifact, search for existing SOP/QMS/process docs so the repo does not fork into parallel standards.

Required searches:
- repo-wide content search for `QMS|SOP|quality|process|audit|acceptance|workflow`;
- repo-wide filename search for `*SOP*`, `*quality*`, `*process*`;
- read the most relevant controlled docs before drafting.

### Gate 1 — Draft
The `G-A` writes the smallest controlled artifact or code change needed.

Rules:
- do not create a grand standard when a supplement to an existing one is enough;
- do not restate repo doctrine as if it were new mathematics;
- keep scope explicit: theorem-bearing, theorem-adjacent, or process-only.
- for Lean artifacts, prefer small files and helper-lemma decomposition over monolithic proof blocks so downstream reuse and audit remain local.

### Gate 2 — Independent audit
The `A-A` must inspect the draft without editing it first.

Minimum audit questions:
- Does the artifact overclaim relative to the code or proof state?
- Does it duplicate an existing standard unnecessarily?
- Are names/docstrings stronger than the actual content?
- Are packet/wrapper layers adding noise instead of verified mathematics?
- Are required verifications narrow and repo-first?
- Is the Lean surface kept small and factored into reusable lemmas rather than one oversized, non-reusable proof block?

### Gate 3 — Corrective revision
The drafting/orchestrating side may revise only in response to audit findings.

Every corrective edit should be traceable to a specific audit finding.

### Gate 4 — Independent acceptance
The `QA-A` reruns the decisive checks and confirms the final wording/scope.

For code artifacts, minimum checks are:
- `lake env lean <changed-file>`
- `lake build <Touched.Module>` where applicable
- vacuity scan where relevant
- axiom scan where relevant
- theorem/lemma traceability to imported mathlib roots, existing owner theorems,
  or explicit local hypotheses
- naming, declaration shape, and proof organization conform to repo/mathlib-native
  style for the touched surface

For controlled-doc artifacts, minimum checks are:
- exact file exists in the intended location;
- referenced companion docs exist;
- wording matches repo authority hierarchy and role separation rules;
- the document does not fork, contradict, or silently narrow an existing controlled standard unless the deviation is explicit and justified.

## 7. Verdict and disposition inheritance

Audit verdicts and acceptance dispositions inherit the parent QMS taxonomy.

Minimum required use here:
- `A-A` may return `PASS`, `REQUEST_CHANGES`, or `REJECT`.
- `QA-A` may return `ACCEPTED`, `ACCEPTED_WITH_LIMITED_SCOPE`, or `REJECTED`.

The definitions below are restated only because this SOP requires them during agent-separated handoff.

## 8. Dispositions

### ACCEPTED
Use only when:
- audit findings were resolved or explicitly judged nonblocking;
- decisive checks were rerun successfully;
- final scope wording matches the verified formal payload and cited theorem roots.

### ACCEPTED_WITH_LIMITED_SCOPE
Use when:
- the artifact is sound but only as process guidance, a hypothesis socket, a readback, or a limited-scope theorem packet;
- remaining promotion debt is explicitly recorded.

### REJECTED
Use when:
- self-audit remains the only basis for acceptance;
- decisive checks were not rerun;
- names/docstrings/claims still outrun verified authority;
- the artifact duplicates or conflicts with an existing repo standard without justification.

## 9. Required record for each run

The orchestrator must preserve, in the session or artifact summary:
- draft artifact path(s);
- audit artifact or summary path/result;
- acceptance summary/result;
- exact commands rerun;
- final disposition;
- remaining open debts.

## 10. Special rule for theorem-adjacent packaging

The following are high-risk and must be audited especially hard:
- `_packet`, `_closure`, `_foundation`, `_compatibility`, `_witness`, `_holds`, `_certificate` surfaces;
- docstrings with words like “complex structure”, “global closure”, “exceptional Lie algebra”, “local symmetric space”, or physical interpretation language;
- definitional `rfl` readbacks presented as abstract structural theorems.

Default correction rule:
- if a statement is just a coordinate readback, label it as a readback;
- if a record merely stores supplied closure data, document it as a supplied witness/socket;
- if a bundle theorem only conjoins existing lemmas and has no downstream use, remove or demote it.

## 11. Example execution template

1. Search existing standards.
2. Draft the smallest artifact.
3. If dispatching a subagent, give it a sandbox-only task: write to a new file under a sandbox path and never ask it to fix or rewrite a live owner file.
4. Provide the subagent with sufficient mathematical and file-context excerpts from the live owner surface so it can work without touching that owner file directly.
5. Dispatch independent audit subagent.
6. Dispatch independent acceptance subagent with a non-overlapping task.
7. Revise only from audit findings.
8. Parent integrates accepted sandbox output into the live owner file with an ordinary reviewed patch.
9. Rerun decisive checks.
10. Report disposition, traceability roots, scope class, and residual debt exactly.

## 12. Subagent sandbox mandate

When this SOP uses subagents, apply the following repository rule:

- subagents must not be tasked with fixing or rewriting an existing live owner file;
- every subagent write target must be a new file under a sandbox/quarantine path;
- the parent agent must pass enough mathematical context, theorem targets, local excerpts, and verification requirements for the subagent to work offline from the owner surface;
- only the parent may promote sandbox output into a live owner file, and only after rereading both the owner file and the sandbox artifact, then rerunning decisive checks.

## 13. Mission rule

This SOP is successful only when it reduces false confidence.
It fails if acceptance is based on tone, summary confidence, or process narration rather than independent evidence, rerun checks, root traceability, and scope fidelity.
