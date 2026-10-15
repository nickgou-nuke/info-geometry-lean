---
description: Adversarially CHECK whether a given mathematical statement is TRUE — by hunting for a counterexample with a multi-agent ultracode Workflow, then ground-truthing every claimed counterexample by RUNNING Lean. Returns FALSE (Lean-confirmed counterexample), CONDITIONAL (true only with an added hypothesis), NO-COUNTEREXAMPLE-FOUND (survived every adversarial lens — "appears true", NOT a proof), or UNCERTAIN. A refutation is a certificate; survival is strong evidence, not a proof. For an actual proof use /prove.
argument-hint: <a mathematical statement — informal English, a Lean signature, or a file:identifier pointer to an on-disk decl>
---

`/check` answers ONE question about `$ARGUMENTS`: **is this statement
mathematically TRUE, or is there a counterexample?** It does NOT construct a
proof — it runs an adversarial **counterexample hunt** as a multi-agent
Workflow, and grounds every candidate counterexample in actual Lean. It is the
standalone, general-purpose version of `/prove`'s Stage-1 headline adversarial
check + the Lean-running tie-breaker, usable on any statement (a headline you're
about to formalise, a lemma you suspect is false-as-stated, a convention fork, a
sibling's hypothesis you want to test).

---

## §0. The epistemics (read first — this governs what `/check` may claim)

Refuting and proving are **asymmetric**, and `/check` only does the first one
rigorously:

- A **counterexample is a CERTIFICATE.** If the hunt finds — and Lean confirms —
  one object satisfying every binder while breaking the conclusion, the statement
  is **FALSE**, definitively. That is the verdict `/check` can assert with
  confidence.
- **The absence of a found counterexample is NOT a proof.** Surviving every lens
  the panel threw at it is strong evidence the statement is true, but it is
  *searching, not proving* — exactly the `/prove` §0 thesis (reading/searching ≠
  proving). So a survived statement is reported as **NO-COUNTEREXAMPLE-FOUND
  ("appears true")** with the lenses checked + calibrated confidence — never as
  "PROVEN". **For a real proof, the user runs `/prove`.** Say this plainly in the
  report; do not let "appears true" read as "proved".

`/check` is read-only / scratch-only. It **writes NOTHING** to
the project's files and makes **no commits** — Lean scratch lives in `/tmp`
only. Its entire output is a chat report (in the user's language).

---

## §1. Workflow self-authorization (no separate ultracode toggle)

`/check` runs its adversarial hunt as a multi-agent **Workflow**. **Invoking
`/check` IS the Workflow opt-in** — per the `Workflow` tool's own rules, *"the
user invoked a skill or slash command whose instructions tell you to call
Workflow"* is a valid authorization, and this section is that instruction. So
the moment the user runs `/check`, the orchestrator is authorized to — and
SHOULD — open the Workflow, whether or not an `ultracode`/`workflow` keyword or
session flag is present. (For a trivially-decidable statement — a degenerate
case checkable by reading or one Lean scratch in seconds — you may answer
directly without a Workflow; the Workflow is for any statement where breadth of
adversarial lenses earns its cost. When in doubt, fan out.)

**Effort and ultracode are orthogonal; opening a Workflow does not drop effort:**
the main-loop orchestrator keeps the session's effort across the Workflow call,
and every Workflow `agent()` inherits its model + effort from its `agentType`
agent-def (pinned there — this skill does not name a model or effort level, so it
never goes stale when you re-tune). **Name `agentType` and do NOT pass
`opts.model`** (a bare `model` resolves only coarse aliases and can DROP a pinned
model variant; there is no per-invocation effort knob — the agent-def is the only
channel).

**Agent types** (both read-only — `/check` proves nothing, so `lean-worker` is
NOT used):
- **`lean-refuter`** — the ADVERSARY. Attacks the statement through a named lens,
  BOTH by reading it against the trap catalog AND by constructing an explicit
  counterexample / vacuity-witness and RUNNING it in Lean (`lake env lean` on a
  `/tmp` scratch). Returns a witnessed verdict; its null hypothesis is "this is
  wrong". (This is `/check`'s primary worker.)
- **`lean-researcher`** — the SCOUT, used when a lens needs pure search:
  existence / citation checks, candidate enumeration, "is there an existing lemma
  that settles this". Returns evidence + a query log; writes nothing. (It does NOT
  build counterexamples — that is the refuter's job.)

---

## §2. The recurring false-as-stated trap catalog (the lenses)

These are the exact defect classes that have made project statements false; the
adversarial panel screens `$ARGUMENTS` against all of them (shared verbatim with
`/prove` §0bis). Each is a lens an auditor attacks through.

- **T1 — raw chart-coordinate / chartJ extraction.** A continuity/derivative
  claim about a RAW `M → E` projection (`(triv).symm x basis`, `coordChange`, an
  `achart`-indexed fibre value) is generically FALSE on multi-chart manifolds
  (`achart` jumps; chartJ is unbounded on S²). CARVE-OUT IS CONDITIONAL: a
  fixed-chart `extChartAt I α` form is safe ONLY if the charted point is PINNED
  at basepoint `α`; if the argument TRAVELS (an orbit `Φ s x`, a curve, any `y`
  leaving `α`) then `mfderiv (extChartAt I α) y ≠ id` off-basepoint and it is
  FALSE off-basepoint. Litmus: does the chart argument stay `= α` or travel?
  travels ⇒ T1 fires. Counterexample family: S² + the inversion-chart derivative.
- **T2 — free-family quantifier.** A family/data argument (`Vpush`, `g_DT`, `Φ`,
  `u`, `repr`, …) with NO hypothesis tying it to what it denotes — a
  counterexample family satisfies the binders and breaks the conclusion.
- **T2′ — `∃…∀…` where uniqueness forces `∃` innermost.** `∃ V, ∀ t, HasFDeriv… V`
  is FALSE when the derivative is unique and varies with `t`.
- **T3 — `HasLocallyConstantChartAt` / locally-constant-chart / global-flatness.**
  Mathematically FALSE on normal manifolds (S²); fully deleted from the library.
  GREP TRAP: the string survives in dozens of docstring DISCLAIMERS with ZERO
  uses — verify it is a real binder before believing any "still used" claim.
- **T4 — vacuous binder.** A hypothesis trivially satisfiable / saying nothing
  (inner product against the zero vector; continuity of a constant; `∀` over an
  empty index; a regularity the type already guarantees).
- **T5 — over-general / leak.** The statement is false at general parameter but
  true only on a special locus (a smallness / scale / fibre-small / finite-
  support condition silently required). Report the locus where it holds.
- **T6 — hypothesis-packaging.** A hypothesis whose type is (defeq to) the
  conclusion — the statement assumes what it claims (vacuously "true").
- **T7 — family-as-INPUT that should be existential-OUTPUT.** Turning an
  existentially-produced object (`repr`, `Nsec`) into a free universal INPUT
  falsifies it (degenerate input `repr ≡ 0`).
- **T8 — per-fibre vs joint.** `∀ x, ContinuousOn (s ↦ f s x)` (per-fibre) does
  NOT give joint `ContinuousOn ((s,x) ↦ f s x)` — `xy/(x²+y²)` is the witness.
- **T9 — two-sided vs one-sided on an interval.** On-disk flow families are
  `= id` outside `(0,T)` and JUMP at endpoints, so a `∀ t : ℝ` two-sided
  `HasMFDerivAt` is unsatisfiable; needs within-interval one-sided.
- **T10 — C∞-at-0 over-demand.** A field only CONTINUOUS at `t=0` (`√s` has
  `∂ₛ → ∞`) breaks any clause demanding C∞ up to 0.

Beyond the catalog, the panel also runs the **classical adversarial lenses**:
degenerate dimension (n = 0, 1); empty / trivial / single-point domain;
boundary / compactness / completeness edge; sign / orientation; degenerate or
non-positive-definite metric; zero / constant curvature; the statement at its
own hypotheses' boundary.

---

## §3. Stages

### Stage 0 — Pin the statement precisely (no fan-out yet)

Establish EXACTLY what is being claimed before attacking it — a vague target
produces vacuous verdicts.

- If `$ARGUMENTS` is a **`file:identifier` pointer or a Lean signature**: Read
  the decl on disk (the on-disk signature is the truth; any prose is only
  documentation). Pin every binder, quantifier order, the ambient typeclass
  context (Boundaryless / Compact / Complete / FiniteDimensional …), and the
  conclusion's exact form.
- If `$ARGUMENTS` is **informal English**: fix a precise mathematical reading —
  quantifier order and scope, the domain, the relevant conventions (the project's
  sign conventions for its operators, e.g. Laplacian / Ricci / Hessian, as fixed by their on-disk
  defs, if they bear on truth),
  and what "edge" inputs (n=0,1; empty; degenerate) the statement implicitly
  covers. If two genuinely non-equivalent readings exist and they DISAGREE on
  truth, surface that as a clarifying question (the answer changes the verdict) —
  otherwise pick the strongest reasonable reading, STATE it, and proceed.
- A short `lean-researcher` survey may locate the natural ambient context, prior
  art, and any project lemma that already states (or contradicts) the claim.

Record the pinned statement at the top of the report.

### Stage 1 — Adversarial counterexample hunt (the Workflow marquee)

One Workflow. `parallel` fan-out of lenses over the pinned statement; scale the
pool to thoroughness (default ≥4–6 distinct lenses — the trap catalog classes
that plausibly apply PLUS the classical adversarial lenses; "be thorough" / a
high-stakes headline → larger pool + the loop-until-dry of Stage 3).

Each lens agent (`lean-refuter` for reading attacks AND explicit Lean
counterexample construction; `lean-researcher` when the lens needs only a
search for an existing settling lemma) returns ONE of:
- **REFUTED** — a concrete object satisfying every binder and breaking the
  conclusion. MUST carry the explicit witness (the manifold / function / metric
  / index, and which clause it breaks). A bare "this looks false" is NOT a
  REFUTED — it is NO-COUNTEREXAMPLE-FOUND with a suspicion noted.
- **CONDITIONAL** — false as stated, but true once a specific hypothesis `H` is
  added (name the minimal `H`, and — if a sibling/related decl already carries
  it — name that sibling). This is the T2/T5/T7-class outcome.
- **NO-COUNTEREXAMPLE-FOUND** — this lens could not break it; report what was
  searched and the strongest near-counterexample that FAILED (a near-miss that
  fails is real evidence of robustness).

Use a structured schema so the orchestrator gets verdicts as data, not prose.

### Stage 2 — Ground-truth every claimed counterexample in Lean

**A claimed REFUTED is a CLAIM, not a fact** (agents over-claim false — `/prove`
§3: a real run had an agent declare a true conjunct false by mis-attributing a
cancelling term). Before any REFUTED enters the verdict:

- Dispatch a `lean-refuter` to CONSTRUCT the counterexample in Lean and RUN
  it (`lake env lean` on a `/tmp` scratch) — actually exhibit the object, instantiate
  the statement at it, and show the conclusion fails (e.g. `mfderiv (extChartAt I
  α) y w = (w : E)` does NOT hold off-basepoint by `rfl`/`simp`/`exact?`; the
  two continuity values disagree at the witness point). A reading-only refutation
  is NOT a verdict; the Lean computation is.
- If the Lean check CONFIRMS → the counterexample stands → verdict **FALSE**.
- If the Lean check REFUTES THE REFUTATION (the "counterexample" does not
  actually break the statement) → discard it; that lens reverts to
  NO-COUNTEREXAMPLE-FOUND, and note the over-claim.

Pipeline this against Stage 1 (ground-truth each REFUTED as it lands) so
confirmation does not wait on the slowest lens.

### Stage 3 — Completeness critic + optional loop-until-dry

A final `lean-refuter` (the completeness critic) asks: *what lens or
counterexample family did the panel NOT try?* (a trap class not screened; a
degenerate case not instantiated; a known pathology — S² for chartJ,
`xy/(x²+y²)` for joint continuity, `√s` for C∞-at-0 — not yet thrown at it).
Anything it names becomes one more lens.

For a high-stakes / "be thorough" check, **loop the hunt until K=2 consecutive
rounds surface no new candidate counterexample** (the unknown-size-discovery
pattern — a single round under-searches the tail). Otherwise one critic round
suffices.

### Stage 4 — Synthesize the verdict + report (in the user's language)

Collapse the lens verdicts into ONE headline verdict:

- **FALSE** — at least one Lean-CONFIRMED counterexample. Report it concretely:
  the witness object, the clause it breaks, the trap class (T#) if it is one, and
  the **minimal restatement** that would make it true (add hypothesis `H` /
  restate intrinsically / move `∃` innermost / within-interval one-sided …).
- **CONDITIONAL** — no unconditional counterexample, but a lens showed it needs
  hypothesis `H`. Report the minimal `H` and where a sibling already carries it.
  (This is the most actionable outcome for `/prove`: it is the signature fix.)
- **NO-COUNTEREXAMPLE-FOUND ("appears true")** — survived every lens (and the
  loop-until-dry, if run). Report: the lenses checked, the strongest
  near-counterexamples that failed, and a **calibrated confidence** ("robust
  across N independent lenses incl. Lean-checked degenerate cases" vs "shallowly
  checked — a proof may still expose a subtle obstruction"). State explicitly:
  **this is not a proof; run `/prove` for one.**
- **UNCERTAIN** — neither refuted nor confidently survived (truth hinges on a
  hard theorem the hunt cannot settle in budget). Report exactly what a proof or
  refutation would require, and the leading hypotheses on each side.

The report (in the user's language) leads with the pinned statement + the headline verdict, then
the evidence (counterexample / minimal `H` / lenses-checked), then a one-line
per-notable-subagent quality evaluation.

---

## §4. Agent reports are untrusted — verify every claim against ground truth

Every agent return is a CLAIM. Confirm before it advances the verdict:
- a **REFUTED** is not a verdict until Lean confirms it (§Stage 2);
- a cited Mathlib/project lemma used in a counterexample is re-verified
  (WebFetch the mathlib4 docs / Read the on-disk decl) — names "remembered" are
  wrong more often than right (NO-ASSUMPTION principle, CLAUDE.md);
- a claimed "no counterexample" from a lens that shows no search is NOT evidence
  — require the lens to state what it tried.

A reading split (auditors disagree on truth) is NOT settled by majority — it is
settled by RUNNING LEAN (the `/prove` Stage-1 tie-breaker lesson: a 1-1 reading
split on the md3 headline was resolved only by a Lean computation). Dispatch the
`lean-refuter` to compute the contested identity; the computation is the
verdict.

## §5. STOP / clarify conditions

`/check` is a bounded analysis, not a long autonomous build — it runs the
Workflow, ground-truths, and reports. It does NOT run under `/goal`, does NOT
`ScheduleWakeup`, and never spins. Surface a clarifying question ONLY when:
- `$ARGUMENTS` has two genuinely non-equivalent readings that DISAGREE on truth
  (the answer determines the verdict — ask which is meant);
- the statement references an object/convention not pinnable from the repo
  (ask for the missing definition).
Otherwise pick the strongest reasonable reading, state it, and deliver a verdict.

## §6. Prohibitions / conventions

- **Read-only / scratch-only.** No edits to the project's files, no commits;
  Lean scratch in `/tmp`. `/check` is diagnosis, not construction.
- **Never assert PROVEN.** The strongest truth-direction verdict `/check` may
  give is NO-COUNTEREXAMPLE-FOUND; a counterexample-free hunt is not a proof.
- **A counterexample must be exhibited, not asserted** — Lean-confirmed before it
  becomes FALSE.
- **NO-ASSUMPTION principle** (CLAUDE.md): every Mathlib/project citation behind
  a counterexample is verified in-dispatch (WebFetch / Read), never from memory.
- Communicate with the user in **their language**; give a short quality evaluation of each
  notable returned subagent. Never reference confidential planning docs.
