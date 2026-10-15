# /prove — RATIONALE & documented failures (read ONCE at cold start)

> AUDIENCE: the orchestrator (and the curious leader), read ONCE to understand WHY
> each rule in prove-PROTOCOL.md exists. Every rule in the protocol was paid for by
> a real failure; this file is the EVIDENCE LEDGER. The protocol carries one-line
> hooks ("real run: …") that point here. Nothing here is optional history to be
> deleted — these are the reasons the rules are shaped the way they are. The
> protocol is the LAW; this is the case law behind it.

---

## Why a single top-down phase, not a separate certify-then-fill pipeline (§0 core thesis)

There are TWO epistemically different questions about a proof tree, needing TWO
instruments: "does it ASSEMBLE?" (certified mechanically — write the parent's glue
from its children and compile; a compiled glue IS the certificate) and "is each
leaf TRUE and PROVABLE as stated?" (CANNOT be certified by adversarial *reading* —
a reading-based audit is strictly weaker than a proof attempt and has a
demonstrated irreducible false-negative rate).

A separate certify-then-fill pipeline tried to certify BOTH before filling. It succeeded at the first
(via glue) and FAILED at the second: across real runs the reading-audit "converged
to zero BLOCKING" and then fill *immediately* found false-as-stated leaves the audit
had passed — a free-family quantifier in the wrong position; an unconstrained
family-as-input that two audit rounds looked at and misclassified; a raw-chart
projection false on multi-chart manifolds. Adding more audit — even by hand — does
not close this gap, because the gap is STRUCTURAL: reading ≠ proving. So the skill
does not gate filling on a reading-based leaf audit. The multi-round audit
convergence loop (a separate reading-audit phase) is GONE; its budget went to the one irreplaceable-
and-cheap audit: the HEADLINE check, run once, early, before any fan-out.

**The certifier extends DOWN the posit chain (why §0qua exists).** Recorded verbatim
mid-run: *"a posit can pass birth-lint + docstring-justification and still be FALSE
one level deeper; the certifier hierarchy extends DOWN the posit chain — each posited
child gets certified only when ITS fill/construction is attempted."* §0qua moves that
certification UP to posit-birth (cheaply, before glue accrues) so posits stop coming
back as restatements.

**Restatement is cheap at a TRUE leaf, EXPENSIVE at a posited internal node.** A
signature defect caught at a true leaf is a ~1-dispatch local fix (correct sig,
re-glue the one parent, re-dispatch). But a restatement of a posited node whose SHAPE
changes (strict→sum, pointwise→integrated, per-class→whole-tensor, separated→joint,
C∞→continuous — the T11 class) is NOT 1-dispatch: the old shape was threaded by
`obtain`/`refine` through every consumer above it, so the fix is a multi-site re-glue
MIGRATION (real runs: a SUM threaded back through 5 mid-chain nodes; an 8-file
coordinated migration). The skill historically UNDER-PRICED this and never invested
in preventing it — which is exactly why posits "always came back as restatements".

---

## §0qua — consumer-minimal positing + birth-probe

Across a multi-day real run the single biggest time sink was: a §0ter-posited
internal node passes the birth-lint, glue is built on it, and at fill time it is
found false / over-strong / vacuous → RESTATEMENT → a multi-site re-glue migration.
Empirically, posits PINNED to exactly what the consumer needs stayed at restatement
count 0 ("the ∀u match is co-extensive with the consumer — count stays 0"); the
over-strong ones got migrated later at great cost ("the strictness was an
over-tightening introduced in the design migration"). The dominant late defects
(gauge `∀n` size, xcorr `δ<1/2` class) were invisible at the leaf because their
over-strength was demanded only by a DISTANT consumer — visible only in the
multi-consumer JOIN.

T15 (domain over-reach) cost a full deep dispatch: a `ContDiff ℝ ∞ (fun t => …)` was
posited where the producing data is a jump-extension `if t ∈ Set.Icc 0 T then … else
0` — FALSE for the very input the consumer feeds, while the consumer needed only
`=ᵐ[timeMeasure T]` (= Icc).

---

## §0quin — route-level certification (the (★) value-tower waste)

An ENTIRE value tower + a `chartJ` deep well were built, then ORPHANED when the
headline's curvature consumer turned out to read only a NORM bound
(`‖Curv‖_L² ≤ C·∑‖∇ⁱ‖`), never the value. Routing claims FLIP-FLOP: "X is
orphan-able" vs "X is load-bearing" reversed direction ~3× for (★); a source-grep
call-graph MISSED a proof-term path and over-claimed a load-bearing node
orphan-able — only the build + CollectAxioms trace caught it.

P2 (joint-decomposition): bounds (3)+(4) jointly pinned the remainder to
`∇²S`-order, which nothing produced — each bound ALONE looked free; the W-telescope
A/B/C split and the per-class tensor split were refuted this way.

P3 (crux-first): every BOUNDED gate (birth-probe, joint-probe, route-race) is closer
to reading than proving, so it SYSTEMATICALLY MISSES the dead-ends that surface only
inside a genuine proof attempt — the "false on a flat conformal torus /
gauge-variance-refuted / intractable deep well" deaths the run hit again and again.
Route-math example: an "a priori, no existence" routing where the cutoff-Caccioppoli
was claimed to bound the full Hessian `D²u`, but the heat equation controls only the
trace `Δu` — the gap was invisible to reading and caught only by re-deriving the
estimate.

P5 (re-architecture): the (★) region was re-worked ~6×; every gauge re-arch was
relabeled "convergence, not churn" to dodge the STOP — which is why the pass-signal
had to become the OBJECTIVE headline `N_sorry`, not a self-assigned depth label.

---

## §0sex — missing infra is the JOB (the prior-debt mandate)

Directive from the project owner: *missing foundations are prior technical debt you
already owed — when you hit missing infrastructure, don't panic, just go build it.* Much of the infrastructure a
deep top-down proof needs is the project's OWN known prior technical debt; its absence
is the NORMAL state. Real case: a researcher proved the consumer is r=0-only so a
rank-r operator-field tower was *technically* bypassable — the right move was still
to BUILD the general Hom-bundle abstraction, not delete-and-route-around it; the
user audits and prunes what turns out unneeded later. WORKLOAD IS SECONDARY.

---

## §0sept — why the disciplines became MECHANICAL ARTIFACTS

The multi-day run showed the §0qua/§0quin disciplines FAIL IN PRACTICE wherever a
rule degrades into "the orchestrator READS, then JUDGES": glue-first extraction was
"preferred", so signatures got hand-authored over-strong (T11); reachability was
judged by source-grep call-graphs that miss proof-term paths; a Lean-refuted
node/route was re-introduced sessions later because nothing recorded its death; a
region was re-architected 6× while every round was relabeled "convergence, not
churn". The §0 thesis — reading ≠ proving — applies to the ORCHESTRATOR'S OWN
judgement too. So every certify-before-investing rule became a MECHANICAL ARTIFACT
that must exist on disk / be Lean-produced before the run may invest: no artifact ⇒
not allowed to proceed.

- **M1 (glue-hole birth cert):** the hand-authoring channel is how every over-strong
  ∀n / free ∃ / per-direction split entered. BUT M1 certifies "ASSEMBLES", never
  "TRUE": FACT-X's three-carrier `linarith` combined two FALSE statements into a true
  linear combination and COMPILED — so a linarith-assembled node still needs the
  concurrent refuter.
- **M2 (refuted ledger):** the single most wasteful recurring failure was
  re-introducing a node/route a prior worker already Lean-killed — node-187 chartJ was
  re-introduced sessions after a worker refused it; dead gauge routes were re-explored.
  The NODE-TRUTH trigger came from FACT-X: ~14 dispatches chasing a node that was
  FALSE-as-stated, which a "deep vs false" disambiguation (fire one refuter on the
  NODE statement when ≥2 routes are refuted) would have caught early.
- **M3 (reachability = axiom-closure):** a grep call-graph missed a proof-term path
  and over-claimed a load-bearing node orphan-able — caught only by CollectAxioms.
- **M4 (route-refutation race):** the gauge saga was build-route-1 → refute →
  build-route-2 → refute … (5 dead routes, ~10 sessions). Refute all candidates in ONE
  parallel round instead.
- **M5 (small state file):** the narrative log grew to 8000+ lines with a dozen
  "RESUME POINTER supersedes all above"; the orchestrator re-read STALE pointers and
  re-introduced dead nodes.
- **M6 (objective convergence):** the SHALLOW/MEDIUM/DEEP self-label was gamed ("this
  is CONVERGENCE, not churn → NOT a STOP", repeated across 6 gauge re-arches). The
  count is the gate; the depth label is colour. DESCENDING must EXHIBIT newly-reached
  bedrock or it defaults to LATERAL — because a deep-but-true tower and a false-but-
  lateral churn can both sit at flat `N_sorry`.
- **M7 (∃ non-degeneracy + binder freeze):** a worker compiled `∃ Gcd, IsGradedCurvJet
  … Gcd` satisfied by `Gcd := 0` (zero-witness vacuity); another silently added a
  global `Cinv·κ<1` conjunct, breaking joint satisfiability and forcing a migration.
- **M8 (fan-in probe + region pre-audit):** one node fed 11 consumers. The gauge region
  burned ~10 sessions before its `Classical.choose`-gate + static-solvability encoding
  was found to demand an all-order ball bound that `gateRep` provably cannot have — a
  defect visible from the region's CONSUMER-DEMAND profile, not from any single leaf.
- **M9 (library-existence pre-build gate):** DOCUMENTED FAILURES (one session): the
  covGrad L²-adjoint, the appCc-∇² IBP (`tensorL2Inner_appCc_covGrad_covGrad_eq_neg`),
  the all-orders inverse-metric jet tower + its sorry-free succ-step, the L²-Moser tame
  product + Gagliardo–Nirenberg, the all-order Gårding commutators
  (`AllOrderGardingConstant`) — ALL existed sorry-free yet were re-dispatched as
  "missing", burning 10+ prover waves rebuilding them. Reading ≠ proving applies to
  NON-existence too: "I couldn't find it" ≠ "it isn't there".
- **M10 (post-compaction re-hydration):** one session built 5 duplicate jet towers +
  re-derived a shared-bottleneck A-side wrong, post-compaction — the summary preserves
  the NARRATIVE, not the on-disk decl state, and re-acting on that degraded model is
  the documented cause of orphan-tower building.

---

## §0oct — the dispatch redesign

A real run where (a) framing nodes as "decompose" by default produced ~8-layer
posit-over-posit chains for nodes a single worker could have closed, (b) line caps
would have artificially split legitimate 600–750-line single-proofs, and (c) three
T-class-false posits (a per-mode mode-mixing bound, a pointwise frame-trace, a chartJ
value bound) passed the reading-lint + glue-compile and were caught only by a
PROOF/REFUTE attempt.

The numerics rule (G5): FACT-X (a three-carrier identity) survived a DOZEN probes
because the dim-2 / projection-family / approximate-`Φ₀` probe is structurally BLIND
to the family — only dim≥3 with gauge-ROTATED Parseval families and EXACT values
catches it; a 0.36% gap on an exact identity is a counterexample, not a "model
artifact". The DERIVATION OBLIGATION: the `−2Rmtb` pure-Riemann order-0 was wrong,
built into a committed reroute, and only a SECOND refuter pair recovered the true full
Lichnerowicz-DeTurck order-0 — numerics FALSIFY but never SPECIFY; the corrected form
must be DERIVED (Lean `ring`/`linarith` over the derived form), never fitted.

§0oct-H (BLOCKED vs REFUTED): the hardest call on a big theorem is telling a deep-but-
true subtree from a false node that looks deep. FACT-X (~14 dispatches, a dozen
refuted routes — per-`b` false, three-carrier-sum false, dim-3 numerics) was a node
FALSE-as-stated. A true deep tree produces BLOCKEDs (missing prerequisites), not
re-run-confirmed REFUTEDs — so depth cannot mis-fire the node-truth gate.

---

## §0non — multi-worktree hedge

When this worktree is the ALTERNATIVE to a primary (e.g. a maximal-regularity primary
and a Hölder/Schauder alternative): do NOT duplicate the primary's sorry-free
machinery; this worktree's value is INDEPENDENCE + library byproducts (a Schauder
estimate, a C^{k,α} Banach structure are library wins regardless of which route
reaches the headline). Mothballing-as-dead deletes reusable library; deep-as-mothball
abandons a viable path; dead-as-deep burns cycles on a false node — confusing the
three categories wastes the most.

---

## §0undecim — pre-dispatch certificate

A run's most expensive failures are structurally-foreseeable DOOMED dispatches the
orchestrator could predict in MINUTES but instead spent a full deep dispatch (tens of
minutes, ~150–250k tokens) to discover. Real run: dispatched "close POSIT-1 via C3"
without reading C3's real signature — `contDiff_integral_fiberInner_of_jointContMDiffOn`
is whole-`ℝ` (despite the `On` in its name), but the goal/source is `Set.Icc 0 T`-only,
so the named brick could not serve. A name is not a fit; the signature is. A run lost
~5–6 deep dispatches to foreseeable DOOMED statements.

---

## §3 — why agent reports are untrusted (the comment-free library)

A real batch once had 8 of 15 agents claim PROVEN with clean axioms while disk showed
ZERO changes (phantom writes). An agent declared a headline conjunct false; a scoping
researcher then dissolved it — the conjunct was true, the agent mis-attributed a
cancelling term.

All docstrings/comments were stripped library-wide precisely because they
MASSIVELY misled agents: stale "body is `sorry`" claims (the Moser tame product was
PROVED while its docstring still said sorry), aspirational FALSE mathematics (the
readoff "pure order-0", POSIT-A "∀T≤1 in-ball"), and mis-stated routes. The library is
now CODE-ONLY; naming + the elaborated statement carry intent; the ground truth is the
code + `#print axioms`, never prose.
