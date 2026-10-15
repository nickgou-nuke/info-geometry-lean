# /prove — the recurring false-as-stated TRAP CATALOG (§0bis)

> AUDIENCE: the `lean-refuter` (statement-lint + headline check + birth-probe) and
> every `lean-worker` authoring a child signature. This is the §0bis trap catalog,
> the EXACT defect classes that have slipped past reading-based audits and surfaced
> in fill. The Stage-1 headline check and the Stage-2 statement-lint screen every
> critical / leaf signature against this catalog (one shot, at signature birth). The
> fill proof attempt is the backstop. War-story detail lives in prove-RATIONALE.md.

These are the EXACT defect classes that have slipped past reading-based
audits and surfaced in fill.

- **T1 — raw chart-coordinate / chartJ extraction.** A signature that
  asserts continuity / differentiability of a RAW `M → E` projection
  (`(triv …).symm x (basis)`, `coordChange`, a fibre value pulled to `E`)
  is generically FALSE on multi-chart manifolds: the preferred-chart index
  `achart x` JUMPS as `x` moves (chartJ is genuinely unbounded on S²). The
  total-space SECTION is continuous; the raw E-coordinate is not. **FIX:**
  state it intrinsically — total-space section / `g`-inner pairing — never
  extract `M → E`. (KEY DISTINCTION — do NOT blanket-exempt
  `extChartAt`/`chartRawRepr`: a fixed-chart `extChartAt I α` form is chartJ-
  SAFE only if the charted point is **PINNED at the basepoint `α`**. If the
  argument is a MOVING point — an orbit `Φ s x`, a curve, any `y` that leaves
  `α` — then `mfderiv (extChartAt I α) y = coordChange (achart y) (achart α) y
  ≠ id` off-basepoint, and the raw integrand / derivative is FALSE off-basepoint
  exactly like the `coordChange`/`achart` case. **This was the md3 headline
  defect — the single thing the whole 7-round run hinged on catching, so the
  carve-out must NOT clear it.** Litmus: does the chart argument stay `= α`, or
  travel? If it travels, **T1 FIRES** — restate with the explicit
  trivToE/coordChange chart-transition factor, or intrinsically.)
- **T2 — free-family quantifier.** A statement quantifying over a family /
  data argument (`Vpush`, `Cmet`, `g_DT`, `Φ_fam`, `u`, …) with NO hypothesis
  tying it to the object it denotes — a counterexample family satisfies the
  binders but breaks the conclusion. **FIX:** add the tying hypothesis
  (usually the exact one a sibling already carries — name the sibling).
- **T2′ — `∃…∀…` where uniqueness forces `∃` innermost.** `∃ V, ∀ t, HasFDeriv… V … t`
  is FALSE when the within-derivative is the UNIQUE Fréchet derivative and
  varies with `t`. **FIX:** move `∃` innermost: `∀ t, ∀ x, ∃ V, …`; mirror
  the sibling's already-correct shape.
- **T3 — `HasLocallyConstantChartAt` / locally-constant-chart / global-
  flatness hypothesis.** Mathematically FALSE on normal manifolds (S²); a
  HARD prohibition, fully deleted from the library. GREP TRAP: the string
  survives in ~dozens of docstring DISCLAIMERS with ZERO uses — verify
  def/binder vs disclaimer before believing any "still used" claim. Never a
  public-signature hypothesis.
- **T4 — vacuous binder.** A hypothesis trivially satisfiable / saying
  nothing (inner product against the zero vector; continuity of a constant;
  `∀` over an empty index; a regularity hypothesis the type already
  guarantees). **FIX:** remove or replace with the real constraint.
- **T5 — headline-leak.** An internal node may carry a validity-domain /
  scale / fibre-small / finite-support hypothesis IF it is dischargeable AND
  non-leaking. It LEAKS when the same hypothesis is forced onto the HEADLINE
  signature (e.g. fibre-smallness that only holds for `g_bg = g₀` leaking to
  a general-`g_bg` headline). **FIX:** discharge it internally, or restate
  the headline (STOP-to-user if the headline must change).
- **T6 — hypothesis-packaging** (the single most severe violation). A
  hypothesis whose type is (defeq to) the conclusion, returned as the proof.
  FORBIDDEN everywhere; auto-revert + LIED. (See §Prohibitions in prove-PROTOCOL.md.)
- **T7 — family-as-INPUT that should be existential-OUTPUT.** A re-
  parameterisation that turns an existentially-produced object (`repr`,
  `Nsec`) into a free universal INPUT falsifies it (`repr ≡ 0`
  counterexample). **FIX:** keep it an existential output, or pin it with the
  identity the producer guarantees (`∀ u, … repr u … = … deTurckRemainderSection g₀ u …`).
- **T8 — per-fibre vs joint.** `∀ x, ContinuousOn (fun s => f s x) …` (per-
  fibre) does NOT give `ContinuousOn (fun (s,x) => f s x) …` (joint).
  Separate continuity ⇏ joint continuity (`xy/(x²+y²)`). **FIX:** state and
  prove the joint form (uniform-in-`x` approximation + time-continuity).
- **T9 — two-sided vs one-sided on an interval.** On-disk diffeo / flow
  families are `= id` outside `(0,T)` and JUMP at the endpoints, so a
  `∀ t : ℝ` TWO-sided `HasMFDerivAt` is UNSATISFIABLE. **FIX:** restate
  within-interval one-sided (`HasDerivWithinAt … (Ici 0)` / `Ioo 0 T`).
- **T10 — C∞-at-0 over-demand.** A field only CONTINUOUS at `t=0` (not C∞;
  `√s` has `∂ₛ → ∞`) breaks any clause demanding flow-/coefficient-C∞ up to 0.
  **FIX:** interior `ContDiffOn (Ioo)` + up-to-0 `ContinuousOn (Ico)`; use a
  bounded-coefficient (norm-bound, not differentiability) Grönwall endpoint
  argument for `t=0` continuity. (Generalised: a FINITE-order time-regularity
  hypothesis can NEVER carry a C∞/all-order-in-time conclusion — a continuous-but-
  not-C¹ forcing makes the all-order time tower FALSE; demand only the order the
  consumer uses.)

The next classes are the SEMANTIC ones the reading-lint historically PASSED and
fill then caught as restatements (each appears in the recorded run lessons). The
lint flags the obvious instances, but their reliable certifier is the §0qua
**birth-probe** (a Lean-running refute-or-reduce), NOT reading — treat a lint
PASS on these as provisional until the posit is consumer-minimal and probed.

- **T11 — over-strong / aesthetic / non-tensorial posit (the DOMINANT restatement
  driver).** A posited child stated stronger than its parent consumes: STRICT or
  SEPARATED where only a **SUM** bound holds; **POINTWISE** where only
  **INTEGRATED** holds; **PER-CLASS / PER-DIRECTION** where only the **summed
  whole-tensor** cancels (the per-piece split is individually false — the
  cancellation is a property of the whole tensor); **separated** where only
  **joint** holds. **FIX:** posit the consumer-minimal weakening (§0qua A) —
  ideally by glue-first extraction of the exact consumed shape; if it slipped
  through, the birth-probe returns OVER-STRONG with the weaker provable form.
- **T12 — ∃-freedom checked per-conjunct instead of jointly.** An `∃ w, P₁ w ∧
  … ∧ Pₙ w` posited as "satisfiable because each `Pᵢ` alone leaves `w` free" —
  but the conjuncts JOINTLY pin `w` (real run: bounds (3)+(4) jointly forced the
  witness to an `∇²S`-order remainder that no construction supplies, while each
  alone looked free). **FIX:** check ∃-freedom against ALL conjuncts jointly
  (birth-probe); if jointly pinned to an unconstructible object, the posit needs
  the missing producer as a child, or a weaker conclusion.
- **T13 — all-order single-constant (order-dimension) vacuity/falsity.** `∃ c, ∀
  k, ‖∇ᵏ…‖ ≤ c · …` with ONE constant `c` over a quantity that GROWS in `k` is
  unsatisfiable (`sup_k‖∇ᵏR‖ = ∞` generically) — yet it passes a lint that only
  checks the `k=0` instance. **FIX:** index the bound by order (`c : ℕ → ℝ`), or
  state only the finite order range the consumer reads (often just `k=0`); the
  birth-probe checks the all-`k` dimension, not just `k=0`.
- **T14 — authority-name as confidence / skip-derivation (a DERIVATION trap, not a
  statement-shape trap; the lint cannot catch it mechanically — it is orchestrator +
  reading discipline).** A claim or proof-sketch that leans on an authority name
  ("this is Chow–Knopf's well-studied parabolic regularity", "classical Lieberman
  estimate", "standard", "well-known") to inflate confidence or to SKIP the
  derivation. Two distinct failures, both common: (a) **skip-license** — "it's
  classical" substitutes for building the proof (a defer in disguise; §0ter forbids
  it — the node must be PROVED or posited-and-recursed, the authority is not a
  proof); (b) **misattribution** — the authority is cited for a result it does NOT
  prove (it ASSUMES / black-boxes it). Canonical case: Chow–Knopf *black-boxes*
  parabolic short-time existence (it cites standard PDE theory for STE — "the black
  box this route opens"); claiming "Chow–Knopf does the parabolic STE" is doubly
  wrong. **RULE:** an authority name is a ROUTING HINT (it points to the textbook
  route/mechanism) and at most a WEAK truth-signal (a standard-book result is
  plausibly true, worth attempting) — NEVER a proof and NEVER a license to skip.
  Before leaning on one: (i) verify what it ACTUALLY does — prove, or assume/black-
  box? (read the source, don't take the name on faith); (ii) the DERIVATION must be
  built — cite the specific MECHANISM (§0quin P3) + prove/posit-recurse the node;
  (iii) a docstring or agent claim "this is the classical X" is non-evidence (§3).
  Rigorous mathematical derivation outranks every authority name.
- **T15 — DOMAIN / QUANTIFIER over-reach (the silently-FALSE over-strength; the
  DOMAIN twin of T11, enforced by §0qua A consumer-minimal DOMAIN).** A conclusion
  quantified over a LARGER domain than the hypotheses constrain: `ContDiff ℝ ∞
  (fun t => …)` (all of `ℝ`) where the data is controlled only on `Set.Icc 0 T`;
  `∀ t, …` where only `∀ t ∈ Set.Icc 0 T` is fed; a UNIFORM `∀ n, … ≤ C` where the
  producer is small-`T` / finite-`n` only; `∀ T ≤ 1` where the estimate needs `T`
  small. Unlike T11 (over-strong SHAPE — strict vs sum, pointwise vs integrated),
  this is over-strong DOMAIN, and it is the **silently-FALSE** kind: the statement
  is FALSE for the very input the consumer feeds. Real run: a whole-`ℝ` `ContDiff`
  posited whose forcing path is a jump-extension `fun t => if t ∈ Set.Icc 0 T then
  S₀ t else 0` (hardcoded `0` outside Icc → discontinuous at the endpoint → whole-`ℝ`
  `ContDiff` impossible), while the consumer needed only `=ᵐ[timeMeasure T]` (= Icc)
  — a full deep dispatch was lost discovering this after the fact. **LINT:** for
  every produced regularity / bound / uniform constant, ask "is the conclusion's
  domain or index-range ⊆ the set the hypotheses actually constrain?" — a `∀` /
  `ContDiff` / `Continuous` / uniform-`C` over a set bigger than the hypotheses'
  set FIRES. **FIX:** restrict to the consumer's true domain (`ContDiffOn …
  (Set.Icc 0 T)`, `∀ t ∈ Set.Icc 0 T`, an order-indexed or small-`T` constant) —
  zero consumer loss when the consumer is itself domain-restricted. The birth-probe
  refuter must test the BOUNDARY / JUMP / large-argument case, not an interior point.

When the lint flags a trap: fix the on-disk signature immediately (the fix is
usually mechanical and local), then re-glue any affected parent. A flagged
signature is NOT a STOP unless the fix forces a HEADLINE restatement.

**The lint RE-ARMS on binder change — it is not a one-time-at-birth screen.**
Any edit that adds or FREES a family/data binder (`repr`, `Nsec`, `u`, `Φ`,
`T_s`, `g_DT`, …) on an existing signature — a glue SIGNATURE-DEFECT fix
(Stage 2.5), a Stage-3 local re-entry (Stage 3.6), a re-parameterisation —
**re-runs the §0bis screen on EVERY signature whose binder list changed since
its last `CLEAN` lint**, not only at first materialisation. This is exactly how
a free-family-input defect (T7) was once BORN: an existing signature was re-
parameterised mid-descent so a produced object became a free universal INPUT;
the lint had run at birth, the defect arrived later, and two reading-audit
rounds then missed it. Re-arming on binder change closes that hole.
