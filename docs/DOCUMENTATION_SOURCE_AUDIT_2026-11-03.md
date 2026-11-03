# Documentation/source reconciliation — 2026-11-03

> Status: `generated/historical report`
> Review date: 2026-11-03 in Europe/Sofia (2026-11-02 UTC).
> Audited base: [`214f7bcf733eaf4720913bc2c082936f2480d3fc`](https://github.com/nickgou-nuke/info-geometry-lean/commit/214f7bcf733eaf4720913bc2c082936f2480d3fc).
> Scope: source inspection, documentation links and commands, and recorded
> GitHub workflow outcomes. No fresh full Lean build or local pre-push/post-build
> quality gate was run for this review.

## Method and coverage

The audit used the tracked Git tree, blob-verified source contents, and the
GitHub comparison from the preceding local baseline to the audited commit.
The main code and documentation surfaces were available at that revision;
unavailable archival/vendor copies were not treated as absent from Git.

The tracked inventory contained 2,822 Markdown files (`.md` and `.MD`), including
33 at the root and 1,210 under `docs/`. Relative-link scanning covered 1,279 root, documentation,
and selected README files. Semantic review focused on the principal agent
instructions, README claims, cited Lean owners, operational scripts, and
build configuration. This was not an exhaustive semantic audit of every
historical transcript or every theorem.

The existing
[repo_lean_scope_audit.scan](../tools/quality/repo_lean_scope_audit.py) function
was applied to all 16,262 tracked `.lean` files under `lean/InfoGeometry/`.
It returned zero `sorry`, `admit`, or `axiom` findings in that scope. This is a
lexical scan using the repository's comment/string filtering, not a compiler
or transitive axiom audit. Outside that scope, the
[Pauli negative tests](../tests/lean/InfoGeometry/Lint/PauliTest.lean) deliberately
exercise `sorry`, and recovered material retains proof debt.

## Mathematical corrections and scope

| Base-document issue | Source evidence and documentation response |
|---|---|
| Universal grade-generator A60 used the wrong signs | [CyclotomicBridge](../lean/InfoGeometry/OperatorAlgebra/PeirceSpine/CyclotomicBridge.lean) proves reflection difference `-J - 2Σ` and the `hProjSig` coefficient `-16`, under `[Ring B]` and idempotence of `P`. The transcript's matching formulas are corrected and its historical role is explicit. |
| README described three broader NCG bridges | [Stabilizer](../lean/InfoGeometry/NCG/GunaydinGurseySU3Stabilizer.lean), [Cuntz shift](../lean/InfoGeometry/NCG/CuntzHoppingCantorLattice.lean), and [finite Lax data](../lean/InfoGeometry/NCG/LaxPairIsospectralMassGap.lean) are now summarized by their actual declarations. |
| Global continuum language conflated construction levels | Documentation distinguishes compatible cones, diagonal cylinder models, full-matrix algebraic limits, categorical colimits, and additional analytic conclusions. Actual [matrix](../lean/InfoGeometry/Clifford/Cl11TensorTowerLimit.lean) and [categorical Zorn](../lean/InfoGeometry/Categorical/ZornUHFColimit.lean) owners remain credited. |
| General-ring coefficients were described as scalar spectra | The [double-commutator owner](../lean/InfoGeometry/OperatorAlgebra/SquareZeroPairSpectral/InnerDerivationSpectra.lean) retains operator coefficients. Spectral interpretations require separately stated scalar-action, representation, nonvanishing, and analytic hypotheses. |
| New noncommutative results were hard to discover | The README and operator guide now expose tripotent parity, chiral kernel restriction, operator RPA blocks, and operator-weighted phonon commutators. |
| Old subsystem summaries claimed complete realizations | E8, Peirce ladder, Bost–Connes, and mirror summaries now state their local owner scope and separate historical motivation. The findings do not assert that stronger related mathematics is absent elsewhere. |

`README-CURRENT.md` remains a topic-specific CAR/Krein/projectivization note.
The newly merged kernel restriction assumes anticommutation, tripotence, and
involutivity; it does not construct a nonzero kernel vector or derive a
Majorana zero mode from CAR alone. The documentation preserves that distinction.

## Baseline workflow evidence

These completed runs are evidence about the audited base, not a prediction
about subsequent commits or the result of a build performed in this audit:

| Workflow | Observed outcome |
|---|---|
| [CI](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/41230458822) | Failed at `Validate local Lake package checkouts`; `Baseline build` was skipped. |
| [Reviewed PR Integration](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/41230458879) | Checkout failed; Lean verification was skipped. |
| [Sorry Gate](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/41230458801) | Repository-wide Lean debt-audit step failed. |
| [CI bootstrap regressions](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/41230458824) | Succeeded. |

An infrastructure failure before compilation does not establish a failed
theorem. A source scan or a successful narrow workflow does not establish a
full default-target build. New status claims should identify the commit,
command, scope, environment, result, and evidence location.

## Operational reconciliation

- Root and leaf agent guides now describe portable checkout roots, actual
  source authority, scoped proof acceptance, and serialized verification.
- Examples distinguish locked file checks, named-module builds, changed-owner
  mode, umbrella imports, and all Lake default targets.
- Cache guidance preserves the prohibition on destructive cleaning while
  documenting the helper's implemented empty-cache hydration behavior.
- Service availability and graph freshness are deployment observations, not
  invariants implied by an Arango database name in prose.
- The directory-specific `proofs/AGENTS.md` replaces the unrelated personal
  assistant template; the Lake `proofs` target remains recognized.
- Nested README grounding links are resolved relative to each containing file.
  Archived root setup guides are linked as history; the maintained setup route
  is [Getting started](GETTING_STARTED.md).

## Source issues documented for separate implementation work

The documentation changes do not claim to repair these implementation or
deployment prerequisites:

1. Root Pi launcher/implementation files named by older guides are absent.
   The [Lean extension](../extensions/lean-prover-tool.ts) and
   [orchestrator extension](../extensions/agent-orchestrator.ts) reexport missing
   root implementations; adding `extensions/` to old commands is insufficient.
2. The Archon launcher requires a separately provisioned local checkout. Its
   configured root must not be silently substituted with a differently located
   reference dependency.
3. `dag-toolchain.json` is not tracked at the audited base.
   [dag_config.py](../tools/infra/dag_config.py) resolves explicit/environment/
   local/default configuration and requires the resulting configuration data.
   The experimental Lake DAG facets additionally need lock handoff when their
   refresh action runs under the locked build wrapper: source inspection
   predicts a child waiting on the outer build's lock. This was not reproduced
   by execution; the [infra guide](../tools/infra/README.md) records the chain
   and its conditions.
4. [refresh_markdown_status.py](../tools/docs/refresh_markdown_status.py) still
   hardcodes `2026-05-02` and old root-path classifications. Review that tool
   before bulk relabeling the maintained documentation.
5. The CAS E2E runner's tiers 3 and 4 include direct Lean invocations. Its fixed
   timing checks are benchmarks; its token checks do not compare elaborated
   proposition ASTs against Git HEAD. See [TEST_INFRA.md](../TEST_INFRA.md).
6. The recorded path-dependency and integration-checkout CI failures require
   separate diagnosis. Lean source, dependency pins, and workflows are not
   changed by this documentation reconciliation.

## Continuing maintenance

Use the existing [Markdown governance](MarkdownCorpusGovernance.md),
[repository surface index](../tools/infra/reports/generate_repository_surface_index.py),
and [hygiene report](../tools/infra/reports/generate_markdown_hygiene_report.py).
Keep historical evidence intact. Review the small authority surface by hand,
check its relative links and command interfaces, and attach exact source
owners and hypotheses to mathematical feature descriptions.
