# Markdown corpus governance

> Status: `current authority`
> Source reviewed: 2026-11-03 at `214f7bcf733eaf4720913bc2c082936f2480d3fc`.
> Scope: documentation ownership, evidence, and historical status. This is not
> a certification of every document linked from the maintained index.

## Maintained authority and topic guides

The maintained operational entry points are the root
[README](../README.md), [AGENTS.md](../AGENTS.md),
[documentation map](README.md), [getting-started guide](GETTING_STARTED.md),
and [canonical pipeline](CANONICAL_AGENT_PIPELINE.md). Subsystem guides provide
local routing and must identify their actual code owners. A link from the index
does not certify every statement in the destination.

Source and recorded verification determine implementation and proof status.
Documentation specifies intended workflow and explains results. Generated
reports and transcripts remain evidence with their own provenance.

## Protected history

Do not rewrite `docs/black_books/`, `docs/black_books_refactor/`, or vendored
dependency trees during a documentation cleanup. Preserve research input and
historical reports. When a historical note is used for current navigation,
add a clearly scoped status note or maintained index entry rather than
silently treating its proposed mathematics as accepted source.

## Status vocabulary

| Status | Meaning |
|---|---|
| `current authority` | Maintained operational policy or entry map |
| `maintained local guide` | Source-backed guidance for a specific subsystem |
| `reference memory` | Topic notes requiring source review before use |
| `generated/historical report` | Evidence from a particular run or revision |
| `archival reference` | Preserved provenance rather than current guidance |
| `historical handover` | Work-session history with an explicit date and scope |
| `workflow-local reference` | Guidance specific to one configured workflow |

A status label is not a proof. Record a reviewed source revision and the
review's scope. Keep the date a document was generated separate from the date
its claims were compared with source. A link repair alone does not justify
changing a document's semantic-review date.

## Mathematical feature records

For each maintained feature claim, state:

1. The mathematical carrier and operations.
2. The exact owner and declaration name.
3. The hypotheses, including any supplied witness or assumed interface.
4. The conclusion and any separately proposed interpretation.
5. Relevant imports or consumers.
6. The reviewed revision and any compilation/axiom-audit evidence.

Distinguish definitions, conditional results, constructed witnesses, and open
bridges. Compatible cones, colimit universal properties, analytic completions,
and spectral conclusions are separate claims. A source scan and a completed
kernel check must not be reported as interchangeable evidence.

## Existing documentation tools

The repository already has documentation and inventory tools:

- [Repository surface index](../tools/infra/reports/generate_repository_surface_index.py)
- [Markdown corpus classifier](../tools/infra/reports/classify_markdown_corpus.py)
- [Markdown hygiene report](../tools/infra/reports/generate_markdown_hygiene_report.py)
- [Generated documentation](../tools/docs/generate_auto_docs.py)
- [Documentation refresh orchestration](../tools/docs/update_repo_docs.py)
- [Legacy status refresher](../tools/docs/refresh_markdown_status.py)

Use reports as review inputs. Inspect options and prerequisites before running
generators: documentation refresh can invoke compiler/graph operations and is
subject to the shared build discipline.

At the reviewed revision, `refresh_markdown_status.py` hardcodes the audit date
`2026-05-02` and classifies several old root paths. It must not be used to stamp
a newly reviewed authority surface without first updating and reviewing its
classification/date behavior. Its generated labels do not establish semantic
review. The [dated source audit](DOCUMENTATION_SOURCE_AUDIT_2026-11-03.md)
records this outstanding tooling limitation.

## Review requirements for documentation changes

- Check relative file links from the containing document, including links in
  repeated headers. Keep external/local-only references explicitly labeled.
- Check commands against their actual argument parsers, target declarations,
  working-directory requirements, and optional configuration.
- Record validation scope. Do not turn a narrow successful run into a whole
  repository claim or an infrastructure failure into a theorem failure.
- Date generated statistics and CI observations. Avoid copying floating counts
  into several maintained guides.
- Keep useful historical content; give the small maintained surface accurate
  current routing and explicit proof boundaries.
