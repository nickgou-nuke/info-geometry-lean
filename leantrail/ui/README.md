<!-- repository-context-rule -->
> **Repository grounding:** For repository work, the checked-out codebase is
> the context. Search existing implementation and trace its real definitions,
> imports, instances, theorems, and uses before declaring a structure missing
> or incorrect. A finding in one file is not a repo-wide finding. See
> [`docs/REPO_DEEP_SEARCH_PROTOCOL.md`](docs/REPO_DEEP_SEARCH_PROTOCOL.md).

# LeanTrail UI (MVP Stub)

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Not part of the maintained authority surface unless explicitly promoted.
> See: [README.md](../../README.md), [docs/README.md](../../docs/README.md), [docs/CODEBASE_STATUS.md](../../docs/CODEBASE_STATUS.md)

This folder is reserved for the Sourcetrail-style frontend.

Initial target panels:

- graph panel
- code panel
- proof-state panel
- diagnostics panel

`index.html` is a placeholder surface that can be wired to the HTTP API.
