<!-- repository-context-rule -->
> **Repository grounding:** For repository work, the checked-out codebase is
> the context. Search existing implementation and trace its real definitions,
> imports, instances, theorems, and uses before declaring a structure missing
> or incorrect. A finding in one file is not a repo-wide finding. See
> [`docs/REPO_DEEP_SEARCH_PROTOCOL.md`](../../docs/REPO_DEEP_SEARCH_PROTOCOL.md).

# Alexandria Docker & Environment Configuration (`configs/alexandria/`)

> Status: `maintained local guide`
> Source reviewed: 2026-11-24 at commit `9bbab55c38`.
> See: [tools/alexandria/README.md](../../tools/alexandria/README.md), [docs/alexandria/README.md](../../docs/alexandria/README.md), [skills/alexandria-pipeline/SKILL.md](../../skills/alexandria-pipeline/SKILL.md), [docs/CANONICAL_AGENT_PIPELINE.md](../../docs/CANONICAL_AGENT_PIPELINE.md), [docs/ArangoDB_Management.md](../../docs/ArangoDB_Management.md)

This directory holds Compose definitions and environment templates for running isolated ArangoDB instances dedicated to the Alexandria literature and PDF-to-DAG-brain retrieval lane (`retrieval_context_only`).

## Files

| File | Role | Notes |
|---|---|---|
| [`docker-compose.pdf.yml`](docker-compose.pdf.yml) | **Preferred** Compose stack (`name: alexandria_pdf`, `arangodb:3.12`) | Parameterized container name, port (`127.0.0.1:${ALEXANDRIA_ARANGO_PORT:-8532}:8529`), and persistent volumes for running either the default `:8532` store or dedicated isolated brains |
| [`docker-compose.yml`](docker-compose.yml) | Legacy single-service Compose file (`container_name: arango_alexandria`) | **Caution:** On the maintainer workstation, `arango_alexandria` is bound to port `8530` (the Lean Declaration/InfoTree DAG lane). Do **not** start this alongside or confuse it with `:8532` / `:8538` PDF instances |
| [`.env.example`](.env.example) | Default non-secret Alexandria configuration template | Sets `ALEXANDRIA_ARANGO_PORT=8532`, `ALEXANDRIA_ARANGO_DB=alexandria`, `ALEXANDRIA_ARANGO_USERNAME=root`; copy to local `.env` and supply password locally without committing secrets |

## Environment Variable Precedence & Guardrails

Implemented in [`src/igf/config/env_aliases.py`](../../src/igf/config/env_aliases.py) (re-exported via [`tools/infra/arango_env.py`](../../tools/infra/arango_env.py)):

1. **Explicit CLI flags** (`--endpoint`, `--database`, `--username`, `--password`) override everything else.
2. **Pre-set shell environment variables** take precedence over `.env` files — `load_alexandria_arango_env()` never overwrites already-set `ALEXANDRIA_*` variables.
3. **`ALEXANDRIA_ARANGO_ENV_FILE`** (or default `configs/alexandria/.env`) supplies defaults when shell vars are unset.
4. **Port-only shortcut**: setting `ALEXANDRIA_ARANGO_PORT=8538` without `ALEXANDRIA_ARANGO_ENDPOINT` automatically resolves to `http://127.0.0.1:8538`; when no explicit `ALEXANDRIA_ARANGO_DB`/`..._DATABASE` is set, that port now defaults to `alexandria_dag_brain`. Port `8532` keeps the default database `alexandria`. Explicit endpoint/database overrides always win.
5. **Strict lane isolation**:
   - Alexandria loaders do **not** read or mutate generic `ARANGO_*` or `HIVE_*` variables.
   - `guard_alexandria_target(endpoint, database)` raises `ValueError` (and Alexandria CLIs exit with code `2`) if targeting forbidden ports `{8530, 8540}` or forbidden databases `{"infogeometry", "darwin_commits", "hive_live", "aiclaw_auto_rag"}`.

## Compose Variables (`docker-compose.pdf.yml`)

| Variable | Default in `docker-compose.pdf.yml` | Purpose |
|---|---|---|
| `ALEXANDRIA_ARANGO_CONTAINER` | `arango_alexandria_pdf` | Docker container name |
| `ALEXANDRIA_ARANGO_PORT` | `8532` | Loopback host port (`127.0.0.1:<port>:8529`) |
| `ALEXANDRIA_ARANGO_DATA_VOLUME` | `alexandria_pdf_arango_data` | Named Docker volume for `/var/lib/arangodb3` |
| `ALEXANDRIA_ARANGO_APPS_VOLUME` | `alexandria_pdf_arango_apps` | Named Docker volume for `/var/lib/arangodb3-apps` |
| `ALEXANDRIA_ARANGO_PASSWORD` | falls back to `ARANGO_ROOT_PASSWORD`, then `alexandria_root` | Initial Arango root password on fresh volume creation |

### Launching the Default `:8532` Instance

```bash
docker compose -f configs/alexandria/docker-compose.pdf.yml up -d
```

### Launching a Dedicated Isolated Instance (Example: `:8538` / `alexandria_dag_brain`)

Use distinct `-p` project name, container name, port, and volume names so multiple Alexandria corpora stay physically isolated:

```bash
ALEXANDRIA_ARANGO_CONTAINER=arango_alexandria_dag \
ALEXANDRIA_ARANGO_PORT=8538 \
ALEXANDRIA_ARANGO_DATA_VOLUME=alexandria_dag_brain_data \
ALEXANDRIA_ARANGO_APPS_VOLUME=alexandria_dag_brain_apps \
docker compose -p alexandria_dag_brain -f configs/alexandria/docker-compose.pdf.yml up -d
```

Never print or commit `.env` passwords in prompts, docs, or command logs.
