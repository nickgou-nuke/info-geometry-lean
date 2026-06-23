# Free Claude Code Pinned Review

Reviewed upstream:

```text
repo: https://github.com/Alishahryar1/free-claude-code
commit: b2af3f63d20a29e1a0ebfbceec048b0f59668b49
package version: 2.3.6
date reviewed: 2026-06-18
```

## Verdict

Use only through the pinned wrapper:

```bash
scripts/install_free_claude_code_pinned.sh
```

Do not use the upstream `curl | sh` installer in this repository workflow. The
upstream installer is straightforward, but it is broader than needed: it can
install or update Claude Code, Codex, uv, Python 3.14, and the FCC tool from a
moving Git branch.

## What It Does

Free Claude Code is a local provider proxy. It exposes Anthropic-compatible
routes for Claude Code and OpenAI Responses-compatible routes for Codex, then
routes requests to configured providers such as OpenRouter, Gemini, DeepSeek,
Groq, local Ollama, LM Studio, and others.

The reviewed commit has both launchers:

```text
fcc-claude -> cli.entrypoints:launch_claude
fcc-codex  -> cli.entrypoints:launch_codex
```

`fcc-claude` starts the real `claude` binary with `ANTHROPIC_BASE_URL` pointing
at the local proxy. `fcc-codex` starts the real `codex` binary with ephemeral
Codex config for the local proxy's `/v1/responses` endpoint and strips official
OpenAI credentials from the child environment.

## Risks And Mitigations

- The upstream installer installs from a moving branch. The local wrapper pins
  the exact commit in the `uv tool install` spec.
- The upstream installer can install or update global tools. The local wrapper
  requires `uv`, `python3`, `claude`, and `codex` to already exist.
- The upstream config template binds the server broadly unless configured. The
  local wrapper writes `HOST="127.0.0.1"`.
- The upstream config template enables local web server tools. The local wrapper
  writes `ENABLE_WEB_SERVER_TOOLS=false`.
- FCC structured trace logs can contain conversation text. Treat `~/.fcc/logs`
  as sensitive, keep raw logging flags disabled, and do not commit those logs.
- The generated `ANTHROPIC_AUTH_TOKEN` protects the local proxy. Keep
  `~/.fcc/.env` private.

## Commands

Install pinned FCC:

```bash
scripts/install_free_claude_code_pinned.sh
```

Start the proxy:

```bash
scripts/fcc_server_local.sh
```

Start the proxy and open the provider setup UI:

```bash
scripts/fcc_server_setup.sh
```

Run Claude through FCC:

```bash
scripts/fcc_claude_local.sh
```

Run Codex through FCC:

```bash
scripts/fcc_codex_local.sh
```

These wrappers force `HOST=127.0.0.1`. This matters in conda/Sage shells where
`HOST` can be exported as a build triple such as `aarch64-conda-linux-gnu`,
which overrides `~/.fcc/.env` and causes Uvicorn name-resolution failure.

The pinned config defaults to `MODEL="open_router/openrouter/free"` but does not
write an OpenRouter key. If OpenRouter returns HTTP 401 with `Missing
Authentication header`, configure `OPENROUTER_API_KEY` in the Admin UI or switch
`MODEL` to a provider that does not need a remote key, such as a local Ollama or
LM Studio model.

After FCC is installed and `fcc-server` is running, Claude can delegate to
Codex-through-FCC by changing the project MCP server command from `codex` to
`scripts/fcc_codex_local.sh` with the same `["mcp-server"]` args.
