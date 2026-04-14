# Codex CLI Troubleshooting

This note tracks operational fixes for Codex CLI issues that can interrupt
repo work even when Lean/tooling code is correct.

## Remote Compact Error: `prompt_cache_retention`

### Symptom

```text
Error running remote compact task: {
  "error": {
    "message": "Unknown parameter: 'prompt_cache_retention'.",
    "type": "invalid_request_error",
    "param": "prompt_cache_retention",
    "code": "unknown_parameter"
  }
}
```

### Meaning

This failure comes from Codex's remote auto-compaction path, not from
`tools/infra` pipeline payloads in this repository.

### What Was Verified (2026-04-14)

- Repo-side Gemini wrappers were hardened to strip passthrough args containing
  `prompt_cache_retention`:
  - `tools/infra/injection_capture_gemini_cli.py`
  - `tools/infra/gemini_account_adapter.py`
- Both wrappers compile and sanitize correctly in local smoke checks.
- Codex still emitted the same compact failure even with:
  - `enable_request_compression = false`
  - `codex features list` showing
    `enable_request_compression       stable             false`
- `~/.codex/log/codex-tui.log` confirms repeated
  `codex_core::compact_remote` failures against
  `/backend-api/codex/responses/compact` with
  `Unknown parameter: 'prompt_cache_retention'`.

Interpretation: repository scripts are protected, but this specific compact
failure is external to this repo.

### Mitigation

1. Start a fresh Codex thread/session (recommended for long conversations).
2. Run Codex with a high auto-compact threshold:

```bash
codex -c model_auto_compact_token_limit=1000000000
```

Optional checks:

```bash
codex features list | rg enable_request_compression
rg -n "compact_remote|prompt_cache_retention" ~/.codex/log/codex-tui.log
```

### Legacy Toggle (May Not Resolve This Path)

You can still toggle request compression:

```bash
codex --disable enable_request_compression
codex features disable enable_request_compression
```

but this setting can already be `false` while the remote compact endpoint still
fails with `prompt_cache_retention`.

### Restore Prior Feature State

```bash
codex features enable enable_request_compression
```

### Notes

- This is orthogonal to repository Lean proofs and DAG reports.
- If persistent feature toggles cannot write `~/.codex/config.toml` due to
  sandbox restrictions, run them in an unsandboxed shell.
