# Outdated Generated Routing Archive

These files are intentionally removed from active repo surfaces because they
advertise obsolete paths or unsafe tool routes.

Reasons archived:

- stale `/home/goutev/auto` workspace instructions;
- direct `ws://localhost:1956` / ChatGPT-Connect bridge instructions;
- standalone `gepa_optimizer.py` prompt mutators superseded by
  `tools/infra/socratic_oracle_prompt_gepa.py` and
  `tools/quality/oracle_prompt_regression_gate.py`;
- generated "zero debt" Cocycle Complex summaries with stale theorem counts;
- direct API scripts that read `.DEEPSEEK_API_KEY` instead of using the guarded
  oracle lane.

Current authority:

- `AGENTS.md`
- `docs/CANONICAL_AGENT_PIPELINE.md`
- `docs/AICLAW_CHATGPT_REVIEW_RUNBOOK.md`

Current ChatGPT/aiClaw route:

```bash
python3 tools/infra/aiclaw_chat.py status
python3 tools/infra/aiclaw_chat.py queue-status --platform chatgpt
python3 tools/infra/socratic_clawbot.py --file <owner-file> --theorem <name> --dry-run --json
```

Do not restore these files to active docs, tools, or scripts without updating
them to the canonical pipeline first.
