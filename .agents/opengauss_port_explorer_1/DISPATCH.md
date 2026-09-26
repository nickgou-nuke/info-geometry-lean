## 2026-09-21T19:40:20Z
You are an Explorer investigating the repository for the OpenGauss Native Antigravity Plugin Port project.
Your mission is strictly read-only exploration and analysis. Do NOT modify any files.

Repo root: /home/goutev/info-geometry-lean

Please investigate and report in detail on the following:
1. OpenGauss slash commands & workflows:
   - Search the codebase for the 9 OpenGauss slash commands/workflows. What are the names, roles, instructions, and prompt templates of all 9 commands? (Check `gauss_cli`, `.opengauss`, `tools/`, `scripts/`, or anywhere in the repo).
2. `lean-lsp-mcp`:
   - Where is `lean-lsp-mcp` located in the repo? What files implement it (e.g. in `tools/lean-lsp-mcp`, `external/`, etc.)?
   - Where is the OpenGauss virtual environment (`venv/bin/python`)? Does it exist at `venv/bin/python` or elsewhere? What python packages/binaries are installed there?
   - How is `lake env` invoked with the MCP server, and how should `mcp_config.json` be configured?
3. Antigravity Plugins and Custom Subagents:
   - Inspect `.agents/` and `.agents/plugins/`. Does `.agents/plugins/opengauss/plugin.json` exist? Are there any other existing plugins or plugin schemas in the repository or Antigravity app data (`/home/goutev/.gemini/antigravity-cli`)?
   - How are custom subagents and plugins defined in Antigravity? What is the schema of `plugin.json`?
4. Existing test scripts:
   - Check if `scratch/test_opengauss_workflows.py` and `scratch/test_mcp_connection.py` exist. If so, what do they contain? If not, what tests need to be created?
   - Check Lean version, lake version (`lean --version`, `lake --version`), and git head.
5. Critical repository rules:
   - Check `AGENTS.md` and `tools/infra/run_locked_lake_build.py`.

Please return a comprehensive report detailing your findings.
