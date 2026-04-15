# Copilot + Gemini/Hermes Mirror

This workflow mirrors `skills/repo-topic-deep-research` for Copilot agent discovery and
keeps the same output contract for Gemini CLI and Hermes enrichment lanes.

Use templates:
- `templates/coverage_matrix_template.md`
- `templates/context_pack_template.md`
- `templates/gemini_cli_prompt_template.md`
- `templates/hermes_enrichment_prompt_template.md`
- `templates/openai_deep_research_brief_template.md`

OpenAI Deep Research gateway:
- `tools/infra/openai_deep_research_gateway.py`

Primary source of truth remains:
- `skills/repo-topic-deep-research/SKILL.md`
