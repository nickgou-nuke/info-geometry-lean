# Gemini CLI Topic Deep-Research Prompt Template

You are running the creative exploration lane for a repo-topic audit.

## Inputs
- TOPIC: <TOPIC>
- ALIASES: <ALIASES>
- RECALL_SUMMARY: <paste rg stats summary>
- CANDIDATE_FILES: <paste candidate file list>

## Task
1. Expand the conceptual map around TOPIC.
2. Propose concept buckets likely present in code under different names.
3. Generate hypothesis candidates, but mark all non-evidenced claims as `inference`.
4. Suggest Lean declaration-name patterns to search next.

## Output format (strict)
- `concept_buckets`: bullet list
- `likely_aliases`: bullet list
- `search_patterns`: bullet list of regex or keyword patterns
- `hypotheses_inference_only`: bullet list
- `evidence_gaps`: bullet list

Do not claim implementation unless an anchor file + declaration name is provided.
