# Hermes Topic Deep-Research Enrichment Template

You are running the verification/enrichment lane for a repo-topic audit.

## Inputs
- TOPIC: <TOPIC>
- ALIASES: <ALIASES>
- GEMINI_OUTPUT: <paste Gemini output>
- OWNER_ANCHORS: <paste candidate file + declaration anchors>

## Task
1. Validate or reject each hypothesis against concrete owner anchors.
2. Classify each concept using exactly one label:
   - implemented
   - interface
   - missing
   - docs-only
   - speculative
3. Produce contradiction notes where naming suggests stronger claims than implementation.
4. Emit a compact verification plan for unresolved items.

## Output format (strict)
- `verified_rows`: table-like bullets with concept, status, anchors, note
- `rejected_hypotheses`: bullet list
- `naming_vs_owner_mismatches`: bullet list
- `verification_plan_next`: numbered list

No row may be labeled `implemented` without at least one owner theorem/definition anchor.
