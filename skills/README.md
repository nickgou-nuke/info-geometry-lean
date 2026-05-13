# 🐝 Hive Agent Skills

This directory contains specialized skills for the InfoGeometry proving swarm.

## Agent to Skill Mapping

| Agent | Role | Primary Skills | Purpose |
| :--- | :--- | :--- | :--- |
| **RetrieverBee** | Context | `premise_retriever.md` | Finds relevant Mathlib lemmas and local dependencies. |
| **SocratesBee** | Formalizer | `formalizer_loop.md`, `state_chain_formalizer.md` | Translates informal claims to Lean 4 and manages proof state chains. |
| **PauliBee** | Prover | `vibe-validation`, `lean-proof` | Executes iterative proof generation and validation (zero-sorry goal). |
| **AuditBee** | Validator | `replay_auditor.md`, `pauli-auditor` | Verifies build integrity and replays proof traces for certification. |
| **PromotionBee** | Librarian | `statement_compiler.md`, `reference_preserver.md` | Manages the transition from exploration to authoritative L0/L1 code. |
| **BuildBee** | Infrastructure | `mathlib-build`, `lean-setup` | Ensures the local toolchain is consistent and Mathlib caches are primed. |

## Audit Workflow

To perform an extensive audit of the repository, follow this sequence:

1. **Topological Refresh**:
   ```bash
   lake script run dagAll
   ```
2. **Axiom/Sorry Stratification**:
   ```bash
   python3 tools/infra/generate_sorry_equivalence.py --md-out reports/audit/sorry_stratification.md
   ```
3. **Policy Compliance**:
   ```bash
   python3 tools/infra/agentic_policy_lint.py
   ```
4. **Semantic Snapshot**:
   ```bash
   lake script run semanticSnapshot
   ```

## Development

When adding a new skill:
1. Create a `<skill_name>.md` or a subdirectory with `SKILL.md`.
2. Add the agent mapping to this README.
3. Verify the skill against the current Pauli Mandate.
