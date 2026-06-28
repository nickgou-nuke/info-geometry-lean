# Workflow: Browser Harness Formal Audit

Use this workflow to perform a rigorous formal audit of a Lean 4 bridge or module using external AI collaboration (ChatGPT/Claude) via the Browser Harness.

## 1. Selection & Context Packaging
- Identify the target file (e.g., a "bridge" or "socket" implementation).
- Identify the relevant **Pauli Mandates** to audit against.
- Package the code and mandates into a markdown block for transmission.

## 2. Initialize Guarded Browser Harness
- Prefer `tools/infra/socratic_clawbot.py` through the aiClaw queue.
- If direct `browser-harness` is unavoidable, wrap it with
  `tools/infra/chatgpt_lane_guard.py`.
- Do not use raw DOM injection or Enter-key fallback.
- Ensure "Temporary Chat" is enabled if privacy is required.

## 3. The Socratic Audit Loop
- **Upload**: Provide the packaged context to the auditor.
- **Prompt**: Use a Senior Formal Methods Auditor persona.
- **Query**: "Audit the following Lean 4 code against the provided mandates. Identify any 'Lyrical Overfit' or 'Symbolic Inflation'. Check for 'Genuine Witness Dependency' (Mandate IX)."
- **Extract**: Identify the auditor's specific refactoring suggestions and Mathlib-rooting proposals.

## 4. Implementation & Surgical Refactor
- Treat extracted suggestions as proposal-only candidate artifacts.
- Implement the refactor locally as a normal reviewed patch.
- Prefer minimal, surgical changes that preserve existing theorem statements while strengthening the mathematical logic.
- Resolve scaling or syntactic mismatches using Mathlib-canonical lemmas (e.g., `smul_ite_zero`).

## 5. Verification: Nomological Closure
- **Build**: Run `lake build <target>` to ensure zero errors.
- **Audit**: Run `#print axioms <target>` to ensure zero `sorryAx` or `admit`.
- **Verdict**: Mark the module as **CERTIFIED** only if both checks pass.

## 6. Memorization
- Load the `memorize` skill.
- Update the module-local `README.md` or the root status log.
- Record the certification date, mandate compliance, and key technical learnings (e.g., "Use `rw [← smul_ite_zero]` for scaling distribution").

---
> [!IMPORTANT]
> ChatGPT/browser-harness is an oracle-advice lane, not a source editor.
> Candidate code must be inspected, patched by the coding agent, and verified
> locally before it counts.
