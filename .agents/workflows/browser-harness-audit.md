# Workflow: Browser Harness Formal Audit

Use this workflow to perform a rigorous formal audit of a Lean 4 bridge or module using external AI collaboration (ChatGPT/Claude) via the Browser Harness.

## 1. Selection & Context Packaging
- Identify the target file (e.g., a "bridge" or "socket" implementation).
- Identify the relevant **Pauli Mandates** to audit against.
- Package the code and mandates into a markdown block for transmission.

## 2. Initialize Browser Harness
- Load the `browser-harness` skill.
- Navigate to the external auditor (e.g., `https://chatgpt.com`).
- Ensure "Temporary Chat" is enabled if privacy is required.

## 3. The Socratic Audit Loop
- **Upload**: Provide the packaged context to the auditor.
- **Prompt**: Use a Senior Formal Methods Auditor persona.
- **Query**: "Audit the following Lean 4 code against the provided mandates. Identify any 'Lyrical Overfit' or 'Symbolic Inflation'. Check for 'Genuine Witness Dependency' (Mandate IX)."
- **Extract**: Identify the auditor's specific refactoring suggestions and Mathlib-rooting proposals.

## 4. Implementation & Surgical Refactor
- Implement the refactor locally.
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
> This workflow follows the **"Bitter Lesson"**: it prioritizes direct browser-based action and external high-level reasoning over narrow tool abstractions.
