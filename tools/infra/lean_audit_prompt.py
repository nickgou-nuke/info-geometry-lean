"""Shared Lean prompt text with explicit audit-vs-repair lane separation."""

from __future__ import annotations

from collections.abc import Mapping
import re


ANTI_CONFABULATION_RULES = """ANTI-CONFABULATION / ANTI-OBFUSCATION RULES

1. Lean compilation is not proof quality.
   A theorem is acceptable only if its proof derives the statement from:
   - Mathlib declarations,
   - repository owner declarations with genuine mathematical definitions,
   - explicit theorem hypotheses in the theorem statement.
   Lean success alone is not evidence.

2. Do not turn missing mathematics into data.
   Forbidden:
   - structures/classes containing fields named `*_holds`, `*_valid`, `*_law`,
     `*_proof`, `*_certificate`, `*_eq_*`, or any proposition used only to
     re-read a theorem;
   - bridge structures whose fields are the target theorem;
   - theorem proofs that are merely record projections of a stored hypothesis;
   - arbitrary `Prop` fields standing in for constructions;
   - hypotheses hidden as data or calibration packets.
   A proof that compiles but only projects a field or wrapper is still a cheat.

3. Missing proof has exactly one representation: `sorry`.
   If the required theorem is not already available in Mathlib or in the
   theorem-owner repository files, output the exact owner theorem statement
   with `sorry`. Do not invent wrappers, helper certificates, bridge records,
   semantic aliases, or replacement theorems.
   If the theorem is genuinely open, say so plainly and keep the owner theorem exact.

4. Imports are not proof.
   Do not add broad imports to make a name available unless:
   - the imported file is the mathematical owner of the required definitions
     or theorem, or
   - the imported Mathlib file contains a directly relevant theorem used in
     the proof.
   Every new import must be justified by an actual declaration used in the file.
   Do not import project "bridge", "closure", "dictionary", or "architecture"
   files to simulate theorem ownership.

5. The theorem owner rule is mandatory.
   If a theorem naturally belongs to Mathlib or to an existing repository
   theory file, formalize it there or state that it belongs there.
   Do not create a new file, namespace, bridge module, or certificate layer
   merely to make the theorem compile.

6. No name laundering.
   Do not prove a nearby theorem under the requested theorem name.
   The proof must establish the requested mathematical content, not a weaker,
   unrelated, renamed, or trivially true statement.

7. No semantic overloading.
   Names such as "D4", "Hurwitz", "KacMoody", "Virasoro", "central charge",
   "modular discriminant", and "triality" may be used only when the file
   contains typed definitions connecting those objects.
   Otherwise the theorem must remain open with `sorry`.

8. Projection audit.
   Before final output, inspect each theorem proof. If the proof is one of:
   - `exact B.some_field`,
   - `B.some_field`,
   - `simpa using B.some_field`,
   - `rw [B.some_field]`,
   where `some_field` is an assumption stored in a structure/class,
   then classify the theorem as vacuous and replace it with the owner theorem
   statement ending in `sorry`.

9. Explicit owner-debt output.
   If the theorem cannot be closed, output only:
   - minimal necessary imports,
   - the correct namespace,
   - the exact theorem statement,
   - `:= by
       sorry`
   plus a Lean comment identifying the missing owner declarations.
   Do not add auxiliary abstractions.

10. Final output must prefer honest incompleteness over fake closure.
    A file with one precise `sorry` is better than a compiling file whose
    mathematical content is encoded as assumptions.

11. Open problems may be stated plainly.
    Do not obscure an open problem as a structure field, a wrapper theorem, or
    a cosmetic refactor. If the problem is open, keep it open.
"""


PROOF_ADMISSIBILITY_CHECK = """PROOF ADMISSIBILITY CHECK

Before writing Lean code, silently answer:

A. What is the target mathematical theorem?
B. Which existing declaration defines each mathematical object in the statement?
C. Which imported theorem proves the key mathematical step?
D. Is the proof more than a field projection or restatement?
E. Does the theorem belong in the current file, or in a Mathlib/theory owner file?

If A–D cannot be answered concretely, do not attempt closure.
Emit the owner theorem with `sorry`.
"""


BUCKET_CLASSIFICATION = """/-
#### BUCKET 1: CLOSED OWNER THEOREMS
Theorems proved from definitions and existing lemmas, with no theorem-as-data
fields, no certificate structures, no projection proofs, no fake bridge modules,
and no `sorry`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT THEOREM PARAMETERS
Theorems proved from assumptions appearing directly as theorem parameters,
not hidden inside structures/classes. These assumptions must be mathematically
named, unavoidable, and visible in the theorem statement.

#### BUCKET 3: OPEN OWNER DEBT
The exact theorem statements that should exist but are not derivable from
available Mathlib/repository declarations. These must be represented by `sorry`
only.
Lean comments should name the missing owner declarations and the debt type.
-/
"""


REPAIR_RESPONSE_CONTRACT = """LEAN PROOF-REPAIR RESPONSE CONTRACT

This is a concrete repair lane, not a closure-debt audit lane.
Do not include audit-bucket classification.
For a broken Lean owner file, the replacement is the complete corrected Lean
file content. It is not a diff hunk and not a theorem fragment.
Preserve mathlib-style file discipline: minimal imports, cohesive owner scope,
short local helper lemmas, and no architecture expansion inside a proof-repair
file.

Return exactly this shape:

### Cause
One concise paragraph.

### Replacement
```lean4
-- Full corrected Lean file content only.
-- No diff hunks. No prose inside the code block. No one-line minification.
```

### API
One concise paragraph, or "No API correction."
"""


def _normalize_lean_code(code: str) -> str:
    stripped = code.strip()
    if "\n" not in stripped and "\\n" in stripped:
        stripped = stripped.replace("\\r\\n", "\n").replace("\\n", "\n").replace("\\t", "  ")
    return stripped


def extract_replacement_lean(text: str) -> str:
    """Extract the canonical `### Replacement` Lean file from an oracle reply.

    Falls back to the first Lean fenced block, then to raw Lean declarations.
    """
    if not text:
        return ""
    replacement = re.search(
        r"###\s*Replacement\b.*?```(?:lean4|lean)?\s*\n?(.*?)```",
        text,
        re.DOTALL | re.IGNORECASE,
    )
    if replacement:
        return _normalize_lean_code(replacement.group(1))
    block = re.search(r"```(?:lean4|lean)?\s*\n?(.*?)```", text, re.DOTALL)
    if block:
        return _normalize_lean_code(block.group(1))
    raw = re.search(
        r"^\s*(?:import|open|namespace|section|variable|def|abbrev|theorem|lemma|instance|structure|class|inductive)\b",
        text,
        re.MULTILINE,
    )
    return _normalize_lean_code(text[raw.start():]) if raw else ""


def build_audit_prompt(
    body: str,
    *,
    context_label: str | None = None,
    context_code: str | None = None,
    error_text: str | None = None,
) -> str:
    parts: list[str] = [ANTI_CONFABULATION_RULES, "", PROOF_ADMISSIBILITY_CHECK, "", BUCKET_CLASSIFICATION]
    if error_text:
        parts.extend(["", "Lean compilation error:", "```", error_text, "```"])
    if context_label and context_code is not None:
        parts.extend(["", f"{context_label}:", f"```lean4", context_code, "```"])
    parts.extend(["", body.strip()])
    return "\n".join(parts).strip() + "\n"


def build_repair_prompt(
    body: str,
    *,
    context_label: str | None = None,
    context_code: str | None = None,
    error_text: str | None = None,
) -> str:
    """Build a Lean repair-oracle prompt without audit bucket taxonomy."""
    parts: list[str] = [
        ANTI_CONFABULATION_RULES,
        "",
        PROOF_ADMISSIBILITY_CHECK,
        "",
        REPAIR_RESPONSE_CONTRACT,
    ]
    if error_text:
        parts.extend(["", "Lean compilation error:", "```", error_text, "```"])
    if context_label and context_code is not None:
        parts.extend(["", f"{context_label}:", "```lean4", context_code, "```"])
    parts.extend(["", body.strip()])
    return "\n".join(parts).strip() + "\n"


def build_findings_prompt(findings: list[dict[str, object]], context_files: Mapping[str, str] | None = None) -> str:
    body = [
        "I encountered the following Lean 4 compilation errors in my project.",
        "Analyze them and provide a mathematical fix only if it is actually derivable.",
        "If the missing mathematics is not already available from Mathlib or owner files,",
        "return the exact owner theorem statement with `sorry` instead of inventing wrappers.",
        "",
    ]
    for f in findings:
        body.append(f"FILE: {f['file']}")
        body.append(f"LINE: {f['line']}")
        body.append(f"ERROR: {f['message']}")
        body.append("-" * 20)
    if context_files:
        body.append("")
        body.append("Relevant code context:")
        for path, content in context_files.items():
            body.append("")
            body.append(f"--- {path} ---")
            body.append("```lean")
            body.append(content)
            body.append("```")
    body.append("")
    body.append("Requirement: Prefer owner-debt output over fake closure. If closure is unavailable, output the exact theorem statement with `sorry`.")
    return build_audit_prompt("\n".join(body))


def build_lean_fix_prompt(
    *,
    target_name: str,
    context_code: str,
    error_text: str | None = None,
    target_file: str | None = None,
    target_line: int | None = None,
) -> str:
    location = f" at `{target_file}:{target_line}`" if target_file and target_line is not None else ""
    body = [
        f"Prove `{target_name}` in Lean 4{location}.",
        "Use only genuine owner mathematics, explicit theorem hypotheses, or Mathlib.",
        "If the theorem is not currently derivable, keep the exact owner theorem statement and use `sorry`.",
        "If the theorem is open, say so plainly; do not hide it as data, a wrapper, or a bridge record.",
        "Do not invent bridge records, semantic aliases, theorem-as-data wrappers, or projection proofs that merely read back a field.",
        "Do not classify the answer into audit buckets. This is a repair request.",
    ]
    if error_text:
        body.extend(["", "Current Lean compilation error:", "```", error_text, "```"])
    body.extend(["", "Context:", "```lean4", context_code, "```"])
    body.append("Return the canonical Cause / Replacement / API response. The Replacement code block must be the full corrected Lean file content.")
    body.append("Keep the file small and mathlib-style: minimal imports, cohesive owner scope, short local helper lemmas, no architecture expansion.")
    return build_repair_prompt("\n".join(body))
