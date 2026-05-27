# Proof-Only Standard Operating Procedure

This SOP governs all Lean work in this repository.

## Non-negotiable proof rule

A theorem is closed only when Lean's kernel checks a proof built from definitions and lower theorems/lemmas.  Do not replace an honest proof hole with any of the following:

- `axiom`, `postulate`, `admit`, unsafe constants, or hidden trusted code
- witness/datum/certificate/guard/socket fields used as proof payloads
- `*_law`, `*_valid`, `*_readback`, `*_certificate`, `*_witness` proof surfaces
- re-export theorems whose proof is just a structure field or hypothesis
- assumptions/hypotheses introduced solely to supply the target proposition
- `by trivial`, `rfl`, or packaging proofs when the mathematical content is not definitional

If the proof is not known, keep an explicit `sorry` at the exact theorem and document the missing mathematical bridge.

## UlamAI proving loop

For each target file:

1. Run the proof-hole inventory:
   ```bash
   python3 tools/lean4-skills/sorry_analyzer.py lean --format=summary
   ```
2. Run UlamAI health check, with no axioms:
   ```bash
   ulam checkpoint <file.lean> --lean-project . --strict --no-allow-axioms \
     --out-json artifacts/ulamai/reviews/<file>.checkpoint.json
   ```
3. For each real `sorry`, classify the target:
   - genuine theorem needing a proof; or
   - vacuous theorem/readback shell that must be deleted or refactored, not proved by field projection.
4. Before editing, search in this order:
   - local lower lemmas in this repo
   - Mathlib docs/source and `#check`/`#find`/Loogle
   - other Lean libraries in `external_refs/`
   - Lean Zulip / forums
   - arXiv, Google Scholar, and math forums for paper proofs
5. Translate the found mathematical proof into Lean 4 using lower lemmas.
6. Build the touched file:
   ```bash
   lake env lean <file.lean>
   ```
7. Run policy gates:
   ```bash
   python3 tools/quality/check_no_hypothesis_mandate.py --root lean/InfoGeometry
   python3 tools/quality/proof_only_mandate_gate.py
   ```
8. Commit non-artifact source changes regularly and push to both `origin` and `upstream`.

## Vacuity cleanup rule

Deleting an obfuscating readback theorem is valid cleanup when the theorem had no mathematical proof content.  Do not replace it with a new wrapper.  If downstream code depended on it, either:

- prove the downstream statement directly from real lower lemmas, or
- leave the downstream theorem as honest `sorry` until the proof is found.

## Mathlib compliance

All new Lean code must follow the downloaded Mathlib contribution/style references in `external_refs/mathlib_docs/` and the project summary in `.agents/workflows/mathlib_rules_sop.md`.
