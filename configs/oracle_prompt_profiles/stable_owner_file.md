Preserve the stable owner-file protocol:

- Use the complete owner file and the complete relevant Lean build output.
- Repair the target owner file directly.
- Keep the proof small, local, and source-faithful.
- The final answer must be useful to a coding agent replacing one broken Lean
  file with one corrected Lean file.
- Keep the corrected file small and mathlib-style: minimal imports, cohesive
  owner scope, short local helper lemmas, no architecture expansion.
- Lean verifies; the chatbot only reviews.
