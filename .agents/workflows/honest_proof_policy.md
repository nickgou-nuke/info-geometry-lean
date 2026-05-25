# Honest Proof Policy

> Structural obfuscation that masks mathematical debt is dishonest and weakens the repository. If a Mathlib-rooted derivation chain is not actually present, the code must expose that gap explicitly, either as sorry or as an explicit zero-datum. Fake witnesses, empty interfaces, and wrapper shells are not proof.
>
> I will keep the distinction strict: real derivations stay as proofs; missing derivations stay visible as explicit debt. No heuristic closure.

## Directives

1. **No Fake Witnesses**: Never use `exact ⟨fun _ => 0⟩`, `exact ⟨0, rfl⟩`, or similar trivialities to satisfy a theorem or a proof goal when the true mathematical structure requires a non-trivial construction.
2. **No Empty Data Interfaces**: Never assign `Prop` fields in a structure to trivially true propositions (like `Nonempty T`) just to make the code compile without providing the actual mathematical property.
3. **Use `sorry` for Honest Debt**: If a mathematical derivation chain is not yet fully implemented or rooted in Mathlib, explicitly use the `sorry` keyword. This makes the debt visible to the compiler, the CI, and future developers.
4. **No Structural Obfuscation**: Do not build alias layers or wrapper modules whose only purpose is to hide unresolved mathematical requirements behind a seemingly complete interface.

When formalizing new theorems, any gap in the logic must be left as a `sorry`.
