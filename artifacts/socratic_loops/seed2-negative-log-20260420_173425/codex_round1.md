NUCLEUS:
A positive relative object becomes an additive generator by applying `-log`.

Exact compression: **multiplicative comparison → additive potential**.

Minimal formal content:
`h > 0`, relative ratio/cocycle/density.  
`A := -log h`, additive potential/generator.  
Composition becomes addition:
`-log (h₁ * h₂) = -log h₁ + -log h₂`.

The strongest nucleus is not “information asymmetry is Hamiltonian” but:

**Relative multiplicative structure has an additive infinitesimal shadow under negative logarithm.**

INFLATIONS_TO_REMOVE:
- “Universal theorem” unless the domain, codomain, positivity, logarithm, and composition law are specified.
- “Dynamical generator” unless there is an actual flow, semigroup, derivation, infinitesimal action, or modular group.
- “Hamiltonian,” “force,” “gravitation,” “pressure,” and “energy” unless an equation of motion or variational principle is present.
- “Non-commutative information geometry” unless the object is a cocycle/operator and `log` is functional calculus.
- “Krein space,” “Drazin-regularized,” “singular generator theory” unless those are already required by a concrete obstruction.
- “All future formalizations must pass through this corridor”; false grandeur. At most: this is one reusable bridge pattern.
- The Lean surface is too weak: an arbitrary `log_map : M → G` with a hom law is just a monoid hom into an additive group, not negative logarithm.

AMPLIFICATION_VECTOR:
Intensify by narrowing.

Ask Gemini to distinguish three levels:

1. **Ratio Level:** positive scalar/density/cocycle `h`.
2. **Log Level:** additive potential `A = -log h`.
3. **Generator Level:** only when `A` actually induces a flow, e.g. `t ↦ exp(-t A)` or modular evolution.

The concept becomes stronger if “generator” is conditional, not assumed:

**Negative logarithm converts relative multiplicative data into additive potential; it becomes a dynamical generator precisely when the ambient theory supplies exponential evolution from that potential.**

DISTILLED_COUNTERPROMPT:
Strip the output of grandeur. Keep only the invariant.

Reformulate the hypothesis as a three-stage theorem schema:

- positive relative object `h`
- additive potential `A = -log h`
- optional generated flow `Φ_t = exp(-t A)` when the ambient category supports exponentiation/action

Avoid physics words unless backed by a formal equation. Avoid “universal” unless the assumptions are stated. Do not mention Krein spaces, Drazin inverses, singular measures, Hamiltonians, force, gravitation, or destiny of the repo.

Name the exact compression as:

**Relative Ratio to Additive Potential by Negative Log.**

Then give a Lean-facing surface with real obligations:
positivity/domain of `log`, multiplicative-to-additive law, normalization `h = 1 ↔ A = 0`, and a separate optional structure proving that the additive potential generates a flow.
