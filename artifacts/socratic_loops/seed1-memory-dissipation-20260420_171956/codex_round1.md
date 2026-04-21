NUCLEUS:
A system “remembers” only where its evolution preserves distinguishability; it “dissipates” where evolution strictly contracts distinguishability.

Minimal form:

`mature informational dynamics = reversible invariant factor ⊕ strictly contractive transient factor`

The strongest mathematical nucleus is not “every mature system must split,” but:

Given an informational evolution with a stable invariant structure and a genuine contraction/entropy production functional, there is a canonical decomposition into:
- a protected reversible component: fixed, unitary, isometric, or sufficient-statistic-preserving;
- a dissipative component: contractive, entropy-producing, asymptotically forgetful.

Exact conceptual compression achieved:
**Memory is the non-dissipative subspace of an information contraction.**

INFLATIONS_TO_REMOVE:
- “Every mature informational generator must” is too universal. Replace with conditional hypotheses: Markov semigroup, CP map, contraction, spectral gap, invariant state, entropy monotonicity.
- “Spectral bifurcation” is plausible but premature unless the operator class supports spectral theory.
- “Informational Hodge Decomposition” is ornamental unless exact/coexact/harmonic analogues are defined.
- “Janus Involution” is symbolic excess unless there is an actual involution.
- “Krein Space Decomposition” is likely false grandeur unless an indefinite inner product is structurally present.
- “Relative entropy to Ricci flow” is a bridge too far. It mixes analogy with theorem-demand.
- The Lean surface is overcommitted: `exp`, `IsUnitary`, strict contraction, and commutation are all heavy obligations. Also `L_mem ∘ L_diss` is not the right composition notation for continuous linear maps without care.
- “Maturity > 1” is empty. Maturity must be replaced by explicit analytic assumptions.

AMPLIFICATION_VECTOR:
Intensify by moving from mythic dualism to a precise contraction theorem.

Best direction:
Use **information monotonicity** as the primitive. Memory is the equality case of contraction; dissipation is the strict inequality case.

Possible theorem shape:
For an evolution `T` acting on states/observables with divergence `D`,
if `D (T x) (T y) ≤ D x y`, then the memory sector consists of pairs/substructures where equality holds, while the dissipative sector consists of directions where inequality is strict.

This gives a sharper Lean-facing surface:
- define an information divergence or seminorm;
- define `MemorySector T D := {directions where D is preserved}`;
- define `DissipativeSector T D := {directions where D strictly decreases}`;
- prove under assumptions that preserved directions form an invariant/reversible part;
- only later ask for direct-sum decomposition.

DISTILLED_COUNTERPROMPT:
Purify the Memory-Dissipation Bifurcation again, but remove all unsupported grandeur.

Do not invoke Hodge theory, Krein spaces, Ricci flow, Janus, modular theory, or spectral bifurcation unless you define the exact formal structure that licenses the term.

Reformulate the hypothesis around one primitive: **information contraction**.

Core demand:
Memory is the equality case of an information contraction.
Dissipation is the strict inequality case.

Produce:
1. A minimal mathematical statement using an evolution `T` and an information divergence or seminorm `D`.
2. The weakest assumptions under which a protected reversible sector can be defined.
3. The precise difference between “invariant,” “isometric,” “fixed,” and “unitary.”
4. A Lean4 hypothesis surface with definitions first, theorem second, and no fake maturity scalar.
5. One symbolic/archetypal phrase only, and it must correspond to the formal structure.

Target compression:
**Memory = preserved distinguishability. Dissipation = contracted distinguishability.**
