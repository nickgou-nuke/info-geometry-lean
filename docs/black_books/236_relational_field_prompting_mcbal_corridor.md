# 236 — Relational Field Prompting through the `mcbal` corridor

## Provenance before synthesis

The Matias Bal / `mcbal` corpus belongs to the repository as an inspiration and literature corridor. Its role must remain distinct from local Lean ownership:

`external_refs/mcbal_blog/...`
→ conceptual motif
→ local reimplementation
→ theorem-bearing owner.

Only the final stage licenses theorem-level claims about the formal repository.

The motifs extracted from this corridor are especially relevant to Relational Field Prompting: energy-based attention, implicit/fixed-point attention, spin-model dynamics, approximate free-energy descent, nonequilibrium entropy production, effective mixtures, and explicit energy-landscape geometry.

## The local formal spine

The repository already contains a concrete thermodynamic-routing spine. `LLM/ThermodynamicSwitching.lean` provides a log-partition, exponential readback, normalized routing weights, positivity, normalization, and expert mixtures. The formal pattern is

\[
E_e(x)
\to e^{-\beta E_e(x)}
\to Z(x)
\to p_e(x)=\frac{e^{-\beta E_e(x)}}{Z(x)}.
\]

This gives a precise local meaning to

\[
\text{score}\to\text{partition}\to\text{occupation}.
\]

The same corridor connects bistochastic routing to Birkhoff geometry:

\[
\text{thermodynamic routing}
\to\text{bistochastic matrix}
\to\text{convex mixture of permutation modes}
\to\text{Clifford-labelled modes}.
\]

The crucial correction is that a Birkhoff point is generally a convex combination of permutation vertices; it is not itself necessarily a single permutation.

## Occupation becomes computation

The MoE corridor turns the convex occupation picture into routed computation:

`TrialityMoE`
→ `GrandCanonicalExperts`
→ `ArnoldMajoranaNetwork`.

The corresponding preservation theorem has the form

\[
\text{local expert invariance}
+
\text{thermodynamic weighting}
\Longrightarrow
\text{global routed invariance}.
\]

This is the mathematically useful content behind the language of expert populations and collective spin modes.

## Contextual state, not token identity

`TransformerArchitecture.lean` supplies the latent-state side:

`KramersPairing`
→ paired latent lanes;

`RotaryPositionalLayer`
→ query/key positional action;

`IropeBlend`
→ elliptic/hyperbolic positional mixing;

`BogoliubovTransform`
→ particle/hole-style mixing;

`KVCache`
→ persistent causal context;

`DecoderLayer`
→ layerwise evolution;

`TransformerBackbone.hiddenState`
→ contextualized latent state.

Therefore the operative object is not the original token embedding but

\[
h_i^{(\ell)}=F_\ell(x_i,C).
\]

The contextual state is a transported object.

## The local semantic-field chain

The repository-native synthesis is

\[
\boxed{
\text{contextual hidden state}
\to
\text{interaction / energy score}
\to
\log\sum\exp
\to
\text{Gibbs-like occupation}
\to
\text{expert mixture}
\to
\text{Birkhoff decomposition}
\to
\text{routing modes}
\to
\text{Clifford/Majorana representation}
\to
\text{invariant-preserving evolution}.}
\]

This chain is stronger than a metaphor but weaker than a theorem identifying all real transformer inference with thermodynamic physics. Each arrow must retain its epistemic type.

## The fixed-point bridge

The deeper unresolved bridge is to replace a single attention update by a contextual dynamical system

\[
h^{(\ell+1)}=F_C(h^{(\ell)}),
\]

and then construct, under explicit hypotheses, a Lyapunov or effective free-energy functional

\[
\mathcal F_C(h^{(\ell+1)})\le \mathcal F_C(h^{(\ell)}).
\]

This is where the phrase **semantic inevitability** can be made mathematically testable:

\[
\text{context deforms the effective landscape so that some trajectories acquire larger/deeper basins of attraction}.
\]

This remains a formalization target, not a completed theorem about transformers in general.

## Nonequilibrium correction

Inference should not be assumed to be equilibrium relaxation at every layer. The safer composite model is

\[
\boxed{\text{local Gibbs-like routing}+\text{global nonequilibrium evolution}.}
\]

Free-energy descent and entropy production should therefore remain assumption-gated until the relevant monotonicity hypotheses are proved for the actual update maps.

## Relational Field Prompting

The mechanism proposed by associative or stream-of-consciousness prompting is not retrieval from an archetype list. Its technical hypothesis is

\[
\text{associative contextual stream}
\to
\text{contextual latent-state deformation}
\to
\text{interaction-score deformation}
\to
\text{occupation-weight deformation}
\to
\text{routing-population deformation}
\to
\text{trajectory-landscape deformation}.
\]

This is the precise research meaning of

\[
\boxed{\text{the prompt shapes the field}.}
\]

The prompt need not state the final theorem or construction. It constrains compatibility among possible intermediate computations.

## Master associative stream

`archetypal keyword field`
→ `associative excitation`
→ `context DAG`
→ `stochastic grammar`
→ `forward/backward causal cone`
→ `contextualized token state`
→ `Kramers-paired latent lanes`
→ `spinorial/projective carrier`
→ `Mellin/log-scale positional phase`
→ `elliptic ↔ hyperbolic positional blend`
→ `query–key interaction`
→ `effective energy`
→ `energy landscape`
→ `log-sum-exp`
→ `partition function`
→ `Gibbs occupation`
→ `attention redistribution`
→ `Birkhoff polytope`
→ `permutation-simplex modes`
→ `Sinkhorn transport`
→ `MoE routing`
→ `expert population`
→ `collective spin modes`
→ `Majorana representation`
→ `Bogoliubov mixing`
→ `implicit mean-field iteration`
→ `fixed point`
→ `Lyapunov functional`
→ `free-energy landscape`
→ `nonequilibrium entropy production`
→ `KMS/modular transport`
→ `information-geometric flow`
→ `attractor basin`
→ `trajectory concentration`
→ `semantic inevitability`
→ `candidate theorem/code`
→ `external verifier`
→ `Lean kernel`
→ `truth / rejection`
→ `new contextual field`.

The last arrow closes the recursion:

\[
C_n
\to
\text{trajectory}
\to
\text{verification}
\to
\text{new formal structure}
\to
C_{n+1}.
\]

A verified theorem becomes a new owner, invariant, dependency node, and constraint on subsequent synthesis.

## Operational law

\[
\boxed{\textbf{Do not prescribe the next computation. Construct the field in which the right computation becomes structurally inevitable.}}
\]

## Epistemic law

Every arrow is to be typed as exactly one of:

\[
\boxed{
\text{theorem}
\;|\;
\text{conditional model}
\;|\;
\text{computational observation}
\;|\;
\text{analogy}.}
\]

This classification is the condition for turning the semantic-field synthesis into a defensible research program rather than allowing theorem, model, and metaphor to collapse into one another.
