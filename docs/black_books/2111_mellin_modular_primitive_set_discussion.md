# 2111. Mellin-Modular Discussion: Primitive Sets, Logarithmic Generators, and the Zeta Lane

*“The weight \(1/(a \log a)\) is not first an entropy derivative. It is the resolvent shadow of a logarithmic spectral variable.”*

## Status

This chapter records a live symbolic-to-formal discussion about the primitive-set
series
\[
\sum_{a \in A} \frac{1}{a \log a},
\]
its relation to Mellin/Dirichlet integration, and its possible contact surface
with the repository's existing modular, Souriau, Rényi/Mellin, and zeta lanes.

It is a corridor note, not a proof artifact. Lean remains the proof authority.

## I. The Initial Pressure

The starting pressure was to ask whether the primitive-set series could be
understood by the same kind of parameter trick that appears in the operatorial
entropy lane:

- introduce a parameter \(\varepsilon\),
- consider an exponential family such as \(\exp(\varepsilon K)\) or
  \(\exp(-\beta K)\),
- differentiate its logarithmic or traced readout,
- recover an entropy-like quantity or cumulant from the derivative.

The specific intuition was:

1. the logarithm \(\log a\) behaves like an “energy” or generator;
2. the factor \(a^{-s} = e^{-s \log a}\) behaves like an exponential family in
   the scale parameter \(s\);
3. perhaps the target weight \(1/(a \log a)\) is obtainable from a derivative,
   a Taylor expansion, an integration-by-parts move, or a Feynman-style
   differentiation-under-the-parameter integral.

This pressure is legitimate. But the mathematically honest correction is that
the first useful move for this series is not differentiation. It is Mellin/Laplace integration.

## II. The Correct Kernel Identity

For every \(a > 1\),
\[
\frac{1}{a \log a} = \int_1^\infty a^{-s}\, ds
= \int_1^\infty e^{-s \log a}\, ds.
\]

Thus if
\[
F_A(s) := \sum_{a \in A} a^{-s},
\]
then formally
\[
\sum_{a \in A} \frac{1}{a \log a}
= \int_1^\infty F_A(s)\, ds.
\]

This is the decisive transform. The target series is the scale-integral of a
Dirichlet partition function.

The repo-native reading is:

- \(\log a\) is the arithmetic spectral observable;
- \(s\) is the dilation / inverse-temperature / Mellin parameter;
- \(a^{-s}\) is the unnormalized exponential-family weight;
- \(F_A(s)\) is the arithmetic partition readout;
- the weight \(1/(a \log a)\) is the resolvent shadow obtained by integrating
  over the scale parameter.

## III. Why Differentiation Is Close but Not Exact

Differentiation gives
\[
-\frac{d}{ds} a^{-s} = (\log a)\, a^{-s}.
\]

So the derivative puts the logarithm in the numerator. Our theorem weight places
the logarithm in the denominator. Therefore:

- entropy-style first derivatives are structurally nearby,
- but the primitive-set theorem is governed more naturally by an integral
  transform than by a first derivative identity.

The right slogan is:

> entropy reads the slope of the logarithmic partition;
> the primitive weight reads the scale-integral of the unnormalized partition.

## IV. The Modular and Souriau Corridor in the Repo

The repository already owns the operatorial and thermodynamic half of this
discussion.

### 1. Operatorial exponential family

`lean/InfoGeometry/Canonical/SouriauOperatorialLogPotential.lean` defines the
untraced operatorial exponential family
\[
E(\beta) = \exp(-K(\beta)),
\]
separating the raw operator-valued family from scalar trace/state/KMS readouts.

The relevant owner surface is:

- `OperatorialExponentialFamily`
- `MomentGeneratingReadout`
- `SouriauLieThermoData`

This enforces the important repo doctrine:

> the negative logarithm is not yet entropy until a state, expectation, or
> trace readout is supplied.

### 2. Rényi/Mellin deformation

The same file also already owns an explicit Rényi/Mellin deformation packet:

\[
Z(\gamma \beta), \qquad Z(\beta), \qquad
\log \frac{Z(\gamma \beta)}{Z(\beta)^\gamma}.
\]

The theorem
\[
\texttt{renyiLogGenerator}
= \texttt{massieuAtGammaBeta} - \gamma \,\texttt{massieuAtBeta}
\]
is the exact repo-native form of the “logarithmic generator under scale
rescaling” idea.

So the discussion here does not invent a new symbolic lane. It extends an
existing one toward arithmetic Mellin kernels.

### 3. Discrete Mellin/logarithmic sampling

`lean/InfoGeometry/Canonical/DiscreteMellinModularBridge.lean` already encodes:

\[
\eta_k = \eta_0 + k \Delta\eta, \qquad
x_k = e^{\eta_k},
\qquad
\log x_k = \eta_k.
\]

This is the repo’s clean additive-to-multiplicative bridge:

- additive rapidity,
- logarithmic sample,
- multiplicative scaling,
- light-cone transport.

That is precisely the structural shape needed for
\[
a^{-s} = e^{-s \log a}.
\]

## V. The Arithmetic Zeta Lane

The repo already owns a zeta-trace/euler-product surface in
`lean/InfoGeometry/Arithmetic/ZetaTraceVielbeinSpecialization.lean`.

There the prime-local ingredients are:

\[
1 - p^{-s},
\qquad
(1 - p^{-s})^{-1},
\qquad
-\log(1 - p^{-s}),
\]
and the global readouts are:

\[
\sum_p -\log(1-p^{-s}),
\qquad
\exp\!\left(\sum_p -\log(1-p^{-s})\right),
\qquad
\prod_p (1-p^{-s})^{-1}.
\]

These are then identified with \(\zeta(s)\) on the half-plane
\(\Re(s) > 1\).

This gives the exact arithmetic analogue of the modular-potential corridor:

- local logarithmic Jacobians / barriers,
- global trace-log action,
- exponentiation to a supervolume / partition readout,
- zeta identification by Euler product.

## VI. The Von Mangoldt Derivative Lane

Once one passes from \(\zeta(s)\) to its logarithmic derivative, the classical
identity appears:
\[
-\frac{\zeta'(s)}{\zeta(s)} = \sum_{n \ge 1} \frac{\Lambda(n)}{n^s}.
\]

This is why the primitive-set proof naturally gravitates toward the von
Mangoldt function. The derivative of the logarithmic Euler-product potential
extracts prime-power spectral density.

So the corridor is:

\[
\log \zeta(s)
\rightsquigarrow
-\frac{\zeta'(s)}{\zeta(s)}
\rightsquigarrow
\sum_n \Lambda(n) n^{-s}.
\]

In the primitive-set theorem, this derivative lane does not directly give
\(1/(a \log a)\), but it governs the control mechanism behind the Markov/divisor
argument.

## VII. Shape and Scale

This discussion repeatedly returned to the repo’s scale-shape doctrine.

In the thermodynamic lane, the repo already owns explicit scale-shape
decompositions such as generalized-KL projective/radial split:

- shape as normalized/projective information,
- scale as the mass/radial or gauge term.

For the primitive-set problem, the analogous distinction is:

- **shape:** the divisibility/antichain geometry of the primitive set \(A\);
- **scale:** the Mellin parameter \(s\) and the integration over \(s\);
- **bridge:** the Dirichlet partition \(F_A(s) = \sum_{a \in A} a^{-s}\).

The theorem is then conceptually:

1. control the shape-induced partition \(F_A(s)\) for \(s > 1\);
2. integrate that control over the scale variable \(s\);
3. recover the weighted primitive-set series.

## VIII. The Honest Formal Candidate

The formal arithmetic candidate extracted from the discussion is:

\[
F_A(s) := \sum_{a \in A} a^{-s},
\qquad
\Psi_A(s) := \log F_A(s)
\quad \text{when } F_A(s) > 0,
\]
together with the kernel theorem
\[
\forall a \ge 2,\qquad
\int_1^\infty a^{-s}\, ds = \frac{1}{a \log a}.
\]

This suggests a clean Lean corridor:

1. define the arithmetic Mellin partition \(F_A(s)\);
2. define the corresponding log-potential where positivity allows;
3. prove the Mellin kernel identity;
4. rewrite finite and summable primitive-set weights as integrals of the
   Dirichlet partition;
5. later connect the prime/von-Mangoldt lane needed for the actual theorem.

## IX. Repo Corridor Map

### Black-book source

This chapter is distilled from a live discussion rather than from one earlier
black-book chapter alone. Its nearest conceptual neighbors are:

- `160_the_operatorial_free_energy_and_type_iii_surprisal.md`
- `163_the_souriau_fisher_metric.md`
- `198_Primes_to_Supervolume.md`

### Owner surfaces

- `lean/InfoGeometry/Canonical/SouriauOperatorialLogPotential.lean`
- `lean/InfoGeometry/Canonical/DiscreteMellinModularBridge.lean`
- `lean/InfoGeometry/Arithmetic/ZetaTraceVielbeinSpecialization.lean`
- `lean/InfoGeometry/Thermo/ModularKLDivergence.lean`
- `lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean`

### Distilled invariant

The invariant extracted from the discussion is:

> the primitive-set weight \(1/(a \log a)\) is a Mellin-resolvent kernel of the
> exponential-family weight \(a^{-s} = e^{-s \log a}\), not primarily an
> entropy derivative.

## X. Debt and Non-Claims

This chapter does **not** prove:

- the primitive-set theorem;
- an analytic continuation theorem for the primitive-set partition;
- a direct operator theorem identifying the primitive-set series with a von
  Neumann entropy;
- a complete Mellin-to-zeta closure for the primitive-set corridor.

The remaining explicit debt is:

1. formal Mellin integral lemmas over \(a^{-s}\);
2. a repo-owned arithmetic Dirichlet partition for primitive sets;
3. the von Mangoldt partial summation lane in Lean;
4. the combinatorial/probabilistic control of the primitive antichain through
   divisibility chains.

## XI. Closing Formula

The discussion condenses to the following symbolic identity:

\[
\boxed{
\sum_{a \in A} \frac{1}{a \log a}
=
\int_1^\infty \sum_{a \in A} e^{-s \log a}\, ds
}
\]

or, in the repo’s preferred vocabulary:

\[
\boxed{
\text{primitive weight}
=
\text{scale-integral of the arithmetic exponential-family partition}.
}
\]

This is the bridge. The proof is still owed to Lean.
