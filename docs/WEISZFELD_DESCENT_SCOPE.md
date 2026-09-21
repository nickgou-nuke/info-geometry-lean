# Weiszfeld descent: proof scope

`Spectrometry.WeiszfeldDescentLemma` reuses `GeometricMedianCore` for the
distance objective, inverse-distance weights, and Weiszfeld step. It reuses
`WeightedQuadraticDescent` for the weighted Huygens identity instead of
introducing another barycenter implementation.

The proof dependencies are:

1. Nonnegative square gives norm majorization at a nonzero anchor.
2. Termwise majorization and tangency give the quadratic surrogate.
3. The weighted Huygens identity and positive total weight give the unique
   surrogate minimizer.
4. Majorization, tangency, and minimization give quantitative objective descent.
5. A nonzero step gives strict descent; equal objective values characterize
   fixed points at regular anchors.
6. For a sequence whose every iterate avoids the observations, monotonicity
   and the zero lower bound give convergence of objective values to their
   infimum along that sequence.

Positive total weight requires a nonempty observation type. Regularity means
the anchor differs from every observation. It is not automatically preserved:
a single observation at `3` sends the initial point `0` to `3`. The next
unmodified formula is singular; Lean's total inverse at zero does not repair
the algorithm. Regression tests demonstrate failure of both majorization and
descent when regularity is dropped.

`WeiszfeldEnergyConvergence` proves convergence of objective values, not
convergence of the point sequence or identification of its limit with a
global minimizer. Those require additional arguments or a specified modified
algorithm at data points. No unconditional optimization or epistemic claim
is inferred from monotonicity alone.
