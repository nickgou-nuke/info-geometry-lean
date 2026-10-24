# IS barrier derivative bridge contract

Carrier: real functions with Mathlib `HasDerivAt`. Reuse
`Canonical.ScalarLogBarrier` and `Canonical.SelfConcordantLogGeneratingLyapunov`.
The latter proves algebraic dissipation for explicitly defined derivative slots;
the former proves actual first through third derivatives of negative logarithm.

The bridge identifies the three IS kernel slots with actual derivatives away
from zero, and applies the chain rule to a supplied differentiable trajectory
whose velocity equals the existing natural-gradient field. This makes the
algebraic dissipation identity an actual derivative identity. No existence,
global convergence, zeta-function statement, or infinite Euler-product bound
is asserted. The earlier scaled Euler counterexample and its cutoff repair
remain separate; scalar self-concordance is not promoted to a zeta theorem.

Source search: recursive maintained Lean searches for HasDerivAt/isBarrierKernel
and lyapunovPotential, plus direct reads of both owners and derivative-slot
definitions. No matching actual derivative bridge was found in those searches.
Independent semantic review passed. Final independent QA session 70798 exited
successfully (3772 jobs), with six axiom reports each containing exactly
`propext`, `Classical.choice`, and `Quot.sound`. Both audit examples compiled;
zero warnings in the new sources, zero strict-screen traps, and clean scoped
diff checks. Log: `/tmp/is-barrier-qa.log` (session-local evidence).

The trajectory hypothesis is pointwise at the evaluation time. The derivative
identity holds for nonzero inputs, including negative inputs under Mathlib's
real logarithm; the nonnegative divergence interpretation remains positive-domain.
