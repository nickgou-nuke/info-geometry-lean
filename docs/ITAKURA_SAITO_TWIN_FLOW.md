# Itakura–Saito twin potential

`InfoGeometry.OptimalTransport.ItakuraSaitoTwinFlow` reuses the existing
`InformationGeometry.ItakuraSaito.isDivergence` definition and positivity theorem.
The new source proves the derivative of `D(state || 1 - state)`, its unique zero
on `(0,1)`, and the instantaneous energy-decay identity along a differentiable
negative-gradient trajectory. It does not assume an ODE solution exists globally.

The logical dependencies are:

- Existing positive-input divergence → restricted twin potential → unique minimum.
- Restricted twin potential → derivative → unique stationary point.
- Derivative plus a trajectory satisfying the gradient ODE → energy derivative
  equals minus the gradient squared.
- Zero gradient plus an arbitrary residual field → cancellation of the gradient
  term, not a proof that the residual field is unitary or preserves energy.

The domain restrictions matter: Lean's totalized division also makes the displayed
rational gradient vanish at `0` and `1`. Neither is in the intended domain.
The constant residual field `1` makes the total velocity nonzero at `1/2`.

No Klein-bottle quotient, optimal-transport problem, Fisher-information bound,
unitary operator, superconducting system, or zeta-zero correspondence is defined
by these scalar statements. No RH or Selberg conclusion follows from them.

Verification status: source proofs and regression examples supplied; kernel
checking is pending the repository's shared build queue.
