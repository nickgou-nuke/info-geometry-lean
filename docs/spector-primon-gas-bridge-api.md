# Spector Primon Gas Bridge API

Lean module:

- `lean/InfoGeometry/Arithmetic/SpectorPrimonGasBridge.lean`

This module gives the finite theorem-backed Spector corridor for the primon
gas.  It is deliberately arithmetic and finite: it reuses the existing
prime-bit, Mobius, finite-supertrace, and Euler-factor owners without claiming
an analytic or physical completion.

## Theorem Surface

- `spector_state_mobius_eq_fermionParity`
  shows that an occupied finite prime-bit state has Mobius value equal to its
  fermion parity.

- `spector_squarefree_state_mobius_eq_fermionParity`
  gives the same readout for the subset-register square-free primon state API.

- `spector_repeated_prime_sector_killed`
  states the arithmetic exclusion clause: nonsquare-free integers have zero
  Mobius coefficient.

- `spector_finite_witten_index_cancel`
  proves finite Boolean Witten-index cancellation over a nonempty prime
  register.

- `spector_finite_boson_signed_closure`
  proves the regulated finite Euler-factor cancellation
  `Z_boson * Z_signed = 1`.

- `spector_finite_positive_fermion_ratio`
  proves the finite positive-fermion square-energy ratio identity.

- `spector_finite_fermion_signed_secondOrder`
  proves the finite second-order factorization
  `(1+x_p)(1-x_p)=1-x_p^2` multiplied over a finite register.

- `spector_finite_supertrace_supported_on_squarefree`
  proves that the finite Mobius supertrace only sees square-free states.

## Boundary

This module does not formalize Spector's analytic asymptotics, Witten's
unorientable parity anomaly, Shu et al. Bethe-state counting, KMS/BEC phase
structure, GUE asymptotics, zeta-zero statistics, or the Riemann Hypothesis.
It is the finite arithmetic base those future bridges would have to import.
