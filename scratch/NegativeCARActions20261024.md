# Negative CAR actions — sandbox contract

G-A proposal; uncompiled. Parent owns promotion, Popper independent AA, and
Ampere serial locked QA. No live edits or builds were performed.

Import and operation owner:
`InfoGeometry.OperatorAlgebra.QuadraticNoncommutativeIdentity`.
The namespace is `InfoGeometry.OperatorAlgebra`; reuse its
`quadraticCommutator`, `quadraticAnticommutator`, and signed convention from
`negative_car_bilinear_commutator`. No definitions or structures are added.

Two separate lemmas over arbitrary `Ring A` and `DecidableEq ι`:

- `negative_car_bilinear_action_forward`:
  `[-(d i * b j), d k] = if j = k then d i else 0`.
  Requires only same-forward anticommutation and mixed negative CAR.
- `negative_car_bilinear_action_backward`:
  `[-(d i * b j), b k] = if i = k then -(b j) else 0`.
  Requires only same-backward anticommutation and mixed negative CAR.

The mixed hypothesis is `{d i,b j} = if i=j then -1 else 0`.
The proof expands `[-ab,c] = -a{b,c}+{a,c}b`, then substitutes the primitive
CAR relations. Neither result assumes its conclusion, a representation, or
a desired bracket table. No finite index, scalar-field, square-zero, or
characteristic assumption is needed beyond the displayed anticommutators.

For the proposed three-mode operator application use the existing associative
endomorphism carrier and separately prove the signed CAR for `d i = L_(U i)`
and `b j = L_(-V j)`; nonassociative element products cannot substitute for
operator composition. The name `b` does not assert adjoint duality.

These actions complement the existing signed bilinear Lie closure. They do
not prove associative matrix-unit multiplication, faithfulness, or a
`gl(3|1)` identification. Central mixed odd brackets remain distinct from
the noncentral odd brackets of that matrix Lie superalgebra.
