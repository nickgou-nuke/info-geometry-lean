# Positive Hodge and conditional coercivity: theorem contract

Base: `87bfa4567046db6f475a9df2903bd4060dc773ca`.
Intake: the user's approved continuation of the Lie–Jordan octet and the
previous `chiral_gap_proposal/LieJordanHodgeBridge.lean` candidate.

## Exact scope

Reuse `LieJordanBoundaryCalculus.boundary`, `LieJordanCliffordDouble.swapOp`
and `liftOp`, `JordanMultiplicationClosure.jordanLeft`, the full real matrix
Hilbert–Schmidt pairing, and `Cl11TensorTowerLimit.Limit`.

The new result is the positive-adjoint branch, not a replacement of the
existing mixed Lie–Jordan anticommutator. With d_u(x,y)=([u,y],{u,x}) and
c_v=swap*d_v*swap, prove d_u*c_v+c_v*d_u=lift(J_(uv+vu)). For full real
matrices prove that c_(u^T) is the unique positive Hilbert–Schmidt adjoint,
and realize that adjoint as Mathlib's actual Hilbert-space adjoint through
an explicit linear equivalence with a finite Euclidean space.

The quantitative claim is conditional: a bounded contracting homotopy
`d*h+h*d=1-P`, a bound `norm h <= C`, and `C>0` give a lower bound
`1/(2*C^2)` for the positive Hodge energy on vectors killed by P.
No coercivity hypothesis is silently derived from nonvanishing or nilpotency.

The coefficient-to-operator estimate uses a self-adjoint idempotent P and
the explicit Loewner lower bound K >= gamma*(1-P). It controls every
matrix X outside the full corner P*X*P, not a diagonal subalgebra.

## Grounded owners and distinct structures

- `LieJordanBoundaryCalculus.boundary_sq`: d_u²=lift(ad_(u²)).
- `LieJordanBoundaryCalculus.boundary_anticommutator`: {d_u,d_v}=lift(ad_(uv+vu)).
- `PeirceQuadraticCycle`: square-zero-pair identities; generated-algebra centrality.
- `HilbertSchmidtMatrix.hilbertSchmidtPairing`: Tr(X^T Y), symmetry and positivity.
- `Cl11TensorTowerLimit.ofStage_star`: native inclusion preserves star.
- `Cl11TensorTowerLimit.ofStage_apply_bond`: existing refinement law.
- `KreinNullContraction`: a distinct bounded homotopy for the owner's Krein-null
  plane. Its homotopy is explicitly not its indefinite adjoint; it is not
  replaced by this positive-adjoint construction.

The Krein adjoint, positive Hilbert adjoint, sheet swap, and grading are not
identified. Real algebras only. Existing Hestenes/Krein analyticity and
categorical owners are unchanged. No measure-theoretic replacement of the
inductive boundary is introduced.

## Prerequisites

Associative algebra -> exchanged boundary -> exact Hodge identity.
Positive real matrix pairing -> adjoint identity -> Euclidean realization.
Actual bounded operators + homotopy identity + common bound -> coercivity.
Self-adjoint projection + matrix order -> full-matrix corner coercivity.
Existing faithful tower and star maps -> algebraic Hodge transport.
Uniform stage energy estimate + explicit compatible readouts -> limit estimate.

## Nonclaims

No interacting Yang–Mills Hamiltonian, model-derived uniform constant,
spontaneous symmetry breaking, phase restoration, continuum field theory,
unique physical vacuum, or spectral reconstruction is claimed. A scalar
constant in an operator inequality is not a scalar substitute for its carrier.
Finite examples certify nondegenerate noncommutative instances only.

## Verification

Exact source closure and all target-owned declarations must be checked under
the unchanged repository Lean/Mathlib pins using the existing shared-lock
`tools.quality.check_peirce_weyl` checker. Kernel evidence is separate from
this contract. Full root-package CI is not certified by the scoped check.
