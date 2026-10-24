# Two-mode elliptic particle-hole reuse contract

Status: source-reviewed G-A discovery, 2026-10-23. No compilation or tests.
No Lean candidate was created: the concurrent native SignedBogoliubovCAR
owner covers the planned cross-bracket delta by direct substitutions.

## Carrier, primitive inputs, and output convention

Use `[CommRing R] [Ring A] [Algebra R A]`. Write `{x,y}` for the
native `thermalAnticommutator x y`. Input modes are `(a,c)` and `(b,d)`:

- `a*a = c*c = b*b = d*d = 0` (four separate primitive hypotheses);
- `{a,c}=1`, `{b,d}=1`;
- `{a,b}=0`, `{c,d}=0`, `{a,d}=0`, `{b,c}=0`.

These are exactly the relations inspected in
`Physics/NambuSpinorGrassmannian.lean`, `NambuGrassmannian.TwoModeCAR`,
with `(n1,p1,n2,p2)=(a,c,b,d)`. No new structure is needed.

The elliptic output convention is:

```
a' = u • a + v • d      c' = u • c + v • b
b' = u • b - v • c      d' = u • d - v • a
```

## Exact existing theorem substitutions

All particleHole names below are in `InfoGeometry.OperatorAlgebra`, owned by
`OperatorAlgebra/SignedBogoliubovCAR.lean`.

| Output relation | Existing declaration and arguments |
| --- | --- |
| `{a',b'}=0` | `particleHole_annihilator_cross a c b d u v` |
| `{c',d'}=0` | `particleHole_annihilator_cross c a d b u v` |
| `{a',d'}=0` | `particleHole_mixed_cross a d u v v` |
| `{b',c'}=0` | `particleHole_mixed_cross b c u (-v) (-v)`, simplifying scalar negations |
| `{a',c'}=(u*u+v*v) • 1` | `particleHole_diagonal a c b d u v v` |
| `{b',d'}=(u*u+v*v) • 1` | `particleHole_diagonal b d a c u (-v) (-v)`, simplifying signs |

For creator-cross the required input diagonal brackets `{c,a}` and `{d,b}`
are the original normalized brackets by `thermalAnticommutator_symm`.
Its cross inputs are `{c,d}=0` and `{a,b}=0`.
For the second diagonal formula the required cross inputs `{b,a}=0` and
`{d,c}=0` likewise follow by native symmetry.

Cross relations need no coefficient normalization. For both diagonal
relations equal to one, use `particleHole_normalized` with the same argument
substitutions and `u*u+v*v=1` (equivalently `u^2+v^2=1`).

For the four output squares, reuse
`InfoGeometry.Algebra.ChiralCARTransport.linear_mix_square` with
`(p,q; coefficients)` respectively `(a,d;u,v)`, `(b,c;u,-v)`,
`(c,b;u,v)`, `(d,a;u,-v)`. Each residual anticommutator is zero
by the primitive mixed input relations and symmetry. No division by two,
characteristic restriction, or duplicate square-zero theorem is required.

The native cross-annihilator and diagonal proofs directly use
`thermalAnticommutator_expand`. The mixed-cross proof uses native
`linear_mix_anticommutator`. These are full algebraic reductions, not
assumptions of the output relations.

## Consumer boundary and promotion decision

All requested algebraic two-mode CAR relations are covered by these native
lemmas plus substitutions and sign simplification. Do not add wrappers for
creator-cross, second-mode normalization, or reversed brackets merely to
rename these applications. There is no remaining theorem delta for this
bounded cross-bracket task.

This does not identify the transformation with a particular rotor sandwich,
prove implementability, or assert star preservation. Under a star-compatible
scalar action, `c=star a`, `d=star b`, and self-adjoint scalar coefficients
`star u=u`, `star v=v` imply the corresponding output adjoint identities;
those are additional assumptions, not consequences of CAR alone. For general
complex coefficients the displayed same-coefficient formula is not an
unconditional adjoint transformation. No star lemma is added in this task.

Parent and independent reviewers own source acceptance and kernel checking.
This document records source correspondence only, not a build/QA PASS.
