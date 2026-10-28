# Lie--Jordan octet: theorem contract

## Intake and provenance

Source: `Pasted text(20261028-150403).txt`, SHA-256 `8cad16c145458a913ffb933dab2ab48a47f590f36daa85ce58657bf6544f3ad9`.
Parent: `819b26fc3fc40727234f9afdf6b485c3a2ec0702` (PR #259).
The source's eight-row table, four readouts, grading duality and signed trace
identity are the requested mathematical scope. Its physical terminology is
recorded as interpretation, not included in theorem names or conclusions.
The source's claim of prior verification is not used as compilation evidence.

## Carrier and existing owners

An associative algebra `A` over a commutative base ring `R`; the carrier `A`
is not required to be commutative. Operators are native `Module.End R A`,
with multiplication denoting composition. The concrete ordered instance is
full `Matrix n n ℝ`; no diagonal restriction or complexification is used.

Reuse `LieAlgebra.ad`, `JordanMultiplicationClosure.jordanLeft`,
`LieJordanBoundaryCalculus.crossTransport` and `orientedTransport`, the
existing `IdempotentProjector` corners, and `Cl11TensorTowerLimit.Limit`.
The supplied verified source export was inspected for these definitions and
proof bodies; the connected PR head was checked before extending it.

Put D(u)(x)=ux-xu, J(u)(x)=ux+xu, C(u,v)(x)=uxv+vxu,
A(u,v)(x)=uxv-vxu, K=uv+vu and S=uv-vu.

## Exact octet and declaration ownership

| Row | Equality of endomorphisms | Declaration |
| --- | --- | --- |
| 1 | J(u)D(v)+J(v)D(u)=D(K) | Existing `jordan_lie_sum` |
| 2 | D(u)J(v)+D(v)J(u)=D(K) | New `lie_jordan_sum` |
| 3 | D(u)D(v)-D(v)D(u)=D(S) | Existing `lie_lie_difference` |
| 4 | J(u)J(v)-J(v)J(u)=D(S) | New `jordan_jordan_difference`, reusing `commutator_apply` |
| 5 | J(u)J(v)+J(v)J(u)=J(K)+2C(u,v) | Existing `jordan_jordan_sum` |
| 6 | D(u)D(v)+D(v)D(u)=J(K)-2C(u,v) | Existing `lie_lie_sum` |
| 7 | D(u)J(v)-D(v)J(u)=J(S)+2A(u,v) | Existing `lie_jordan_difference` |
| 8 | J(u)D(v)-J(v)D(u)=J(S)-2A(u,v) | New `jordan_lie_difference` |

These require neither an idempotent nor square-zero coefficients.
The source's four readouts are division-free equalities for 2J(K), 4C,
2J(S), and 4A. Cancelling those factors would require additional hypotheses.

## Peirce specialization and new consequences

Assume only p*p=p. Define u=peirce10 p a and v=peirce01 p b, with a and b
independent, and g=p-(1-p). Prove g*C(x)=C(x)*g=A(x) and
g*A(x)=A(x)*g=C(x). This is multiplication by the grading element, not
conjugation by it.

Additional derived consequences, explicitly beyond the source's listed
left-output identities: C(g*x)=-A(x), A(g*x)=-C(x); both maps annihilate
the two off-diagonal input corners and depend only on pxp+(1-p)x(1-p).
The 11 and 00 output readouts are uxv and vxu for C, and uxv and -vxu for A.
Both outputs commute with p; the arbitrary input is never assumed to do so.

## Cyclic trace branch

For an additive map tau with the named hypothesis tau(ab)=tau(ba), prove
  tau(C(x))=tau(Kx), tau(A(x))=-tau(Sx).
The former is reused. Also derive bilinear dualities
  tau(C(x)y)=tau(xC(y)), tau(A(x)y)=-tau(xA(y)).
No positivity, nondegeneracy or Hilbert-space inner product is inferred.

## Real matrix obstruction

For the non-diagonal real matrix u=[[1,1],[-1,-1]], prove u*u=0 and
u*uᵀ ≠ uᵀ*u. Its signed action on 1 equals [[0,-4],[-4,0]], whose quadratic
form at (1,1) is -8. The Lean obstruction uses native `Matrix.PosSemidef`.
Thus even an adjoint-paired signed action is not automatically a positive
map. This countermodel is an audit of a stronger interpretation, not a
replacement for the universal noncommutative theorems.

## Inductive colimit

Use the existing real full-matrix tensor tower, its bonding maps, `ofStage`,
and `directLimitLift`. Prove Peirce-sandwich naturality, the grading identity
in the limit, compatibility with refinement, and both universal-lift laws.
The existing faithful-inclusion nonvanishing theorem remains available.
No new colimit, diagonal cylinder model, limiting trace, completion, or
analytic structure is invented. Hestenes/Krein analyticity is not a
conclusion of the purely algebraic intake and is not weakened or replaced.

## Source corrections and scope barriers

The isolated prose occurrence N_- X N_- is a transcription error relative
to the source's subsequent definition N_- X N_+. The formalization follows
the definition and the eight-row table; this choice is explicit.
The six words are a formal expansion list, not necessarily a linearly
independent basis after evaluation in a matrix algebra.
Cancellation of sandwich terms does not prove unitarity or a time flow.
The term "Kraus" is not applied to general or signed maps: positivity and
normalization require separate hypotheses. No mass-gap, field equation,
quantum channel classification, or physical conservation law is asserted.

## Verification scope

The existing `check_lie_jordan_peirce.py` target list is extended to all five
new modules; its existing serial source-closure and transitive-axiom audit
remain the checker. Repository dependency pins and pre-existing workflows
are unchanged. The exact run result, checked revision, hashes and warnings
are supplied by the CI artifact, not by this contract. A passing scoped
check does not certify a root-package build or unrelated repository CI.

## Entry point

```lean
import InfoGeometry.Canonical.LieJordanOctetSynthesis
```
