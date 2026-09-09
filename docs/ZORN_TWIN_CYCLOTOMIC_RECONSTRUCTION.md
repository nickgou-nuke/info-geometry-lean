# Twin-state ratios and coefficient sectors of the nonassociative Zorn field

## Scope and verification

The reconstruction target is `Pasted text(20260906-071521).txt`. Its equations
are proposals, not proof assumptions. The base is relational state data and
homogeneous representatives; no external spacetime is manufactured from
internal Zorn labels. Source-owner discovery is recorded in the adjacent
`ZORN_TWIN_CYCLOTOMIC_REUSE_MAP.md`.

Entry point:

```lean
import InfoGeometry.Canonical.OperatorZornTwinCyclotomic
```

The carrier is the existing `NCZornElement A` / `OperatorZornMatrix A`.
The coefficient ring A is associative. The full Zorn multiplication is not.
All displayed parentheses, ordered dot products, and cross products remain.
Only a native `NonUnitalNonAssocRing` structure is added where needed to
package proved additive and distributive laws. That structure has no
associativity field. Native multiplicative equivalences do not require an
associative multiplication and do not create one.

**Verification boundary:** the source contains explicit Lean proof scripts.
No successful native build of this continuation is asserted in this document.
The previous launcher attempt stopped because Lake was unavailable. A fresh
exact-head elaboration and complete transitive-axiom audit are required. The
provided independent checker supplies separate algebraic evidence only.

## 1. Repair the product without removing its noncommutative channels

Let C(U,V) denote the native ordered cross product. The attachment's
half-epsilon-commutator expression is exactly

    C_comm(U,V) = (C(U,V) + C(V,U))/2.

This is symmetric in its two operator-vector arguments. For commuting
coefficients it vanishes. The native classical cross product does not:
C(e1,e2)=e3. The remaining channel is

    C_ext(U,V) = (C(U,V) - C(V,U))/2,
    C(U,V) = C_ext(U,V) + C_comm(U,V).

Likewise the ordered dot product splits as

    dot(U,V) = (dot(U,V)+dot(V,U))/2 + (dot(U,V)-dot(V,U))/2.

Discarding either part changes the multiplication. At U=V the commutator
cross channel equals the full ordered self-cross and retains the three
coefficient commutators. These are not removed by the scalar identity
u cross u=0.

`OperatorZornOrderedChannels` proves these statements on the existing
operator vector carrier. The undivided epsilon identity is over any ring;
the half-sums use the real scalar action.

A diagnostic `sourceProduct` reproduces the proposed symmetric-dot /
commutator-cross product only to test it; it is never installed as an
instance. Over real coefficients, take X with zero diagonals and both vector
entries e1, and take Y=sigmaPlus(e2). For this proposed product,

    X X = 1,   X Y = 0,
    (X X)Y = Y != 0 = X(XY).

It therefore fails left alternativity already on scalar coefficients.
The actual native Zorn product, not this replacement, is used throughout.

## 2. Distinguish the three kinds of exchange

The existing unsigned flip S(a,b,u,v)=(b,a,v,u) is an additive involution.
Its precise product defect is

    S(XY)-S(X)S(Y) = (0,0,2 C(u_X,u_Y),-2 C(v_X,v_Y)).

Thus its square-one law alone does not make it an algebra automorphism.

The signed exchange

    F(a,b,u,v) = (b,a,-v,-u)

satisfies F^2=1, additivity and F(XY)=F(X)F(Y) for freely noncommuting
coefficient rings. It is packaged as a native `MulEquiv` on the same
nonassociative carrier. It transports the associator rather than killing it:

    F(as(X,Y,Z)) = as(FX,FY,FZ).

The source also conflates a complex-linear fundamental symmetry with a
conjugate-linear modular conjugation. On a fixed complex module the only map
that is both complex-linear and conjugate-linear is zero: its action on i*x
would have to be simultaneously i*T(x) and -i*T(x). The source provides
native linear/semilinear statements of that obstruction. In particular an
invertible complex-linear symmetry is not that conjugation. This does not
rule out separately constructed real internal-phase descriptions.

No Klein-bottle quotient topology, cyclic/separating vector, Tomita polar
decomposition, modular operator, or identification of an algebra with its
commutant is derived from either sheet exchange. Those need their own data
and proofs. The separate existing glide and Hodge modules are not renamed
as such theorems.

## 3. Gauge transport keeps the field strength and associators

The signed exchange intertwines the parent's actual coefficientwise
commutator derivative delta_p. Consequently it transports the existing
covariant action, field strength, curvature action and cyclic Bianchi
expression for arbitrary direction labels. It commutes with the existing
coefficient-unit gauge family.

The parent curvature identity remains

    [nabla_x,nabla_y]Z = delta_[p_x,p_y]Z + F_xy star Z
                        - as(Phi_x,Phi_y,Z) + as(Phi_y,Phi_x,Z).

The Bianchi expression retains its background-commutator terms and the full
six-term associator alternation. Neither is assumed zero. The generator
transformation p'=p-[p,g]g^-1 remains inherited from the parent. These are
algebraic identities, not a differential-geometric or Noether theorem
obtained merely by choosing names for the labels.

## 4. The coefficient nucleus justifies the allowed Peirce parentheses

Embed a coefficient by iota(a)=(a,a,0,0). Its multiplication and injectivity
are proved. More importantly, for every a and arbitrary full X,Y,

    (iota(a) star X) star Y = iota(a) star (X star Y),
    (X star iota(a)) star Y = X star (iota(a) star Y),
    (X star Y) star iota(a) = X star (Y star iota(a)).

These are exactly three nucleus laws. They do not assert that iota(a)
commutes with X, or that an arbitrary Zorn element is in the nucleus.

Define a corner with its parentheses fixed:

    corner(p,q,X) = (iota(p) star X) star iota(q).

Every internal coefficient is then p*x*q. The product law is

    corner(p,q,X) star corner(r,s,Y)
      = corner(p,s, X star (iota(q*r) star Y)).

It vanishes when q*r=0. The interior product is not replaced by a scalar or
by multiplication of observations. Exchange commutes with corner extraction.
A coefficient gauge change transports both projectors and the field; it is
not legitimate to move the field and silently freeze the projectors.

## 5. All finite coefficient blocks, then the fourfold example

For arbitrary finite index J and arbitrary coefficient ring B, the native
matrix coefficient algebra Matrix J J B has constructed projectors

    P_k = diagonal(1 at k, 0 elsewhere).

Their idempotence, mutual orthogonality and sum-one resolution are proved.
Applied through the nucleus, these give every J-by-J corner of the full
operator-Zorn field and an exact reconstruction

    X = sum_j sum_k corner(P_j,P_k,X).

No operator-vector channels are dropped. This is not replacing the Zorn
algebra by a matrix algebra: matrices are the coefficients in this
instantiation, and the generic nucleus layer is independent of matrix size.

In the fourfold complex coefficient example,

    U = diagonal(1,i,-1,-i),
    N e_k = e_(k+1) for k<3,   N e_3=0.

The code constructs and proves

    U^4=1, N^4=0, N^3!=0,
    U N = i N U,
    P_k = (1/4) sum_(m=0)^3 (-i)^(k*m) U^m,
    N P_k = P_(k+1 mod 4) N.

The source's ordinary commutator equation [U,N]=iN is false for this
realization. The q-commutation law above is the one that yields the stated
sector shift. At the last sector both sides of the shift identity are zero;
there is no cyclic raising transition there.

The fourfold data are assembled into the existing `FourierCyclotomicReadout`
interface only after its projector laws have been proved. A fourfold field
has sixteen coefficient Peirce blocks, not just four. The nonzero field
iota(N) has every diagonal corner zero. Keeping only those four corners
would erase a nonzero field. No physical generation count, superselection
rule, protected particle content or classification of all order-four
operators follows from this finite example.

## 6. Twin dyads are homogeneous, not automatically projectors

For a complex Hilbert space H, the native rank-one dyad is

    P_psi = rankOne(psi,psi),
    P_psi^2 = <psi,psi> P_psi.

Normalization is needed before calling it an idempotent projector.
`twinPotential` puts the two dyads in the existing diagonal Zorn slots and
leaves both three-component operator vectors arbitrary. It imposes no
matrix realization of the full nonassociative product.

The amplitude ratio is guarded:

    weakRatio(Q,psi,phi) = none                    if <phi,psi>=0,
                        = some(<phi,Qpsi>/<phi,psi>) otherwise.

It is invariant under psi -> a psi and phi -> b phi for two independent
nonzero complex scalars. It need not be a positive expectation functional.
No physical amplification, measurement dynamics, or success probability is
inferred from the ratio identity alone.

## 7. Exact trace identity on its stated finite-dimensional domain

For finite-dimensional H, Mathlib's trace of rankOne(x,y) is <y,x>.
The native rank-one sandwich identity gives

    Tr(P_phi Q P_psi) = <phi,Qpsi><psi,phi>,
    Tr(P_phi P_psi) = <phi,psi><psi,phi>.

The denominator vanishes precisely at zero overlap. Therefore the guarded
trace quotient equals the guarded amplitude ratio, including the undefined
locus, and has the same two independent representative-scale invariances.
The trace is on the associative coefficient operator algebra, not on an
undefined product representation of the whole Zorn carrier. This does not
assert a finite trace on a general C*-algebra, an unbounded operator domain,
or a Type III state space.

This particular diagonal readout is independent of the free U,V entries.
It does not prove that those entries disappear from the Zorn multiplication
or that they encode this ratio without a separate readout construction.
Products and associators still precede any linear observation of the full
field, as in the parent projective-state construction.

## 8. Exact remaining boundary and reproducibility

The completed source-level continuation consists of ordered-channel
reconciliation, a full multiplicative exchange, the coefficient nucleus,
all finite matrix Peirce sectors, a concrete Fourier/raising system,
linear/semilinear separation, and native twin-ratio identities.

A genuine analytic modular standard form, quotient topology, global gauge
bundle with differential compatibility, and a Noether conservation theorem
require additional constructions. None appears here as a field assuming
its desired conclusion. These are distinct from the finite algebraic
statements, not reasons to stop developing the next local proof.

Native verification in a complete idle checkout:

```sh
python3 tools/quality/audit_zorn_twin_sources.py
bash scripts/quality/check_operator_zorn_twin.sh
```

The audit generator enumerates source declarations and hashes. The native
script uses the existing locked narrow-build owner and rejects missing axiom
readouts and axioms other than propext, Classical.choice and Quot.sound.
The lexical generator is not itself kernel verification.

Independent algebra diagnostics:

```sh
python3 tools/quality/check_operator_zorn_twin_exact.py
```

These diagnostics distinguish universal free noncommuting-coefficient
polynomial identities from finite matrix examples. Neither kind substitutes
for successful Lean elaboration of the exact published sources.
