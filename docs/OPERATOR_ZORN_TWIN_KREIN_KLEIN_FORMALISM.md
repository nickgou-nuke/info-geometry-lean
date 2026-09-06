# Operator-Zorn twin, modular/Krein, Weyl, and Klein formalism

## Exact reconstruction

The proposed architecture contains several related but non-identical objects.
The implementation keeps them typed separately.

### 1. The `4+4` operator coordinate

For any operator ring `A`, one four-operator vector is

```text
V4(A) = A x A^3.
```

The doubled coordinate is

```text
V4(A) x V4(A) = (a,u) | (v,b).
```

This is exactly equivalent, as coordinate data, to the native four-field
operator-Zorn carrier

```text
(n_plus, n_minus, sigma_plus, sigma_minus).
```

The two halves are the two Peirce sheets.  The equivalence itself is not an
assertion that arbitrary noncommuting coefficients form the classical split
octonion algebra.

### 2. Two distinct products

The repository owns two products and this PR does not conflate them.

#### Native operator-valued Zorn product

The native product contains the operator cross product.  For a pure chiral
coordinate `(0,u;v,0)`, its square contains

```text
operatorCross u u,
operatorCross v v.
```

For noncommuting entries these self-cross terms need not vanish.  The theorem

```text
operatorCross u u = 0
```

is equivalent to three pairwise commutation equations among `u 0`, `u 1`, and
`u 2`.  Thus native chiral nilpotency is conditional.

#### Associative operator-Zorn shell

`InfoGeometry.Physics.OperatorZornMatrix A` is transported from ordinary
`2 x 2` matrices over `A`.  Its multiplication is associative.  Strict upper
and lower Peirce channels square to zero for purely triangular matrix reasons.

The associative shell is used for Dirac--Kahler blocks, group representations,
and block-operator calculations.  It is not renamed as the native
non-associative Zorn product.

## Peirce and Cartan structure

In the associative shell define

```text
e_plus  = diag(1,0),
e_minus = diag(0,1),
Gamma   = diag(1,-1),
S       = [[0,1],[1,0]].
```

The implementation proves

```text
e_plus^2=e_plus,
e_minus^2=e_minus,
e_plus e_minus=e_minus e_plus=0,
e_plus+e_minus=1,
Gamma^2=1,
S^2=1.
```

Every block has its four Peirce corners

```text
e_plus X e_plus,
e_plus X e_minus,
e_minus X e_plus,
e_minus X e_minus,
```

and their sum is exactly `X`.

The inner Cartan involution

```text
theta(X)=Gamma X Gamma
```

fixes diagonal entries and negates off-diagonal entries.  Its commutator table
is

```text
[even,even] -> even,
[even,odd]  -> odd,
[odd,odd]   -> even.
```

## Twin light-cone/Weyl soldering

An operator-valued four-vector `x=(x0,x1,x2,x3)` is soldered to

```text
sigma(x) = [[x0+x3, x1-i x2],
            [x1+i x2, x0-x3]].
```

For scalar complex coefficients this specializes exactly to the existing
Pauli paravector matrix and therefore recovers the repository's Minkowski
determinant theorem.

Two four-vectors and two chiral channel operators form the nested block

```text
Z = [[sigma(Psi_forward), A_LR],
     [A_RL,               sigma(Psi_backward)]].
```

The outer Cartan involution fixes the two Weyl waves and negates `A_LR,A_RL`.
The sheet exchange swaps both diagonal waves and both channel directions.

## Algebra and commutant

A `ModularTwinRepresentation A B` contains:

```text
leftRep  : A ->+* B,
rightRep : A ->+* B,
[leftRep(a),rightRep(b)] = 0,
J : B ≃+* B,
J^2=1,
J(leftRep(a))=rightRep(star a),
J(rightRep(a))=leftRep(star a).
```

The induced outer Zorn exchange is an involutive ring automorphism.  The two
diagonal entries represent algebra and commutant boundary operators.  The two
off-diagonal entries are independent twisted intertwiners.

For opposite channels

```text
q_plus  left(a)  = right(star a) q_plus,
q_minus right(a) = left(star a)  q_minus,
```

the closed two-step products satisfy

```text
[q_minus q_plus, left(a)] = 0,
[q_plus q_minus, right(a)] = 0.
```

A single twisted channel does not imply this result; both directions are
required.

## Krein polarization

Each sheet can carry an independent bounded real Hestenes--Krein modular datum
with fundamental symmetry `J_plus` or `J_minus` and modular generator `K_plus`
or `K_minus`.

Componentwise conjugation

```text
T |-> J T J
```

is involutive.  The stored modular generators are fixed because they are
Krein self-adjoint.  Spatial/operator rails can be assigned even or odd Krein
parity separately.

This Krein symmetry is not identified with Tomita conjugation, Kramers time
reversal, or the Klein glide.

## Two-boundary normalized matrix coefficients

A boundary pair consists of

```text
pre, post : C^2,
<post,pre> != 0.
```

For a matrix operator `A`, the normalized matrix coefficient is

```text
A_w = <post,A pre>/<post,pre>.
```

The implementation reads all four outer Zorn entries in this way.  Under
Cartan polarization, diagonal readouts are fixed and channel readouts change
sign.  Under sheet exchange, the forward/backward and left/right readouts are
swapped.

This is the exact algebraic core of a pre/post-selected readout.  No claim of
nonlocal transport or a physical TSVF experiment follows from the definition.

## Dirac--Kahler block

For ring elements `d,delta` satisfying

```text
d^2=0,
delta^2=0,
```

define

```text
D=d-delta,
Delta=d delta + delta d.
```

The implementation proves

```text
D^2=-Delta.
```

The pure odd outer block

```text
[[0,D],[D,0]]
```

squares to

```text
diag(-Delta,-Delta).
```

For independent diagonal boundary waves `W_plus,W_minus`, the general square
is retained with the exact noncommutative off-diagonal defects

```text
W_plus D + D W_minus,
D W_plus + W_minus D.
```

Diagonal decoupling is proved only when those expressions vanish.

## Klein representation

For a unit `u` in the coefficient ring, define

```text
T(u)=diag(u,u^-1),
G=[[0,1],[1,0]].
```

Then

```text
G^2=1,
G T(u) G=T(u^-1).
```

This is a finite operator representation of the Klein presentation relation.
It is distinct from constructing the topological quotient, which is supplied
by the stacked base PR.

## Chiral Lorentz action

The abstract owner accepts any two representation homomorphisms and a pair of
opposite intertwiners.

The concrete owner specializes to

```text
SL(2,C)_L x SL(2,C)_R.
```

The diagonal Weyl matrices transform by

```text
X_plus  |-> g_L X_plus g_L^dagger,
X_minus |-> g_R X_minus g_R^dagger,
```

and the channels by

```text
A_LR |-> g_L A_LR g_R^dagger,
A_RL |-> g_R A_RL g_L^dagger.
```

The action law, Cartan equivariance, sheet-exchange covariance, and determinant
preservation on both diagonal Weyl waves are proved.

## Cyclotomic and nilpotent sectors

The diagonal Cartan clock

```text
C(zeta)=diag(zeta,zeta^-1)
```

satisfies `C(zeta)^n=1` whenever `zeta^n=1` in the unit group.

Strict upper and lower Peirce channels satisfy

```text
N_plus^2=0,
N_minus^2=0
```

in the associative shell.  The existing two-sheet/three-colour clock--shift
module supplies the independent cubic Weyl relations.

## Involutions kept separate

The formalism contains several involutions or square laws:

```text
Cartan theta^2       = +1,
Tomita-style J^2     = +1,
Klein sheet G^2      = +1,
Kramers T^2          = -1.
```

They act on different carriers and are not equated.

## Public import

```lean
import InfoGeometry.OperatorAlgebra.OperatorZornTwinAll
```

## Verification boundary

The source introduces no intended `sorry`, `admit`, or custom axiom.  The
transitive audit is

```lean
InfoGeometry.OperatorAlgebra.OperatorZornTwinAudit
```

and the focused script is

```bash
bash scripts/check_operator_zorn_twin.sh
```

The branch is source-level until a functioning Lean runner elaborates the new
modules.  In particular, it does not yet prove:

1. that the fully noncommutative native operator-Zorn product is alternative;
2. that it is isomorphic to the classical split-octonion algebra;
3. a full `Spin(5,5)` spinor representation on the nested Weyl block;
4. that a pre/post boundary pair physically realizes Aharonov's TSVF;
5. analytic domains, self-adjoint extensions, or spectral completeness for an
   unbounded Dirac--Kahler operator;
6. an equality between the modular, Krein, Kramers, Cartan, and Klein maps.
