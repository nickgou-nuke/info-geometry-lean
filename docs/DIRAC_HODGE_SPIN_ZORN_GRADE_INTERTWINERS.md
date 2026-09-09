# Dirac--Hodge, real spin, and operator-Zorn grade intertwiners

## Scope

This development closes the next algebraic frontier above the two-sheet
operator-Zorn carrier.  It builds three distinct structures and then proves the
maps between them:

1. a specified finite two-term differential-form complex with `D=d+delta`;
2. a real spin representation and the correct left/right Weyl relation;
3. faithful grade-preserving maps from native `Cl(5,5)` and the corrected
   Freudenthal contact algebra into one associative operator-Zorn envelope.

The construction does not identify the Clifford and Freudenthal algebras.  They
act through separate factors of a direct-product coefficient algebra.

## 1. Specified differential-form complex

For a real matrix

```text
B : C^0 -> C^1
```

on finite cochain spaces, set

```text
Omega = C^0 x C^1,
d(f,g)     = (0, B f),
delta(f,g) = (B^T g, 0).
```

The code proves

```text
d^2 = 0,
delta^2 = 0,
D = d + delta,
D^2 = d delta + delta d.
```

The form-degree involution

```text
gamma(f,g) = (f,-g)
```

satisfies

```text
gamma^2 = 1,
D gamma = - gamma D,
[D^2,gamma] = 0.
```

The transpose definition gives the finite adjoint identity

```text
<d omega, eta> = <omega, delta eta>.
```

The operator-Zorn block is

```text
Z_D = [[0,delta],[d,0]].
```

Its square is

```text
Z_D^2 = diag(delta d, d delta).
```

If one embeds a form diagonally in the two sheets and then adds the two output
sheets, the result is exactly `D omega`.  This is the explicit intertwiner:

```text
sumSheets (Z_D . diagonalForm(omega)) = (d+delta) omega.
```

## 2. Dagger multiplier versus right-handed representation

For `g in SL(2,C)` and a Hermitian Pauli matrix `X`, the vector action is

```text
X |-> g X g^dagger.
```

Here the right matrix multiplier is literally `g^dagger`.  It is an
antihomomorphism:

```text
(gh)^dagger = h^dagger g^dagger.
```

Therefore it is not the right-handed spinor representation.  The latter is

```text
g_R = (g^{-1})^dagger,
```

which is a genuine homomorphism:

```text
g_R(gh) = g_R(g) g_R(h).
```

The paired Weyl action

```text
(psi_L,psi_R) |-> (g psi_L, (g^{-1})^dagger psi_R)
```

is proved to satisfy the group-action law.  The Pauli-vector congruence action
preserves both Hermiticity and determinant.

This resolves the ambiguous slogan `g_R = g_L^dagger`:

- it is correct for the right multiplier in `g X g^dagger`;
- the right-handed group representation is inverse-adjoint.

## 3. Faithful operator-Zorn envelope

For any associative ring `A`, define

```text
Env(A) = Matrix (Fin 2) (Fin 2) A.
```

This is the faithful matrix representation of the repository's associative
operator-Zorn carrier.  The diagonal map

```text
a |-> diag(a,a)
```

is an injective ring/algebra homomorphism and preserves commutators.

For an `R`-algebra `A`, the left-regular action

```text
L_a(x) = a x
```

is a faithful algebra representation.  It preserves adjoint grades:

```text
[H,x] = k x  =>  [L_H,L_x] = k L_x.
```

## 4. Native real `Cl(5,5)` spin representation

The repository already supplies

```text
spinorRepresentation 5 : Cl(5,5) -> Matrix 32 32 R.
```

The new owner defines its action on real spinors and proves

```text
rho_s(xy) psi = rho_s(x) (rho_s(y) psi).
```

It also proves the intertwining law

```text
rho_s(L_x y) = rho_s(x) rho_s(y).
```

The common envelope nevertheless uses the left-regular representation for
faithfulness, because injectivity of the existing `spinorRepresentation 5` is
not assumed.  The spin representation is a proved finite-dimensional readout
of the same Clifford multiplication.

## 5. One common Clifford--Freudenthal target

Let

```text
A_Cl = End_R(Cl(5,5)),
A_F  = End_R(H_common),
A_joint = A_Cl x A_F.
```

The common operator-Zorn envelope is

```text
Env(A_joint).
```

The two source maps are

```text
Cl(5,5) -> Env(A_joint),
x |-> diag((L_x,0),(L_x,0)),
```

and

```text
g_contact -> Env(A_joint),
u |-> diag((0,rho_F(u)),(0,rho_F(u))).
```

Both are injective and preserve their respective brackets.  Their cross
commutator vanishes because they occupy different direct-product factors.
This is a direct-product representation, not an isomorphism or dynamical
coupling.

The component maps are bundled as native Mathlib Lie homomorphisms.  More
strongly, the branch constructs one faithful map

```text
rho_joint : Cl(5,5)_Lie x g_contact ->_Lie Env(A_joint)
```

with

```text
rho_joint([z,w]) = [rho_joint(z),rho_joint(w)].
```

Its injectivity is proved by evaluating the Clifford left-regular component at
the unit and using faithfulness of the existing contact representation on the
second component.

## 6. Grade preservation

The joint Euler coefficient is

```text
(L_D, rho_F(H)).
```

The target grade is the adjoint eigenspace

```text
Env_k = { X | [diag(L_D,rho_F(H)), X] = k X }.
```

The code packages `Env_k` as a Mathlib `Submodule` and proves with native Lie
identities

```text
[Env_k, Env_l] subset Env_(k+l).
```

It constructs restricted linear maps

```text
g_Cl,k -> Env_k,
g_F,k  -> Env_k
```

and proves both are injective.  It also constructs the synchronized product
map

```text
g_Cl,k x g_F,k -> Env_k
```

and proves it injective.

The selected native Clifford lanes are

```text
[v5,v4] : -2,
v5       : -1,
D        :  0,
u5       : +1,
[u5,u4] : +2.
```

The selected Freudenthal lanes are

```text
E_-       : -2,
x_-       : -1,
T_0       :  0,
x_+       : +1,
E_+       : +2.
```

Both packets land in the same target integer-grade convention, while remaining
in commuting product factors.

## Public import

```lean
import InfoGeometry.OperatorAlgebra.DiracHodgeSpinZornAll
```

## Verification

```bash
bash scripts/check_dirac_hodge_spin_zorn.sh
```

The focused audit owner is

```text
lean/InfoGeometry/OperatorAlgebra/DiracHodgeSpinZornAudit.lean
```

and requests transitive `#print axioms` reports for the principal theorem
chain.

## Remaining frontier

The following are not inserted as assumptions:

1. an interacting coupling between the Clifford and Freudenthal direct-product
   factors;
2. injectivity or surjectivity of the `32 x 32` spinor representation beyond
   the theorems already owned by the repository;
3. an unbounded analytic Dirac operator with domains and self-adjoint closure;
4. a continuum de Rham/Hodge complex or a spectral triple;
5. an isomorphism between the native `Cl(5,5)` conformal grading and the
   Freudenthal contact grading.

The next exact mathematical step is a nontrivial bimodule or Lie action
coupling the two product factors while preserving the joint grade.
