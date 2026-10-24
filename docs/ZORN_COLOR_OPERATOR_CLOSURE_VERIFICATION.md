# Corrected native Zorn color operator closure

## Result and scope

The submitted duplicate octonion carriers were not installed. Existing native
`ZornVectorMatrix R`, `L_map`, `Module.End`, CAR, grading, Majorana and color
bilinear owners were reused and independently checked. Four focused owners
extend generator relations to actual homogeneous submodules, faithful parameter
maps, bracket closure, dimensions and an obstruction to the gl(3|1) claim.

Conventions: coordinates `(a,u,v,b)`, `Q_i=L(U_i)`, `C_i=L(-V_i)`, and
operator multiplication `AB=A after B`. The existing Catto element basis V,-U
is different; the signed-CAR owner explicitly accounts for that distinction.

The correct projector and grading are

```
P = L(E11) : (a,u,v,b) ↦ (a,u,0,0)
Gamma = L(diagonal 1 (-1)) : (a,u,v,b) ↦ (a,u,-v,-b)
Gamma = product_i [C_i,Q_i] = 2 P - 1.
```

The existing `ZornRightProjectionObstruction` provides a permanent counterexample
to the proposed `(0,u,0,b)` projector. Existing Majorana owners prove opposite
squares, mixed anticommutation, mode products and flips, six-factor volume,
collective squares ±3, and rotation covariance with the **difference** of the
positive- and negative-signature bivectors. Their proofs are included below.

## New owner declarations

All paths are under `lean/InfoGeometry/Algebra/`; namespace
`InfoGeometry.Algebra.ZornColorOperatorCoordinates`.

- `ZornColorOperatorCoordinates.lean`: `evenMap`, `oddMap`, explicit action,
  injectivity, actual submodule ranges, disjointness in every characteristic,
  `finrank_evenPart = 10` and `finrank_oddPart = 6` over a field.
- `ZornColorOperatorClosure.lean`: all homogeneous bracket formulas,
  `bracket_mem`, `homogeneousBracket`, inherited `homogeneous_super_jacobi`,
  even-projector commutation, odd tangency, and `odd_bracket_central` against
  **every** ambient endomorphism.
- `ZornColorOddDerived.lean`: faithful native Mathlib `gl3Representation`,
  exact `oddDerived_eq_scalar`, `finrank_oddDerived = 1`, and total even-plus-odd
  dimension 16.
- `ZornColorGL31Obstruction.lean`: a native `SuperMatrix 3 1 R` noncentral odd
  bracket, and `not_faithful_gl31_with_CAR_odd`. Over **any nontrivial commutative
  ring**, no injective linear map preserving homogeneous superbrackets can send
  the entire gl(3|1) odd component into the raw CAR odd submodule.

The even operator is the actual sum `Σ M_ij E_ij + c I`, not a substituted
matrix action. The odd operator is `L(offDiagonal p (-q))`. The proved laws are

```
[even(M,c), even(N,d)] = even(MN-NM,0)
[even(M,c), odd(p,q)]  = odd(Mp,-transpose(M)q)
{odd(p,q), odd(r,s)}   = -(dot(p,s)+dot(r,q)) I.
```

Together with disjointness, these realize the gl3 action on the fermionic
Heisenberg operator superalgebra. The implementation uses actual Mathlib
submodules and a closed homogeneous bracket, not a new assumed-law class or
an asserted bundled semidirect-product equivalence.

## Verification

- Locked build of `InfoGeometry.Algebra.All` and `InfoGeometry.All`: **PASS,
  27,012 jobs**, `/tmp/zorn-color-integrated-final.log`.
- Strict all-declaration kernel replay/transitive axiom allowlist: **14 selected
  owners, 780 declarations, all PASS**, `/tmp/zorn-color-closure-axioms.log`.
- Source hashes unchanged across final CAS and kernel replay: `SOURCE_DRIFT []`.
- New four owners: no admitted proofs, custom axioms, unsafe/partial declarations,
  or native-decision proofs in the source-aware scan. Their final builds emitted
  no owner warnings. Staged task whitespace checks passed.
- Allowed axioms: `propext`, `Classical.choice`, `Quot.sound` only.

Audit counts, including compiler-generated declarations:

| Owner | Count |
|---|---:|
| ZornVectorMatrix | 524 |
| ZornSignedCAR | 11 |
| ZornLeftGrading | 8 |
| ZornLeftParity | 6 |
| ZornLeftMajorana | 28 |
| ZornMajoranaRotations | 8 |
| ZornColorBilinears | 9 |
| ZornRightProjectionObstruction | 2 |
| ZornColorOperatorCoordinates | 24 |
| ZornColorOperatorClosure | 13 |
| ZornColorOddDerived | 12 |
| ZornColorGL31Obstruction | 2 |
| Canonical/GLSupermatrixGradedLie | 103 |
| OperatorAlgebra/QuadraticNoncommutativeIdentity | 30 |

The four new owners contribute **51** audited declarations. The larger count
includes reused owners; it is not a count of newly written theorems. The umbrella
build is not a repository-wide axiom audit or a globally warning-free build.
Unrelated existing dependency/linter warnings remain. No task commit was made.

## Exact computational reproduction

```
/home/goutev/miniforge3/envs/sage/bin/python \
  scripts/check_zorn_color_operator_closure.py
```

Run under the shared build lock after compiler-process inspection. The checker
reuses `tools/sympy/split_octonion_multiplication.py`, freezes the ordered column
basis `(E11,E22,U0,U1,U2,V0,V1,V2)`, records source SHA-256 values, and uses exact
SymPy arithmetic. It checks CAR, bilinear brackets, Majorana/rotation laws,
collective squares, actual ranks 10/6/16 and odd-derived rank 1, the wrong-projector
witness, and standard gl(3|1) odd-bracket rank 9. Final output:
`/tmp/zorn-color-closure-cas.json`. CAS is supplementary evidence only; the
universal non-faithfulness obstruction above is proved independently in Lean.

New-owner SHA-256 values:

```
66e441a85922e1ce562dd800d57e462e056e4c172ed112487d82bdec55738caf  ZornColorOperatorCoordinates.lean
e1dd50c2cbacce7e64a8efe9777e3d05c6f6565e7dc3e5ac0330ee9364227763  ZornColorOperatorClosure.lean
e3b5c0be389354812e8e7e39647e0df57f246d33b13eba0ed5905bf8436dc915  ZornColorOddDerived.lean
1ff76078bfb2300d589f5e0cdf1804de98ab49dc7407f3488454ae34523e3ed1  ZornColorGL31Obstruction.lean
```

## Explicit nonclaims

No global super-Grassmannian, atlas, sheaf or representability theorem is derived
from the projector tangent equation. No Hilbert adjoint/unitarity, paper equation
authentication, physical color identification, or full Clifford faithfulness is
asserted. In characteristic two the projector decomposition remains meaningful,
but the involution's eigenvalues do not distinguish the two halves. Earlier
staged derivation/triality/Pauli-product extensions are separate work and are
not included in this receipt's selected-owner audit.
