# Non-isotropic `Conf_3` external computation plan

Target complement, after translation:

```text
U_D = {(a,b) in C^D x C^D | q(a) q(b) q(a-b) != 0}
```

For `D=4` use the split complex quadric

```text
q(z)=z0*z1+z2*z3
```

which is equivalent over `C` to the light-cone quadric.

## Current audit status

The naive logarithmic Orlik--Solomon/Arnold relation is false for the literal
forms `alpha_ij = dlog q(x_i-x_j)`.  The OS-alpha rank-24 branch is therefore a
quotient/projection branch, not the literal de Rham algebra.  The rank-32
product/Leray branch is also only a candidate/socket until a genuine
Dupont/Gysin or D-module computation is supplied.

Finite-field point count for the `D=4` sum-of-squares/split-positive form gives

```text
#U_4(F_q) = q^2 (q-1)^2 (q+1) (q^3 - 2q^2 - q + 3)
```

This does not match the naive independent rank-32 specialization
`q*(q-1)^5*(q+1)^2` and does not match the naive OS rank-24 specialization.
So point counting is a warning invariant, not a proof of rank 32.

## Installed local tool

A local conda environment was created with Singular:

```bash
conda run -n singular-noniso Singular -q proofs/singular_noniso_conf3_d4_strata.sing
```

This script verifies for the split `D=4` model:

- `I=(q(a),q(b),q(a-b))` has dimension `5`, hence codimension `3` in `A^8`.
- The triple intersection is generically transverse: the rank-defect locus has
  dimension `4 < 5`.
- An explicit smooth triple-intersection point is `a=e0`, `b=e2`, where a 3x3
  Jacobian minor evaluates to `1`.
- The hypersurface critical locus of `f=q(a)q(b)q(a-b)` has dimension `6`.

This supports the conclusion that the three divisors are not globally governed
by a naive Arnold relation.

## Software route to actual cohomology

To actually prove or refute total rank `32`, use one of:

1. **Oaku--Takayama D-module computation** for
   `Q[a,b,1/f]`, with `f=q(a)q(b)q(a-b)`.  Preferred tools:
   - Macaulay2 `Dmodules` if available;
   - Risa/Asir Oaku packages;
   - Singular/Weyl-algebra tooling if sufficient.
   - SageManifolds is used only for geometry/spec checks (parameter-base charts,
     vector fields, flow bookkeeping), not for replacing the de Rham computation.

2. **Dupont/Gysin model after resolving the divisor**:
   - compute the singular stratification of the union of quadrics;
   - build a wonderful/resolution model;
   - compute the Gysin differential and cohomology ranks.
3. **Independent finite-field/E-polynomial campaign**:
   - count over many finite fields/forms;
   - compare with candidate mixed Hodge/E-polynomial;
   - use only as evidence unless mixed-Tate/polynomial-count comparison is proven.

## Theorem-honest Lean import target

Any external result should be imported as a finite certificate, not as an axiom
leak.  The desired certificate should include at least:

```text
Betti numbers b_0,...,b_8 for U_4
basis labels for cohomology classes
multiplication table or enough relations for the ring presentation
cooperad pullback/collision maps on basis labels
trace/log of the external computation: software version, script, output hash
```

Until then, the repository should say:

```text
rank-32 = finite product/Leray candidate socket
rank-24 = OS-alpha projection quotient
actual de Rham cohomology = open external Dupont/Gysin/D-module computation
```
