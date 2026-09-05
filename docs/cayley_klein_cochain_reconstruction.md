# Cayley, binary cochain twist, and diagonal Berezinian: corrected reconstruction

## Scope and base

This is a separate development branch stacked on `bipolar-crossratio-log-sl2` (PR #136), starting at `1234190ece109cbd4a98b6e60abcbb043351a6b4`. It does not modify the older branch. The inherited project declares Lean v4.28.1 and Mathlib revision `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

There are eight new Lean modules, containing 86 public theorem/lemma declarations, one private finite-case helper, and explicit proof scripts. The audit module contains `#print axioms` commands for all 86 public declarations.

## 1. Equal real dimension is not algebraic identity

The carriers are the actual native `Matrix (Fin 2) (Fin 2) ℂ` and `InfoGeometry.Algebra.ZornMatrix ℝ`, not proxy products. `matrixSplitLinearEquiv` is a real-linear equivalence. Both real dimensions are eight. A concrete native associator gives a stronger obstruction than the failure of this particular map: no surjective multiplicative map from the associative matrix algebra to the full Zorn algebra exists.

Consequently the biquaternions are not an algebra real form of complex octonions. An algebra real form would complexify to that algebra; associativity survives scalar extension. A complex quaternion subalgebra or a real-linear slice is a different assertion.

The common `M₂(ℝ)` core is embedded along one native Zorn axis. With right-coefficient notation `A+B ell`, native multiplication gives

```
(A+iB)(C+iD) = (AC-BD) + i(AD+BC)
(A+B ell)(C+D ell) = (AC+conj(D)B) + (DA+B conj(C)) ell.
```

Here `conj` is the two-by-two adjugate. The proof scripts establish `ell²=I` and `ell A=conj(A) ell`. Anticommutation with trace-zero core elements is the relevant quaternionic law. A square-one generator is not a supercommutative Grassmann odd scalar; odd Clifford operators are a separate concept.

## 2. The product twist has two arguments

The existing `Z2ThreeCochainBridge` already owns `associatorCochain`, `twistedScalar`, `Z2Grade`, and `signUnit`. This PR reuses those definitions, but does not identify the owner's previously unconnected concrete example cochain with native Zorn multiplication.

The new tables are checked against native products. For grades `x,y` with coordinates indexed 0,1,2,

```
b_H(x,y) = x1*y0 + x2*y2
b_O(x,y) = x1*y0 + x2*y0 + x2*y1
           + x2*y0*y1 + x1*y0*y2 + x0*y1*y2
F_H = (-1)^b_H,   F_O = (-1)^b_O,   T = F_O / F_H.
```

All arithmetic in the exponents is in `ZMod 2`. The source is a binary cocycle. The target has cubic terms, and its associator parity is the sum of the six determinant monomials in `x,y,z`.

The actual homogeneous native-product identity is

```
splitGrade x * splitGrade y
  = (T x y : ℝ) • matrixSplitLinearEquiv (matrixGrade x * matrixGrade y).
```

Its associator is the coboundary of `T`, and satisfies the pentagon coefficient identity. The value on the three coordinate grades is `-1`. This nontrivial value does not give a nontrivial cohomology class: the explicit cochain makes it a coboundary. A generic bilinear parity exponent has trivial associator; `splitCochain_not_bilinear` rules out that proposed description for this actual table.

The PR establishes the concrete coefficient identities, not a bundled monoidal equivalence of graded categories or a constructed group-cohomology class.

## 3. The Cayley map is a coordinate map

The existing `cayleyToTemperature z=z/(1+z)` and `crossRatio01 s=s/(1-s)` are reused. With `C(z)=(z-1)/(z+1)` and `p(s)=2s-1`, the new scripts prove

```
C(crossRatio01 s) = p(s)
C(exp W) = Complex.tanh (W/2),  when exp W + 1 ≠ 0.
```

The chosen Cayley convention maps the right half-plane to the unit disk. It is not the upper-half-plane convention `(z-i)/(z+i)`. On the real slice, `logisticEquiv` constructs the equivalence from real rapidity to `(0,1)` with inverse logarithmic odds, and `2 logistic(t)-1=tanh(t/2)`.

The native Zorn Cayley map instead uses the composition-algebra inverse. Both inverse identities are proved from `N(X)≠0`. Its regular domain is `N(X+I)≠0`; on the diagonal idempotent plane it restricts to two scalar Cayley maps. No ordinary associative block-matrix inverse is used.

A concrete nonzero element whose square is `-I` yields a nontrivial zero sum of squares. Thus merely symmetrizing the split algebra does not supply the formally-real positivity needed for a Euclidean Jordan tube-domain interpretation.

## 4. The diagonal Berezinian requires two invertible blocks

`diagonalBerezinian : (ℂˣ × ℂˣ) →* ℂˣ` is an actual group character, `(a,d)↦a/d`. Its scalar readout is tied to the repository's `NCG.berezinianBlockDiag` using native one-by-one matrix determinants, not an arbitrary determinant functional.

For the proposed diagonal pair, BOTH `1+z` and `1-z` must be nonzero. On this domain,

```
Ber diag(1+z,1-z) = (1+z)/(1-z) = -1/C(z)
Ber diag(1+exp W,1-exp W) = -1/tanh(W/2).
```

After substituting the existing cross-ratio, the rational readout is `-1/(2s-1)`. On `s=1/2+i y`, the polarization is `2i y` and the readout is `i/(2y)` for `y≠0`. Only the midpoint is singular. The genuine punctured-neighborhood regularized limit is

```
lim_(s→1/2, s≠1/2) (s-1/2) (-1/(2s-1)) = -1/2.
```

No Goldstone mode, conformal anomaly, sheet collision, microscopic statistics, entropy production, or Lorentz-to-G₂ symmetry conversion follows from this rational pole. A Zorn grading is not a Berezinian supercommutative coefficient ring.

## 5. Verification status

These are source-level Lean proof scripts, NOT a kernel-certification claim. The actual local targeted build attempt exited 127 because `lake` is not installed or on PATH. The transitive axiom audit therefore has not executed. Inherited imported modules also require kernel verification; new-source scans cannot certify their dependencies.

A comment-aware scan of the eight new Lean modules found no proof placeholders, new axioms, `unsafe`, `implemented_by`, or `native_decide`. An independent exact integer/SymPy check passed both 64-entry native product tables, 512 source-associativity cases, 512 target-associator cases, 512 relative-coboundary cases, all 4096 pentagon cases, both full symbolic doubling laws, both quadratic inverse laws, the diagonal Zorn Cayley identity, and the scalar rational identities. This independent check is NOT Lean elaboration.

Run from the repository root:

```sh
bash scripts/check_cayley_klein.sh
python scripts/audit_cayley_klein_exact.py
```

The Python companion requires SymPy. A valid Lean audit must contain only standard logical axioms such as `propext`, `Classical.choice`, and `Quot.sound`, or none. Any `sorryAx` or project-specific mathematical axiom is a failure. Keep this PR draft until the build and audit have actually passed.

## Primary mathematical background

- H. Albuquerque and S. Majid, *Quasialgebra structure of the octonions*, https://arxiv.org/abs/math/9802116.
- H. Albuquerque and S. Majid, *Clifford algebras obtained by twisting of group algebras*, https://arxiv.org/abs/math/0011040.
- J. C. Baez, *The Octonions*, Bulletin of the AMS 39 (2002), 145–205; https://math.ucr.edu/home/baez/octonions/octonions.html.

The particular sign table here is derived from this repository's native multiplication convention; the cited papers do not substitute for that table calculation.
