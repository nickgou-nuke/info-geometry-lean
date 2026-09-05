# Penrose CCR: source reconstruction, obstruction, and explicit composition completion

## Source and conventions

The supplied source is Roger Penrose, “Quantized Twistors, G2*, and the Split Octonions”, Chapter 7 of *Dialogues Between Physics and Mathematics* (2022), printed pp. 165–189. The attachment is named `193-217.pdf`; those filename numbers are not its printed page numbers. Its DOI is `10.1007/978-3-031-17523-7_7`.

This extension addresses the algebraic steps of Section 7.6 and their concrete polynomial CCR realization from Section 7.5. It does not purport to formalize the whole chapter, the Penrose transform, sheaf cohomology, positive-frequency Hilbert spaces, or a classification of exceptional groups.

There are three logically separate results:

1. The literal six-term alternating operator triple really closes on linear bi-twistors in the concrete CCR representation.
2. Combining that triple with the displayed cross-product prescription (7.105) does not give an alternative composition product. An explicit counterexample is supplied, including for the historical codebase product.
3. The same real quadratic twistor carrier does admit a chosen genuine split composition product through the repository's existing Witt-to-Zorn map. This product is proved different from the literal candidate.

The third statement is a mathematical completion with explicitly chosen additional multiplication data, not a silent correction of the source formula.

## 1. Concrete CCR, not an assumed operator interface

`PenrosePolynomialCCR.lean` uses the existing `TwistorCarrier = Fin 4 -> Complex` for coefficients and the native algebra

```
WavePolynomial = MvPolynomial (Fin 4) Complex
Operator = Module.End Complex WavePolynomial.
```

For `A=(a,b)` and a scalar parameter `h`, define

```
Q_h(A) p = (sum_i a_i X_i) p - h (sum_i b_i partial_i) p.
```

The directional derivative is Mathlib's `mkDerivation`, with its equality to the sum of the native `pderiv` operators proved on polynomial generators. Commutation of constant partials is proved by showing their commutator derivation vanishes on every generator.

The resulting actual operators satisfy

```
Z_i W_j - W_j Z_i = h delta_ij id,
Z_i Z_j = Z_j Z_i,
W_i W_j = W_j W_i,
[Q_h(A), Q_h(B)] = h Omega(A,B) id,
Omega(A,B) = sum_i (a_i d_i - b_i c_i).
```

These are not finite-dimensional matrix CCR. The space of polynomials is not truncated.

Associativity of operator composition gives

```
Alt_3(A,B,C) = A[B,C] + B[C,A] + C[A,B].
```

Thus the chapter's `i Alt_3` equals `Q_h` applied to

```
i h (Omega(B,C) A + Omega(C,A) B + Omega(A,B) C).
```

This recovers the linear closure described around (7.89)–(7.90), without inserting the commutator or triple-closure result as a structure field.

## 2. Correct signed real form

`PenroseSignedCCRGeometry.lean` reuses `InfoGeometry.Twistor.PenroseTwistor.twistorHermitian`, whose diagonal frame has complex signature `(2,2)`. Its realification has signature `(4,4)`:

```
H(z,w) = conjugate(z0) w0 + conjugate(z1) w1
         - conjugate(z2) w2 - conjugate(z3) w3,
g = 2 Re H,  sigma = 2 Im H,  Jz = i z.
```

The signed reality embedding into the coefficient pair is

```
R(z) = (z, diag(1,1,-1,-1) conjugate(z)).
```

The dual sign matrix is essential in this frame. The proofs establish

```
i Omega(Rx,Ry) = sigma(x,y),
i Omega(Rx,R(Jy)) = g(x,y),
J^2 = -id,   g(Jx,Jy)=g(x,y).
```

After the source's choice `h=1`, the real triple is therefore

```
T(x,y,z) = sigma(y,z) x + sigma(z,x) y + sigma(x,y) z.
```

Its signed embedding is proved equal to the coefficient triple, and its polynomial-operator realization is the original alternating operator expression.

We use the explicitly intended pairing (7.97) and the normalization (7.100). The page image of (7.96) contains an additional `i` inside the parenthesis; that printed formula is not silently substituted for an ordinary commutator. The calculations above make the commutator convention explicit.

## 3. Exact obstruction at the proposed binary product

Set `E=e0`, `X=e1`, `Y=e2` in the existing complex four-coordinate carrier, considered over the reals. Then

```
g(E,E)=2,  g(X,X)=2,  g(Y,Y)=-2,
g(X,Y)=g(X,E)=g(Y,E)=0.
```

Under the literal prescription `cross(x,y)=T(Jx,Jy,JE)`, all pairwise symplectic contractions of these real coordinate directions vanish, so `cross(X,Y)=0`.

More generally, on the symplectic-orthogonal hyperplane to E,

```
cross(x,y) = sigma(x,y) JE.
```

That line-image property is incompatible with the nondegenerate 7-dimensional octonionic cross product. The formal obstruction does not depend on a dimensional analogy: it is an explicit failure of an algebra identity.

Expose the scalar metric normalization as `k` in the scalar/vector assembly of (7.107). The new `candidateProduct` satisfies

```
X *k Y = 0,
X *k X = -2k E,
X *k (X *k Y) = 0,
(X *k X) *k Y = -2k Y.
```

For every `k != 0`, left alternativity fails. This covers both the printed coefficient `k=1` and the norm-normalized coefficient `k=1/2`. Composition fails for every k: `q(X *k Y)=0`, whereas `q(X)q(Y)=-1`, for the existing `twistorRealQuadraticForm q`.

This is a statement about the displayed CCR/triple/cross construction with these explicit conventions. It does not claim that quantized twistor theory cannot have other octonionic structures or that a corrected construction with additional data is impossible.

## 4. Direct audit of the historical codebase owner

The historical namespace `InfoGeometry.Physics.PenroseTwistor` contains a different `BiTwistor`, a positive-definite `twistorDot` readout, and a function named `splitOctonionicMul`. Its previously proved self-unit and repeated-triple facts do not establish alternativity or split signature.

`PenroseLegacyProductAudit.lean` evaluates that exact existing product, without redefining it, on two bi-twistors satisfying its own reality predicate. It supplies the same explicit left-alternativity counterexample. It also proves that its dot value on the test Y is +2, whereas the signed Hermitian metric used in the new reconstruction gives -2. No existing operation is overwritten or treated as equivalent without a proof.

## 5. Positive completion using the actual native Zorn product

The repository already provides

- the real/complex twistor carrier and Hermitian form;
- `penroseWittCoordinates`;
- `real8CircularPeirceEquiv` and `penroseWittZornMap`;
- a theorem that the native Zorn norm of that map equals the twistor quadratic form;
- native composition, alternativity, and a genuine real-linear multiplication-stabilizer group.

`PenroseWittCompositionCompletion.lean` proves the inverse of the existing Witt coordinates and upgrades the map to

```
wittZornEquiv : TwistorCarrier equiv_linear[Real] CanonicalZorn.
```

It preserves the existing quadratic form and sends the SAME chosen E to the actual Zorn identity. The selected operation is

```
selectedMul x y = F.symm (F x * F y),  F = wittZornEquiv.
```

Its bilinearity, both unit laws, both alternative laws, and composition identity are proved using the existing native owners. This does not replace the already available pointwise `Mul` instance of `Fin 4 -> Complex`; `selectedMul` is an explicitly distinct operation.

The new theorem `selectedMul_ne_literal_candidate` proves that the selected product differs from every scalar normalization of the literal candidate, already on `(X,Y)`. The previously constructed native multiplication-stabilizer acts on this completed product by conjugation through F; no nominal dimension-14 constant is substituted for a group or Lie-algebra classification.

## 6. Verification boundary and execution

All public theorem declarations have proof scripts. `PenroseCCRAudit.lean` requests transitive axiom reports for all public definitions, abbreviations, and theorems in this extension. It does not certify them before Lean executes.

The inherited toolchain is Lean `v4.28.1`, with Mathlib revision `8f9d9cff6bd728b17a24e163c9402775d9e6a365`. The local check launch stopped with exit 127 because `lake` is not installed or on PATH. Consequently neither elaboration nor the transitive audit has run locally. No kernel-certification claim is made.

From a full repository checkout with the pinned dependencies:

```sh
bash scripts/check_penrose_ccr.sh
python3 scripts/audit_penrose_ccr_exact.py
```

The second command requires SymPy and checks exact symbolic identities independently. It has been run successfully for the general differential-operator commutator and six-term triple, signed-pairing and triple closure, counterexamples, native Zorn composition and alternativity, and the Witt coordinate inverse. These tests are not substitutes for Lean elaboration. The source scan is comment-aware but does not inspect imported transitive axioms.

The next development boundary is kernel execution of this dependency closure, followed by an explicitly specified corrected cross product or categorical structure if the source's intended extra data can be identified. The literal failed candidate is not treated as a missing lemma to be assumed.
