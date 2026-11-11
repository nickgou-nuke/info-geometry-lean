# Two-qubit Weyl phase conventions

This development extends the actual Sylvester/Kronecker matrices from
`BinaryWeyl` and `TwoQubitPauliGeometry`. It makes changes of real sign convention
explicit and separates the product multiplier from the commutation sign.

## Conventions and the correction

Write a label as `v = ((x₁,z₁),(x₂,z₂))`, with coordinates in `ZMod 2`. This is
the interleaved version of the grouped coordinates `(x₁,x₂,z₁,z₂)` often used
with the block symplectic matrix. The coefficient ring `R` is a commutative
ring; it is not assumed to have characteristic two.

The ordered words are

\[
D(v)=(X^{x_1}Z^{z_1})\otimes(X^{x_2}Z^{z_2}),\qquad
X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
\]

For `w = ((x₁′,z₁′),(x₂′,z₂′))`, define

\[
c(v,w)=z_1x'_1+z_2x'_2,\qquad
\omega(v,w)=c(v,w)+c(w,v),\qquad q(v)=c(v,v).
\]

These two equations have different right-hand sides:

\[
D(v)D(w)=(-1)^{c(v,w)}D(v+w),
\qquad
D(v)D(w)=(-1)^{\omega(v,w)}D(w)D(v).
\]

The input proposed using `ω(v,w)` as the product multiplier in the first
equation. That is false for these matrices. In characteristic two the
alternating form is symmetric, so such a product formula would force all
representatives to commute. The new theorem
`not_rephasedPauli_symplectic_product` rules it out for **every** choice of real
signs in characteristic zero.

## Arbitrary real signs

For any function `f : Label → ZMod 2`, the new matrix definition is

\[
P_f(v)=(-1)^{f(v)}D(v).
\]

Its ordered product law is

\[
P_f(v)P_f(w)=(-1)^{c_f(v,w)}P_f(v+w),\qquad
c_f(v,w)=c(v,w)+f(v)+f(w)+f(v+w).
\]

The added term is the binary coboundary of `f`. The formalization proves the
associative cocycle identity directly and proves
`c_f(v,w) + c_f(w,v) = ω(v,w)`. Consequently all real-sign choices preserve the
commutation test. An arbitrary `f` need not produce a bilinear cocycle.

Normalization is explicit: `P_f(0) = (-1)^(f(0)) I`, so `f(0)=0` gives the
identity representative. The square law does not require normalization:

\[
P_f(v)^2=(-1)^{q(v)}I.
\]

## The quadratic sign convention from the input

The parity `q(v)=x₁z₁+x₂z₂` obeys

\[
q(v+w)=q(v)+q(w)+\omega(v,w).
\]

Taking `f=q` therefore gives the **opposite ordered cocycle**:

\[
c_q(v,w)=c(w,v)=x_1z'_1+x_2z'_2,
\qquad
P_q(v)P_q(w)=(-1)^{x\cdot z'}P_q(v+w).
\]

This is the corrected composition law for the real phase in the input. The
same representative is the transpose and two-sided inverse of the ordered
word:

\[
P_q(v)=D(v)^{\mathsf T}=D(v)^{-1}
       =(Z^{z_1}X^{x_1})\otimes(Z^{z_2}X^{x_2}).
\]

The inverse notation here summarizes the two proved equations
`D(v) * P_q(v) = I` and `P_q(v) * D(v) = I`; the implementation does not rely on
a totalized matrix inverse or a hidden invertibility assumption.

## Symmetry and Hermiticity

The transpose law holds for every sign function:

\[
P_f(v)^{\mathsf T}=(-1)^{q(v)}P_f(v).
\]

In characteristic zero, `P_f(v)` is symmetric exactly when `q(v)=0`. For a
coefficient ring with trivial star, this is also the exact criterion for
Mathlib's native `Matrix.IsHermitian`; in particular it applies over the reals.
Thus multiplying `XZ` by a real sign cannot make it Hermitian.

For the concrete label `v=((1,1),(0,0))`, the quadratic convention gives
`P_q(v)=ZX⊗I`. In the basis `(0,0),(0,1),(1,0),(1,1)` this is

\[
\begin{pmatrix}
0&0&1&0\\
0&0&0&1\\
-1&0&0&0\\
0&-1&0&0
\end{pmatrix}.
\]

The matrix is skew-symmetric and its square is `-I`. Meanwhile
`ω(v,v)=0` and `P_q(v+v)=I`. The theorem
`quadraticPauli_xz_product_ne_symplectic` proves that the proposed product
formula fails at this label on the actual four-by-four carrier.

Over the complex numbers, the tensor-Pauli Hermitian convention instead uses
`i` for each `XZ` factor: `i^(x₁.val*z₁.val + x₂.val*z₂.val) D(v)`. Using
`i^(q(v).val) D(v)` also gives Hermitian representatives, but differs by a sign
when both factors are `XZ`. Neither formula is the real-sign convention
formalized here; no complex Hermitian lift or Clifford action is added.

## Native Lean surface

All names below live under `InfoGeometry`; prefixes are shortened in the table.

| Owner | Principal additions |
|---|---|
| `Projective.BinarySymplecticGeometry` | `quadraticPhase`, its polarization, `rephasedCocycle`, associativity, unchanged symplectic pairing, and the opposite-cocycle specialization |
| `Quantum.BinaryWeyl` | `word_transpose_eq_reverse`, `word_transpose` |
| `Quantum.TwoQubitPauliPhase` | `rephasedPauli_mul`, `rephasedPauli_mul_self`, `rephasedPauli_phase_commutation`, `rephasedPauli_commute_iff` |
| `Quantum.TwoQubitPauliPhase` | Native transpose, symmetry/Hermiticity criteria, inverse laws, preserved noncommutativity, and counterexamples |
| `Quantum.TwoQubitPauliAudit` | Public declaration axiom audit covering the five owners, including the existing basis development |

The generic identities use `[CommRing R]`. Converse tests and obstructions use
`[CharZero R]`, which suffices to distinguish `1` from `-1`. The implementation
keeps the native matrix product and Kronecker product throughout. It introduces
no group/cohomology quotient, structure with the conclusion as a field, or
replacement scalar carrier.

## Verification scope

The repository pins Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The maintained focused checker
compiles the actual sources under `lean/` and uses the repository's shared
build lock:

```sh
python3 verification/language-symmetry/check.py build InfoGeometry.Quantum.TwoQubitPauliAudit
python3 verification/language-symmetry/check.py env lean /absolute/repository/lean/InfoGeometry/Quantum/TwoQubitPauliPhase.lean
```

These are reproducible commands, not a statement that the entire root package
passes. The PR records the observed results, independent source review, native
axiom audit, and any unrelated repository integration failures. Allowed axiom
dependencies are `propext`, `Classical.choice`, and `Quot.sound`.

## Sources and prior owners

- Pascal Baßler, *Hamiltonian Engineering and Quantum Compilation*, §2.4,
  equations (2.30)–(2.32), printed p.13: an `i` phase for Hermitian Pauli
  representatives and the symplectic sign for **reversing operator order**.
  [Dissertation](https://docserv.uni-duesseldorf.de/servlets/DerivateServlet/Derivate-77602/Ba%C3%9Fler%20Diss___Kopie__2_-1.pdf).
- Jeroen Dehaene and Bart De Moor, *The Clifford group, stabilizer states, and
  linear and quadratic operations over GF(2)*, pp.1–2, Lemma 1. Their real
  words use `Z^z X^x`; the coordinate/order translation must be retained.
  [Original paper](https://arxiv.org/pdf/quant-ph/0304125).
- Existing repository owners `Canonical.ProjectiveRepresentationCocycle` and
  `Canonical.ProjectiveMultiplierCohomologyClass` discuss general multiplicative
  lifts and rephasing relations. The former's `rephase_multiplier` expands a
  scalar homomorphism; the latter assumes normalized cocycle fields. This
  extension derives the concrete binary matrix laws from `pauli_mul` and the
  native Sylvester generators.
- `src/InfoGeometry/Canonical/SuperGrassmannianParaKahlerInfoGeometryPoset.lean`
  has a separate arbitrary-bit `Bool`-indexed Clifford basis. No unproved
  identification with that carrier is used here.
