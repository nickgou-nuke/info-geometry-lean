# Quadratic Hamiltonian bridge: source and theorem contract

Source: F. Bagarello, E. Balistreri, S. Kuzhel, *An unified approach for the
(inverted) quantum harmonic oscillator and the Berry-Keating hamiltonian*,
arXiv:2610.08437v1, 6 October 2026. User-supplied 22-page PDF.
Reference: https://arxiv.org/abs/2610.08437v1
Base: 2d3a6ed286fde7098d152b83c9c75580b98865d0.

## Source-derived scope

- Equations (2.1)--(2.3): H0=p*p+q*q, H1=p*q+q*p, H2=p*p-q*q,
  their real linear combination, and canonical rotation Q=c*q+s*p,
  P=-s*q+c*p. The paper omits the usual overall factor 1/2; so do these definitions.
- Equations (2.6)--(2.7): exact conditional diagonal reconstruction and
  xi=beta0*beta1. We use the inverse coefficient formulas, not division by cos(2 theta).
- Section II.1: the exceptional angle pi/4, including its precise signs:
  H1(Q,P)=H2(q,p), H2(Q,P)=-H1(q,p). Equivalently H1(q,p)=Q*Q-P*P.
- Equations (5.1)--(5.3): quadratic CCR closure and the scaled K1,K2,K3
  Lie relations. No star relations are asserted merely from these brackets.

## Repository reuse

`SplitClifford.CCRPair` and its commutator field are imported from the existing
Physics.SplitCliffordAlgebras owner. No competing CCR/CAR predicate is declared.
The native associative `Ring` bracket is used. The existing
Canonical.BerryKeatingOperatorBridge supplies the real differential identity;
the new normalization adapter retains its real carrier and accounts for the
factor two. The separate polynomial realization supplies physical momentum -iD.
`FiniteSpinAlgebra` is the existing finite matrix import owner; its matrices are
not represented as exact finite-dimensional CCR position and momentum.

The source inspection covered the BerryKeatingOperatorBridge,
QuantumGeometry/BerryKeatingDilationBridge search surface, SplitCliffordAlgebras,
RealDoubledWaveplate context and oscillator/SU11 search results. This is not a
repo-wide claim that no related result exists under any other name.

## Additional derivations, not quoted paper theorems

- Native finite symmetric coefficient matrix S_alpha has determinant xi.
- The classical Hamilton vector-field matrix is
    M_alpha = [[2a1, 2(a0+a2)], [-2(a0-a2), -2a1]].
  It has trace zero and M_alpha^2=-4xi I. A nonzero null example has square zero.
  This 2x2 coefficient action is not the quantum Hamiltonian on a Hilbert space.
- The derivative/X pair on native complex polynomials is an explicit exact CCR
  representation. The algebra is infinite dimensional and no inner product is
  imposed. This prevents the conditional CCR algebra from being the only example.
- The unhalved dilation acts on a polynomial f as -i(2 X f' + f).

## Deliberately outside this PR

The paper's Section III uses tempered distributions for the inverted ladder,
Section IV changes the inner product/completes a different carrier, and the
Section V similarity exponentials are explicitly discussed formally. This PR
neither replaces those constructions by ordinary L2 eigenvectors nor certifies
their analytic claims. There is no theorem here about a discrete L2 IHO/BK
spectrum, resonance completeness, self-adjoint extensions, unitary implementation
of the canonical rotation, exponentiation of unbounded operators, or zeta zeros.
The Casimir and ladder formulas beyond (5.3) are not included in this scope.
No identification with a finite CAR mode, Zorn product, modular state, detector,
or the previous Zorn shift/tilt candidates is asserted.

The determinant identity is the algebraic part of the paper's regime
classification, not a complete analytic classification theorem or construction
of a diagonalizing angle for every coefficient triple. The zero Hamiltonian is
not silently treated as a nonzero free-particle generator.

## Verification contract

Status: candidates until actual scoped compilation and public collectAxioms pass.
The added wrapper reuses the unchanged strict source-closure checker, the exact
repository Lean/Mathlib pins, all imported owner files, and the shared sequential
build lock. It audits all owned declarations, including generated ones, rejecting
unsafe/partial definitions and all axioms outside propext, Classical.choice,
and Quot.sound. No imports are stripped and no dependency pins are changed.
This is not a root Lake or All.lean build.

Acceptance target:

    python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
      InfoGeometry.Canonical.QuadraticHamiltonianPolynomial
