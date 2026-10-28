# Real Peirce coupling: kernels, positivity, and Krein adjoints

## Source and parent

Source: `Pasted text(20261028-104033).txt`, SHA-256
`fc76f3c1295af250a9aac658b305d0860fc9726fa581ccdd30c735e808bea659`.
The same bytes were already handled by PR #255 under another attachment name.
This continuation is stacked on its verified head
`c192b99fdee5783915c247b35f64e8c32ab117a0`; the parent branch and its
verification record remain unchanged. It does not duplicate the core coupling
identities or modify the twistor/glide and DMP branches.

The source names the corners photons and their sum an electron, but its Lean
conclusions are algebraic identities. Neither automatic nonzero square nor
strict positivity is among those conclusions. This continuation formalizes
the exact additional metric conditions, not the physical interpretation.

## Native owners and carrier

Use the full `Matrix n n R`, existing `Core.PeirceDecomposition.component10`
and `component01`, existing `Core.PeirceGrading.reflection` and actual
even/odd ranges, and existing `NonCommutativeFredholmIndex` brackets.
Mathlib supplies PosSemidef, PosDef, Gram trace faithfulness, Matrix.toLin'
and LinearMap.ker. No parallel bracket, grading, or generalized inverse is
introduced. No diagonalization or pairwise commutativity is assumed.

Source search read these owners and Algebra.IdempotentProjector,
Algebra.PeirceDeWittChiralSplit, Algebra.PeirceParityClosure, and
Core.IdempotentCartan. Searching open PRs located the exact-source parent.
No inaccessible graph index is asserted to have been generated or queried.

All new concrete operator carriers and examples are over ℝ. The parent's six
complex-only positivity theorems are generalized in place to ordered star-ring
coefficients with explicit hypotheses. Their names and algebraic conclusions
are retained, allowing direct real specialization without complexification.
The old RCLike import is retained for caller compatibility; it is not a scalar
extension or a construction of a complex carrier in this continuation.

## Ground-truth contract

Write X=P*A*(1-P), Y=(1-P)*B*P, H=X+Y and S=2P-1.
The parent proves X²=Y²=0, H²=XY+YX, [X,Y]=S*(XY+YX), parity, corner
readouts, and trace formulas. These facts do not impose X!=0 or nonzero H².

The new metric module proves:
1. Multiplication by P and 1-P extracts the two output arrows. Hence
   H*x=0 iff X*x=0 and Y*x=0.
2. For real P=Pᴴ and B=Aᴴ, Y=Xᴴ and H² is a positive Gram sum.
   Its trace is zero iff X=0 and strictly positive iff X!=0.
3. H²*x=0 iff X*x=0 and Xᴴ*x=0, and the corresponding actual kernel
   submodules satisfy ker(H²)=ker(X) inf ker(Xᴴ).
4. H² is positive definite iff that common kernel is trivial. Nonzero
   coupling and positive trace alone do not suffice.
5. K=S*H has K²=-H² and S*Kᴴ*S=K. If X!=0, K² is not positive
   semidefinite for the positive real metric.

The last point distinguishes the explicitly displayed Krein adjoint from the
positive-metric adjoint. It is a finite operator statement, not a claimed
Hilbert/Krein completion or a physical Hamiltonian construction.

## Nondiagonal matrix regressions

A full real 4x4 example uses a nondiagonal orthogonal projector and a
nonsymmetric square-zero arrow U with UUᴴ != UᴴU. The self-adjoint coupling
has square trace 100 and a nonzero zero-mode vector (5,12,1,0), proving it is
not positive definite. Another full nondiagonal coupling has an explicit
left inverse and positive-definite square. No spectral-basis substitution
occurs in the proofs.

## Dependency order

The finite native PartialOrder is defined by inclusion of explicit stage
prerequisite sets. Trace and adjoint inputs are incomparable. The Gram stage
contains faithful trace and kernel results as well as positivity, followed
by the separate Krein square and concrete witnesses. This is a mathematical
stage specification, not the full extracted declaration graph or physical
causality. Cyclic trace alone is not a positivity theorem.

## Scope boundaries

Square-zero does not establish a mass-shell condition. H*H²=H²*H is
associativity, not a new Dirac/Drazin equation. The even subalgebra is generally
noncommutative and not automatically a Cartan subalgebra. The weighted trace
tr(S*[X,Y]) equals tr(H²)=2*tr(XY), not twice tr(H²).

No theorem here identifies photons, electrons, spin, electric charge, nuclear
sectors, or a uniform spectral gap. No claim is made that arbitrary StarRing
coefficients carry a positive order. The parent source contract is preserved
as a record of the earlier, narrower complex specialization.

## Verification

Pending the actual scoped workflow for these additions. The authoring
container has no local Lean executable. The extended checker reuses the
repository's exact-pin source-closure compiler and public Lean.collectAxioms
audit. It compiles the complete selected closure sequentially under the shared
build lock and enumerates all declarations in the parent and new owners,
including generated/private declarations. It rejects unsafe/partial definitions
and axioms beyond propext, Classical.choice and Quot.sound. The original
convenience audit and semantic-vacuity error gate are also rerun.

The toolchain, Lake manifest, dependency sources, and main are unchanged.
Only this dependent branch generalizes the parent's positivity API and extends
its scoped verifier; it does not rewrite the parent branch. A passing scoped
run is not a full root Lake or all-green-CI assertion.
