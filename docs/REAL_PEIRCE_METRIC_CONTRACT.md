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
Mathlib.Algebra.Order.Star.Real supplies the native real star-order instance.

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

## Completed verification

**Passed scoped GitHub Actions run:**
https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40679505962

Kernel job: `122786298840`.
Checked source head: `c921aab2d539f37f54884a885afeb0534ec29ba9`.
Checked PR merge snapshot: `5eeb04abef73eb1b8cdb09a2c3c6063d8e345820`.
Their Git trees coincide at `a157607c2b734baabcbc8a494122cca24858d07d`.

The authoring container has no local Lean executable. Verification is the
completed GitHub run and its downloaded proof artifact, not a local build.

- Official Lean **4.34.1**, executable commit
  `5045d0056413266e57c625dcd7c365b10e377c52`.
- Unchanged Mathlib revision
  `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- All **10 repository modules** in the complete selected import closure
  compiled from exact source with return code zero, under the shared build lock.
- **29 new named theorems**: 11 in RealMetric, 14 in Witness, 4 in Order.
  The 29 parent named theorems are also recompiled, for **58 named theorems**
  across the five mathematical owners. Six of the retained parent theorems
  now have generalized coefficient assumptions, not duplicate names.
- Native public `Lean.collectAxioms` enumerated **144 owned declarations**,
  including generated/private declarations and definitions. Each passed the
  foundational allowlist: only `propext`, `Classical.choice`, `Quot.sound`, or
  no axioms. Unsafe/partial declarations are rejected by the checker.
  This is a count of declarations, not 144 theorems.
- The downloaded audit contains all 58 named theorem declarations.
- All ten module compiler logs contain **zero errors and zero warnings**.
- Semantic-vacuity lexical gate read all five mathematical owners and reports
  **zero findings**, no read failures, and complete requested coverage.
  This heuristic gate is not represented as a semantic proof.
- Source scan of the five checked mathematical owners found no `sorry`,
  `admit`, `native_decide`, custom axiom or unsafe/partial declaration.
- A separate exact-rational matrix calculation confirms the stated witness
  identities; it is a cross-check, not the proof authority.

### Artifact provenance

Artifact `opposite-peirce-proof-logs`, ID `12812136975`, contains exact sources,
compiler logs, native declaration audit, toolchain version, source manifest,
and semantic-vacuity report. Its downloaded ZIP SHA-256 matches GitHub's digest:

`c28da8971bc4d0f10a6d40ac2b37f5bf4eb232c04db1d829ac66eb862c6dcf40`.

All ten extracted source SHA-256 values were checked against `status.json`.
Selected owner source hashes:

| Owner | Source SHA-256 |
| --- | --- |
| OppositePeirceCoupling | e7ff68b70a87806d409d7fafb219af4af738e9f809928bc72daea8ffdac682ef |
| OppositePeirceTrace | 720b489f3a6f20e4e9101009b014f93745803b0ebf22abbf2607d8baf5b28644 |
| OppositePeirceRealMetric | b866d911ccd0ef40e892e5fb6bc09ad246b17e8a81f7510b125fed243ccaa1b8 |
| OppositePeirceWitness | c970aeb06daaba9db68c00418bdeed1fb5af524c255e94e21d3da0dd0bc36a88 |
| OppositePeirceOrder | f6e80285f563e477a59f84048591dbed3086e2e8ef0a8799605b51dbcb70d29f |
| OppositePeirceAudit | 91368a4303278c8973257040d2c279d7c467be07b40129af354da1a641eeeea6 |

The final evidence update changes only this document; the verified Lean
sources, checker, workflow and pins remain unchanged.

### Repair history and remaining gates

The first child run exposed the missing explicit real star-order import;
the second compiled the metric theorems but stopped at a finite corner
calculation. The accepted source adds the native real instance import, removes
unused generic assumptions, and expands the Peirce complement before entrywise
matrix simplification. None of the target conclusions was weakened.

The checker reuses the repository's full source-closure compiler and native
all-owned-declaration audit. The original convenience audit is also rerun.
The toolchain, Lake manifest, dependency sources, main and the parent branch
are unchanged. Only this dependent branch generalizes the parent's positivity
API and extends its scoped verifier.

This is **not** a full root Lake or all-green-CI assertion. On the checked
source commit, the unrelated Sorry Gate and thesis/blueprint/docs workflows
failed. No merge is performed. The verified package is ready for review with
that explicit scope.
