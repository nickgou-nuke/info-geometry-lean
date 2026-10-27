# Peirce, BdG and centered operator geometry

## Intake and theorem contract

Source: the repository owner's request of 2026-10-27 to extract canonical
mathematics from Peirce sectors, Nambu/Majorana/BdG intersector coupling,
trembling motion, mass gap, Yang–Mills, chiral chains, Pfaffian/Berezinian,
Zorn operators, centered correlations, BKM, QGT and Onsager forms. The requested
carriers are noncommutative matrix and operator algebras, with complete native
Lean/Mathlib proofs and no scalar, diagonal or commuting replacement.

Base inspected: `b143075bbf27e75860a1011e04423a0f227b7c41`.

### Source-confirmed existing owners

* `Physics.BdGChiralBlockMatrix` defines `BdGBlock A`, `diracOperator Δ`,
  `chiralGrading`, `diracSquare`, and `connesDifferential` over a possibly
  noncommutative star ring. `diracSquare_eq_diagonal` retains the distinct
  ordered products `Δ * star Δ` and `star Δ * Δ`. Self-adjointness, chirality,
  sheet mixing and the commutator Leibniz rule are already proved.
* `Core.PeirceTangent` proves the first-order idempotent equation
  `p*x + x*p = x`, its equivalence to vanishing diagonal corners, and its
  off-diagonal reconstruction. The generic declarations are reusable
  independently of the Moore–Penrose specialization at the end of that owner.
* `Clifford.ChiralProjectorBerryCurvature.projectorCurvature p X Y` is
  `p * (X*Y - Y*X) * p`. The present work must connect this coefficient to
  a constructed projected connection, rather than infer geometry from a name.
* `Canonical.SouriauOnsagerBKMBridge` defines the genuine Kubo–Mori integral
  on the full bounded-operator algebra of a finite complex Hilbert space,
  using native continuous-functional-calculus powers of a strictly positive
  trace-one density. `BKMScalarGaugeQuotient` and
  `SouriauOnsagerBKMStrictPositivity` supply centering and strictness.
* `OperatorAlgebra.PartnerEigenspaces.nonzeroEigenspaceEquiv` pairs the
  ordinary nonzero eigenspaces of `BA` and `AB` for arbitrary composable maps.
  `Canonical.SpinorialCore.FiniteSupertrace` and
  `NCG.BlockSupermatrixGradedTrace` already own polynomial supertrace and
  graded-trace cancellation.

### New mathematical obligations

1. Preserve the commutator terms in the square of the existing massive BdG
   block. Derive the double commutator with chirality while retaining the
   operator `H²`.
2. Represent the existing block algebra faithfully on the product space by
   actual continuous linear maps. From lower bounds on both `Δ` and `Δ*`,
   prove a lower bound on its chiral action and exclusion of a disc from its
   native finite-dimensional spectrum. Nonzero pairing alone is insufficient.
3. Factor the existing projector curvature through Peirce corners; construct
   the module `pA`, its retraction, its compressed inner-derivation connection,
   and prove the curvature formula. With adjoints, identify the compressed
   two-point operator with a Gram product and prove matrix positivity.
4. Prove that existing BKM centering preserves commutators and off-diagonal
   Peirce corners. Prove that the genuine BKM commutator energy vanishes
   exactly when the two operators commute, including the centered quotient.
5. Extend the existing partner map `A` to a native linear equivalence between
   the generalized eigenspaces of `BA` and `AB`, at every depth and every
   nonzero eigenvalue. Preserve actual Jordan-chain equations.

### Hypotheses and scope

All products retain their order. The block coefficient algebra is arbitrary
and associative; it may itself be a full matrix or bounded-operator algebra.
The gap estimate explicitly requires lower bounds for both adjoint sector
maps. The spectrum theorem uses finite-dimensionality. Projected curvature is
the curvature of the explicitly constructed algebraic connection; no
manifold, integration by parts, Yang–Mills PDE or physical electron mass is
inferred. The BKM continuity hypothesis is recorded at the theorem type.

Pfaffian, supertrace, Berezinian and operator curvature have distinct carrier
requirements. This development reuses their existing owners where relevant
and does not assign an ordinary determinant to arbitrary noncommuting block
entries. Nonassociative Zorn elements and their associative endomorphisms
remain distinct carriers.

## Dependency order

The dependency order is the proof-prerequisite DAG of the named owners:

* idempotence → tangent equation → Peirce corners → compressed correlation;
* idempotence → Peirce submodule retraction → compressed connection;
* tangent/corner identities + compressed connection → projected curvature;
* adjoint → Gram factorization → matrix positivity;
* native faithful density + centering + trace obstruction → BKM detection;
* arbitrary composable maps → intertwining → generalized eigenspace pairing;
* existing BdG blocks → faithful action → sector bounds → spectral exclusion.

This is a dependency order, not a claim of physical causal dynamics.

## Canonical statements added

Write `[x,y] = xy-yx`, `q=1-p`, and `H(Δ)=[[0,Δ],[Δ*,0]]`.
The following table specifies the actual mathematical objects and conditions.
The linked Lean files contain complete proof terms elaborated from their proofs.

| Owner | Proved mathematical statement | Essential hypotheses |
|---|---|---|
| [MatrixNoncommutativity](../lean/InfoGeometry/Algebra/MatrixNoncommutativity.lean) | The shared non-diagonal swap and tilted matrices do not commute and are self-adjoint | Any nontrivial ring for the inequality; star ring for adjoints |
| [BdGOperatorCalculus](../lean/InfoGeometry/Physics/BdGOperatorCalculus.lean) | `[[D,M],[M,-D]]² = [[D²+M²,[D,M]],[-[D,M],D²+M²]]`; the off-diagonal square vanishes iff `DM=MD`; `[H,[H,Γ]]=4 H²Γ` | Arbitrary associative ring; star ring for `H` |
| [ChiralBlockSpectralGap](../lean/InfoGeometry/OperatorAlgebra/ChiralBlockSpectralGap.lean) | Faithful full block action; a common lower bound for `Δ` and `Δ*` bounds every eigenvalue in norm; invertible `Δ` gives a positive spectral gap | Complex Hilbert space; completeness for adjoints; finite dimension for the conclusion about the whole spectrum |
| [PartnerGeneralizedEigenspaces](../lean/InfoGeometry/OperatorAlgebra/PartnerGeneralizedEigenspaces.lean) | `A` induces `(BA).genEigenspace μ k ≃ₗ[K] (AB).genEigenspace μ k`, and intertwines all shifted powers | Arbitrary composable linear maps between two vector spaces, `μ≠0`, `k:ℕ∞`; no finite-dimensionality or diagonalizability hypothesis |
| [PeirceCompressionCurvature](../lean/InfoGeometry/OperatorAlgebra/PeirceCompressionCurvature.lean) | `Qp(x,y)=pxqyp`; `Qp(x,y)-Qp(y,x)=p[x,y]p`; adjoint exchange and Gram factorization | `p²=p`; tangent equations for the alternating-curvature identity; self-adjointness for the Gram interpretation |
| [PeirceProjectedConnection](../lean/InfoGeometry/OperatorAlgebra/PeirceProjectedConnection.lean) | The native submodule `{s:ps=s}`, its retraction, and `∇a(s)=p[a,s]`; `[∇a,∇b]-∇[a,b]=L(p[[a,p],[b,p]]p)` | An algebra over a commutative scalar ring; `p²=p` |
| [PeirceCompressedGramPositivity](../lean/InfoGeometry/OperatorAlgebra/PeirceCompressedGramPositivity.lean) | `Qp(x,x)` is positive semidefinite; its trace vanishes exactly when `qxp=0`, and exactly when `x=0` for self-adjoint tangent `x` | Full finite complex matrices; self-adjoint projection and direction |
| [BdGPeirceCurvature](../lean/InfoGeometry/OperatorAlgebra/BdGPeirceCurvature.lean) | `H(a)` is tangent at the first-sheet projection; `Qp(H(a),H(b))=diag(ab*,0)` and `Fp(H(a),H(b))=diag(ab*−ba*,0)` | Arbitrary associative star-ring coefficients, including full matrix/operator algebras |
| [CenteredBKMCommutatorGeometry](../lean/InfoGeometry/Canonical/CenteredBKMCommutatorGeometry.lean) | Real centering preserves commutators, off-diagonal corners, and self-wedges; centered BKM commutator energy vanishes iff the operators commute | Full bounded-operator algebra of a finite complex Hilbert space; faithful trace-one density; explicit continuity of its real-power path |

The block diagonal expressions in the table are **derived squares or corner
compressions of arbitrary operator blocks**. They do not restrict the original
coupling to a diagonal, scalar, normal, or commuting family. In particular,
`ΔΔ*` and `Δ*Δ` remain distinct.

### Curvature and second-order correlations

The ordered compressed correlation is operator-valued:

\[
Q_p(X,Y)=pX(1-p)Yp.
\]

For self-adjoint `p`, `X`, `Y`, it satisfies `Qp(X,Y)*=Qp(Y,X)`.
For `p²=p` its diagonal is the actual Gram operator

\[
Q_p(X,X)=((1-p)Xp)^*((1-p)Xp).
\]

For tangent directions `pX+Xp=X`, `pY+Yp=Y`, its alternating part is

\[
Q_p(X,Y)-Q_p(Y,X)=p[X,Y]p.
\]

The connection theorem supplies the geometric meaning of this coefficient:
its action is the curvature of the explicitly constructed projected
inner-derivation connection on the Peirce submodule. The positive diagonal
readout and the alternating operator coefficient thus come from the same
ordered compression. A smooth manifold, bundle, or exterior derivative is
not inserted by terminology.

The BKM branch uses the existing genuine integral

\[
\langle X,Y\rangle_\rho
=\int_0^1\operatorname{Tr}(\rho^sX^*\rho^{1-s}Y)\,ds,
\qquad
C_\rho X=X-\operatorname{Re}\operatorname{Tr}(\rho X)I.
\]

The new equalities are `[CρX,CρY]=[X,Y]` and
`p(CρX)(1-p)=pX(1-p)`. Strict BKM positivity and the finite trace obstruction
then prove

\[
g_\rho^{\mathrm{centered}}([X,Y],[X,Y])=0
\quad\Longleftrightarrow\quad XY=YX.
\]

For self-adjoint `X,Y`, their commutator is skew-adjoint and has zero real
expectation; consequently the centered and uncentered BKM commutator
energies are equal. These are proved relations between the two constructions;
no equality between the BKM metric and the compressed Gram tensor is assumed.

### Existing neighboring structures

These source-confirmed owners classify the remaining intake terms. They are
navigation and scope references, not new results or targets of this change's
fresh kernel run.

| Intake structure | Existing exact mathematical owner | Boundary of the claim |
|---|---|---|
| Majorana / Clifford coefficients | `Canonical.MajoranaCoefficientAction.quadraticElement_commutator_linearCombination` | A quadratic Clifford element acts on its Majorana span through its skew coefficient matrix, under the explicit CAR relations |
| Pfaffian and conserved Majorana combinations | `Canonical.MajoranaPfaffianKernelCriterion.pfaffian_zero_iff_conserved_majorana`; `Canonical.CARMajoranaFiniteBridge.fourMode_pfaffian_iff_conserved_field` | The general criterion uses a supplied Pfaffian square law for the same matrix; the four-mode model supplies it with all six coefficients. A conserved linear operator is a kernel vector of the commutator action, not necessarily a state-space zero mode |
| Supertrace and partner operators | `NCG.BlockSupermatrixGradedTrace.supertrace_superbracket_eq_zero`; `Canonical.SpinorialCore.polynomial_supertrace` | Full block matrices and parity-sensitive brackets; polynomial supertrace cancellation is finite and does not assert a heat-kernel index theorem |
| Schur/Berezinian expression | `NCG.berezinian_block_gaussian_factorization` in `BerezinianGaussianFactorization` | Ordered products of arbitrary matrix blocks over a commutative coefficient ring, with a two-sided inverse of the lower block. Supercommutative odd-entry Berezinian theory requires separate data |
| Split-quaternion and circular polarization | `Clifford.Cl11` in `Cl11SplitQuaternions`; `Clifford.c_plus_sq`, `c_minus_sq`, `c_plus_mul_c_minus`, `c_plus_add_c_minus` in `Cl11CircularBasis` | Concrete real Clifford matrix relations; circular complementary projectors over an arbitrary complex algebra. Circular/Witt bases do not impose commutation on subsequent operator insertions |
| Zorn multiplication and operator algebra | `Algebra.Zorn.FirstQuantizedLeftRegular.leftMul_comp_defect_eq_associator`; `Lie.SplitOctonionChiralOperatorSupergrading.leftRegular` | The Zorn carrier is nonassociative. Its native linear endomorphisms form an associative algebra, but left multiplication need not preserve the Zorn product; its defect is an associator |

## Concrete regressions

The generic shared matrix pair is reused by the actual finite BKM operator
witness and the nested BdG curvature witness. Noncommutativity is exported
as a proved carrier-level fact as well as exhibited inside those constructions.

* `BdGPeirceCurvature.exists_noncommuting_coefficients_with_nonzero_curvature`
  uses two non-diagonal Hermitian coefficient matrices in `M₂(ℂ)` and produces
  nonzero curvature in `M₂(M₂(ℂ))`.
* [PartnerGeneralizedEigenspacesTests](../lean/InfoGeometry/OperatorAlgebra/PartnerGeneralizedEigenspacesTests.lean)
  uses noncommuting full `3×3` matrices. A nonzero vector has exact Jordan
  depth three at eigenvalue one in each partner, and the equivalence maps
  the displayed source vector to the displayed target vector.
* [BdGOperatorGeometryTests](../lean/InfoGeometry/OperatorAlgebra/BdGOperatorGeometryTests.lean)
  supplies a nonnormal invertible `2×2` coefficient operator, its actual
  inverse, unequal adjoint Gram operators, and a nonempty spectrum with a
  positive gap. A nonzero nilpotent coefficient operator supplies an actual
  nonzero zero mode, proving that nonzero coupling alone does not imply a gap.

## Verification record

Independent verification on 2026-10-27 passed against Lean **4.34.1**
(commit `5045d0056413266e57c625dcd7c365b10e377c52`) and the repository-pinned
Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`.

* **27 repository source modules** rebuilt from a fresh copied source closure.
* **13 selected owners; 247 total owned declarations** audited natively,
  including generated and private declarations. This is not a count of
  247 named mathematical theorems.
* Collected axioms: exactly `[propext, Classical.choice, Quot.sound]`. No
  disallowed axiom, unsafe declaration, or partial declaration passed the audit.
* All selected owners compiled successfully. There was **1 style warning** in
  `MatrixNoncommutativity` (Lean suggests `simp at hentry` instead of
  `simpa using hentry`); the other selected owners had none. The existing
  dependency owners produced **28 linter warnings**: 15 in
  `BdGChiralBlockMatrix`, 10 in `FiniteMatrix`, and 3 in `OperatorExteriorAlgebra`.
* The staged proof-integrity gate and whitespace check passed. The semantic
  vacuity source scan read all 27 changed Lean files, reported zero errors and
  45 advisory warnings about structure fields/definitional interfaces. Its
  heuristic output was reviewed separately from native proof acceptance.
* Source SHA-256 hashes matched after verification. The two legacy extraction
  wrappers, `Core.PeirceTangent` and `Thermo.SusceptibilityOnsagerStress`, are
  outside this fresh kernel closure; their unchanged qualified theorem types
  and proof bodies received independent preservation review.

The [verification manifest](verification/peirce_bdg_geometry_20261027.json)
records source hashes, the actual acyclic repository import graph, per-module
results, and declaration counts. The [native audit output](verification/peirce_bdg_geometry_axioms_20261027.txt)
records every audited declaration and the final axiom set. The manifest's
base revision identifies the working-tree ancestor; its source hashes bind
the actual additions and edits verified in this change.

### Reproduce

With the pinned Lean toolchain installed and a Mathlib checkout at the
repository manifest's exact revision:

```bash
python tools/quality/check_peirce_bdg_geometry.py \
  --mathlib-root /absolute/path/to/pinned-mathlib \
  --output /absolute/path/to/new-verification-directory \
  --fetch-cache
```

The output directory must be new. The checker retrieves the required pinned
Mathlib cache when requested, uses the shared build lock, compiles every
repository import from copied source, excludes old project oleans, and runs
the native complete-owner axiom audit. It does not run the root Lake package
or claim full-repository downstream compatibility. The scoped GitHub workflow
runs this same command and uploads its logs, source snapshot, and report.
