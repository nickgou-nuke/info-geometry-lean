Published **[draft PR #391 — Native real Dirac counterexamples and Casimir reduction boundaries](https://github.com/nickgou-nuke/info-geometry-lean/pull/391)**. I also updated **[PR #375 — QGT matrix positivity and real phase Fourier transport](https://github.com/nickgou-nuke/info-geometry-lean/pull/375)** with a correction identified by its first native Lean run.

**Both remain drafts. The source checks passed, but native compilation and the complete recursive axiom audits are still pending at the current heads.** The PR descriptions record that distinction.

| PR | Current head | Contents | Latest observed native status |
|---|---|---|---|
| [#391](https://github.com/nickgou-nuke/info-geometry-lean/pull/391) | `9072e4c10f742659e624f4b8e357e13786744881` | Native Clifford current counterexample, ordered Dirac phase identity, and Casimir reduction results | [Focused CI queued](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44091081724) |
| [#375](https://github.com/nickgou-nuke/info-geometry-lean/pull/375) | `555573257c882b7651cb920735c2895f2194238b` | Finite-family QGT positivity, complex congruence, and real internal-phase Fourier integrals | [Repair verification queued](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44096945179) |

The four uploaded files contain **two distinct texts**. PR #391 preserves both original byte streams, a hash and deduplication manifest, the inspected owner inventory, and a correction ledger.

## 1. The new Dirac construction uses the actual Clifford algebra

The new HestenesNativeDiracCurrent.lean[HestenesNativeDiracCurrent.lean](sandbox:/workspace/scratch/f2133092acd6/info-geometry-lean/lean/InfoGeometry/Canonical/HestenesNativeDiracCurrent.lean) works in the existing native Mathlib carrier:

\[
V=\mathbb R^4,\qquad
Q(x)=x_0^2-x_1^2-x_2^2-x_3^2,
\]

with `CliffordAlgebra Q`, its even subalgebra, and native Clifford reversion. The current is the actual algebra product

\[
J(\psi)=\psi\gamma_0\widetilde\psi,
\]

and the axial current is

\[
K(\psi)=\psi\gamma_3\widetilde\psi.
\]

The file contains full proof scripts for a concrete singular spinor:

\[
\boxed{\psi=1+\gamma_3\gamma_0.}
\]

Since \((\gamma_3\gamma_0)^2=1\), its reverse satisfies

\[
\widetilde\psi=1-\gamma_3\gamma_0,
\qquad
\psi\widetilde\psi=0.
\]

Nevertheless,

\[
\boxed{
\psi\ne0,\qquad
J(\psi)=K(\psi)=2(\gamma_0+\gamma_3)\ne0.
}
\]

The construction also identifies this Clifford element with the native image of the genuine spacetime vector

\[
v=2(e_0+e_3),
\]

and establishes the proposed conclusions

\[
v^0=2,\qquad Q(v)=0.
\]

That vector identification matters: square-zero of an arbitrary multivector would not establish that it is a null spacetime vector.

### What this corrects

The implication

\[
\psi\ne0\Longrightarrow J(\psi)\text{ is strictly timelike}
\]

fails on the full even Clifford carrier. The displayed nonzero spinor has a nonzero null current. The same example prevents a universal claim that its axial current must be strictly spacelike.

The missing distinction is between singular and nonsingular spinors. Hestenes’s polar decomposition explicitly assumes \(\psi\widetilde\psi\ne0\); extending conclusions obtained in that sector to every nonzero even spinor loses a necessary hypothesis. [davidhestenes.net](https://davidhestenes.net/geocalc/pdf/caiqm.pdf?utm_source=chatgpt.com)

This also exposes a concrete gap in the existing codebase. The inspected `HestenesSTA4DMaxwellDiracBridge` supplies an eight-real-coordinate construction and a sum-of-squares `current_j0`. The new file supplies actual Clifford sandwiches. A native coefficient map and a proof identifying those two current readouts remain a separate task. The contract.md[Dirac/metriplectic contract](sandbox:/workspace/scratch/f2133092acd6/info-geometry-lean/docs/epistemic/2026-11-17-dirac-metriplectic/contract.md) records that boundary.

### The right-phase equation preserves multiplication order

The same new owner contains the generic associative-ring statement

\[
B^2=-1
\quad\Longrightarrow\quad
\boxed{
DB-G=M
\iff
D=-(M+G)B.
}
\]

It then specializes to the real phase bivector

\[
B=\gamma_2\gamma_1.
\]

Thus, with the convention used in the intake,

\[
DB-eA\psi=m\psi\gamma_0
\]

gives

\[
\boxed{
D=-(m\psi\gamma_0+eA\psi)B.
}
\]

Both contributions acquire a minus sign. Every factor remains in its original order; the argument requires associativity, not commutativity. The choice \(B=\gamma_2\gamma_1\) agrees with Hestenes’s real form of the Dirac equation. [davidhestenes.net](https://davidhestenes.net/geocalc/pdf/caiqm.pdf?utm_source=chatgpt.com)

Here `D` is an algebra element. The theorem does not construct a spacetime derivative, a spin connection, or a PDE solution. Those analytic structures are explicit open obligations.

## 2. The primal–dual reduction now has an exact kernel theorem

The addition to BilinearMetriplecticReduction.lean[BilinearMetriplecticReduction.lean](sandbox:/workspace/scratch/f2133092acd6/info-geometry-lean/lean/InfoGeometry/Thermo/BilinearMetriplecticReduction.lean) addresses the main structural problem in the thermodynamic text.

Let \(B\) be a nondegenerate bilinear form on a finite-dimensional real space \(W\), and let

\[
A:W\longrightarrow V.
\]

The existing reduced sharp map is

\[
L_{B,A}
=
A\circ(B^\flat)^{-1}\circ A^\vee:
V^*\longrightarrow V,
\]

where \(A^\vee\alpha=\alpha\circ A\) is the **algebraic dual map**. It is not a positive Hilbert adjoint.

The new kernel statement is

\[
\boxed{
A\text{ injective}
\Longrightarrow
\bigl(L_{B,A}\alpha=0\iff A^\vee\alpha=0\bigr).
}
\]

Equivalently,

\[
\ker L_{B,A}
=
\{\alpha\in V^*:\alpha|_{\operatorname{im}A}=0\}.
\]

This requires nondegeneracy of \(B\), not positivity. It therefore applies to the skew form used by the reversible construction.

For an actual linear equivalence \(e:W\simeq V\), the code constructs the corresponding native `LinearEquiv`:

```lean
e.dualMap.trans ((B.toDual hB).symm.trans e)
```

It identifies its underlying linear map with the existing reduced sharp map and derives injectivity.

The consequence is precise: **an invertible change of state coordinates preserves invertibility of this sharp map. It cannot create a nontrivial covector kernel.**

### Why this matters for entropy Casimirs

In Morrison’s metriplectic construction, entropy is tied to Casimirs of the Poisson structure. That is stronger than requiring it to commute with one chosen Hamiltonian. [web2.ph.utexas.edu](https://web2.ph.utexas.edu/~morrison/86PHD_morrison.pdf?utm_source=chatgpt.com)

At the linear, pointwise level, the Casimir condition is

\[
L\,dS=0.
\]

If \(L\) is injective, this forces \(dS=0\). The repository’s existing `GenericMetriplecticFlow` already contains that obstruction, so the PR reuses it.

The addition to Cl55MetriplecticReduction.lean[Cl55MetriplecticReduction.lean](sandbox:/workspace/scratch/f2133092acd6/info-geometry-lean/lean/InfoGeometry/Clifford/Cl55MetriplecticReduction.lean) applies it to the existing two-mode model, whose entropy production rate is \(2\). The proposed conclusions are that:

- its reversible map is noninjective;
- that map cannot equal the full inverse of the nondegenerate `diagonalOmega`.

This distinguishes a reduction with a genuine kernel from an invertible coordinate transformation. It does not claim the existence of nonconstant global Casimir functions, a state-dependent Poisson structure, or a global thermodynamic evolution.

Across these three owners, PR #391 adds **28 theorem declarations—23 public and five private support lemmas—and six definitions**.

## 3. The Fourier, uncertainty, and phase connections now have concrete interfaces

PR #375 handles two other parts of the original request. Its 2026-11-17-phase-scale-contract.md[phase and QGT contract](sandbox:/workspace/scratch/f2133092acd6/phase-scale-check/docs/epistemic/2026-11-17-phase-scale-contract.md) records their actual assumptions and their relationship to existing owners.

### Finite families of noncommuting operators give a positive QGT matrix

For a normalized state \(\psi\), define the centered vectors

\[
v_i=P_{\psi^\perp}(X_i\psi),
\qquad
Q_{ij}=\langle v_i,v_j\rangle.
\]

The \(X_i\) are arbitrary bounded complex-linear operators. They need not commute, and the complete Hilbert space need not be finite-dimensional.

The new QGTMatrix.lean[QGTMatrix.lean](sandbox:/workspace/scratch/f2133092acd6/phase-scale-check/lean/InfoGeometry/QuantumGeometry/Projective/QGTMatrix.lean) identifies this matrix with Mathlib’s native Gram matrix. Its proof scripts cover:

\[
Q=Q^\dagger,\qquad Q\succeq0,
\]

and the full coefficient identity

\[
\boxed{
c^\dagger Qc
=
\left\|\sum_i c_i v_i\right\|^2.
}
\]

For rectangular complex coefficients, the new operators are constructed first:

\[
Y_j=\sum_i C_{ij}X_i.
\]

The corresponding transformation law is

\[
\boxed{Q(Y)=C^\dagger Q(X)C.}
\]

The real and imaginary parts retain the repository’s convention

\[
g=\operatorname{Re}Q,\qquad
\Omega=-2\operatorname{Im}Q,
\qquad
Q=g-\frac{i}{2}\Omega.
\]

Real family mixing transports both \(g\) and \(\Omega\) by ordinary congruence. The commutator readout retains its separate skew-adjoint hypothesis and the sign established by the existing projective owner.

This is a useful finite-family uncertainty interface. Four channels are an immediate specialization of the indexing. A relativistic four-parameter Cramér–Rao theorem still needs actual transformation laws for those operators and states, a statistical model, estimator hypotheses, and—where generators are unbounded—appropriate domains. Gram positivity alone also does not provide an inverse Fisher matrix: the matrix may be singular.

### Real internal phase gives an actual Bochner integral

InternalPhaseFourier.lean[InternalPhaseFourier.lean](sandbox:/workspace/scratch/f2133092acd6/phase-scale-check/lean/InfoGeometry/Analysis/InternalPhaseFourier.lean) defines

\[
\mathcal F_K f(\xi)
=
\int_{\mathbb R}
\left[
\cos(2\pi\xi x)f(x)
-
\sin(2\pi\xi x)Kf(x)
\right]\,dx.
\]

This uses real Lebesgue measure and Mathlib’s Bochner integral. It includes the integrability argument for integrable \(f\).

For bounded real-linear maps, the transport laws are:

\[
TK=LT
\Longrightarrow
T\mathcal F_K f(\xi)
=
\mathcal F_L(T\circ f)(\xi),
\]

and

\[
TK=-LT
\Longrightarrow
\boxed{
T\mathcal F_K f(\xi)
=
\mathcal F_L(T\circ f)(-\xi).
}
\]

The latter is the precise connection between reversing an internal phase axis and reversing frequency.

DoubledInternalPhaseFourier.lean[DoubledInternalPhaseFourier.lean](sandbox:/workspace/scratch/f2133092acd6/phase-scale-check/lean/InfoGeometry/Analysis/DoubledInternalPhaseFourier.lean) specializes this construction to the existing doubled real space and its actual complex, modular, and spectral operators. The frequency reversals follow from their proved product signs.

### Scale and convex duality require different additional steps

The logarithmic adapter applies the integral to \(f(e^u)\) against \(du\). This supplies a concrete phase-and-log-scale construction. A Mellin statement against \(dx/x\) still needs the measure-change theorem; inversion and Plancherel need their own analytic proofs.

The Legendre transform has a different definition:

\[
F^*(p)=\sup_x\{\langle p,x\rangle-F(x)\}.
\]

Connecting it to an integral transform requires an additional theorem, such as a suitable stationary-phase or Laplace-principle result. The repository search found relevant finite log-Laplace constructions and conditional rate-function interfaces, but no derived asymptotic bridge in the inspected owners. The contract keeps that missing implication visible.

## 4. What the existing codebase already contributes

The owner search found substantial reusable material. These are separate constructions whose compatibility must be established through explicit maps; their names alone do not combine them into one physical theory.

| Topic | Inspected owner or family | Actual useful content |
|---|---|---|
| Hodge–Dirac square | `DiscreteDiracHodgeChiral` | The algebraic square of \(d+\delta\), under explicit square-zero hypotheses |
| Graph Dirac operators | `BipartiteGraphDirac` | A concrete incidence-based operator, its block square, and distinct Hilbert/Krein adjoint signs |
| Dirac dispersion | `FourVectorDiracReadout` | A finite matrix slash operator, mass factorization, and mass-shell/nonzero-kernel results |
| Spinor bilinears and ideals | `KreinIdealBilinears`, `SpinorBilinearSoldering`, related covariance owners | Product-order reversal, ideal transport, and algebraic bilinear reconstruction |
| Split-octonions acting as operators | `SplitOctonionCliffordAction` | A native Clifford representation into real endomorphisms derived through alternativity |
| Circular operators | `SplitOctonionCARRightRegularBridge` and related owners | Three-mode CAR, anticommutation, bivector squares, and operator conjugation |
| Rapidity and logit | `AmariBinarySimplexBridge`, `AitchisonJaynesRapidityBridge` | The exact factor \(\operatorname{logit}(p)=2\chi\) for \(p=(1+\tanh\chi)/2\) |
| Reciprocal null scaling | `FocalRapidity` | Opposite exponential scalings preserving a product, on its stated positive-pair carrier |
| Penrose constructions | `HomogeneousTwistorCech`, `PenroseContourTransform` | Laurent/Čech constructions and an explicit Maxwell-field example |
| Poincaré/SUSY presentations | The inspected Peirce and super-Poincaré owners | Algebra under stated relations; some closure conditions remain supplied presentation data |

The full source references and qualifications are in the two contracts linked above. In particular, the inspected square-root, Hodge, curvature-remainder, and matrix-dispersion owners do not collectively construct a curved spacetime Dirac equation without further geometric data.

The split-octonion distinction is especially useful here: regular multiplication operators compose associatively in `End`, while raw octonion multiplication remains nonassociative. Existing owners explicitly detect the difference between \(L_aL_b\) and \(L_{ab}\). A proposed Fourier or Lie-group action must respect that difference.

## 5. Corrections retained in the intake ledger

The contracts preserve the broader ideas while assigning them concrete proof obligations. The following are documented mathematical corrections and boundaries; they are not all additional Lean theorems in these PRs.

**Positive flux and indefinite pairings.** A diagonal observer flux or squared Hilbert norm can support positivity. A general mixed spinor pairing need not be positive. A Krein adjoint also does not automatically make \(A^\sharp A\) positive; a compatible positive inner product must first be constructed.

**Associators and entropy production.** For a positive Gram construction,

\[
D(s,s)=\gamma\sum_a\|R_aPs\|^2,\qquad \gamma>0,
\]

strict positivity requires at least one nonzero active channel. Nonassociativity by itself is insufficient. Likewise, putting only the state in a quaternion subalgebra does not force every associator involving arbitrary ambient arguments to vanish.

**Eight-dimensional carriers.** Equal real dimension permits a linear identification after choices. It does not give an algebra isomorphism between an associative even Clifford algebra and the nonassociative split-octonions. A representation can be transported through a verified linear equivalence into an endomorphism algebra; a particular tensor enlargement is not forced merely by dimension.

**Para-Kähler Hessian formulas.** For

\[
g=
\begin{pmatrix}
0&A\\
A^\mathsf T&0
\end{pmatrix},
\]

the determinant calculation gives

\[
\det g=(-1)^n(\det A)^2,
\qquad
\log|\det g|=2\log|\det A|.
\]

The sign and factor of two matter. Defining a function from this determinant does not solve a prescribed Monge–Ampère equation, and strict convexity alone does not guarantee an everywhere positive-definite Hessian.

**Gibbs convergence.** A Gibbs construction needs the action, moment map, measure, and convergence hypotheses. Under Marle’s normal-convergence definition, a nonempty temperature domain is open and convex in the full Lie algebra. It therefore cannot be confined to a fixed proper linear subspace. That is a statement about the specified convergence domain, not a consequence of labelling a generator “compact.” [marle.perso.math.cnrs.fr](https://marle.perso.math.cnrs.fr/pdffiles/2020/GibbsStatesJGSPPart1.pdf?utm_source=chatgpt.com)

**The \(2m\) threshold.** For the one-dimensional Klein step, the interval

\[
m<E<V_0-m
\]

is nonempty when \(V_0>2m\). This is a specific scattering condition. It does not establish a universal energetic-stability criterion for arbitrary Dirac systems. [scoap3-prod-backend.s3.cern.ch](https://scoap3-prod-backend.s3.cern.ch/media/files/71260/10.1093/ptep/ptac085.pdf?utm_source=chatgpt.com) Normal ordering also does not guarantee positive local energy density in every Dirac-field state; explicit negative-density states and their quantum-inequality constraints are known. [arxiv.org](https://arxiv.org/abs/hep-th/0307102?utm_source=chatgpt.com)

These distinctions prevent a finite algebraic identity from being silently promoted into a conservation law, spectral theorem, Gibbs existence theorem, or thermodynamic limit.

## 6. Validation and the outstanding acceptance checks

The environment remains pinned to **Lean `v4.34.1`** and Mathlib **`d13f23b723b8a846827a245b89c10fc7d3f11612`**.

| Check | Result |
|---|---|
| Independent mathematical and pinned-API source review | Passed for the proposed additions; the QGT repair received a separate review |
| Installed staged proof gate | Passed |
| Selected placeholder/unsafe/custom-axiom scans | No matches in the selected owners |
| Selected semantic-content gate | Passed with zero findings and complete selected coverage |
| Native compilation at the current PR heads | Pending |
| Complete recursive declaration axiom audit | Pending |
| Whole root-package acceptance | Not established |

The semantic-content gate is a lexical/source check. Its result is separate from Lean elaboration and kernel acceptance.

The preceding [PR #375 native run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44088120137) did provide actionable compiler evidence:

- Both Fourier modules compiled.
- The QGT congruence proof failed because the inner-product expansion and matrix multiplication exposed the two finite sums in opposite orders.
- The internal Fourier owner had four unused-assumption warnings; the QGT owner had six warnings.
- The doubled Fourier adapter had zero warnings.

The published correction explicitly exchanges the left-hand sums with

```lean
conv_lhs => rw [Finset.sum_comm]
```

before comparing summands. It also removes the reported unused assumptions and tactics. The subsequent `ring` step rearranges complex scalar coefficients; it does not commute the original operators or exchange the inner-product arguments. The fresh native run must still validate that repair.

The focused workflows use the maintained checker and retain their evidence. Their repository source closures contain **10 modules for PR #375** and **148 modules for PR #391**. Successful selected checks would certify those selected surfaces, not the entire repository.

Locally, the maintained single-file and targeted Lake wrapper attempts returned **exit 2 because the shared compiler lock was held**. The root preflight also records the separate HomotopyHypothesis, Atlas, and GIFT dependency blockers. Those are reported in the PRs rather than treated as successful builds.

The next mathematical bridge recorded in the contract is concrete: construct the native eight-coefficient map into the even Clifford algebra and prove that the actual current’s time component equals the existing sum of eight squares. Observer covariance and PDE-derived current conservation can then build on that identification with their required hypotheses.