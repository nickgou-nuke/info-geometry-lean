# Mathematical claims review for the Wilson contribution

Reviewed against upstream `c25e77e9654a54fc5e4a04bfb637b7144defacc0` and the proposed native Gaussian Markov/reflection additions. Review date: 2026-11-25. This is a mathematical/source audit, not a report of a completed Lean build.

## Current upstream scope

The current base replaces the previously cited `9a4492cc6bdf3338379123a085af59dfd8018a9c`. The Gaussian package sources and its dependency pins are unchanged across that comparison; the changes include further CoreLean small-field/localization work and its import umbrella. Packaging must preserve the current umbrella rather than reconstruct it from the older commit. The restored checkout is shallow, so no commit-distance claim is inferred from its local history.

Primary sources:

- [Exact comparison](https://github.com/MathePhysics/4D_Wilson_Loop_RG/compare/9a4492cc6bdf3338379123a085af59dfd8018a9c...c25e77e9654a54fc5e4a04bfb637b7144defacc0).
- [Current README](https://github.com/MathePhysics/4D_Wilson_Loop_RG/blob/c25e77e9654a54fc5e4a04bfb637b7144defacc0/README.md).
- [Gaussian toolchain](https://github.com/MathePhysics/4D_Wilson_Loop_RG/blob/c25e77e9654a54fc5e4a04bfb637b7144defacc0/LEAN/Libraries/GaussianBlockSpin/lean-toolchain) and [pinned Lake configuration](https://github.com/MathePhysics/4D_Wilson_Loop_RG/blob/c25e77e9654a54fc5e4a04bfb637b7144defacc0/LEAN/Libraries/GaussianBlockSpin/lakefile.toml).

The stated target is renormalized Wilson correlations in a fixed finite periodic four-dimensional volume. The README's correlation theorem concerns pairwise vertex-disjoint admissible loops. The manuscript's claimed results, the currently formalized declarations, and a full infinite-volume relativistic reconstruction are distinct scopes.

## Claim ledger

| Proposed claim | Correct contract and useful contribution |
| --- | --- |
| Exact matrix elimination solves background-dependent nonlinear Yang–Mills blocking. | It solves the Gaussian quadratic subproblem for positive definite `A,R` and arbitrary rectangular `Q`, without commutation assumptions. The interacting remainder remains. |
| Removing gauge directions or adding gauge fixing makes the Hessian strictly positive. | Positivity, kernel identification, and coercivity must be proved for the actual operator and chosen subspace. Gauge reduction alone does not eliminate physical negative or residual zero modes. |
| A non-Abelian background forces a matrix-valued nonscalar coarse precision. | A covariant `Q(A)` may coexist with scalar `R = α I` in an invariant inner product. General positive `R` is useful for anisotropic/correlated noise, but covariance of that choice is an additional obligation. |
| Native Markov kernels directly give Fisher contraction and QFT `c`/`a` theorems. | Native Mathlib gives extended KL data processing for the same kernel applied to both finite measures. Fisher variants and QFT monotonicity require separate hypotheses and arguments. |
| Reflection commutation plus positive precision preserves OS positivity. | Commutation and ordinary positive definiteness do not imply reflection positivity. The finite covariance bridge requires positive reflected fine/noise forms and transport of the chosen positive-time tests. |
| Convergent renormalized loop correlations immediately give an inductive-limit state and physical Hamiltonian. | One must establish the observable algebra, all relevant products/relations, positivity, normalization, bounds, and compatible transition maps. Ordinary GNS then gives a cyclic representation; dynamics and physical OS reconstruction are further steps. |
| `Ey` is the full classical minimizer, and fluctuations use the coarse covariance. | `Ey` minimizes the quadratic part. Fine fluctuations have covariance `H⁻¹`; `S⁻¹` is the coarse effective covariance. |

## Exact Gaussian content and the interacting remainder

For real finite-dimensional matrices define

\[
H=A+Q^{\mathsf T}RQ,\qquad E=H^{-1}Q^{\mathsf T}R,\qquad
S=R-RQH^{-1}Q^{\mathsf T}R.
\]

The positive Schur theory and Gaussian integration give the exact quadratic elimination and `S⁻¹ = R⁻¹ + Q A⁻¹ Qᵀ`. Adding a nonlinear term `V` gives the algebraic decomposition

\[
\tfrac12x^{\mathsf T}Ax+\tfrac12(y-Qx)^{\mathsf T}R(y-Qx)+V(x)
=\tfrac12y^{\mathsf T}Sy+\tfrac12z^{\mathsf T}Hz+V(Ey+z),\quad z=x-Ey.
\]

The remaining factor is an expectation of `exp(-V(Ey+z))` against fine fluctuations with covariance `H⁻¹`. The full stationary equation is `Hx - QᵀRy + ∇V(x) = 0`; it need not be solved by `Ey`. These identities explain where the Gaussian contribution fits without claiming control of the interacting integral.

Upstream [`EffectiveForm.lean`](https://github.com/MathePhysics/4D_Wilson_Loop_RG/blob/c25e77e9654a54fc5e4a04bfb637b7144defacc0/LEAN/Libraries/GaussianBlockSpin/GaussianBlockSpin/EffectiveForm.lean) supplies the Gaussian elimination context. [`GaussianGraphs.lean`](https://github.com/MathePhysics/4D_Wilson_Loop_RG/blob/c25e77e9654a54fc5e4a04bfb637b7144defacc0/LEAN/Libraries/GaussianBlockSpin/GaussianBlockSpin/GaussianGraphs.lean), particularly `truncExp_gaussProb_eq_connected`, expresses a finite polynomial cumulant/truncated expectation as a connected-graph sum. It does not by itself prove convergence of an exponential or polymer expansion, remainder estimates, or large-field control.

## Gauge directions and positivity

Gauge invariance naturally gives Hessian null directions at a critical background. Away from a critical point, differentiating the gauge-invariance identity also differentiates the infinitesimal gauge vector field; a first-variation term remains. The blanket off-shell assertion that every pure gauge tangent is in the Hessian kernel is therefore too strong.

Even exact removal of gauge directions need not yield positivity. The elementary example `A = diag(0,-1)` with gauge image spanned by the first coordinate leaves a negative physical mode. Adding `ξ⁻¹ D Dᵀ` yields `diag(ξ⁻¹,-1)` and does not repair it. A useful positive theorem instead assumes a self-adjoint positive-semidefinite operator, identifies its kernel with the removed directions, and restricts to an orthogonal complement. A uniform cutoff-independent coercivity bound is a further analytic assertion.

An original source distinguishing critical Yang–Mills backgrounds, transverse variations, index, and nullity is Bourguignon–Lawson, *Stability and isolation phenomena for Yang–Mills fields*, [DOI 10.1007/BF01942061](https://doi.org/10.1007/BF01942061), §6. The reviewed primary paper text was available through an [author-paper mirror](https://www.academia.edu/49690289/Stability_and_isolation_phenomena_for_Yang_Mills_fields).

There is also concrete current upstream machinery to examine: [`SmallFieldOperator.lean`](https://github.com/MathePhysics/4D_Wilson_Loop_RG/blob/c25e77e9654a54fc5e4a04bfb637b7144defacc0/LEAN/CoreLean/CoreLean/SmallFieldOperator.lean) contains `DeltaS_pos` and `Gp'_pos` under small-background and compressed/Dirichlet hypotheses. Its operator on Hermitian matrix-valued scalar fields is not automatically the full gauge-field Hessian. The relevant bounds and carrier must be matched explicitly before reuse.

For native matrix Lean code, a transverse subspace is the vector-space carrier. Choose an orthonormal basis indexed by a finite type to obtain a matrix on that subspace; the subspace's vectors are not themselves the finite coordinate index type.

## Information monotonicity: what the native theorem says

Pinned Mathlib [`DataProcessing.lean`](https://github.com/leanprover-community/mathlib4/blob/8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a/Mathlib/InformationTheory/KullbackLeibler/DataProcessing.lean) proves `klDiv_comp_right_le` for two finite measures and the same Markov kernel. Its [`Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a/Mathlib/InformationTheory/KullbackLeibler/Basic.lean) uses extended nonnegative KL with the finite-measure mass correction. Probability inputs recover the familiar relative entropy formula.

The same-channel hypothesis matters if a blocking kernel depends on a background, coupling, or state: two different kernels cannot be substituted into this theorem. Nor does data processing provide strict contraction, summable RG error, or continuum compactness.

Relative spatial Fisher information does not have arbitrary-channel contraction in this form. As an elementary calculation, take `p = N(0,1)`, `q = N(1,1)` and the deterministic invertible channel `y = c x`. Their KL remains `1/2`, while `∫ |∂ log(p/q)|² dp` changes from `1` to `1/c²`, increasing when `0 < c < 1`. Parametric Fisher information has different regularity and parameter-independent-channel hypotheses. This calculation is a mathematical counterexample, not a claim of a new Lean theorem.

Original QFT monotonicity sources use further structure: Casini–Testé–Torroba, [arXiv:1704.01870](https://arxiv.org/abs/1704.01870), combines quantum entropy, Lorentz invariance and a vacuum Markov property; Komargodski–Schwimmer, [arXiv:1107.3987](https://arxiv.org/abs/1107.3987), uses trace anomalies, dilaton scattering and unitarity. A classical Gaussian kernel DPI is a useful input in its own scope, not a substitute for these arguments.

## Reflection positivity and reconstruction

The proposed finite reflection source explicitly proves a counterexample to commutation sufficiency. Take the swap reflection, positive-time test `e₁`, and noise covariance

\[
N=\begin{pmatrix}1&-1/2\\-1/2&1\end{pmatrix}.
\]

`N` is strictly positive and reflection commuting, yet its reflected test form is negative. With identity fine covariance and identity blocking, the output remains strictly positive and reflection commuting while failing reflected-form positivity. A correct preservation statement needs a positive reflected noise form in addition to the fine form and test transport. The new bridge proves precisely that finite matrix statement; it does not assert the full Gaussian-measure OS theorem for all positive-time observables.

Deterministic coarsening maps of configurations induce **inductive** pullbacks of observables; consistent measures form the corresponding **projective** system. A stochastic averaging operator is generally positive and unital but not multiplicative: for uniform `Y ∈ {-1,1}`, averaging `f(Y)=Y` gives `Tf=0` and `T(f²)=1`. It cannot automatically supply a `StarAlgHom`.

The reported limits for pairwise disjoint loops do not alone supply positivity on the whole observable star algebra: expressions `F*F` involve products, including overlapping or coincident loops. Relations, normalization, bounds and compatibility with renormalization must be established. Given a positive normalized state, ordinary GNS constructs a cyclic representation. A self-adjoint Hamiltonian requires suitable dynamics and continuity; positive energy requires additional input.

Full OS reconstruction concerns a suitable Euclidean correlation hierarchy, reflection positivity, covariance and regularity/growth conditions. The original reference is Osterwalder–Schrader, *Axioms for Euclidean Green's Functions*, [DOI 10.1007/BF01645738](https://doi.org/10.1007/BF01645738), and [Part II](https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-42/issue-3/Axioms-for-Euclidean-Greens-functions-II-with-an-Appendix-by/cmp/1103899050.pdf). These are contextual primary references; this audit does not claim a line-by-line review of the full original PDF. A fixed periodic torus has only its torus-preserving rotation symmetries, and periodic Euclidean time is not the full Minkowski vacuum reconstruction setting. The source proposal's automatic Lorentzian or split-signature conclusion is therefore not justified by the finite Gaussian code.

## Recommended publication claims

Publish the concrete native kernel, its exact composition, extended KL monotonicity, and the separately qualified finite covariance reflection theorem. Explain that gauge coercivity, interacting RG error control, observable/state compatibility and physical reconstruction are future model-specific obligations. Those qualifications preserve a useful, mathematically substantive contribution without upgrading finite Gaussian algebra into a continuum Yang–Mills theorem.
