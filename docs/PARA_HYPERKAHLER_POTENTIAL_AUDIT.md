# From potential archetypes to exact statements

The valid common structure is **a potential with specified geometric data,
domain, and derivative operation**. It is not an equality between all the
potentials in the manuscript. The implementation extends existing owners at
`ec7c289661eb1cd45b2afcd886847ca992318de5` and proves a flat split-quaternion
model, its finite products, and the corrections needed before making further
geometric identifications.

## 1. The preserved mathematical construction

Let `V = M₂(ℝ)` carry the existing determinant polarization `g`, and let
`I`, `S`, `T` act by left multiplication by the existing split atom's
`I`, `J`, `K`. Then

\[
I^2=-1,\qquad S^2=T^2=1,\qquad IS=-SI=T,
\]
\[
g(Iu,Iv)=g(u,v),\qquad
g(Su,Sv)=g(Tu,Tv)=-g(u,v).
\]

These are compatible structures on the **four-dimensional regular module**.
The two-dimensional real spinor module does not by itself provide this tangent
model. On `Vⁿ`, use the sum pairing and componentwise actions. The signature
formula is the sum of `aᵢ²+bᵢ²-cᵢ²-dᵢ²`.

The distinguished quadratic potential is

\[
K(x)=\tfrac12g(x,x)=\tfrac12\sum_i\det x_i.
\]

With the flat affine derivative `D`, the new proofs establish

\[
DK_x(v)=g(x,v),\qquad D^2K_x(u,v)=g(u,v).
\]

Consequently the **gradient relative to `g`** is the Euler vector `E(x)=x`.
For a Hilbert scalar product with `g(u,v)=⟨ηu,v⟩`, the Hilbert gradient is
`ηx`. This explains the repository's `krein_grad` convention: changing the
metric used to define a gradient changes the resulting vector.

For `A ∈ {I,S,T}`, put `ω_A(u,v)=g(Au,v)`. All three are ordinary real
alternating nondegenerate two-forms; their compatible endomorphisms distinguish
the complex and para-complex cases. The normalization used here is

\[
\alpha_A=-\tfrac12 DK\circ A=\tfrac12g(Ax,\cdot),
\qquad d\alpha_A=\omega_A.
\]

Indeed,

\[
d\alpha_A(u,v)=\tfrac12\{g(Au,v)-g(Av,u)\}=g(Au,v).
\]

`extDeriv_potentialOneForm` uses Mathlib's actual `extDeriv` and continuous
alternating maps; `potentialTwoForm_closed` uses its `d²=0` theorem. These are
not definitions of the derivative to be the desired answer.

For a curved manifold, the corresponding calculation requires a metric
connection, parallel compatible `I,S,T`, and a closed homothety `∇E=id`.
With `K=g(E,E)/2`, metric compatibility then gives `dK=g(E,·)` and
`∇dK=g`. General Kähler potentials do not automatically satisfy this real
Levi-Civita Hessian equation. This change does not construct a global curved
cone or a Levi-Civita connection in Lean. Nor does the scalar alone select
the three endomorphisms: they are supplied by the split-quaternion owner.

## 2. Corrections that are essential to the construction

| Manuscript association | Exact replacement |
|---|---|
| `K=0` makes the spacetime metric degenerate | The ambient quadratic Hessian is constant and nondegenerate at null points too. The metric restricted to the smooth null hypersurface is degenerate; these are different statements. |
| Every potential zero set is a geometric boundary | `K+ℓ+c` has the same affine Hessian as `K`. Its zero set can change. A zero set needs a specified normalization and an independent geometric interpretation. |
| Euler scaling is the `SL₂` Iwasawa `A` generator | Scalar scaling multiplies the quadratic potential by `r²`. Every determinant-one left action preserves it, including the split torus. The scalar identity generator lies in `gl₂`; the split-torus generator is traceless. |
| Orthogonality to `∇K` selects just the `K` and `N` sectors | It selects tangent directions to a level of `K`. The determinant-one `A` action is tangent too. |
| A general `(2n,2n)` null cone is the Klein quadric | The classical Klein quadric is the Plücker quadric in `P(Λ²ℝ⁴)`, whose six-dimensional ambient quadratic space has signature `(3,3)`. The general `4n`-dimensional model requires a separate map to that carrier. |
| A null vector is a zero eigenvector of the metric | Isotropy `g(x,x)=0` does not imply `g(x,·)=0` or `ηx=0`. The nonzero projector `Pplus` supplies a checked counterexample to ambient Hessian degeneracy. |
| A Krein norm, a free energy, and a logarithmic barrier are one function | Their carriers, signatures, homogeneity laws, and allowed gauges must first be related by proved maps. |

The projective null quadric, the Klein bottle quotient, a modular-time seam,
an Aharonov-type denominator, and an Andreev reflection are not identified by
any of the new theorems. Such identifications require explicit maps and
equations; a shared zero or a shared name is insufficient.

A specified Euler field and homogeneous normalization remove the freedom to
add arbitrary affine terms while still calling the result the same cone
potential. The affine-gauge theorem concerns the Hessian alone.

## 3. The trace correction

For the existing doubled grading `Γ²=1`, define
`Z^sharp=Γ Z† Γ`. The existing supertrace is `str(A)=tr(ΓA)`. Hence

\[
\operatorname{str}(Z^\sharp Z)
=\operatorname{tr}(Z^\dagger\Gamma Z),
\qquad
\operatorname{tr}(Z^\sharp Z)
=\operatorname{tr}(\Gamma Z^\dagger\Gamma Z).
\]

The manuscript equated the left expression in the first identity with the
right expression in the second. They already differ for `Z=1` on an equally
doubled nonzero space: the supertrace is zero and the ordinary trace is the
total dimension. `trace_superTrace_counterexample` checks this on complex
`2×2` matrices. An operator realization of Zorn coordinates must separately
specify which pairing it preserves; associative matrix multiplication is not
automatically the nonassociative Zorn multiplication.

## 4. Information geometry and the strain barrier

The repository already has the exact route through
`Geometry/DualFlatKreinLegendreGraph.lean`: the normalized neutral pairing
pulls back to a symmetric duality pairing on its graph, and the skew form
vanishes on that graph. `Geometry/BinaryLegendreEntropyFlow.lean` supplies an
analytic Bernoulli instance. This preserves the information-geometric
connection without identifying a positive Fisher metric with the neutral
ambient metric. `Physics/ParaKahlerFisherCompatibilityObstruction.lean`
already records the obstruction to that unrestricted identification.

The matrix barrier requires the positive-definite domain
`Λ²I-FᵀF ≻ 0`. Its scalar restriction is

\[
B_\Lambda(x)=-\log(\Lambda^2-x^2),\qquad
B'_\Lambda(x)=\frac{2x}{\Lambda^2-x^2},\qquad
B''_\Lambda(x)=\frac{2(\Lambda^2+x^2)}{(\Lambda^2-x^2)^2}>0.
\]

The new `IntervalBarrierPotential` proofs establish these derivatives and
the precise conditional estimate

\[
B_\Lambda(x)\le C
\quad\Longrightarrow\quad
x^2\le\Lambda^2-e^{-C}.
\]

At `Λ=1,x=0`, the barrier is zero and its Hessian is `2`: the potential vanishes
at an interior point with positive Hessian. A finite bound on the barrier gives a gap to
its singular wall. The existence or propagation of this bound along a
Navier–Stokes solution is a separate analytic theorem. No PDE regularity,
topological reflection, or blow-up exclusion follows from the definition of
the barrier alone. Its positive Hessian does not supply a para-hyperkähler
triad without additional compatible geometric structure.

## 5. Cubic, quartic, and logarithmic potentials

The existing split-Albert owner has a cubic norm on `H3Zorn ℝ`, whereas its
Freudenthal charge carrier has a quartic invariant. This distinction agrees
with the cubic invariant of the basic `E₆` representation and the quartic
structure associated with groups of type `E₇`.
[Xu, E₆ polynomial representation](https://arxiv.org/abs/0811.1399),
[Borsten et al., Freudenthal transformations](https://arxiv.org/html/1905.00038v2).

The `16+46+16` decomposition is an adjoint grading, not a definition of a
quartic scalar prepotential. Vector-multiplet special (para-)Kähler geometry
and (para-)quaternionic geometry obtained by the local c-map must also be
distinguished.
[Cortés et al., vector multiplets](https://arxiv.org/abs/hep-th/0312001),
[Cortés et al., local c-map](https://arxiv.org/abs/1507.04620).

On the **positive quartic chamber** the implementation reuses the actual
`H3ZornFreudenthal.quarticInvariant_smul` theorem to prove

\[
L(Q)=-\log Q_4(Q),\qquad
L(rQ)=L(Q)-4\log r\quad(r>0),
\]
\[
L(Q)=0\iff Q_4(Q)=1,
\qquad
\pi\sqrt{Q_4(Q)}=\pi\exp[-L(Q)/2].
\]

The last identity is an exact logarithmic rewrite, not a derivation of a
horizon or an attractor solution. The physical leading-order entropy formula
in the relevant symmetric theories uses `π√|Q₄|`; the new theorem chooses
the positive chamber explicitly.
[Borsten et al., equations (1.1)–(1.2)](https://arxiv.org/html/1905.00038v2).

Mathlib's `Real.log` is total, including at zero. Therefore none of these
theorems uses `Real.log 0` as a singular boundary value. The positive-domain
hypotheses are part of the statements.

## Implementation map

| Owner added | Scope |
|---|---|
| `Geometry/QuadraticPotentialCalculus.lean` | Actual first/second Fréchet derivatives, affine gauge freedom, metric gradient, normalized twisted primitive, native exterior derivative and closedness |
| `Geometry/FlatSplitQuaternionPotential.lean` | Existing determinant-polarized regular module, nondegeneracy, exact triad, null-point example, Euler versus determinant-one actions |
| `Geometry/FlatSplitQuaternionFamily.lean` | Finite products, split relations, signature formula, potential Hessian, exact triad |
| `Analysis/LogHomogeneousPotential.lean` | Positive-domain logarithmic homogeneity, radial calculus, zero-set normalization, square-root rewrite, sublevel gap |
| `Analysis/IntervalBarrierPotential.lean` | Actual scalar strain-barrier derivatives, positive Hessian, interior zero, conditional gap |
| `Modular/KreinPotentialTrace.lean` | Existing grading/supertrace identity and explicit complex-matrix counterexample |
| `Exceptional/FreudenthalLogPotential.lean` | Specialization to the existing split-Albert Freudenthal quartic |

The two Freudenthal dependency files use narrower Mathlib imports; their
mathematical declarations are preserved. Verification details are recorded
with the change, with the actual runtime version distinguished from the
repository's toolchain pin.

## Verification

The seven new modules compile without warnings, and a combined import check
passes. An exhaustive `#print axioms` audit of their **67 theorems** reports
only `propext`, `Classical.choice`, and `Quot.sound`: no `sorryAx` or custom
axiom occurs in these theorem dependencies. The two existing Freudenthal
owners with narrowed imports also compile without warnings. Some untouched
dependencies emit existing linter warnings.

| Item | Checked environment |
|---|---|
| Lean runtime | `4.28.0`, commit `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b` |
| Mathlib | `8f9d9cff6bd728b17a24e163c9402775d9e6a365`, matching the repository manifest |
| Execution | Sequential checks under `/tmp/info-geometry-build.lock`, in an isolated output directory with existing dependency caches |
| Integration | Seven imports added to `InfoGeometry/All.lean`; the combined check imports those seven modules together |
| Remaining gate | The repository pins Lean `4.28.1`; this runtime and the complete repository umbrella build were not checked |

No toolchain, manifest, or vendored dependency was changed. In an environment
with the repository's pinned runtime installed, the narrow build command is:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Geometry.QuadraticPotentialCalculus \
  InfoGeometry.Geometry.FlatSplitQuaternionPotential \
  InfoGeometry.Geometry.FlatSplitQuaternionFamily \
  InfoGeometry.Analysis.LogHomogeneousPotential \
  InfoGeometry.Analysis.IntervalBarrierPotential \
  InfoGeometry.Modular.KreinPotentialTrace \
  InfoGeometry.Exceptional.FreudenthalLogPotential
```

This verification establishes the stated flat geometric and analytic results.
It does not establish a curved para-hyperkähler classification, an exceptional
prepotential metric, a cosmological action, or a Navier–Stokes regularity theorem.
