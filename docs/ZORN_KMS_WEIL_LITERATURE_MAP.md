# Zorn operators, modular theory, and the arithmetic positivity boundary

## Scope

This note records a bounded primary-source literature review for the supplied
brainstorm. It distinguishes literature theorems, elementary deductions, and
the repository's finite algebraic implementation. It does not certify native
compilation; the owner checks and declaration axiom reports do that separately.
The implementation contract is [ZORN_SOURIAU_INTAKE_CONTRACT.md](ZORN_SOURIAU_INTAKE_CONTRACT.md).
The companion [evidence map](ZORN_SOURIAU_EVIDENCE_MAP.md) covers the separate
Souriau, triality, and physical-model sources. This note adds the KMS/Weil
comparison and the native declaration map below.

There is substantial precedent for the broad connection between quantum
statistical systems and zeta zeros. There is also a direct dihedral example.
The reviewed sources do not identify the proposed Zorn carrier with the
arithmetic test-function quotient or establish its required positive form.
The labels `2.1.3`, `2.2.7`, `2.4.1`, and `2.4.2` supplied without a source
map cannot be reliably resolved; precise author, title, and section references
are used below instead.

## 1. The direct dihedral precedent

In [Connes, *Trace Formula in Noncommutative Geometry and the Zeros of the
Riemann Zeta Function*](https://alainconnes.org/wp-content/uploads/selecta.ps-2.pdf),
Section VIII, printed pages 45–46, the position and Fourier cutoff projections
give a unitary representation of

\[
C_2*C_2\cong D_\infty,\qquad U_i=2P_i-I.
\]

Their noncommuting relative position is part of the trace-formula analysis.
This provides a specific precedent; the reflections are not Tomita's modular
conjugation. The paper's introduction leaves the number-field global trace
formula open and relates its validity to RH.

The group presentations must remain distinct:

| Data | Relation | Group presented by that data |
|---|---|---|
| One involution | `r² = 1` | `C₂` |
| Two commuting involutions | `r² = s² = 1`, `rs = sr` | `C₂ × C₂` |
| Two unrestricted involutions | `r² = s² = 1` | `C₂ * C₂` |
| Involution and a flow | `r U(t) r = U(-t)` | An inversion action on the flow |

These presentations describe universal groups; a particular action can have
an additional kernel. Thus two involutions alone do not establish a faithful
infinite-dihedral action. A finite matrix sign-flip model requires an actual
intertwining map before it can be identified with the arithmetic cutoff action.

## 2. KMS and Tomita conjugation

[Bost–Connes, *Hecke Algebras, Type III Factors and Phase Transitions with
Spontaneous Symmetry Breaking in Number Theory*](https://repo-archives.ihes.fr/FONDS_IHES/I_Prepublications/CONNES/1994-1998/M_95_38/M_95_38_web.pdf),
Section 6, equation (3) and Theorem 25, gives

\[
H e_n=(\log n)e_n,\qquad
\operatorname{Tr}(e^{-\beta H})=\zeta(\beta)\quad(\beta>1).
\]

Extreme low-temperature KMS states are parametrized by the cyclotomic Galois
group. Section 7 treats uniqueness for `0 < β ≤ 1`. A partition function on
this real temperature range is not yet a positive spectral realization of
critical-strip zeros.

[Dereziński, *Introduction to Representations of the Canonical Commutation and
Anticommutation Relations*](https://users.fuw.edu.pl/~derezins/derezinski.pdf),
Sections 8.1–8.3, printed pages 101–102, describes standard representations,
the antilinear Tomita operator, and the KMS boundary condition. In the convention

\[
F_{A,B}(t)=\varphi(A\alpha_t(B)),
\qquad F_{A,B}(t+i\beta)=\varphi(\alpha_t(B)A),
\]

the strip boundary exchanges operator order. It does not assert periodicity
of every correlation function or the operator identity `α(iβ)(B) = B`.

The modular conjugation relations are also stated in
[Dereziński–Pillet, *Tomita–Takesaki theory*](https://pillet.univ-tln.fr/data/pdf/Tomita-Takesaki_theory.pdf),
pages 2–3. The following sign calculation is an elementary consequence of
antiunitary functional calculus in that setting:

\[
J\Delta J=\Delta^{-1},\qquad
J(\log\Delta)J=-\log\Delta,
\]
\[
J\Delta^{it}J
=e^{-itJ(\log\Delta)J}
=\Delta^{it}.
\]

Antiunitarity conjugates the scalar `i`; the two signs cancel. Generator
reversal therefore does not give inversion of this unitary parameter. Unbounded
identities retain their domain requirements. A proposed “helical KMS tubule”
would need its own geometric definition and compatibility theorem; that name
is not used by the sources inspected here.

## 3. The arithmetic realization and the positivity obligation

[Connes–Consani–Marcolli, *Noncommutative geometry and motives: the
thermodynamics of endomotives*](https://arxiv.org/pdf/math/0512138), checked
version 2, Sections 4.2–4.4 and Theorem 4.16, obtains a spectral realization
from the distilled Bost–Connes system. Section 5.4, Theorem 5.11, states the
RH-equivalent requirement

\[
\operatorname{Tr}\!\left(\vartheta_m(f\star f^\sharp)|_{H^1}\right)\ge0
\quad\text{for every }f\in\mathcal S(C_K),
\qquad
f^\sharp(g)=|g|^{-1}\overline{f(g^{-1})}.
\]

Here the assertion concerns all Grössencharakter L-functions over `K`. The
trace pairing has a substantial radical, discussed in Lemma 5.12. Its
positivity on the arithmetic quotient remains a separate obligation.

[Suzuki, *On the Hilbert space derived from the Weil distribution*](https://arxiv.org/pdf/2301.00421),
version 3, Section 1, states Weil's criterion on complex-valued
`C_c^∞(ℝ)`: with `ψ̃(x) = conjugate(ψ(-x))`, RH is equivalent to
`W(ψ * ψ̃) ≥ 0` for every admissible `ψ`. Theorem 1.1's identification with
a de Branges/model Hilbert space assumes RH. Consequently that theorem
cannot serve as an unconditional proof of the needed positivity. The paper's
screw-kernel discussion should not be conflated with an arbitrary indefinite
Krein space.

### What the off-critical pair calculation does establish

In centered spectral coordinates a reflected pair is `γ, conjugate γ`.
Writing `a` and `b` for the two transformed test values, its weighted
contribution is the Hermitian block

\[
m(a\overline b+b\overline a),\qquad
\begin{pmatrix}0&m\\m&0\end{pmatrix},\qquad m>0.
\]

This elementary block has one positive and one negative eigenvalue; `a=1`,
`b=-1` gives `-2m`. Passing from that calculation to the full Weil form needs
admissible test functions realizing or approximating these values while
controlling every other zero and the infinite tail. Finite interpolation at
two points does not supply that control. The weight `m` also does not by
itself give `m` independent negative directions.

## 4. What related approaches actually supply

| Primary source and location | Established or conditional content relevant here |
|---|---|
| [Conrey–Li, *A note on some positivity conditions related to zeta and L-functions*](https://arxiv.org/pdf/math/9812166), Sections 2–3 | Particular proposed de Branges shift-positivity conditions fail for the displayed zeta/L-function examples. This obstructs those hypotheses, not Weil's criterion or all de Branges constructions. |
| [Banaszak–Uetake, *Abstract intersection theory and operators in Hilbert space*](https://arxiv.org/pdf/0908.2909), OP1–OP5, INT1–INT3, Theorem 3.5 | For the stated operator class, critical-line spectrum is equivalent to existence of their intersection theory. An arithmetic application still requires the actual zero spectrum, Hodge inequality, growth bounds, and Lefschetz trace identity. An arbitrary indefinite pairing does not supply these assumptions. |
| [Bender–Brody–Müller, *Hamiltonian for the zeros of the Riemann zeta function*](https://arxiv.org/pdf/1608.03679), version 4, abstract and pages 3–4 | The proposed metric analysis is heuristic. The inverse metric is unbounded, and the displayed eigenfunction space has infinite norms. Genuine self-adjointness and a valid Hilbert-space domain remain necessary for the stated RH implication. |
| [Sierra, *The Riemann zeros as energy levels of a Dirac fermion in a potential built from the prime numbers in Rindler spacetime*](https://arxiv.org/pdf/1404.4252), Section IV.D and the Riemann-model discussion, equations (152)–(172) | The Dirac construction has a positive `L²` norm and a separate indefinite boundary-flux pairing. The zeta interpretation uses a small-reflection limit, a zero-dependent boundary phase, and further unproved limiting assumptions. The discussion after (172) explicitly qualifies the apparent RH argument. |

## 5. Connection to the finite Zorn implementation

[Krasnov, *Spin(11,3), particles and octonions*](https://arxiv.org/pdf/2104.01786v1),
Section 3.2, equations (28)–(29), gives the seven real `8 × 8`
left-multiplication generators and their `(4,3)` Clifford relations. Section
3.3 separately gives the invariant split form for the bivector action.

The repository reuses an actual native Clifford lift and an existing coordinate
equivalence. The full Clifford map is not injective: its source dimension is
128 and the endomorphism dimension is 64. Injectivity of the generator map
and injectivity of the full algebra map are different propositions.

Mathlib's native [`IsUnit`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Units/Defs.html#IsUnit)
asserts a two-sided inverse. Its [`unitary`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Star/Unitary.html#unitary)
instead requires `star U * U = 1` and `U * star U = 1` for the specified star.
Both definitions were also inspected at the repository's pinned Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Hilbert unitarity additionally
requires identifying that star with the adjoint for a positive inner product.

An elementary counterexample explains why indefinite preservation is insufficient:

\[
G=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
T=\operatorname{diag}(2,\tfrac12),\qquad T^TGT=G.
\]

If a positive inner product were invariant under `T`, its first basis vector
would satisfy `4 ‖e₁‖² = ‖e₁‖²`, which is impossible. Choosing a positive
norm can therefore destroy invariance of the original action. For unbounded
operators, domains and completeness add further requirements.

## 6. Native Lean dependency and declaration map

The source statements below were inspected at
[`67a54aed7f4d860a531fe012c606f9bc79a37c5d`](https://github.com/nickgou-nuke/info-geometry-lean/commit/67a54aed7f4d860a531fe012c606f9bc79a37c5d),
the published Zorn/Souriau draft. The regular-norm, Witt-bridge, and exact-determinant
owners originate in the parent Zorn regular-operator change. This documentation
update introduces no additional Lean owner and does not turn source inspection
into kernel acceptance. Consult the exact-head native build, fresh
warnings-as-errors, and declaration-axiom results for that separate status.

Use the existing `InfoGeometry.Canonical.ZornMatrix ℝ` carrier, its actual
cross-product multiplication, and the existing linear
`leftRegularRepresentation`. Its target `Module.End ℝ (ZornMatrix ℝ)` is
associative under composition; the source product remains nonassociative.
The causal algebraic order is coordinates and norm, regular action and
alternativity, conjugate contractions and inverse, then determinant and
incidence. The Clifford extension separately uses the trace-zero generators.
The cotangent-graph construction is another algebraic result on a native
vector/dual carrier; no map from the Zorn action to that construction is assumed.

Namespace abbreviations in this table are:

- `RN = InfoGeometry.Lie.CanonicalZornRegularNorm`.
- `WB = InfoGeometry.Lie.CanonicalZornWittRegularBridge`.
- `ED = InfoGeometry.Lie.CanonicalZornRegularExactDet`.
- `CG = InfoGeometry.Algebraic.CotangentBilinearGraph`.

| Mathematical statement | Existing native declaration and actual scope |
|---|---|
| Two separately chosen four-vectors give one eight-dimensional Zorn element. | `WB.wittZornEquiv`, `WB.wittZornEquiv_coordinates`: a native linear equivalence with coordinates `(a,b,u,v) = (x₀,p₀,x⃗,p⃗)`. |
| The reduced norm is the primal–dual pairing. | `WB.zornNormFun_wittZornEquiv`: `zornNormFun (wittZornEquiv (x,p)) = wittPairing x p`. |
| Left alternativity gives the operator square law, and polarization gives the anticommutator. | `RN.leftRegular_square`, `RN.leftRegular_anticommutator`, valid for all source elements. The polarized right-hand side need not be scalar. |
| Both ordered conjugate contractions equal the norm times identity. | `RN.leftRegular_mul_conj`, `RN.conj_mul_leftRegular`, in the actual endomorphism algebra. |
| Nonzero norm gives a two-sided inverse; invertibility forces nonzero norm. | `RN.leftRegular_mul_inverse`, `RN.inverse_mul_leftRegular`, `RN.isUnit_leftRegular_iff`. The inverse is the reciprocal-norm conjugate left action. |
| The affine chiral squares retain their scalar coordinates. | `WB.leftRegular_primal_square`, `WB.leftRegular_dual_square`: `L_X² = x₀ L_X`, `L_P² = p₀ L_P`. |
| The full mixed anticommutator has two nonscalar terms. | `WB.leftRegular_primal_dual_anticommutator`: `L_X L_P + L_P L_X = x₀ L_P + p₀ L_X − η(x,p) I`. |
| Singularity expresses incidence with the existing covector kernel. | `WB.not_isUnit_leftRegular_iff_mem_ker`, `WB.det_leftRegular_iff_mem_ker`. `WB.finrank_ker_toDualPlus` gives dimension three under `p ≠ 0`. |
| The determinant has the exact signed fourth-power value, in every eight-element basis. | `ED.leftRegular_cartesian_matrix`, `ED.det_leftRegular_eq_norm_pow_four`; the latter has no nonzero-norm or trace-zero hypothesis. |
| The operator action retains the defect of source associativity. | `WB.leftRegular_chiral_sum_defect`: the stated native chiral sums give `−2 • (zornMinus − zornPlus)`. `WB.leftRegular_primal_dual_noncommute` also supplies actual ordered noncommutativity. |
| The full seven-generator Clifford map is not injective. | `InfoGeometry.Lie.SplitOctonionImaginaryAction.splitOctonionLeftCliffordRepresentation_not_injective`; the same owner proves source dimension 128, target dimension 64, and kernel dimension at least 64. |
| The alternating cotangent graph has coefficient `1 − 2t`. | `CG.cotangentForm_pullback_signedGraph`; `CG.cotangentForm_negativeGraph` gives `3B`, and `CG.negativeGraph_plane_counterexample` separates that value from `−B`. |

Exact source owners:

- [Regular norm and inverse](https://github.com/nickgou-nuke/info-geometry-lean/blob/67a54aed7f4d860a531fe012c606f9bc79a37c5d/lean/InfoGeometry/Lie/CanonicalZornRegularNorm.lean).
- [Witt coordinates, chiral operators, and incidence](https://github.com/nickgou-nuke/info-geometry-lean/blob/67a54aed7f4d860a531fe012c606f9bc79a37c5d/lean/InfoGeometry/Lie/CanonicalZornWittRegularBridge.lean).
- [Exact determinant](https://github.com/nickgou-nuke/info-geometry-lean/blob/67a54aed7f4d860a531fe012c606f9bc79a37c5d/lean/InfoGeometry/Lie/CanonicalZornRegularExactDet.lean).
- [Full Clifford noninjectivity](https://github.com/nickgou-nuke/info-geometry-lean/blob/67a54aed7f4d860a531fe012c606f9bc79a37c5d/lean/InfoGeometry/Lie/SplitOctonionCliffordNoninjective.lean).
- [Cotangent graph](https://github.com/nickgou-nuke/info-geometry-lean/blob/67a54aed7f4d860a531fe012c606f9bc79a37c5d/lean/InfoGeometry/Algebraic/CotangentBilinearGraph.lean).

### Coordinate and interpretation checks

The full norm `N(a,b,u,v) = ab − u·v` is a quadratic form on eight real
coordinates. Put `A=(a+b)/2`, `D=(a−b)/2`, `U=(u+v)/2`, and `V=(u−v)/2`.
Elementary expansion gives

\[
N=A^2+\lVert V\rVert^2-D^2-\lVert U\rVert^2,
\]

so its full signature is `(4,4)`. The pairing `η(x,p)` of two separately chosen
four-vectors restricts to the Minkowski quadratic form on the diagonal section `p=x`. On the
parity section `p=(x₀,−x⃗)` it becomes Euclidean positive definite. The section
`p=−x` instead gives the negative Minkowski form. These coordinate deductions
are not new Lean declarations in this documentation update.

Likewise, `x₀=0` gives a square-zero chiral element/operator, including zero;
claiming nilpotency index exactly two additionally requires nonzero input.
For `x₀=1` the chiral operator is idempotent. Calling it an orthogonal
projection requires a specified inner product and the corresponding adjoint
identity. A proper incidence hyperplane requires `p ≠ 0`; at `p=0` the
covector kernel is the whole four-dimensional space. Projective statements
also require nonzero point representatives and scale compatibility.

The two matrix coordinate orders must not be silently identified:
`canonicalToCoord` uses `(a,u₀,u₁,u₂,b,v₀,v₁,v₂)`, whereas the older `coordLE`
interface uses `(a,u₀,u₁,u₂,v₀,v₁,v₂,b)`. The determinant theorem's arbitrary-basis
statement handles this comparison; an entrywise matrix comparison requires
the actual change of coordinates.

With the convention `assoc(a,b,w) = (ab)w − a(bw)`, one has
`(L_a L_b − L_(ab))w = −assoc(a,b,w)`. The endomorphism ring's associativity
therefore does not make the original regular map multiplicative. Conversely,
the full Clifford dimension obstruction does not contradict injectivity of
the linear regular map, which is detected by evaluation at the unit.

## 7. Required downstream constructions

The finite algebra supplies concrete operations and compatibility identities.
An RH/GRH application still needs all three of the following constructions:

1. A map from genuine completed L-function or explicit-formula test data to
   the proposed carrier or quotient.
2. Compatibility with the actual explicit formula, functional involution,
   operator domains, and quotient relations.
3. Positivity of the resulting arithmetic form on its full admissible space.

Positivity of a KMS state, a finite Fenchel gap, or a chosen auxiliary metric
does not supply the third assertion without the first two identifications.
No native theorem implementing these arithmetic/analytic steps is claimed by
this extension. This review establishes precedent, not novelty or an RH proof.
