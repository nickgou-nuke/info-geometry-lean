# Corrections and remaining mathematical obligations

This is a source and mathematical audit of the frozen `intake.txt`, not a
formalization of all its claims. Implemented theorem types and validation
status are specified in `contract.md`.

The original reference is Narayanan–Neuberger,
[Chiral Determinant as an Overlap of Two Vacua, hep-lat/9307006](https://arxiv.org/abs/hep-lat/9307006).
The transfer, free-eigenvector, and phase formulas match that 37-page paper.
Later primary sources correct parts of its current calculation.

## The current decomposition

For normalized states, native complementary ray operators, and nonzero
`z = ⟨u,v⟩`, direct differentiation gives

\[
\frac{dz}{z}=\underbrace{\langle v,dv\rangle-\langle u,du\rangle}_{b}
 +\underbrace{\frac{\langle(1-P_u)du,v\rangle+
 \langle u,(1-P_v)dv\rangle}{z}}_{j_h}.
\]

[Neuberger, hep-lat/9802033, §2b, Eqs. (2.12)–(2.19)](https://arxiv.org/pdf/hep-lat/9802033)
explicitly corrects the earlier identification: the horizontal contribution
corresponds to the covariant current in the stated overlap construction;
the Berry term is the measure contribution to the consistent current. Its
footnotes correct the earlier Eqs. (3.70) and (3.73). The generic Lean results
therefore use vertical/horizontal terminology.

[Randjbar-Daemi–Strathdee, hep-th/9703092, Eqs. (3)–(5)](https://arxiv.org/pdf/hep-th/9703092)
also separate the phase-independent response from the phase term. Identifying
a local continuum Bardeen–Zumino polynomial requires that field-theory
construction and limiting calculation; the abstract Hilbert identity does not
calculate such a polynomial or its coefficient.

Under differentiable rephasings, direct expansion gives
`b ↦ b + i d(θ_v−θ_u)` and `j_h ↦ j_h`. These transformation laws are additional
targets, not newly checked Lean declarations in this PR. Configuration-space
exterior derivatives, spacetime divergences, and gauge variations must remain
distinct. The quotient is unavailable at `z = 0`; a nonzero chart does not
automatically admit a single global logarithm.

## Ten corrections to the broader narrative

| Intake claim | Correct boundary |
|---|---|
| Inequivalent chiral representations force a rectangular map. | Inequivalence does not imply unequal dimension: the two Weyl representations of `Spin(4)` both have complex dimension two. An equal-dimensional chiral determinant is naturally line-valued until trivializations are chosen. |
| Anomaly cancellation makes the given Berry curvature zero everywhere. | Integrated obstruction, residual curvature, and the chosen measure are separate. A phase change cannot change curvature. See hep-lat/9802033 §3 and the measure curvature in Lüscher's Eq. (3.12). |
| A global smooth phase requires a flat connection. | A smooth trivialization can have nonzero curvature. A parallel trivialization additionally concerns flatness and holonomy; neither supplies locality or gauge equivariance. |
| Excluding regulator zero modes defines the same domain as plaquette admissibility. | Kernel invertibility and a specified plaquette bound are different conditions. A sufficiently strong bound can imply a gap for a specified lattice operator. |
| Near-zero regulator eigenvalues necessarily destroy locality. | An isolated near-zero mode can have a uniformly localized spectral projector and a local one-sided overlap limit. Quantitative hypotheses matter. |
| Index zero guarantees a nonzero vacuum overlap or no zero modes. | Equal occupations can still have orthogonal states; paired Dirac zero modes are not excluded. |
| With `ν=N₋−N₊`, `k` annihilators on the ket require `ν=k`. | They reduce the ket degree to `N₊−k`; a nonzero matrix element requires `ν=−k`. Occupation matching is necessary, not sufficient. |
| A compression determinant computes the overlap for unequal ranks. | The ordinary Slater determinant formula needs a common occupied-frame dimension. The unequal-rank branch must be treated separately. |
| Failure of the displayed eigenvector ratios proves failure of every global frame. | It proves failure of those charts. A global obstruction needs transition data or a characteristic class. A chart zero need not be a spectral crossing. |
| The displayed large-mass limit restores unitarity. | At fixed momentum, `Q²=m²/(|p|²+m²) → 1` and `P*P=|p|²/(|p|²+m²) → 0`. Regulator decoupling is a different statement. |

Two explicit counterexamples clarify the geometry and the rank restriction.
They are direct mathematical calculations, not new Lean theorems here.

On `ℝ²`, the global unit section

\[
u(x,y)=\frac{(1,x+iy)}{\sqrt{1+x^2+y^2}}
\]

has Berry connection and curvature

\[
\alpha=\frac{i(x\,dy-y\,dx)}{1+x^2+y^2},\qquad
F=\frac{2i\,dx\wedge dy}{(1+x^2+y^2)^2}.
\]

Thus the ray bundle is explicitly trivialized while this connection is
nonflat. At the origin, the actual noncommuting tangent matrices `X=σ₁`,
`Y=σ₂` and `P=diag(1,0)` satisfy `tr(P(XY−YX))=2i`.

For the rank issue, take `P₊=diag(1,0)` and `P₋=1` on `ℂ²`. The compression
`P₊P₋P₊` is the identity on `im P₊`, with determinant one. The associated
one- and two-particle exterior states have zero overlap because their degrees
differ. This rules out the unconditional compression formula.

## Analytic and global scope

[Hernández–Jansen–Lüscher, hep-lat/9808010, §§2.1–2.4](https://arxiv.org/pdf/hep-lat/9808010)
derive locality using finite range and controlled spectral bounds, and treat
isolated near-zero modes explicitly. GW alone does not imply locality, absence
of doublers, or the correct continuum limit. Pointwise invertibility of each
finite matrix need not provide bounds uniform in fields or volume.

[Adams, hep-lat/0109019, §3](https://arxiv.org/pdf/hep-lat/0109019)
distinguishes excluded kernel zeros from sufficient plaquette conditions.
Along a continuous gapped finite-dimensional family, occupied ranks are locally
constant. Equal index does not prove that two points lie in the same connected
component. Fixed dimension bounds the possible index; codimension claims need
transversality. A gauge quotient also needs a specified action and regularity.

[Lüscher, hep-lat/9811032, §5 and §§9.2–9.3](https://arxiv.org/pdf/hep-lat/9811032)
provides a constructive nonperturbative U(1) result with explicit charge,
admissibility, and finite-volume conditions. Triviality and zero integrated
flux are distinct from pointwise zero curvature.
[Lüscher, hep-lat/0006014](https://arxiv.org/pdf/hep-lat/0006014)
treats general compact gauge groups to all orders of perturbation theory.
Neither result is the unrestricted nonperturbative iff asserted in the intake.

[Bär–Campos, hep-lat/0001025, §§2–4](https://arxiv.org/pdf/hep-lat/0001025)
state smoothness, locality, anomalous conservation, and Wilson-line/twist
matching for the measure. The SU(2) obstruction concerns a specified loop and
representation. The reconstruction condition is not that every natural Berry
holonomy equals one.

[Freed, Classical Chern-Simons Theory, Part 2, §1.1](https://web.ma.utexas.edu/users/dafr/cs2.pdf)
distinguishes the integral `H²(M;ℤ)` class of an ordinary complex line bundle
from its differential information. The intake's blanket `H²(M,U(1))` notation
needs a specified cohomology theory and coefficient sheaf.

## Ordered algebra retained for future owners

For finite-dimensional Hermitian positive-definite `B` and arbitrary `C`,
the transfer formula retains the order of every factor:

\[
M=\begin{pmatrix}1&C\\0&1\end{pmatrix},\qquad
T=M^*\operatorname{diag}(B^{-1},B)M.
\]

It gives positivity and determinant one without assuming `BC=CB`.
With the principal Hermitian logarithm, `tr(log T)=0`; this does not imply
invertibility of `log T` or equal positive/negative multiplicities. Infinite
propagation requires an actual convergence theorem, spectral isolation, the
correct `exp(−H)` sign, and nonzero boundary projections.

The new GW owner starts from two actual involution laws, consistent with the
algebraic relation studied in
[Neuberger, hep-lat/9801031](https://arxiv.org/abs/hep-lat/9801031).
It does not supply the omitted spectral-sign construction. The present PR
also leaves transfer positivity, Fock selection, determinant gluing, global
anomalies, locality, and continuum traces as explicit obligations. A unique
terminal node in a proposed causal poset proves none of these consequences.
