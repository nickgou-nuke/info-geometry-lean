# Literature, exact implications, and native owners

Audit date: 2026-11-19. Source base:
`fea96b564201654cd4693008585039a56f66adf3`.
The [formal contract](UNIFIED_OPERATOR_BRIDGES_CONTRACT.md) and
[preserved intake](intake/2026-11-19-unified-architecture-original.txt)
record the initiating claims. This document records mathematical scope;
native build and axiom results belong in the separate validation record.

## What the references establish

The source material identifies genuine mathematical traditions. Connections
between them require explicit carriers, maps, analytic domains, and algebraic
hypotheses. Bibliographic proximity does not establish an identification.
The audit did not establish the claims that every proposed connection is
canonical, that no textbook covers the whole proposal, or that fragmentation
into a particular number of research communities explains the situation.

### 1. Divergence, dual connections, and neutral product geometry

Eguchi's diagonal construction takes derivatives of a regular contrast to
produce a metric and conjugate connections. Jun Zhang's 2014 chapter,
Proposition 6, states the diagonal formulas; its subsequent product
construction distinguishes local nondegeneracy near the diagonal from
additional conditions on the whole product. Its symmetric positive-definite
mixed-matrix condition for a particular Kähler construction must not be
confused with the neutral construction below. [R1]

For a real cross pairing `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ`, the actual map

$$
\Phi_B(u,v)=(u,B(-,v))\in E\oplus E^*
$$

pulls the canonical evaluation metric back to

$$
g_B((u,v),(u',v'))=B(u,v')+B(u',v).
$$

Its nondegeneracy is exactly separation by `B` in both arguments. For
`B(u,v)=u^\mathsf T C v` with a square real matrix, it is equivalent to
`det C ≠ 0`. Kim–McCann's product geometry uses the cross derivative
`C=-D_xD_y c`, with a factor `1/2` in the block-metric normalization; their
condition (A2) is the bijectivity of this actual derivative map. No symmetry
of `C` is required for the symmetric doubled form. [R2]

The polynomial contrast used in this change is an elementary counterexample
constructed for this audit, not a result attributed to those papers:

$$
D(x,y)=s^6-3s^4+3s^2
      =s^2\big((s^2-3/2)^2+3/4\big),\qquad s=x-y.
$$

It is smooth and strictly positive off the diagonal, with vanishing first
derivatives on the diagonal. Nevertheless,

$$
-D_{xy}=6(5s^4-6s^2+1),\qquad
-D_{xy}(x,x)=6,\qquad -D_{xy}(1,0)=0.
$$

Thus diagonal information geometry alone cannot supply global
nondegeneracy on the product. The new Lean construction formalizes the
algebraic pullback and this derivative obstruction. Smooth manifold
connections, closedness of the associated two-form, and global para-Kähler
geometry are outside its theorem statements.

### 2. Weyl gauge and conjugacy

Călin–Matsuzoe–Zhang distinguish ordinary conjugacy, generalized conjugacy,
and semi-conjugacy. Their generalized relation includes the term
`-τ(X) g(Y,Z)`, and their gauge transformation is

$$
(g,\tau)\longmapsto(e^\varphi g,\tau-d\varphi).
$$

Reduction to ordinary conjugacy after conformal change needs the appropriate
local exactness condition. Their source cites Norden's 1976 book; this audit
did not verify the attachment's more specific priority claim about the
1940s–1950s. [R3] No Weyl connection is inferred solely from a statistical
metric or from the word “dual.”

### 3. Jaynes, Souriau, and the Gibbs Hessian

Jaynes's two 1957 papers are genuine primary sources, with Part II addressing
the quantum statistical setting. “Prior Probabilities” (1968) is a separate
work and should not be used interchangeably with those papers. [R4]
Marle's treatment of Souriau gives the Hamiltonian action, momentum map,
Liouville measure, convergence domain, and generalized Gibbs state explicitly.
The derivative formulas for the partition function apply on that domain.
Replacing time translation by a nonabelian symmetry group does not itself
replace classical observables by a noncommutative operator algebra. [R5]

The repository already has a stronger, explicitly operator-valued finite
route for the quantum response. In
`Canonical/NoncommutativeGibbsSecondDerivativeCenteredBridge.lean`,
`realDirectionalHessian_eq_centeredBKMRealCovariance` relates a genuine
directional derivative to centered BKM covariance for self-adjoint finite
operators, with faithful Gibbs normalization. The proof uses the actual
Fréchet exponential derivative and Duhamel integral. It does not require
the observable directions to commute with the Hamiltonian. This later owner
must be inspected before treating older docstrings about a missing BKM
comparison as current debt. This change reuses that source result; it does
not re-prove it or claim a new infinite-dimensional theorem.

### 4. Schur factorization, Berezinian, and Gaussian normalization

Ordered Schur factorization is meaningful over an associative coefficient
ring. The genuine Berezinian additionally belongs to an even automorphism of
a finite free supermodule over a supercommutative algebra. Deligne–Morgan
§1.10 spells out this setting and its determinant quotient. Dropping parity
and supercommutativity changes the claim. [R6]

Two current repository owners already enforce that boundary:

- `Algebra/BlockSchurFactorization.lean` proves the ordered upper–diagonal–lower block identity
  and the ordinary determinant product. Its
  `scalar_schur_ratio_counterexample` uses noncommuting triangular rational
  matrices and proves that the ungraded quotient does not obey unrestricted
  multiplicativity.
- `Canonical/OperatorBerezinianDifferential.lean` proves the exact
  multiplicativity defect of `u * Δ⁻¹`, its necessary-and-sufficient
  commutation condition, conjugation covariance, and ordered right
  logarithmic derivative. These are unit-ratio statements with explicit
  operator order.

For a positive-definite real symmetric bosonic quadratic form and an even
dimensional alternating fermionic form, the normalized Gaussian factors
are respectively a reciprocal square-root determinant and a Pfaffian.
Caracciolo–Sokal–Sportiello Appendix A gives the exact integration order
and normalization. A combined squared partition identity determines an
inverse Berezinian; an unsquared square-root expression requires sign,
orientation, or branch information. [R7]

The existing file `Canonical/GaussianBerezinPfaffianDeterminantBridge.lean`
defines `pfaffian2x2 a = a` and `determinant2x2 a = a * a`; its displayed
identities are definitional. Those declarations alone are not a general
Gaussian integration theorem, regardless of the surrounding synthesis
terminology. No such promotion is made here.

### 5. Twistor and quantum super-Grassmannian scope

Cervantes–Fioresi–Lledó construct the `N=1` chiral case
`G(2|0;4|1)` using quantum minors, with the chiral Minkowski space as a big
cell. Their conclusion explicitly points to the larger superflag
`F(2|0,2|1,4|1)` for the appropriate Minkowski/conformal real form. The cited
paper does not supply an arbitrary-superdimension oscillator construction.
[R8] A real split-Clifford model therefore needs an explicit comparison
map and real-form compatibility proof before identification with that
quantum superspace. This change adds no quantum-supervariety theorem.

### 6. Sylvester, gradings, parafermions, and higher differentials

Sylvester's “A Word on Nonions” is an 1882 paper with an 1883 note. The
inspected original gives the third-order nonion construction and associated
finite phase group. Schwinger's 1960 paper is a separate source for general
unitary operator bases. Patera–Zassenhaus's 1988 paper explicitly concerns
one-dimensional Pauli grading spaces of `gl(n, C)`. A grading and an
epsilon-twisted color bracket are distinct pieces of data. [R9–R11]

The ordinary homogeneous bracket and a color bracket have different
specifications:

$$
[x_a,y_b]=x_a y_b-y_b x_a,\qquad
[x_a,y_b]_\varepsilon=x_a y_b-\varepsilon(a,b)y_b x_a.
$$

An epsilon bracket requires a chosen commutation factor satisfying
`ε(a,b) ε(b,a) = 1` as well as multiplicativity in both arguments. These
conditions and the corresponding epsilon-Jacobi law are explicit in
de Goursac–Masson–Wallet. [R16] In fact, when
`ZX = ωXZ` and `W(a,b) = X^a Z^b`, the product coefficient is `ω^(b*c)`;
choosing the induced factor `ε((a,b),(c,d)) = ω^(b*c-d*a)` makes the
homogeneous epsilon-commutator vanish. Their §3.3 records this color
commutativity for the canonical factor. It is not the ordinary matrix
commutator. An ordered clock/shift multiplication formula by itself
also does not prove linear independence or a native direct-sum grading.
The bounded source review of `Canonical/SylvesterGrading.lean` found the
ordered displacement and braid formulas, without a basis/direct-sum
construction in that owner.

Jaffe–Liu genuinely connect planar para algebras, parafermion Pauli matrices,
Jordan–Wigner transformations, reflection positivity, and a family of
subfactor planar para algebras. Their definitions include planar and Hilbert
space data. An arbitrary sequence of matrix embeddings has not thereby
been identified with Jones's basic construction. [R12]

Kapranov studies `N`-complexes; Dubois-Violette–Kerner impose both a graded
twisted Leibniz rule and the relevant nilpotency law. Their matrix example
provides the precise constructive link. For `N ≥ 2` and a primitive `N`th
root `q` in the scalar coefficient field (`ℂ` in the source), it has the form

$$
\delta(X)=QX-\theta(X)Q,
\quad \theta(Q)=qQ,
\quad \theta^N=1
\quad\Longrightarrow\quad
\delta^N=\operatorname{ad}(Q^N).
$$

Centrality of `Q^N` then gives `δ^N=0`. This does not identify an arbitrary
nilpotent operator with a root of unity. Kapranov's preprint was submitted
in 1996 and explicitly says the text was written in 1991. [R13–R14]

The new scalar-phase theorem retains the full noncommutative algebra and
derives the general power identity from the existing quantum binomial
owner. The separate cubic theorem allows the phase itself to be a
noncentral element of that algebra. It assumes only charge-phase
commutation, fixed phase under the automorphism, charge covariance, and the
cubic cyclotomic equation. The real matrix witness makes the distinction
concrete.

Kac's cited Chapter 8 is titled “Twisted Affine Algebras and Finite Order
Automorphisms.” Its publisher table of contents does not support the
attachment's description of a classification of arbitrary matrix roots of
the identity. [R15]

## Verified references and access scope

The links below are primary papers, author copies, or publisher records.
“Inspected” means the indicated source passage was actually retrieved;
it does not mean every page of the work or every historical priority claim
was checked.

| ID | Source | Inspected scope |
| --- | --- | --- |
| R1 | Jun Zhang, *Divergence Functions and Geometric Structures They Induce on a Manifold* (2014), [author PDF](https://sites.lsa.umich.edu/m3lab/wp-content/uploads/sites/1376/2024/11/2014-Zhang-book-chapter-divergence-geometry.pdf) | Proposition 6 and §§3.1–3.3, especially the diagonal/product and local/global distinctions. Original Eguchi papers were not fully accessible in this audit. |
| R2 | Y.-H. Kim and R. J. McCann, *Continuity, curvature, and the general covariance of optimal transportation*, JEMS **12** (2010), 1009–1040, DOI [10.4171/JEMS/221](https://doi.org/10.4171/JEMS/221), [author PDF](https://www.math.toronto.edu/mccann/papers/product_geometry.pdf) | §2, equation (2.1), Definition 2.2(A2), and the split-signature discussion. The author preprint is dated 2008. |
| R3 | O. Călin, H. Matsuzoe and J. Zhang, *Generalizations of conjugate connections* (2009), [author PDF](https://sites.lsa.umich.edu/m3lab/wp-content/uploads/sites/1376/2024/11/2009-Calin-Matsuzoe-and-Zhang-proceedings.pdf) | Definitions in §1 and gauge transformation (9) in §2; Norden reference is the 1976 book. |
| R4 | E. T. Jaynes, *Information Theory and Statistical Mechanics*, Phys. Rev. **106** (1957), 620–630, [DOI](https://doi.org/10.1103/PhysRev.106.620); Part II, **108** (1957), 171–190, [DOI](https://doi.org/10.1103/PhysRev.108.171) | Publisher metadata; Part II author-archive PDF retrieved. No exhaustive chapter-by-chapter historical audit is claimed. |
| R5 | C.-M. Marle, *From Tools in Symplectic and Poisson Geometry to Souriau's theories of Statistical Mechanics and Thermodynamics*, [arXiv:1608.00103](https://arxiv.org/abs/1608.00103), version 2 (2017) | §§7.1–7.2 on generalized Gibbs states, derivative formulas, and covariance. |
| R6 | P. Deligne and J. W. Morgan, *Notes on Supersymmetry (following Joseph Bernstein)*, in *Quantum Fields and Strings: A Course for Mathematicians* (1999), [paper PDF](https://ncatlab.org/nlab/files/DeligneMorgan-NotesOnSusy.pdf) | §1.10, the supercommutative base, even automorphisms, and formula (1.10.6). |
| R7 | S. Caracciolo, A. D. Sokal and A. Sportiello, *Algebraic/combinatorial proofs of Cayley-type identities for derivatives of determinants and pfaffians*, [arXiv:1105.6270v2](https://arxiv.org/abs/1105.6270v2) | Appendix A, Theorem A.3 and Proposition A.13, including the Berezin integration order. |
| R8 | D. Cervantes, R. Fioresi and M. A. Lledó, *The quantum chiral Minkowski and conformal superspaces*, ATMP **15** (2011), 565–620, [arXiv:1007.4469](https://arxiv.org/abs/1007.4469) | The `N=1` construction, §5.3 and concluding §7, including the real-form superflag boundary. |
| R9 | J. J. Sylvester, *A Word on Nonions* (1882; note 1883), [original collected-paper scan](https://rcin.org.pl/Content/162581/PDF/WA35_189974_11371-3_art-76.pdf) | Four-page original, especially the third-order nonion basis. |
| R10 | J. Schwinger, *Unitary Operator Bases*, PNAS **46** (1960), 570–579, [primary archive](https://pmc.ncbi.nlm.nih.gov/articles/PMC222876/), DOI [10.1073/pnas.46.4.570](https://doi.org/10.1073/pnas.46.4.570) | Primary archive metadata; no historical-priority inference beyond the identified paper. |
| R11 | J. Patera and H. Zassenhaus, *The Pauli matrices in n dimensions and finest gradings of simple Lie algebras of type A(n−1)*, J. Math. Phys. **29** (1988), 665–673, DOI [10.1063/1.528006](https://doi.org/10.1063/1.528006) | Indexed primary-paper abstract and opening definitions. Direct publisher/PDF access was incomplete. |
| R12 | A. Jaffe and Z. Liu, *Planar Para Algebras, Reflection Positivity*, Commun. Math. Phys. **352** (2017), 95–133, [arXiv:1602.02662](https://arxiv.org/abs/1602.02662), DOI [10.1007/s00220-016-2779-4](https://doi.org/10.1007/s00220-016-2779-4) | Definitions, Pauli models and §5 Jordan–Wigner formulas. |
| R13 | M. M. Kapranov, *On the q-analog of homological algebra*, [arXiv:q-alg/9611005](https://arxiv.org/abs/q-alg/9611005) | Author abstract and submission history: 1996 submission, text written 1991. |
| R14 | M. Dubois-Violette and R. Kerner, *Universal q-differential calculus and q-analog of homological algebra*, [arXiv:q-alg/9608026](https://arxiv.org/abs/q-alg/9608026) | Introduction and §2 Example 1, in particular `d^N = ad(e^N)` for the graded matrix construction. |
| R15 | V. G. Kac, *Infinite-Dimensional Lie Algebras*, third edition, [publisher contents](https://www.cambridge.org/core/books/infinitedimensional-lie-algebras/053FE77E6E9B35C56B5AEF7336FE7306) | Chapter 8 title and pagination, 125–144. |
| R16 | A. de Goursac, T. Masson and J.-C. Wallet, *Noncommutative ε-graded connections*, [arXiv:0811.3567v2](https://arxiv.org/abs/0811.3567v2) | Definitions 2.1 and 2.10; §3.3 on graded matrix algebras and the canonical commutation factor. |
| R17 | M. Scheunert, *Generalized Lie algebras*, J. Math. Phys. **20** (1979), 712–720, DOI [10.1063/1.524113](https://doi.org/10.1063/1.524113), [publisher issue](https://pubs.aip.org/aip/jmp/issue/20/4) | Publisher metadata verified; original full text was inaccessible. R16 supplies the inspected definitions used above. |
| R18 | V. F. R. Jones, *Index for subfactors*, Invent. Math. **72** (1983), 1–25, [publisher record](https://link.springer.com/article/10.1007/BF01389127) | Publisher metadata only; original text required subscription access. No arbitrary-matrix-tower identification is attributed to it. |
| R19 | G. 't Hooft, *A property of electric and magnetic flux in non-abelian gauge theories*, Nucl. Phys. B **153** (1979), 141, [author publication list](https://webspace.science.uu.nl/~hooft101/gthpub.html) | Author publication 33; full original was not inspected. No theorem about all proposed Sylvester loops or towers is inferred. |

## Source search and residual work

The source search used actual declaration bodies, related imports, native
instances and selected consumers. A bounded `context_preflight.py` run found
the checked-out DAG, type index, LeanSearch records, manifest, and raw infotree
artifacts absent. No global graph refresh or graph-backed completeness claim
is made. The categorical infrastructure map was used for navigation, followed
by source checks; matrix identities are not promoted into a colimit theorem.

The broad intake also cites Massieu, Koszul, Balian, Barbaresco, Rashevskii,
Norden, Kurose, Manin, Penrose, Ferber, Berezin, Efetov, Rittenberg–Wyler,
Scheunert, Jones, 't Hooft, Abramov–Kerner, Arnold and Yaglom. This document
does not certify every edition, date, priority statement or attributed
cross-connection in that list. In particular, no theorem here identifies a
thermodynamic partition function with Gromov–Witten volume, a generic matrix
tower with a Jones basic construction, or a finite real Clifford model with
the specified quantum super-Grassmannian. Each would need its own precise
comparison theorem.

The current additions concern actual endomorphism powers, full-ring phase
order, canonical bilinear pullbacks, and literal derivatives. They supply
checkable implications that can be reused by later geometric and
thermodynamic constructions.
