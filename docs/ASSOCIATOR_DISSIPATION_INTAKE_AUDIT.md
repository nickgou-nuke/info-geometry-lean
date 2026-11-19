# Independent audit of the split-octonion repair proposal

**Disposition: REQUEST CHANGES to the attachment's claimed synthesis. Several finite algebraic repairs are sound, but the proposed composition of them is not a proved metriplectic, Gibbs, Landauer, or uniqueness theorem.**

Input: `upload/Pasted text(20261117-091101).txt`, 36,565 bytes, SHA-256 `1fef0d88c605c9d59f6590503b776362454f6b30b5022bbdec25dc1b12960e48`.

Reviewer: `/root/klein_workflow_audit`, independent non-authoring mathematical/source audit. No source implementation, compiler, tests, or build-lock operations were performed for this intake. Root reports that this exact input hash already occurs in PR383 and related work continues in PR384/385. This report audits the mathematical attachment; it does not independently certify those PRs or recommend duplicate implementation.

## Claim disposition

| Proposed repair | Disposition |
|---|---|
| Standard octonion-conjugation scalar sandwich vanishes | True, with the conjugation and parentheses specified |
| Symmetric cross-potential on the two null eigenspaces | True; nondegeneracy additionally uses the nonsingular norm |
| Tensor-factor Spin action preserves the group law | True as a sufficient construction; necessity and uniqueness are false |
| Projected Hilbert Gram is symmetric, positive semidefinite, and kills the energy gradient | True under explicit positive-inner-product and projection hypotheses |
| Full Morrison entropy Casimir on a nondegenerate symplectic space can grow | False |
| All-pairs associator Gram vanishes on quaternion subalgebras | False; its common kernel is the scalar nucleus |
| Compact temperature generators guarantee Gibbs convergence | False |
| Gibbs convergence requires a compact group or one fixed compact subalgebra | False in general; ellipticity can be necessary under stronger spanning hypotheses |
| Nonnegative entropy production proves a heat cost per erased bit | False |
| Mixed-Hessian potential supplies local para-Kähler geometry | True with invertibility, smoothness, and consistent normalization |
| Mixed Ricci components are universally the positive Hessian of log determinant | False without an opposite curvature convention; the conventional formula has a minus sign |
| Strict convexity alone supplies an everywhere invertible Hessian and Cramér–Rao interpretation | False |
| The 15-node graph is acyclic and transitively reduced | Correct by inspection of its stated edges |
| The displayed rank makes it graded; its top proves unique physical synthesis | False |

## 1. The scalar-potential repair is sound, with a missing nondegeneracy argument

Use the standard conjugation on the real split composition algebra, not an unspecified Clifford reversion. Write

\[
B(x,y)=\operatorname{Re}(x\bar y),\qquad q(x)=B(x,x),\qquad
\bar\ell=-\ell,\quad \ell^2=1.
\]

Then the conjugate of \((\psi\ell)\bar\psi\) is \(-\psi(\ell\bar\psi)\). Since \(\bar\psi=2\operatorname{Re}(\psi)-\psi\), alternativity gives \([\psi,\ell,\bar\psi]=0\). Consequently the sandwich is imaginary and its real part is zero. The antisymmetric scalar cross-expression also vanishes because \(B\) is symmetric. These are real algebraic obstructions, not failures of a numerical approximation.

For \(J=L_\ell\), alternativity gives \(J^2=I\), and norm multiplicativity gives \(q(Jx)=-q(x)\). Thus the complementary eigenspaces \(S^\pm\) are totally isotropic. Nonsingularity of the split norm then shows they each have dimension four and that the cross-pairing \(B:S^+\times S^-\to\mathbb R\) is perfect: an element of either summand orthogonal to the other is orthogonal to the entire algebra and hence zero.

Therefore

\[
\Psi_0(u,v)=B(u,v)=\tfrac12q(u+v)
\]

has invertible mixed Hessian. The expansion of \(q(u+v)\) alone does **not** prove that last property; the perfect-pairing argument supplies it. For an explicit nonzero value, take \(u=(1+\ell)/2\) and \(v=(1-\ell)/2\); then \(\Psi_0(u,v)=1/2\).

**Correct contract:** the native split norm, standard conjugation, and fixed imaginary involution give complementary four-dimensional null subspaces, a perfect cross-pairing, and the constant symplectic form \(\omega(x,y)=B(Jx,y)\). No probability, entropy, or transport interpretation follows from these finite identities alone. Composition-algebra and doubling conventions are available in Knarr–Stroppel [O1].

## 2. Full symplectic nondegeneracy conflicts with the stated entropy Casimir axiom

The attachment explicitly requires \(\{F,S\}=0\) for **every** observable \(F\), then later uses only \(\{H,S\}=0\). These are different hypotheses. The former is the Morrison degeneracy condition \(\pi^\sharp dS=0\), as stated in Bloch–Morrison–Ratiu §4.1 [M1].

If \(\pi=\omega^{-1}\) is nondegenerate, then

\[
\pi^\sharp dS=0\Longrightarrow dS=0.
\]

Hence \(S\) is constant on each connected component, its gradient vanishes, and the proposed Gram entropy production is identically zero. A nonconstant entropy with positive production cannot satisfy all of the attachment's simultaneous hypotheses on that symplectic state space.

The weaker hypothesis is not automatic either. With canonical \(\{q,p\}=1\), \(H=p\), \(S=q\) gives \(\{S,H\}=1\). On \(\mathbb R^4\), \(H=p_1\), \(S=q_2\) gives \(\{S,H\}=0\), yet \(\{S,p_2\}=1\), proving that a first integral need not be a Casimir.

**Two honest contracts:**

1. Use a possibly degenerate Poisson tensor, require \(\pi^\sharp dS=0\), and separately require a positive symmetric tensor \(M\) with \(M dH=0\). This is the full Morrison contract.
2. Retain a symplectic Poisson tensor and explicitly assume only \(\{S,H\}=0\). Then the conservation/monotonicity identities are valid, but they do not establish the stronger Casimir axiom. [M1] explicitly distinguishes this weaker compatibility.

A simple nontrivial full-Morrison model is an extended state space \(\mathbb R^2_{q,p}\times\mathbb R_s\) with canonical Poisson tensor on the first factor and zero Poisson tensor on the last. Let \(H=p\), \(S=s\), and \(M=\partial_s\otimes\partial_s\). Then \(\dot H=0\), \(\dot S=1\), and \(S\) is a Casimir. This illustrates why degeneracy or extra thermodynamic variables matter; it is not a physical erasure model.

## 3. The projected Gram construction is valid; its claimed quaternion kernel is not

Let \(E\) be a finite-dimensional real space with a **positive definite auxiliary inner product**, \(h\ne0\), \(P=I-h\otimes h/\|h\|^2\), and arbitrary linear maps \(R_a:E\to E\). For \(\gamma\ge0\), set

\[
M=\gamma P^*\Big(\sum_aR_a^*R_a\Big)P.
\]

Direct inner-product algebra gives

\[
M^*=M,\qquad Mh=0,\qquad
\langle s,Ms\rangle=\gamma\sum_a\|R_aPs\|^2\ge0.
\]

For \(\gamma>0\), strict positivity holds **exactly when** at least one \(R_aPs\ne0\). An informal assertion of leakage or coarse-graining is not this hypothesis. The split norm of signature \((4,4)\) cannot replace the positive auxiliary inner product in this argument. The adjoints and the basis sum also introduce choices; full split-\(G_2\) invariance of this positive construction has not been established.

The all-pairs specialization is where the attachment fails. Fix the Cayley–Dickson convention

\[
(a+b\ell)(c+d\ell)=(ac+\bar d b)+(da+b\bar c)\ell.
\]

It gives the attachment's own identity \([\ell,i\ell,j]=-2k\). Alternation, or direct multiplication, gives

\[
[j,\ell,i\ell]=-2k\ne0,
\]

even though \(j\) belongs to the associative quaternion subalgebra \(\mathbb H\). Associativity of \(\mathbb H\) guarantees zero only when **all three inputs** are in \(\mathbb H\). It says nothing of that kind when the other inputs range over all seven imaginary basis elements.

For the complete family \(R_{ab}v=[v,e_a,e_b]\), trilinearity and the vanishing of associators containing the unit give

\[
\bigcap_{a,b}\ker R_{ab}=\operatorname{Nuc}(\mathbb O_s)=\mathbb R1.
\]

The nucleus fact is stated for arbitrary octonion algebras in Petyt §2 [O2]. Positive definiteness then gives the same kernel for \(B_R=\sum R_{ab}^*R_{ab}\). Adding unit-indexed pairs, as in an all-64-pairs family, adds zero operators and does not change this kernel.

**Concrete dissipative counterexample:** choose the ordinary positive coordinate inner product, \(h=1\), and \(s=j\). Then \(Ps=j\) and the \((\ell,i\ell)\) summand contributes \(4\gamma>0\). The full Gram does not vanish on this quaternion direction.

**Correct contracts:**

- Full family: scalar common kernel, with \(\ker M=\{v:Pv\in\mathbb R1\}\) for \(\gamma>0\). More explicitly this is \(\mathbb Rh+(\mathbb R1\cap h^\perp)\). Consequently the projected rank is six when \(h\perp1\), and seven otherwise; a universal projected rank-seven claim would be wrong.
- Restricted associative family: choose all fixed arguments inside one specified associative subalgebra \(A\), and require the projected vectors to stay in \(A\). Then the corresponding restricted Gram vanishes there.
- Critical points: the normalized projector formula is only defined as written when \(h\ne0\). A piecewise extension at zero need not be smooth. The polynomial alternative \(Q_h=\|h\|^2I-h\otimes h\), \(M_h=Q_h^*B_RQ_h\), is smooth and kills \(h\) everywhere, but is a different normalization and vanishes at \(h=0\).

Squaring this specific associator family is a valid construction, not a uniqueness or necessity theorem for dissipation.

## 4. Compactness alone neither supplies the Gibbs model nor settles integrability

A theorem must first name \((M,\omega)\), its Liouville measure \(\lambda\), a Hamiltonian group action, and a momentum map \(\mu\). Define

\[
Z(\beta)=\int_Me^{-\langle\mu,\beta\rangle}\,d\lambda,
\qquad D=\{\beta:0<Z(\beta)<\infty\}.
\]

Then normalized Gibbs states exist precisely on \(D\). Its interior is the usual geometric-temperature domain. Convexity comes from Hölder's inequality, and equivariance gives adjoint invariance. These definitions and structural restrictions appear in Neeb [G1]; membership in one fixed compact subalgebra is not their definition.

The following are explicit calculations, independent of any classification theorem:

- **Compact generator, divergent partition:** on \(\mathbb C^2\) with its standard symplectic structure, the periodic circle action with weights \((1,-1)\) has Hamiltonian \(H=(|z_1|^2-|z_2|^2)/2\), up to overall sign. For every nonzero real \(b\), \(\int e^{-bH}d\lambda\) diverges in one plane. At \(b=0\), the volume is infinite. This is a nontrivial compact action with an empty convergence domain.
- **Noncompact group, finite partition outside a fixed maximal compact subalgebra:** \(SL(2,\mathbb R)=Sp(2,\mathbb R)\) acts on \(\mathbb R^2\). The Lie algebra element \(A=\begin{psmallmatrix}0&4\\-1/4&0\end{psmallmatrix}\) has Hamiltonian \(H_A=q^2/8+2p^2\). Thus \(Z(A)=2\pi\) for Lebesgue measure. The group is noncompact and \(A\notin\mathfrak{so}(2)\), although \(A\) is conjugate to an elliptic rotation generator. This does not deny ellipticity restrictions under stronger hypotheses; it refutes confinement to one chosen compact subalgebra.
- **The domain need not be a cone:** the complete Hamiltonian \(\mathbb R\)-action generated on \(\mathbb R^2\) by \(H=\log(1+q^2+p^2)\) has \(Z(b)=\pi/(b-1)\) for \(b>1\), and infinity otherwise. Its domain is \((1,\infty)\), not a scaling-invariant cone.
- **No universal noncompact-direction divergence:** on the zero coadjoint orbit, \(Z(\beta)=1\) for every \(\beta\), including nonelliptic directions. The missing hypotheses about the action and orbit are essential.

There is a stronger **conditional warning specific to the proposed full split-\(G_2\) coadjoint model**. Neeb's 2026 preprint, Theorem 4.7 and Remark 4.2, imply that an invariant measure whose support spans \(\mathfrak g^*\) and has any finite Laplace-transform value forces \(\mathfrak g\) to be admissible. A simple admissible algebra is compact or Hermitian. Split \(\mathfrak g_{2(2)}\), whose maximal compact algebra is the centerless \(\mathfrak{so}(4)\), is neither. A nonzero coadjoint orbit of this simple algebra spans its dual. **Under these stated full-orbit/Liouville assumptions**, no Gibbs parameter exists at all, including inside the compact subalgebra. This is a deduction from [G1], not an assertion about every restricted or trivial model.

**Correct contract:** prove finiteness for the specified measure and Hamiltonian (for example by compact phase-space support or quantitative confining tail estimates), then define \(\Omega=\operatorname{int}D\). Restricting the acting group changes the model and still requires an integrability proof. Killing-form signature does not count divergent integration directions.

## 5. Landauer's bound is not a consequence of the Gram identity

The attachment supplies no memory distribution, erased bit, heat observable, reservoir, temperature relation, or physical entropy normalization. Its arbitrary \(S\) can be rescaled, and \(\gamma\) can be rescaled. Neither operation introduces the fixed information quantity \(\ln2\).

A precise example of the missing contract is Reeb–Wolf Theorem 3 [L1]: an initially uncorrelated system and thermal reservoir undergo a joint unitary evolution. With dimensionless von Neumann entropy and \(\beta=(k_BT)^{-1}\), their result is

\[
\beta Q_{\rm bath}
=\big(S(\rho_S)-S(\rho'_S)\big)
 +I(S':R')+D(\rho'_R\Vert\rho_R)
\ge S(\rho_S)-S(\rho'_S).
\]

Resetting one initially unbiased bit to a specified state produces the familiar \(k_BT\ln2\) lower bound under the erasure assumptions. The entropy decrease of the memory is not interchangeable with an arbitrary metriplectic entropy increase. The equality \(Q=T\Delta S\) is not a generic consequence of dissipation; equality requires additional reversible-limit conditions, and finite reservoirs introduce corrections. This whole physical conclusion must remain outside a pure Gram theorem.

## 6. Mixed-Hessian geometry works; Ricci and Legendre conclusions need correction

Let \(\Psi\) be smooth on a coordinate product domain and let \(C_{ij}=\partial_{x_i}\partial_{y_j}\Psi\) be invertible. Fix conventions explicitly:

\[
g=\sum C_{ij}(dx_i\otimes dy_j+dy_j\otimes dx_i),
\quad J(\partial_x)=\partial_x,\quad J(\partial_y)=-\partial_y,
\quad\omega=g(J\cdot,\cdot)=\sum C_{ij}dx_i\wedge dy_j.
\]

The form is exact, \(\omega=d(\sum_j\Psi_{y_j}dy_j)\), and nondegenerate. The metric has signature \((n,n)\), and the constant integrable product structure with the closed form gives the local para-Kähler structure. Pure \(xx\) and \(yy\) **metric components** vanish; the attachment's literal assertion \(dx_i\odot dx_j=0\) is false.

With \(R(X,Y)Z=\nabla_X\nabla_YZ-\nabla_Y\nabla_XZ-\nabla_{[X,Y]}Z\) and the usual Ricci trace, the mixed components are

\[
\operatorname{Ric}_{i\bar j}
=-\partial_{x_i}\partial_{y_j}\log|\det C|.
\]

Bor–Makhmali–Nurowski derive this sign in §2.3.3 [K1]. An opposite curvature convention reverses the sign; a Ricci two-form also requires specifying which argument receives \(J\). The attachment does neither while switching between tensor and form. Also

\[
\det g=(-1)^n(\det C)^2,
\quad\log|\det g|=2\log|\det C|,
\]

so using the determinant of the full metric introduces an additional factor two.

**Explicit sign check:** \(\Psi=xy+x^2y^2/4\) has \(C=1+xy\). Where \(C>0\), the stated convention gives \(\operatorname{Ric}_{xy}=-(1+xy)^{-2}\), not the positive value in the attachment. Adding \(\sum_{i=2}^4x_iy_i\) gives an eight-dimensional example. Setting \(\sigma=\log|\det C|\) defines a function; it does not solve a Monge–Ampère equation with independently prescribed \(\sigma\).

For Legendre duality in \(x\), require a positive definite \(\Psi_{xx}\) and a locally invertible gradient map. The inverse function theorem then gives the local identity \((\Psi^*)_{uu}=(\Psi_{xx})^{-1}\). Strict convexity alone is insufficient: \(\Psi(x,y)=xy+x^4\) is strictly convex in \(x\), has mixed Hessian one, but \(\Psi_{xx}(0,y)=0\).

Adding \(f(x)+h(y)\) changes neither \(C\) nor \(g,\omega,\operatorname{Ric}\), but changes \(\Psi_{xx}\) and the Legendre transform. Therefore the para-Kähler geometry cannot determine a unique such entropy. A Cramér–Rao interpretation additionally needs a statistical model whose Fisher information equals the chosen Hessian, plus regularity and estimator hypotheses. An arbitrary convex dual is not automatically physical entropy or Fisher information.

## 7. Tensor covariance is sufficient, not necessary or unique

For any representation \(\rho:G\to GL(V)\), the map \(\rho_W(g)=\rho(g)\otimes I_U\) is a representation on \(V\otimes U\). This proves the proposed tensor construction's group-action law.

It does not prove necessity. Choose any real linear isomorphism \(T:V\to\mathbb O_s\), where both spaces have dimension eight. Then

\[
\widehat\rho(g)=T\rho(g)T^{-1}
\]

is an associative group action on the underlying octonion vector space. It need not be multiplication by a single octonion. Nonassociativity of the octonion product does not obstruct composition in \(\operatorname{End}_{\mathbb R}(\mathbb O_s)\). Moreover, the attachment never shows that its illustrative \(\ell,i\ell\) are elements of a specified Spin representation. Their associator refutes unrestricted octonion left multiplication as an associative algebra representation, not every possible spin action.

The tensor carrier has real dimension **64**. Its internal eight-dimensional operators must be lifted as \(I_V\otimes R_{ab}\), and gradients/adjoints must use a stated inner product on the actual state space. The internal para-Kähler form alone does not define a nondegenerate form on this 64-dimensional carrier. A direct sum, transported representation, additional multiplicities, or other specified representation may satisfy different stated requirements. No universal property in the attachment selects one model.

## 8. The poset certifies its own ordering, not the mathematics attached to labels

The displayed 15-node graph has increasing level labels, so its transitive closure is acyclic. Inspection of the stated predecessor sets finds no redundant edge. However, its displayed rank is not a rank function for a graded poset: the cover \(K_{TT}\lessdot\mathfrak B\) jumps from two to four, and the saturated chains

\[
\Delta_0<T<K_{TT}<\mathfrak B,
\qquad
\Delta_0<T<\Pi_{ST}<\mathfrak G<\mathfrak B
\]

have different lengths. The graph is also not a lattice: \(\Pi_{ST},\Sigma_{TS}\) have the incomparable minimal upper bounds \(\mathfrak G,\mathfrak T,\mathcal A_0\).

The named top is indeed the unique join of the two named level-five vertices in this constructed poset. That ordinary order-theoretic fact establishes neither existence nor uniqueness of a mathematical/physical realization of their labels. Tensor choices, auxiliary metrics, rates, and potential gauge terms already give many alternatives. Relations such as \(K_{TT}^2=K_{TT}\) or \([\Sigma,\Pi]\ne0\) need actual operators and proofs; labels and arrows do not supply them.

A related overclaim is “CAR simplicity.” The relation \(ab+ba=1\) proves that \(a,b\) generate the unit ideal. It does not prove that the ambient ring is simple. In \(M_2(\mathbb R)\times M_2(\mathbb R)\), the pair \(a=(E_{12},E_{12})\), \(b=(E_{21},E_{21})\) satisfies even the nilpotent CAR relations while the ring has proper nonzero ideals. Complementary CAR projectors also do not imply null subspaces without a compatible bilinear form.

## Bounded theorem sequence suitable for native formalization

1. Native split-composition conjugation and scalar-sandwich obstruction.
2. Involutive anti-isometry, complementary null eigenspaces, and perfect cross-pairing.
3. Positive Hilbert projected Gram: symmetry, positivity, exact energy annihilation, zero/strict-production criterion.
4. Associator specialization with correct restricted-family theorem and full-family scalar-kernel theorem kept distinct.
5. Poisson compatibility theorem with explicit Casimir hypotheses; separate symplectic no-nonconstant-Casimir obstruction.
6. Tensor-extension representation theorem, labelled a construction rather than a necessity result.
7. Mixed-Hessian para-Kähler construction and convention-bound curvature formula, with analytic existence/Legendre assumptions separate.
8. Gibbs normalization under an actual integrability hypothesis; physical Landauer statements require their own statistical-mechanical contract.
9. Finite reachability/cover/join facts for the supplied graph, with no uniqueness inference about its semantic labels.

This sequence describes correct contracts. Existing implementations for the exact input should be reused and audited against their actual accepted snapshots; this review does not call for another duplicate implementation.

## Primary references checked

- **[O1]** Norbert Knarr and Markus J. Stroppel, *Subalgebras of Octonion Algebras*, especially §1.4 composition and doubling conventions. [arXiv PDF](https://arxiv.org/pdf/2303.00335); published DOI [10.1016/j.jalgebra.2024.10.004](https://doi.org/10.1016/j.jalgebra.2024.10.004).
- **[O2]** Harry Petyt, *Derivations of octonion matrix algebras*, §2: arbitrary octonion-algebra setup and scalar nucleus. [Accepted author manuscript](https://research-information.bris.ac.uk/ws/files/205692320/Full_text_PDF_accepted_author_manuscript_.pdf); DOI [10.1080/00927872.2019.1581212](https://doi.org/10.1080/00927872.2019.1581212).
- **[M1]** Anthony M. Bloch, Philip J. Morrison, and Tudor S. Ratiu, *Gradient flows in the normal and Kähler metrics and triple bracket generated metriplectic systems*, §4.1, including the distinction between full degeneracy and weaker Hamiltonian-entropy commutation. [Author-hosted PDF](https://web2.ph.utexas.edu/~morrison/12arXiv1208.6193_morrison.pdf).
- **[G1]** Karl-Hermann Neeb, *A classification of coadjoint orbits carrying Gibbs ensembles*, 2026 preprint, Definition 4.1, Remark 4.2, Theorem 4.7 and §5. [arXiv HTML](https://arxiv.org/html/2601.04934v1).
- **[L1]** David Reeb and Michael M. Wolf, *An improved Landauer Principle with finite-size corrections*, Theorem 3 and §2.1. [arXiv PDF](https://arxiv.org/pdf/1306.4352).
- **[K1]** Gil Bor, Omid Makhmali, and Paweł Nurowski, *Para-Kähler-Einstein 4-manifolds and non-integrable twistor distributions*, §2.3.3, coordinate Ricci calculation and equation (2.29). [Author-hosted published PDF](https://users.fuw.edu.pl/~nurowski/prace/para_kahler_published.pdf).
