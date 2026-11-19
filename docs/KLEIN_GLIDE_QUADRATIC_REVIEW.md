# Independent mathematical audit: Klein relation and central quadratic algebra

Intake: `docs/sources/klein-glide-intake-2026-11-16.txt`.
Independent baseline: main commit 08c34e03f610b452e03422037949196dc7d92d6d.
The mathematical claim ledger was prepared by an independent reviewer who did not author the Lean modules. Kernel validation and publication are separate from this semantic review; their actual results are recorded in the pull request and workflow evidence.

## 1. Fix the objects before interpreting the claims

Write
\[
\Gamma=\langle U,G\mid GUG^{-1}=U^{-1}\rangle,\qquad
T=G^2,\quad S=U+U^{-1},\quad Y=U-U^{-1}.
\]

Three distinct objects occur:

1. The algebraic group ring \(\mathcal A=\mathbb C[\Gamma]\), equivalently a skew Laurent ring \(\mathbb C[U^{\pm1}][G^{\pm1};\sigma]\), with \(\sigma(U)=U^{-1}\).
2. Its algebraic central specializations and splitting-base extensions.
3. The group C*-completion \(C^*(\Gamma)\).

These are also different from the commutative function algebra of the topological Klein bottle. Hadfield's Sections 6–7 identify the group C*-algebra with \(C(\mathbb T)\rtimes_\sigma\mathbb Z\), with full and reduced completions equal, and exhibit a quotient onto the infinite-dihedral group C*-algebra [S1]. The rank-four and algebraic Brauer statements below concern the first object, not automatically the third.

## 2. Claim ledger

| ID | Intake assertion | Correct contract or boundary |
|---|---|---|
| K01 | The glide relation makes \(G^2\) central. | It commutes with \(U,G\), hence with their generated algebra. Centrality in an arbitrary larger ambient algebra does not follow. |
| K02 | The glide must be non-involutive. | The abstract Klein group has \(G^2\ne1\); a representation satisfying the relation may have \(G^2=1\). A nontrivial square requires an additional hypothesis. |
| K03 | \([G,U]=0\) iff \(U=\pm1\). | The exact general equivalence is \([G,U]=0\iff U^2=1\). The unitary matrix \(\operatorname{diag}(1,-1)\) is neither scalar sign. |
| K04 | The C*-center is \(\mathbb C[T^{\pm1},S]\). | This is the algebraic group-ring center. Its C*-analogue is the continuous-function algebra \(C(\mathbb T\times[-2,2])\), with \(T\) unitary and \(S\) self-adjoint. |
| K05 | The algebra is quaternion-like of rank two. | Rank two over \(\mathbb C[U^{\pm1},T^{\pm1}]\); rank four over its center \(\mathbb C[S,T^{\pm1}]\). |
| K06 | Noncommutativity destroys scalar polynomial evaluation. | Central-coefficient evaluation is an algebra homomorphism into a possibly noncommutative algebra. Arbitrary coefficient evaluation is multiplicative exactly when the evaluation point commutes with the coefficient image. |
| K07 | The displayed two factorizations hold in the same skew polynomial convention. | False: the central-indeterminate and inversion-skew formulas differ. See the exact table below. |
| K08 | Nonzero nilpotents are roots of \(X^3-X\). | False in every ring: a nilpotent tripotent is zero. Nonzero square-zero matrices solve \(X^2=0\), not \(X^3-X=0\). |
| K09 | Galois automorphisms swap \(+1,-1\). | Every unital ring automorphism fixes \(0,1,-1\). A complex algebra automorphism also fixes scalar \(i,-i\). Inversion swaps a noncentral \(U,-U\) only under \(U^2=-1\). |
| K10 | The Klein group C*-algebra is simple. | False: \(U\mapsto\pm1,\ G\mapsto z\), \(z\in\mathbb T\), gives characters. The algebra has proper nonzero quotients. |
| K11 | Nilpotents are intrinsic to the algebraic group ring. | False: the skew Laurent ring is a domain. Nilpotents can occur in split fibers, scalar extensions, and the C*-completion. |
| K12 | Off-branch fibers are matrix algebras. | True for closed complex fibers \(S=s,T=t\ne0\), \(s^2\ne4\), and after an explicit splitting-base extension. The generic fiber over \(\mathbb C(S,T)\) is a division quaternion algebra. |
| K13 | The branch fiber is whatever the specialized 2×2 representation displays. | False: the algebraic branch fiber still has dimension four; the displayed representation has a two-dimensional square-zero kernel and two-dimensional image. |
| K14 | Killing a nonzero nilpotent necessarily collapses the ring. | True in a simple matrix algebra, and for a specified CAR pair by its anticommutator identity. False for arbitrary noncommutative rings and for the whole Klein C*-algebra. |
| K15 | Reduced characteristic polynomial plus Brauer class classifies conjugacy. | False: \(0\) and \(E_{12}\) in \(M_2(\mathbb C)\) have the same characteristic polynomial \(X^2\) and ambient Brauer class, but are not conjugate. Skolem–Noether has additional simple-subalgebra hypotheses [S2]. |
| K16 | The Brauer obstruction is an unconditional permanent obstruction to diagonalization. | An algebraic degree-two Brauer obstruction can be proved over the specified generic center; it disappears after a splitting extension. It does not classify diagonalizability of every element or automatically identify a topological orientation class. |

## 3. Elementary consequences of the relation

Let \(A\) be a ring and \(u,g\in A^\times\) satisfy \(gu=u^{-1}g\). No commutativity, star structure, or characteristic restriction is needed for
\[
gu^{-1}=ug,\qquad
g^2u=ug^2,\qquad
g(u+u^{-1})=(u+u^{-1})g,
\]
\[
g(u-u^{-1})=-(u-u^{-1})g,\qquad
(u-u^{-1})^2=(u+u^{-1})^2-4,
\]
\[
(gY)^2=-g^2Y^2,\qquad
[g,u]=(u^{-1}-u)g,\qquad
[g,u]=0\ \Longleftrightarrow\ u^2=1.
\]

An appropriate generated-subalgebra theorem can promote the commuting statements to centrality. The relation alone does not imply \(g^2\ne1\), or establish a topological covering space.

If \(2\) is invertible and \(P=(1+g)/2\), then
\[
P^2-P=(g^2-1)/4.
\]
This is an exact defect identity; its nonvanishing needs \(g^2\ne1\). In a C*-setting, \(P\) is not automatically self-adjoint.

The topological double-cover statement is instead: the subgroup generated by \(U,G^2\) is an index-two copy of \(\mathbb Z^2\). The orientation double cover is a torus [S6]. No statement about arbitrary gradings of operator algebras follows; geometric spinor chirality requires its own specified bundle and descent hypotheses.

## 4. Polynomial evaluation and exact residues

For a homomorphism \(f:R\to A\), ordinary polynomial evaluation at \(x\in A\) satisfies
\[
\bigl(\forall p,q,\ \operatorname{ev}(pq)=\operatorname{ev}(p)\operatorname{ev}(q)\bigr)
\iff \forall r,\ f(r)x=xf(r).
\]
Necessity follows by using \(p=X,q=C(r)\) and \(XC(r)=C(r)X\). Sufficiency is the usual coefficient calculation. Native mathlib already provides Polynomial.eval₂_mul_noncomm and Polynomial.eval₂RingHom'; Polynomial.aeval is an algebra homomorphism even when its target is only a Semiring.

For a unit \(u\), keep these conventions separate:

| Product | Central indeterminate \(X\) | Inversion-skew indeterminate \(Xa=\sigma(a)X,\ \sigma(u)=u^{-1}\) |
|---|---|---|
| \((X-u)(X-u^{-1})\) | \(X^2-(u+u^{-1})X+1\) | \(X^2-2uX+1\) |
| \((X-u)(X+u^{-1})\) | \(X^2+(u^{-1}-u)X-1\) | \(X^2-1\) |
| \((X-u)(X+u)\) | \(X^2-u^2\) | \(X^2-u^2+(u^{-1}-u)X\) |

For actual ring elements, without any commutation hypothesis, the useful exact defects are
\[
(x-u)(x+u^{-1})-(x^2-1)=xu^{-1}-ux,
\]
\[
(x-u)(x-u^{-1})-\{x^2-(u+u^{-1})x+1\}
=u^{-1}x-xu^{-1},
\]
\[
(x-u)(x+u)-(x^2-1)=xu-ux+1-u^2.
\]
Thus the intake's residual has both an orientation/sign issue and a missing \(1-u^2\) term for its stated product.

In every ring,
\[
x(x-1)(x+1)=x^3-x.
\]
Many matrix roots do not indicate a failed evaluation homomorphism. For example, the matrices \(\begin{pmatrix}a&b\\c&-a\end{pmatrix}\) square to \((a^2+bc)I\) over a commutative coefficient ring. Over \(\mathbb C\), a matrix satisfying \(x^3=x\) is diagonalizable because its minimal polynomial divides a square-free polynomial. Its nilpotent part is zero.

An infinite collection of literal factorizations is not proof of infinitely many nonconjugate factorizations or of a particular noncommutative unique-factorization failure.

## 5. Native rank-four model and matrix splitting

Use the existing carrier
\[
Q(R;s,t)=\mathrm{QuaternionAlgebra}\ R\ (-1)\ s\ t.
\]
For every commutative ring \(R\), it has basis \(1,U,G,UG\) and relations
\[
U^2=sU-1,\qquad G^2=t,\qquad GU=(s-U)G.
\]
The element \(U\) has inverse \(s-U\). When \(t\) is a unit, \(G\) has inverse \(t^{-1}G\). This provides the Klein relation without division by two.

Mathlib supplies QuaternionAlgebra.basisOneIJK, linearEquivTuple, finrank_eq_four, and QuaternionAlgebra.Basis.liftHom/lift. A lift into another \(R\)-algebra should assume the actual three multiplication relations with central scalar parameters, not assume its desired conclusion.

For \(q=a+bU+cG+dUG\), define
\[
\operatorname{tr}(q)=2a+sb,\quad
\operatorname{n}(q)=a^2+sab+b^2-t(c^2+scd+d^2).
\]
Then the substantive central quadratic identity is
\[
q^2-\operatorname{tr}(q)q+\operatorname{n}(q)1=0.
\]
The native quaternion conjugation gives \(q+\bar q=\operatorname{tr}(q)\) and \(q\bar q=\operatorname{n}(q)\). It is not the group/C*-adjoint: it fixes coefficient scalars and sends \(G\) to \(-G\), whereas the group adjoint sends \(G\) to \(t^{-1}G\), \(t\) to \(t^{-1}\), and conjugates complex coefficients.

Over a field \(k\), choose units \(u,t\) and set \(s=u+u^{-1}\). The native lift
\[
\rho(U)=\begin{pmatrix}u&0\\0&u^{-1}\end{pmatrix},\qquad
\rho(G)=\begin{pmatrix}0&t\\1&0\end{pmatrix}
\]
satisfies
\[
\rho(q)=
\begin{pmatrix}
a+bu&t(c+du)\\c+du^{-1}&a+bu^{-1}
\end{pmatrix}.
\]
If \(u-u^{-1}\ne0\), solving two two-variable linear systems proves an actual algebra equivalence \(Q(k;s,t)\simeq M_2(k)\). This condition suffices even in characteristic two. The construction has already chosen a splitting root \(u\); it does not assert that the symbolic universal algebra is split over its original center.

If \(u^2=1\), let \(\eta=U-u1\). Its coordinates are \((-u,1,0,0)\), so
\[
\eta\ne0,\quad \eta^2=0,\quad \rho(\eta)=0.
\]
As an additional mathematical calculation, not formalized by the current Lean owners, \(\ker\rho=\operatorname{span}_k\{\eta,\eta G\}\) is two-dimensional and square-zero, and the image is the two-dimensional algebra \(k[G]/(G^2-t)\). The Lean boundary established here is the explicit nonzero square-zero kernel element and noninjectivity; it does not assert the full kernel or image classification. Identifying that image with \(k\times k\) additionally needs characteristic different from two and a square root of \(t\); both hold over \(\mathbb C\). The whole branch carrier retains dimension four.

## 6. Center, domain, branch fibers, and Brauer boundary

For the algebraic group ring, normal forms give
\[
B=\mathbb C[U^{\pm1},T^{\pm1}],\qquad
\mathcal A=B\oplus BG,\qquad
Z(\mathcal A)=B^\sigma=\mathbb C[S,T^{\pm1}]=R.
\]
Indeed an odd coefficient commuting with \(U\) must vanish because \(B\) is a domain and \(U-U^{-1}\ne0\); the remaining coefficient must be invariant under inversion. The invariant Laurent polynomials are polynomials in \(S\). The quadratic equation for \(U\) then gives the rank-four presentation above.

A leading-\(G\)-exponent argument in the skew Laurent ring proves that \(\mathcal A\) is a domain. Consequently it has no nonzero nilpotents. Localizing its central domain to \(F=\mathbb C(S,T)\) gives a four-dimensional domain over a field, hence a division algebra. With \(Y=2U-S\),
\[
\mathcal A\otimes_R F \cong (S^2-4,T)_F.
\]
This is an algebraic deduction, not a claim that the current Lean scope has proved the group-ring identification or division property.

Let \(\Delta=S^2-4\). After inverting \(\Delta\), the rank-two extension adjoining \(U\) is étale and the displayed matrix map splits the rank-four algebra after that extension. This proves the Azumaya locus is \(\Delta\ne0\). At \(S=\pm2,T=t\ne0\), the nonzero square-zero radical described above obstructs simplicity. “Azumaya” means étale locally a matrix algebra, not a globally simple ring [S3].

There is a genuine nonzero algebraic Brauer class on that open center, of order two: its generic quaternion is division; alternatively the residue of \((\Delta,T)\) at \(S=2\) is the nonsquare class of \(T\) in \(\mathbb C(T)^\times/\mathbb C(T)^{\times2}\), using the standard residue formula [S5]. Degree two gives two-torsion [S3]. These facts require the specified independent central parameters. They do not transfer to every numerical specialization or every analytic completion.

For the C*-completion, central fibers at \(|s|<2,\ t\in\mathbb T\) are \(M_2(\mathbb C)\). At \(s=\pm2\), unitarity implies \(U=\pm1\), since \((U\mp1)^*(U\mp1)=0\), and the central fiber is \(\mathbb C\oplus\mathbb C\). The algebraic branch radical disappears in the C*-quotient. On the interior cylinder one can choose the upper-half-circle root \(u(s)\) continuously and use the displayed matrices to trivialize the matrix bundle. Thus the algebraic nonsplit class must not be described as an automatic nontrivial Brauer obstruction of that interior C*-bundle.

## 7. Galois, conjugacy, and quotient corrections

Inversion defines a quadratic Galois field extension \(\mathbb C(U,T)/\mathbb C(S,T)\); over rings it is a finite étale double cover only away from \(\Delta=0\). Conjugation by \(G\) implements it on \(B\). On the whole crossed algebra, the fixed algebra is larger than the center: when two is invertible,
\[
\mathcal A^{\operatorname{Ad}G}=R\oplus RG,\qquad
\mathcal A^{-\operatorname{Ad}G}=RY\oplus RYG.
\]
Thus “the fixed part is the center” requires restricting the action to the orientable commutative subalgebra.

Skolem–Noether concerns embeddings of a simple algebra into a finite central simple algebra [S2]. It does not make the nilpotent cone a single orbit or make reduced characteristic data a complete invariant. The zero and nonzero nilpotent orbits already differ in \(M_2(\mathbb C)\).

For anticommuting involutions \(A,B\), put \(J=AB\). When two is invertible,
\[
J^2=-1,\quad N_\pm=(B\pm J)/2,\quad N_\pm^2=0,
\]
\[
N_+N_-=(1+A)/2,\quad N_-N_+=(1-A)/2.
\]
Therefore a unital quotient killing even one \(N_\pm\) is trivial, by \(N_+N_-+N_-N_+=1\). This proof needs that actual CAR identity; it does not need an unproved simplicity label.

The general collapse assertion is false. The map
\[
M_2(k[\epsilon]/(\epsilon^2))\longrightarrow M_2(k)
\]
is a proper nonzero quotient killing the nonzero square-zero element \(\epsilon E_{12}\). A character of the Klein C*-algebra kills every nilpotent and still sends \(1\) to \(1\). Peirce compression is also not generally an algebra quotient: \(x\mapsto pxp\) needs a separate multiplicativity condition.

## 8. Recommended theorem dependency order

1. Existing unit-valued Klein relation; inversion transport, square commutation, symmetric and antisymmetric identities.
2. Exact polynomial evaluation multiplicativity criterion and the three ordered-product defects.
3. Native Q(R;s,t), canonical unit generators, native universal lift, central trace/norm identity.
4. Matrix lift of that same carrier; explicit splitting equivalence under \(u-u^{-1}\ne0\).
5. Branch witness \(\eta\ne0,\eta^2=0,\rho(\eta)=0\), keeping the rank-four source separate from its rank-two image.
6. Nilpotent tripotent vanishing, CAR quotient obstruction, and a proper quotient countermodel.
7. Only as separately proved extensions: full group-ring equivalence and center, generic division/Brauer class, algebraic Azumaya locus, analytic completion/fibers, spinor descent, or topology.

Steps 1–6 form a substantive coherent native-mathlib target without pretending to have formalized step 7.

## 9. Existing-owner import review

`Canonical.ProjectiveUnitary6` replaces its blanket `Mathlib` import with
explicit imports for complex scalars, unitary groups, subgroup centers, and
group quotients. `Canonical.KleinPresentedGroup` explicitly imports
`Mathlib.GroupTheory.FreeGroup.Basic`. Both retain `FiniteSpinAlgebra` and its
tactic imports. An independent comparison against the baseline confirmed that
all declarations and proof bodies in these two owners are byte-identical;
only imports and standard file headers changed.

A bounded reverse-import source review found 58 affected existing modules,
including the two owners and aggregate/audit entrypoints. Of these, 35 retain
another transitive blanket `Mathlib` import and 23 have a narrowed import
closure. There are 19 external direct consumers. The new quaternion owners
were not counted in this existing-module inventory.

The review traced sensitive uses of `ZMod`, integer powers, `Real.pi`, matrix
Kronecker products, homology constructions, `FreeGroup.ext_hom`, and
`QuotientGroup.mk'_surjective` to retained or explicit imports. It found no
additional consumer import requiring repair. This is source review, not a
compilation certificate for all 58 modules: narrowing an import can also
change the available simplification and typeclass environment. The focused
kernel certificate covers the six changed owners and their seven-module
repository dependency closure; downstream consumer validation must be
reported separately.

The publication workflow now requires a separate fresh compilation of all
23 existing modules whose closure becomes narrow, including their 34-module
repository dependency closure. It fetches native Mathlib artifacts for the
union of the six-owner and consumer closures, verifies exact consumer coverage
and source hashes, and uploads a separate compatibility report. This consumer
run uses `--skip-audit`; it checks elaboration under the narrower imports and
does not certify every consumer's axiom footprint. The six changed owners
still receive the full recursive axiom audit and must have zero compiler
warnings. Workflow configuration is not an observed successful CI run; the
publication record reports the actual result.

The source semantic gate reports six advisory short-proof findings: the four
unit-coordinate readback lemmas, `eval₂_X_mul_C_defect`, and
`matrixEquiv_apply`. These are direct definitional or elementary readbacks of
the actual constructions, not replacements for the substantive representation,
quadratic, inverse-map, or quotient theorems. They were reviewed at their
declared types. A source-screening pass is separate from compiler warnings and
the recursive axiom audit.

## Primary sources

- [S1] Tom Hadfield, “K-homology of certain group C*-algebras,” Sections 6–7. Exact group relation, amenability/full-reduced equality, crossed product, and infinite-dihedral quotient. https://arxiv.org/pdf/math/0201094
- [S2] Stacks Project, Theorem 11.6.1, tag 074Q. Exact hypotheses and conclusion of Skolem–Noether. https://stacks.math.columbia.edu/tag/074Q
- [S3] Stacks Project, Section 59.62, tag 0A2J. Definition of Azumaya and Lemma 59.62.2 on degree-torsion in the Brauer group. https://stacks.math.columbia.edu/tag/0A2J
- [S4] John Voight, Quaternion Algebras, Chapter 5, Main Theorem 5.4.4 and Lemma 5.4.7. Split/division dichotomy, norm criterion, quadratic splitting fields. https://link.springer.com/chapter/10.1007/978-3-030-56694-4_5
- [S5] Jean-Louis Colliot-Thélène and Alexei N. Skorobogatov, The Brauer–Grothendieck group, author-hosted 2019 manuscript, Section 1.4, formula (1.16). Residue of a quaternion symbol. https://www.imo.universite-paris-saclay.fr/~jean-louis.colliot-thelene/BGgroup_book.pdf
- [S6] Larsen Louder and Michael Magee, “Strongly convergent unitary representations of limit groups,” proof of Proposition 1.3. Orientation double cover of the Klein bottle is a torus. https://arxiv.org/pdf/2210.08953

Pinned native-source checks were read from Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`: Mathlib/Algebra/Quaternion.lean, QuaternionBasis.lean, Polynomial/AlgebraMap.lean, Polynomial/Eval/Defs.lean, and Algebra/Azumaya/Defs.lean and Matrix.lean. The analysis above distinguishes direct calculations from external structural facts and from results that still require a Lean implementation.
