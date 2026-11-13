# Graded Clifford unrolling: independent source-semantic audit

## Provenance, role, and acceptance boundary

This report audits the exact supplied attachment, not a reconstructed or completed
version of its argument. It records mathematical source interpretation, necessary
hypotheses, counterexamples, and a recommended verification scope. It does not
constitute Lean kernel acceptance.

- Original source: /workspace/scratch/9009f3c86480/upload/Pasted text(20261113-100758).txt
- Frozen, byte-identical source: [source-intake.txt](sandbox:/workspace/scratch/9009f3c86480/candidates/graded_unroll/audit/source-intake.txt)
- Length: **24,406 bytes**, **136 lines**, no trailing newline.
- SHA-256: **f21693468fc1ff3ff5ed07361d18f0f65c8461a090ac2ce8c6d7f480f1ce17c4**
- Reviewer: /root/graded_unroll_intake.
- Role: independent source-semantic audit; no mathematical owner authorship or
  repairs, no Lean/Lake builds or tests, no GitHub writes.
- Integration instruction supplied by the parent: prepare a separate extension
  from stable PR #338 / ce34; leave PR #354 untouched. This instruction is
  provenance supplied by the parent, not an independently checked Git revision.

The source ends in Deduction D2, line 136, at the following exact fragment:

~~~text
*Proof:* Under matrix transposition $I^* = I,\; K^* = K,\; \eta^* = \eta,\; \Omega^* = -\Omega$, we have $(a_r K^{q_r^{\mathrm{tot}}})^* = K^{q_r^{\mathrm{tot}}} a_r
~~~

The source does not contain a completed D2 proof or any later deductions. The
correct star formula is stated earlier in J4; its mathematical assessment below
is an independent audit, not an attribution of a missing proof to the attachment.

The source mixes definitions, valid algebraic identities, conditional claims,
false extrapolations, and interpretive language. Labels such as “bosonization,”
“entanglement,” “irreversible chirality,” and “necessary tripotent transition” must
not silently strengthen the actual carrier and algebraic result.

## Executive finding

The attachment contains a sound **graded tensor untwisting construction**. Its
downstream claims need several substantial corrections:

1. The asserted exponential projector-square formula fails already at n = 3.
2. Axiom IV's two even TT boundaries represent only total-even tensors.
3. Anticommutation on an odd-dimensional real carrier forces singularity of the
   swapped operator; it does not force tripotence.
4. An odd external matrix size does not prevent further Clifford doubling inside
   an arbitrary coefficient algebra.
5. The integral lattice index of the chosen tensor quartet is not 4^n.

All positive statements below are semantic contracts or direct mathematical
derivations. None is labeled kernel-verified by this auditor.

## Source-linked claim ledger

Line numbers refer to the byte-frozen source linked above; repeated narrative
claims are mapped to their formal-looking J/D labels as well.

| Source anchor | Claim | Audit classification | Canonical boundary |
|---|---|---|---|
| I line 8; II line 25; J2–J3 lines 99–100; D1 lines 128–133 | Right-tail matrix/graded-tensor equivalence | Valid under explicit algebraic hypotheses | A linear involution between two multiplication structures and an algebra equivalence between those structures |
| I line 14; III line 54; J0 line 97; Axiom I line 113; D1 lines 130–133 | Arbitrary graded terminal B | Valid | B needs supplied grading, not an inner implementer |
| I line 12; IV lines 75–79; J2 line 99; D1 line 133 | Left placement with unchanged right tails | Valid counterexample, overstated interpretation | Exact multiplicativity defect 4η ⊗ η; correct left-head convention is different and needs terminal data if B is graded |
| I line 14; IV lines 76–79; J4 line 101; D2 lines 135–136 | Sign-twisted star | Conditional, with a partial source proof | Even factor stars and K* = K; explicitly distinguish transported transpose from native Clifford star |
| I line 13; IV lines 68–73; J5 line 102 | Exponential projector-square formula | Countermodel found | n = 2 works; n = 3 refutes the universal formula |
| IV line 73 | Pure graded tensor idempotent iff all factors even | Countermodel found | Even idempotent factors suffice; necessity fails for 1 ⊗ P₀ |
| III line 47; IV line 73 | Even Morita corner | Concrete corner statement valid | P M₂(B) P ≅ B is distinct from an unconstructed global categorical Morita statement |
| III lines 55–59; J6 line 103 | Factor-two rank comparison | Valid after defining rank | Underlying real cut rank; homogeneous total-parity tensors preserve rank exactly |
| Axiom IV line 122 | Homogeneous graded TT with even boundaries | Definition restricts the carrier | Only total-even tensors are represented |
| I line 15; III line 55; IV lines 81–84; J6 line 103 | Local core conversion and graded multiplication | Conditional | Bond parity must match actual right-tail parity; graded terminal B needs a final local twist |
| II line 34; J7 line 104 | Operator-sink bound | Valid with dimensional qualifications | Finite dim B for the two-sided finite bound; always r_k ≤ 4^k |
| I line 16; II line 35; IV line 87; J8 line 105 | Odd dimension stops a real Clifford pair | Valid for a finite real carrier | Invertible anticommuting pair forces even real dimension |
| III line 61; IV line 87; J8 line 105 | Odd core forces S³ = S | Countermodel found | Tripotence must be an independent hypothesis |
| I line 16; II line 35; J8 line 105 | Odd r makes M_r(B) irreducible | Countermodel found | Fails for B = M₂(ℝ), including r = 3 |
| I line 16 | Integral reconstruction index 4^n | Countermodel found | Quartet tensor lattice index is 4^(n·4^(n−1)) |
| II line 38; III line 53; J2/J9 | Global categorical bosonization and necessary synthesis | Not established | An inner-grading untwisting map does not trivialize the entire super braiding |

## 1. Prioritized canonical contract

| Priority | Component | Correct contract |
|---|---|---|
| First | J0, J1, J2, J3, D1 | Right-tail algebra equivalence for arbitrary graded terminal B, using an even inner implementer in each nonterminal factor |
| First | J4, D2 | Explicitly transported parity-compatible star; mixed-sign transpose conventions declared |
| First | Wrong-placement example | Preserve the exact nonmultiplicativity defect 4η ⊗ η |
| First | J5 | Preserve n = 2 half-square identity and refute universal scaling at n = 3 |
| Second | J6 | Underlying real cut-rank inequalities from a controlled-parity involution; separate homogeneous TT boundary claims |
| Second | J7 | Scalar-core/operator-sink rank bounds with finite-dimensional hypotheses stated |
| Second | J8 | Finite real parity obstruction, followed only by a conditional tripotent consequence |
| Separate correction | Integral claim | Correct the lattice index and distinguish it from denominators |
| Exclude from inferred theorems | Categorical/physical interpretations | No irreversible chirality, universal symmetry trivialization, or forced KKT transition follows from these identities |

## 2. Main right-tail untwisting

The concrete frame is

\[
\eta=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
\Omega=\begin{pmatrix}0&1\\-1&0\end{pmatrix},\qquad
K=\eta\Omega=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
\]

Its identities are

\[
\eta^2=K^2=I,\quad \Omega^2=-I,\quad
|I|=|K|=0,\quad |\eta|=|\Omega|=1,
\]

\[
Ka=(-1)^{|a|}aK.
\]

Right multiplication by K swaps I with K and η with Ω, with no sign:

\[
IK=K,\quad KK=I,\quad \eta K=\Omega,\quad \Omega K=\eta.
\]

For homogeneous factors set

\[
q_r=|b|+\sum_{s>r}|a_s|\pmod2
\]

and

\[
\rho_n^B(a_1\widehat\otimes\cdots\widehat\otimes a_n
 \widehat\otimes b)
=
(a_1K^{q_1})\otimes\cdots\otimes(a_nK^{q_n})\otimes b.
\]

Moving K past the factors of a second homogeneous tensor gives the exponent

\[
\sum_rq_r|c_r|
=|b|\sum_r|c_r|+\sum_{r<s}|a_s||c_r|\pmod2,
\]

which is the full graded-product crossing sign. This establishes the correct
multiplicativity contract.

Required data:

- A unital associative real algebra B with a genuine direct grading B₀ ⊕ B₁.
- Even involutive grading implementers K_r in each nonterminal factor.
- K_r a = (−1)^|a| a K_r on homogeneous elements.

No inner grading implementer in B is required. Since K is even, the transform
preserves all component parities. Since K² = 1, the same coordinate operation
is the inverse linear map.

This is an algebra equivalence between the graded and ordinary multiplication
structures, not generally an involutive algebra automorphism of one fixed
algebra. Over bases other than ℝ, the explicit grading and implementer hypotheses
must be retained. The existence of 1/2 permits eigenspace projection formulas but
is not intrinsically required when a direct grading is already supplied.

For recursive unrolling the tail parity is

\[
\alpha_{\mathrm{tail}}
=\operatorname{Ad}_{K^{\otimes m}}\otimes\alpha_B.
\]

Omitting α_B for graded coefficients loses the terminal Koszul sign.

## 3. Right-tail versus left-head conventions

The correct two-factor right-tail map is

\[
\rho^R(a\widehat\otimes b)=aK^{|b|}\otimes b.
\]

The map with unchanged tails but moved placement,

\[
F(a\widehat\otimes b)=K^{|b|}a\otimes b,
\]

has the wrong cross-sign in general.

The source's exact counterexample is correct. With

\[
T=\eta\widehat\otimes I+K\widehat\otimes\eta
\]

one has

\[
T^2=2(I\widehat\otimes I+\Omega\widehat\otimes\eta),
\]

\[
F(T)=\eta\otimes I+I\otimes\eta,
\]

and

\[
F(T)^2-F(T^2)=4\eta\otimes\eta\ne0.
\]

A genuinely different left-head convention is

\[
\rho^L_n(a_1\widehat\otimes\cdots\widehat\otimes a_n)
=\bigotimes_r K_r^{p_r}a_r,\qquad
p_r=\sum_{s<r}|a_s|.
\]

For two factors it is a ⊗ K^|a| b. It supplies the correct crossing sign.

The carrier boundary is important:

- Both conventions work for a pure Clifford chain.
- An even terminal B causes no additional problem.
- Reversing the complete chain with arbitrary graded terminal B would require
  an implementer in B or additional replacement data.

The right-tail theorem's unrestricted B hypothesis must not be silently
transferred to a reversed left-head construction. Failure of the mixed convention
does not establish irreversible spatial chirality or a physical time direction.

## 4. Transported star

Assume each factor star preserves parity, K* = K, and B has an even ordinary
anti-involution. Then

\[
\begin{aligned}
&(a_1\widehat\otimes\cdots\widehat\otimes a_n
  \widehat\otimes b)^\star\\
&=
(-1)^{\sum_{r<s}|a_r||a_s|+|b|\sum_r|a_r|}
a_1^*\widehat\otimes\cdots\widehat\otimes a_n^*
\widehat\otimes b^*.
\end{aligned}
\]

The sign comes from

\[
(a_rK^{q_r})^*
=K^{q_r}a_r^*
=(-1)^{q_r|a_r|}a_r^*K^{q_r}.
\]

This is an ordinary anti-involution on the graded algebra: it reverses products
without an additional super sign.

The source's example is valid:

\[
P_{\mathrm{bell}}=\frac12(I\otimes I+\eta\otimes\eta)
\]

is self-adjoint and idempotent, and

\[
\mathcal U_2(P_{\mathrm{bell}})
=\frac12(I\widehat\otimes I+\Omega\widehat\otimes\eta).
\]

The sign-twisted star fixes this element. Naive factorwise transpose changes the
sign of its second term.

The independent native API scout reported that the pinned Mathlib Clifford star
is reverse composed with involute, hence its generators are star-negative. The
source instead uses η* = η and Ω* = −Ω. This report treats the native-star
observation as a scout finding requiring owner-level confirmation during
candidate review; the semantic requirement is unambiguous: the intended
transpose star must be explicitly chosen or transported, never conflated with a
different native Clifford star.

A bare associative real star algebra does not supply an ordered positive cone,
a C* norm, or Hilbert positivity. Star compatibility is the algebraic claim.
Analytic positivity needs independently specified structure.

## 5. Projector scaling: n = 3 countermodel

Let the odd site generators satisfy

\[
e_i^2=1,\qquad e_ie_j=-e_je_i\quad(i\ne j).
\]

Set

\[
q_n=(1+e_1)\cdots(1+e_n),\qquad
p_n=2^{-n}q_n=P_0^{\widehat\otimes n}.
\]

At n = 2 the source is correct:

\[
q_2^2=2q_2,\qquad p_2^2=\frac12p_2.
\]

At n = 3,

\[
\boxed{
q_3^2=4(e_2+e_1e_2+e_2e_3+e_1e_2e_3).
}
\]

The asserted general scaling would require q₃² = 2q₃. Their scalar coefficients
are respectively 0 and 2, so they cannot agree.

Equivalently,

\[
p_3^2
=\frac1{16}(e_2+e_1e_2+e_2e_3+e_1e_2e_3)
\ne\frac14p_3.
\]

A short ordered derivation uses the parity automorphism α:

\[
q_n^2=
\big(q_{n-1}^2+q_{n-1}\alpha(q_{n-1})\big)(1+e_n).
\]

For q₂,

\[
q_2\alpha(q_2)=2(-1-e_1+e_2+e_1e_2),
\]

so the bracket at n = 3 is 4(e₂ + e₁e₂). A second scalar-coefficient diagnostic is

\[
\operatorname{coeff}_1(q_n^2)
=\sum_{r=0}^n {n\choose r}(-1)^{r(r-1)/2}.
\]

For n = 3 it equals 1 + 3 − 3 − 1 = 0.

The assertion that pure graded tensor idempotence holds if and only if every
factor is even is also false:

\[
(1\widehat\otimes P_0)^2=1\widehat\otimes P_0
\]

although P₀ mixes parity. Even idempotent factors are sufficient, not necessary.

The preserved matrix projector statement is instead

\[
\mathcal U_n(P_0^{\otimes n})^2
=\mathcal U_n(P_0^{\otimes n}),
\]

because unrolling is an algebra equivalence.

The even projector P = (I + K)/2 and all its pure graded tensor powers are
idempotent. The concrete corner isomorphism

\[
PM_2(B)P\cong B
\]

is also valid. It is separate from a categorical Morita equivalence that would
require its own bimodule/interface construction.

## 6. Cut rank and the controlled-parity map

Use ordinary real bipartite tensor rank, equivalently matricization rank, unless
a different graded rank has been explicitly defined.

At a cut, remove the invertible local untwisting maps on the left and right.
The remaining map is

\[
C=\operatorname{id}_L\otimes E_R
 +R_{\Gamma_L}\otimes O_R,\qquad
\Gamma_L=K^{\otimes k},
\]

where E_R and O_R are right total-parity projections.

Because Γ_L² = 1 and E_R, O_R are complementary,

\[
C^2=\operatorname{id}.
\]

It maps each simple tensor to at most two simple tensors. Therefore

\[
\boxed{r(Ct)\le2r(t),\qquad r(t)\le2r(Ct).}
\]

These two natural-number inequalities avoid ambiguous natural division by two.
The argument extends to graded B by including its parity in the right
projections. The restriction B₁ = 0 in J6 is unnecessary for this particular
rank statement.

The left cut factor is finite-dimensional, so every algebraic tensor has finite
rank even if B is infinite-dimensional. No analytic SVD is needed.

The factor two is sharp on inhomogeneous tensors:

\[
I\widehat\otimes(I+\eta)
\longmapsto I\otimes I+K\otimes\eta
\]

changes rank from 1 to 2.

### Homogeneous total parity preserves rank exactly

Suppose t has total parity σ. Define a left linear automorphism on each
homogeneous component by

\[
L_\sigma(x_u)=x_u\Gamma_L^{\sigma+u}.
\]

Right multiplication by Γ_L preserves parity and squares to the identity.
Consequently L_σ is invertible. On the total-parity-σ subspace,

\[
C(t)=(L_\sigma\otimes\operatorname{id})(t).
\]

Thus

\[
\boxed{r(Ct)=r(t)\quad\text{for homogeneous }t.}
\]

The sharp rank-doubling examples are inhomogeneous. They cannot be presented as
sharp examples in Axiom IV's homogeneous even-boundary class.

### Rank of the true unrolled diagonal projector

For n ≥ 2 and a proper cut n = k + m, k,m ≥ 1, put

\[
P_A=P_0^{\otimes k},\qquad
P_B=P_0^{\otimes m},\qquad
Q_B=P_1^{\otimes m}.
\]

After local invertible transformations the cut tensor is

\[
P_A\otimes\frac{P_B+Q_B}{2}
+P_A\Gamma_A\otimes\frac{P_B-Q_B}{2}.
\]

The two left matrix units are independent and the two right factors are
independent. Hence the underlying cut rank is exactly 2.

This projector is total-inhomogeneous; it is not represented by the stated
fixed even-boundary TT definition. Its algebraic rank property does not, by
itself, establish a physical entanglement claim.

## 7. TT boundary restriction and local conversion

Axiom IV assigns homogeneous core parity

\[
|W^{[j]}_{a,b}|=|a|-|b|
\]

with both boundary parities zero. Along each complete path,

\[
\sum_j|W^{[j]}|=|r_0|-|r_n|=0.
\]

Every represented tensor is therefore total-even. It cannot cover arbitrary
matrices, odd tensors such as η ⊗ I, or inhomogeneous diagonal projectors.

Valid alternatives for a later author to specify are:

- Fixed total parity σ: require boundary parity difference σ.
- General tensors: represent even and odd components separately.
- A global parity boundary label with a specified readout.

For a homogeneous train with right boundary parity zero and even terminal B,
the right-tail parity at site j equals the outgoing bond parity. Thus the local
conversion

\[
\widetilde W^{[j]}=W^{[j]}K^{|r_j|}
\]

is valid in that setting.

For graded terminal B the final core additionally needs the local map ρ₁^B.
Multiplying the final core only by K^|r_n| = I misses the terminal coefficient
parity.

“Graded SVD” requires finite-dimensional inner-product data. With arbitrary
operator coefficients, use an algebraic factorization contract or explicitly
supply the analytic structure. A parity-blind decomposition can be refined to
track parity or be handled globally; its existence is not impossible merely
because the original bonds lack parity labels.

## 8. Operator-sink dimension law

If the first n−1 cores are scalar Clifford tensors and only the terminal core
contains B, a cut at k has

\[
\dim L=4^k,\qquad
\dim R=4^{n-k}\dim_{\mathbb R}B.
\]

For finite-dimensional B,

\[
\boxed{r_k\le\min(4^k,\;4^{n-k}\dim_{\mathbb R}B).}
\]

The maximum is attained by a full-rank unfolding. This is ordinary finite
linear algebra and does not depend on J5's projector claim or the rank bridge.

For infinite-dimensional B the finite uniform bound is r_k ≤ 4^k. Do not use
Mathlib's finite dimension number without a finite-dimensional hypothesis:
Module.finrank is zero for infinite-dimensional modules.

The source's example using 64 independent B coefficients at n = 3, k = 2 does
refute the old right-half bound. A smaller noncommutative example takes
B = M₂(ℝ), a real basis b₁,…,b₄, and

\[
c_{a_1a_2a_3}=\delta_{a_1a_3}b_{a_2},
\qquad a_1,a_2,a_3\in\{1,2,3,4\}.
\]

The unfolding with rows (a₁,a₂) and columns (a₃,B-coordinate) is a 16×16
identity/permutation matrix. Hence r₂ = 16 > 4. This example is for the general
scalar-core rank claim; it is not asserted to satisfy Axiom IV's homogeneous
boundary restriction.

Allowing B-valued cores at arbitrary sites defines a different noncommutative
module/factorization problem. The scalar tensor-rank formula does not
automatically apply to it.

## 9. Odd real dimension and conditional tripotence

The valid finite-real-carrier obstruction is:

> If K² = I, J is invertible, and JK = −KJ on a finite-dimensional real V,
> then dim V is even.

J identifies the +1 and −1 eigenspaces of K. More generally, two invertible
anticommuting real matrices force even dimension directly by determinants.

For a general S with

\[
JSJ^{-1}=-S
\]

in odd real dimension, determinants imply det S = 0. This does not impose
S³ = S.

The explicit countermodel is

\[
S=\operatorname{diag}(2,-2,0),\qquad
J=\begin{pmatrix}0&1&0\\1&0&0\\0&0&1\end{pmatrix}.
\]

Then J² = I and JSJ⁻¹ = −S, but S³ ≠ S.

A correct conditional consequence assumes S³ = S separately. The eigenspace
decomposition is then into eigenvalues −1,0,1, and J swaps the ±1 spaces. In odd
dimension,

\[
\dim V=2\dim E_+ + \dim E_0
\]

forces dim E₀ to be positive and odd. Under this added hypothesis,
P₀ = I−S² is the zero-sector projector.

Without semisimplicity or tripotence even the nullity parity can fail: nilpotent
Jordan blocks of lengths 3 and 2 give dimension 5, kernel dimension 2, and
admit an alternating-sign diagonal involution anticommuting with S.

### External odd matrix size does not constrain arbitrary B

Take B = M₂(ℝ) and r = 3. Then

\[
M_3(B)\cong M_6(\mathbb R)
\]

contains

\[
I_3\otimes K,\qquad I_3\otimes\eta,
\]

which are invertible anticommuting involutions. Thus odd external r does not
make M_r(B) irreducible under Clifford doubling. Infinite-dimensional operator
algebras can also have matrix self-similarity.

The factorization N = 2^n r is bookkeeping for the external real matrix index,
not a classification of all internal factors of B. An unconditional transition
from binary geometry to KKT geometry is not justified.

The trace-parity argument is valid for an actual finite real matrix involution.
A noncommutative B-valued matrix trace is not automatically cyclic; a trace
argument over B needs its own trace map and hypotheses.

## 10. Integral quartet lattice index

For one quartet,

\[
\begin{pmatrix}a&b\\c&d\end{pmatrix}
=x_I I+x_KK+x_\eta\eta+x_\Omega\Omega.
\]

Integral quartet coordinates exist exactly when

\[
a\equiv d\pmod2,\qquad b\equiv c\pmod2.
\]

The lattice index is 4. The four-by-four coordinate matrix A has determinant
±4.

For n factors, the coordinate matrix is A tensor-powered n times, so

\[
|\det(A^{\otimes n})|=4^{\,n4^{n-1}}.
\]

Therefore the correct lattice index is

\[
\boxed{4^{\,n4^{n-1}},}
\]

not 4^n. At n = 2 the index is 65,536 rather than 16.

The Jordan–Wigner right-tail rule permutes the quartet tensor basis, leaving
the lattice index unchanged. Coordinate denominators divide 2^n, but this is
not the lattice index.

The need for 1/2 belongs to this orthogonal quartet and its eigenspace
projection formulas. Matrix-unit block expansions work over arbitrary rings;
there is no universal impossibility of matrix unrolling without 1/2.

## 11. Actual dependency graph and interpretive boundary

The source's conceptual J-order is not itself a deductive dependency graph.
The mathematical dependencies separate as follows:

1. Independent prerequisites: graded coefficient algebra, concrete frame,
   graded tensor multiplication.
2. Untwisting branch: inner grading identities → right-tail map → multiplication
   and inverse.
3. Independent consequences: transported star; corrected projector
   calculations; controlled-parity cut map.
4. Rank branch: controlled-parity map → cut-rank inequalities.
5. Dimension branch for the operator sink: ordinary finite-dimensional tensor
   linear algebra → maximum cut rank.
6. TT branch: homogeneous core rule and boundary parities → total parity and
   local core conversion.
7. Odd-real-dimension branch: anticommutation → dimension obstruction; explicit
   additional tripotence → zero-sector parity.
8. Integral branch: quartet coordinate matrix → determinant/index formula.

The source's false J5 scaling is not a prerequisite for the valid rank
comparison. The operator-sink bound does not require the entire TT theorem.
Tripotence is not a consequence of the odd-dimension obstruction.

“Inner-grading untwisting” or “Klein transformation” describes the main map
without implying unprovided Hopf/categorical data. Fidaleo's primary paper
studies a Klein transformation under an inner grading assumption in the
C*-graded tensor setting. Majid's bosonization concerns braided groups and Hopf
constructions with extra structure absent here.

- [Fidaleo, Symmetric states for C*-Fermi systems II: Klein transformation and their structure](https://arxiv.org/abs/2202.03709)
- [Majid, Some Comments on Bosonisation and Biproducts](https://arxiv.org/abs/q-alg/9512028)

These sources support the terminology distinction, not the explicit
counterexamples derived in this audit. The coordinate equivalence does not
by itself trivialize all super braiding or establish a global symmetric
monoidal equivalence with ordinary algebras.

## 12. Read-only inspection of prior PR #352's exact-source workflow

The following files in the local continuation were read as workflow evidence:

- [Repository agent policy](sandbox:/workspace/scratch/9009f3c86480/tripotent-krein-continuation/AGENTS.md)
- [Canonical agent pipeline](sandbox:/workspace/scratch/9009f3c86480/tripotent-krein-continuation/docs/CANONICAL_AGENT_PIPELINE.md)
- [Epistemic-compilation skill](sandbox:/workspace/scratch/9009f3c86480/tripotent-krein-continuation/skills/epistemic-compilation/SKILL.md)
- [Prior scoped acceptance record](sandbox:/workspace/scratch/9009f3c86480/tripotent-krein-continuation/docs/tripotent_structure_acceptance.md)
- [Prior exact-source workflow](sandbox:/workspace/scratch/9009f3c86480/tripotent-krein-continuation/.github/workflows/tripotent-structure.yml)
- [Prior owner-selection wrapper](sandbox:/workspace/scratch/9009f3c86480/tripotent-krein-continuation/tools/quality/check_tripotent_structure.py)
- [Shared exact-closure checker](sandbox:/workspace/scratch/9009f3c86480/tripotent-krein-continuation/tools/quality/check_perjes_klein.py)
- [Native audit-source generator](sandbox:/workspace/scratch/9009f3c86480/tripotent-krein-continuation/tools/quality/check_peirce_reflection.py)
- [Preserved verifier review](sandbox:/workspace/scratch/9009f3c86480/candidates/tripotent_verifier_semantic_review.json)
- [Preserved prior remote evidence](sandbox:/workspace/scratch/9009f3c86480/candidates/tripotent-qa/qa-a-final-remote-evidence.json)

This auditor did not execute those workflows, verify their historical remote
status afresh, run the artifact verifier, or adopt their old success as current
acceptance. The inspection is of local source and preserved records only.

### Reusable verification pattern

The prior workflow separates two surfaces:

1. A focused kernel job fetches an exact Git revision and repository-pinned
   Mathlib, installs the exact Lean toolchain, copies the repository import
   closure into a fresh output tree, compiles the closure serially, and then
   audits declarations owned by the selected modules.
2. A source/root job stages the actual nonempty task range in a disposable CI
   checkout, runs the unchanged staged gate, and attempts incremental and full
   root gates separately.

The kernel checker records each copied source SHA, selected targets, ordered
closure, per-module status, actual Lean version, and final status. The native
audit uses module ownership, not namespace-prefix matching. It checks unsafe
and partial flags and collects transitive declaration axioms with an allowlist
of propext, Classical.choice, and Quot.sound.

Important limits visible in the source:

- The generated native audit rejects a zero total declaration count, but does
  not itself prove that every selected owner supplied at least one record.
  The preserved artifact verifier checks per-owner coverage separately.
- “AUDIT_COUNT” in a log is a completion marker, not independent provenance.
- The exact-closure checker checks pinned Mathlib revision and toolchain files.
  The preserved verifier also checks the actual Lean version, checker hashes,
  source snapshots, and authenticated job records.
- A source-closure result is explicitly not a root Lake build.

The preserved verifier review identifies useful safeguards: do not let Python
optimization disable acceptance guards; bind all checker/generator sources to
the reviewed hashes; compare actual tool version with the pin; match copied
source hashes, module results, unique declaration records, owner coverage, and
axiom records against authenticated output; verify commit/tree provenance
separately from claims inside an artifact.

### Recommended verification scope for the new extension

This is a recommendation for the implementation/execution owners, not an
executed verification result:

1. Freeze the new candidate source and its actual base/head/tree identities.
   Preserve this intake SHA and cutoff in its contract. Do not reuse PR #352's
   or PR #354's acceptance as evidence for new source.
2. Select only the modified graded-unrolling owners and any new owner modules
   actually needed by the accepted contract. Compute their repository import
   closure from the exact snapshot; reuse existing owners.
3. Include positive algebraic compatibility results and explicit refutations
   of the rejected extrapolations. A successful proof of the source's stronger
   false statement would indicate a carrier/hypothesis mismatch requiring
   semantic review.
4. Audit all declarations owned by those targets, including private/generated
   declarations, against the foundational axiom allowlist; require nonempty
   per-owner coverage and a recorded declaration list.
5. Independently review types, actual operations, star conventions, homogeneous
   hypotheses, coefficient algebra assumptions, and rank definitions. Compilation
   does not establish that labels such as “super-TT” or “arbitrary B” match the
   declared type.
6. Preserve immutable source/checker hashes, exact pins, actual tool version,
   generated audit source, module logs/status, declaration records, and remote
   commit/tree correspondence if remote execution is used.
7. Report focused kernel acceptance separately from staged/root integration
   gates. Exercise only the relevant required gates; do not infer whole-repository
   success from the narrow closure.
8. Keep the current base and PR #354 untouched as instructed by the parent.

The current audit is complete at source-semantic scope and ready for later
candidate review. No current candidate Lean source has yet been reviewed or
accepted by this auditor.
