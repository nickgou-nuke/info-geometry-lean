# Witt modes, Born exchange, and null exactness

Continuation of draft PR #446 from
`e46d5bc01d977887edc3f0089ad76fe300f158fa`.

## Intake and authority

The attached `Pasted text(20261124-132544).txt` is preserved byte for byte as
`source-intake.txt` (36,159 bytes; SHA-256
`e9015139d818aa18e98c5b37aed417ca17632b24af056746ccce071fd4147ee8`).
It includes assertions that two earlier drafts were repaired, verified, and
fast compiling. Those assertions are input claims, not validation evidence.
The two earlier drafts are not separately supplied by this attachment.

The supplied multiplication table is mathematically invalid as a split-octonion
product. Its coordinate units satisfy e4*e4=e0, e4*e1=e5, and e4*e5=-e1.
Consequently e4*(e4*e1)=-e1 whereas (e4*e4)*e1=e1. Its claimed contraction
also fails: L(e4)L(conj(e4))(e1)=e1, but N(e4)e1=-e1.
This defect is independent of Lean syntax or performance. The new production
theorems use the existing genuine Zorn product, including its cross products.

## Exact carrier and conventions

- Null exactness uses `InfoGeometry.Algebra.ZornVectorMatrix ℝ`, the existing
  conjugation and norm, and `ZornLeftCAR.leftMultiplication`.
- Clifford operators use the existing real `ZornMatrix ℝ` quadratic module
  and `DiracSpinor16 = ZornMatrix ℝ × ZornMatrix ℝ`.
- The actual operator is gamma(x)(s,t)=(x*t,conj(x)*s), and the existing native
  `CliffordAlgebra.lift` supplies its representation.
- The source frame is (1,q1,q2,q3,q4,q5,q6,q7), with norm signs
  (+,+,+,+,-,-,-,-), exactly as in `ZornCliffordSourceVolume`.
- `QuadraticMap.polar` is unhalved: P(x,y)=N(x+y)-N(x)-N(y). The orthogonal
  frame has P(ei,ej)=2*eta(i)*delta(i,j).

No new `OctS` carrier or coordinate multiplication is introduced into the
production owners. There is no asserted product-preserving bridge from the
invalid supplied table.

## Claim ledger

| Input claim | Precise disposition |
| --- | --- |
| The pasted product is split octonion multiplication | False, by the explicit alternativity and contraction counterexample above. |
| The pasted seven integer matrices multiply to I | False for the supplied signs: applying the product to e2 gives -e2. The verification-only integer specialization records each of the seven steps. |
| Unnormalized mixed CAR has coefficient four | Correct for genuine orthogonal gamma generators with squares +I and -I. Formalize on the existing real Dirac carrier. |
| Half-sum and half-difference give standard CAR | Define a_i=(gamma_i+gamma_(i+4))/2 and b_i=(gamma_i-gamma_(i+4))/2; target {a_i,a_j}=0, {b_i,b_j}=0, {a_i,b_j}=delta_ij I. |
| Born exchange is an involution | Define B=gamma4*gamma5*gamma6*gamma7; target B²=I, B commutes with the positive generators and anticommutes with the negative generators, hence B*a_i*B=b_i and conversely. |
| Null image/kernel exactness | For x≠0 and N(x)=0, target range L(conj x)=ker L(x). Reuse the previously owned dimension-four theorems. The inclusion alone permits x=0; equality does not. |
| A new long idempotent rank/trace proof is necessary | Pinned Mathlib already owns `IsIdempotentElem.isProj_range`, `LinearMap.IsProj.trace`, and `Matrix.trace_toLin'_eq`. The minimal exactness extension does not need trace. |
| The pseudoscalar is always +chirality | Its sign depends on the ordered frame. The published frame gives -chirality. No existing orientation theorem is silently changed. |
| Relations and dimension equality prove Cl(4,4)≅M16(R) | They do not prove injectivity or surjectivity. No `AlgEquiv` is claimed by this extension. |
| The repaired module compiles nearly instantaneously | Unsupported input assertion. Record actual compiler commands, results, and elapsed time instead. |

## Causal implementation order

1. Reuse the genuine Zorn norm, conjugation, multiplication, and contraction.
2. For null x, turn L(x)L(conj x)=0 into the native range/kernel inclusion.
3. For nonzero x, use conjugation invariance and the existing two finrank-four
   theorems to upgrade the inclusion to equality.
4. Read the existing source frame in the real quadratic module and calculate
   its scalar norm/polar table.
5. Polarize the existing gamma square theorem through native Mathlib to obtain
   all eight Clifford anticommutators, then the normalized four-mode CAR.
6. Use associative operator multiplication and the Clifford signs to prove the
   four-factor Born square and exchange identities. Do not expand eight dense
   sixteen-dimensional matrix products.

## Scope boundary

The Born terminology names a specific algebraic involution. It does not prove
a physical reciprocity principle, a symplectic transformation on a separately
constructed phase space, or a gauge field theory. The full Clifford algebra
isomorphism, triality classification, smooth geometry, and gauge connections
remain separate targets from the earlier Klein contract.

Complete proposed proof terms, independent source review, native elaboration,
axiom auditing, and repository gates have separate statuses. This contract
does not itself promote any new theorem to kernel-verified status. The final
validation record states which checks actually ran.
