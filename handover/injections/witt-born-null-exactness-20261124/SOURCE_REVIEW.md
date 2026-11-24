# Independent intake and candidate source review

Date: 2026-11-24. Repository inspected:
`/tmp/info-geometry-zorn-primal-dual-20261124`, starting at
`e46d5bc01d977887edc3f0089ad76fe300f158fa`.

Input: the complete attached `Pasted text(20261124-132544).txt`.
The two earlier drafts named by that text were not supplied to this reviewer;
their alleged row typo, truncated literals, and proof holes were not verified.

This is a source and mathematical review. The reviewer ran no Lean compiler,
Lake build, executable mathematical test, or axiom audit. The counterexamples
below were derived from the exact displayed coefficients. A separate small
Lean verification candidate records them for native validation by the root.

## 1. The supplied multiplication is not a split-octonion multiplication

Let `eᵢ` be the coordinate unit at index `i`, and let `⋆` be the exact supplied
`octMul`. Its rows imply

```
e₄ ⋆ e₄ = e₀        (row 0: +x₄ y₄)
e₄ ⋆ e₁ = e₅        (row 5: +x₄ y₁)
e₄ ⋆ e₅ = −e₁       (row 1: −x₄ y₅)
```

Consequently `e₄ ⋆ (e₄ ⋆ e₁) = −e₁`, whereas
`(e₄ ⋆ e₄) ⋆ e₁ = e₁`. Left alternativity fails.
With the attachment's conjugation and norm,

```
L(e₄) L(conj(e₄)) e₁ = e₁,
N(e₄) e₁             = −e₁.
```

This directly falsifies the first conjunct of
`oct_composition_and_trace_identities`; its displayed `ring` proof cannot
prove that statement. This is a mathematical counterexample, not a tentative
Lean API issue.

Norm composition fails as well. Both `x=e₀+e₄` and `y=e₁+e₅` have norm zero,
but `x⋆y=2e₅`, which has norm `−4`. Also, the supplied entries give both
`e₁⋆e₇=e₆` and `e₇⋆e₁=e₆`, so distinct imaginary basis elements need not
anticommute.

There can be no injective multiplication-preserving linear equivalence from
this raw algebra to the genuine alternative Zorn algebra: such a map would
transport the failed left-alternative identity to a true one and force the
distinct vectors `e₁` and `−e₁` to coincide.

## 2. The raw integer seven-product claim also fails

For the exact raw table, applying the proposed product `L₁…L₇` to `e₂`
from right to left gives

```
e₂ --L₇→ −e₅ --L₆→ e₃ --L₅→ −e₆ --L₄→ e₂
   --L₃→ −e₁ --L₂→ e₃ --L₁→ −e₂.
```

Thus `leftMulInt 1 * … * leftMulInt 7 = 1` is false for the displayed
table. The attachment's `by decide` cannot close it.

An earlier reviewer message used `e₁` and misread the sign of the row-6
term `+x₇ y₁`. The root caught this; that witness was withdrawn. The corrected
`e₂` chain above was checked independently against every relevant source row.
The earlier claim that six sign changes alone repair the entire table was
also withdrawn. This review makes no exhaustive coordinate-table repair or
multiplication-bridge claim.

The existing genuine source-ordered volume remains `−I₈` for its seven
left operators and minus chirality for the doubled eight-generator action.
The invalid pasted table does not justify changing that orientation.

## 3. Correct normalization and Born target

For genuine orthogonal Clifford operators with `Pᵢ²=I`, `Nᵢ²=−I`, and
vanishing off-diagonal anticommutators, the unnormalized mixed expression
has coefficient four:

```
{Pᵢ+Nᵢ, Pⱼ−Nⱼ} = 4 δᵢⱼ I.
```

The symmetric normalization `aᵢ=(Pᵢ+Nᵢ)/2`, `bᵢ=(Pᵢ−Nᵢ)/2` gives
`{aᵢ,bⱼ}=δᵢⱼ I`, with zero same-family anticommutators.
The product `B=N₀N₁N₂N₃` commutes with every positive generator and
anticommutes with every negative generator. Its square is
`(−1)^6(−1)^4 I=I`, and `BaᵢB=bᵢ`, `BbᵢB=aᵢ`.
These conclusions depend on the genuine Clifford relations; they do not
rescue the attachment's false construction of those relations.

The construction is a real sixteen-dimensional operator representation.
Neither these identities nor equality of dimensions alone provides a native
`AlgEquiv` between the full Clifford algebra and the endomorphism algebra.

## 4. Pinned Mathlib already owns idempotent rank = trace

Inspected pinned Mathlib source:
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

- `Mathlib/LinearAlgebra/Trace.lean`: `LinearMap.IsProj.trace`,
  `Matrix.trace_toLin'_eq`, and `LinearMap.trace_prodMap'`.
- `Mathlib/LinearAlgebra/Projection.lean`:
  `IsIdempotentElem.isProj_range` and `Submodule.coe_prodEquivOfIsCompl'`.
- `Mathlib/LinearAlgebra/Matrix/ToLin.lean`:
  `Matrix.toLin'_mul` and `Matrix.mulVecLin_mul`.

The attachment's bespoke argument calls the absent
`Submodule.prodEquivOfIsCompl_apply`. It also rewrites with
`LinearMap.trace_prodMap`, which states an identity of linear maps rather than
the applied trace identity supplied by `LinearMap.trace_prodMap'`.

A short replacement for its generic matrix rank/trace lemma can derive
`IsIdempotentElem PM.toLin'` using `Matrix.toLin'_mul`, then use
`hP.isProj_range.trace.symm` and `Matrix.trace_toLin'_eq`. This is an API-guided
proof sketch, not a compiled replacement theorem.

The attachment's blanket invalid-API list is partly wrong for the actual
dependency pin: `Matrix.mulVecLin_mul`, `Matrix.sub_mul`, and
`Matrix.smul_mul` all exist. Its requested correction to the module argument
of `LinearMap.trace` is appropriate.

## 5. Independent review of proposed genuine-Zorn additions

### Witt and Born owner

File reviewed:
`witt-born-candidates/born/ZornCliffordWittBorn.lean`.
SHA-256:
`cc252e95448fb4e51f13fbe8cebc2d2ea55aa28f6ed3bc58979859f94d2ca0ce`.

The candidate uses the existing `ZornMatrix ℝ`, real `DiracSpinor16`,
`diracGammaLinear`, and source vector family. It defines no alternative
multiplication or scalar replacement for the actual operators.

The source-frame scalar norm and polar table are correct. Native
`CliffordAlgebra.mul_add_swap_eq_polar_of_forall_mul_self_eq` takes the
quadratic form implicitly at its definition point; the revised candidate
correctly passes `(Q := zornNorm (R := ℝ))`.

The generic signed-commutation lemma and its four-factor use are
mathematically sound. The proof of `B²=I` factors `B=ab` into commuting
two-generator factors satisfying `a²=b²=−I`; it never reassociates Zorn
products. The two half factors in each normalized CAR are accounted for.

An earlier component readback used bare `rfl` on scalar expressions such
as `−0`; the candidate now first exposes the exact raw coordinates, then
normalizes scalar equalities. No remaining semantic defect was found in this
version. Native elaboration of these tactics and their import closure remains
required.

### Conjugate-range exactness

Addition reviewed: `witt-born-candidates/incidence/addition.lean.txt`.
SHA-256:
`9cd00afcadcdd147f6dcd80343354eca2b8bbcbe7411b4711258ca2fd528a42f`.

The inclusion is the direct consequence of
`Lₓ L_conj(x)=N(x)I` and the exact native orientation of
`LinearMap.range_le_ker_iff` (`g.comp f=0`).
For equality, `conj_conj` proves the conjugate is nonzero, `norm_conj`
preserves nullity, and the existing genuine four-dimensional range/kernel
theorems give equal dimensions. The explicit finite-dimensional instance
supports `Submodule.eq_of_le_of_finrank_eq`.

Both nonzero and null hypotheses are retained for equality. At zero the range
is zero and the kernel is the entire carrier. No extra trace proof or duplicate
octonion universe is introduced. No semantic defect was found.

## 6. Verification candidate and acceptance boundary

`SuppliedTableCounterexample.lean` contains only a private integer
specialization of the supplied table and small finite counterexample
calculations. It belongs in verification provenance, not in production
`InfoGeometry.All` imports.

SHA-256 at this review:
`aff5a59ef1478e42e7e2c4ac550fe22b898e274b5851ab779788e5d3a40b1083`.
Its corrected seven-product witness uses seven small finite step lemmas,
not a dense seven-matrix expansion.

A bounded text scan of the two source additions and counterexample candidate
found no occurrences of `sorry`, `admit`, `axiom`, `unsafe`, or `native_decide`.
This scan is not an axiom audit and is not compilation evidence.

Disposition: the raw multiplication/composition/volume claims are
`countermodel_found`; the genuine-Zorn Witt/Born and exactness additions pass
this independent semantic source review, with kernel acceptance pending.
