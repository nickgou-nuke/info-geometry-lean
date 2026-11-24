# Independent source review: source-ordered Dirac volume

Reviewer: `/root/klein_review`
Date: 2026-11-24
Disposition: **source-reviewed candidate; native validation pending**.

## Exact snapshot and dependencies

Candidate:
`/workspace/scratch/5672353268f8/klein-candidates/clifford/ZornCliffordSourceVolume.lean`

SHA-256:
`cfe9cb440f28021fbfc8a572355ca4d691133cae4e5a89e58494e7df890c6058`.

The separately reviewed hierarchy dependency has SHA-256
`ea37f4082661ebee3c7519e290509c0162e51b9e4e2f61acca76e1db436cc5ba`.
The existing repository owner
`lean/InfoGeometry/Algebra/ZornChiralOperatorReconstruction.lean`, whose exact
seven-operator volume statement was inspected, has SHA-256
`94806af215c43ece8f5f79e6c99af71cefb993462ab850844b6363271a02399a`.

No definite mathematical, sign, carrier, or pinned-API blocker was found in this
snapshot. No candidate or repository owner was edited by the reviewer. This
report is independent of the earlier three-module report and does not extend its
compilation status.

## Order, signs, and the represented identity

The native Clifford product is explicitly ordered as

`(1, V₁-U₁, V₂-U₂, V₃-U₃, U₁+V₁, U₂+V₂, U₃+V₃, E₂₂-E₁₁)`.

The seven imaginary vectors are transported into `ZornMatrix ℝ` through the
existing inverse `canonicalVectorEquiv`. Their stated norm signs are
`(+,+,+,-,-,-,-)`. The source definitions and the coordinate norm calculation
agree with this sign convention. Adding the unit vector of norm one gives four
positive and four negative directions mathematically; norm signs alone are not
being used as a formal orthogonal-basis certificate.

Write `Aᵢ` for the actual eight-dimensional real left action of the i-th imaginary
source vector. Each single gamma readback has the block form

```text
γ(qᵢ)(s,t) = (Aᵢ t, -Aᵢ s),
γ(1)(s,t) = (t,s).
```

The candidate's `sourceLeftOperator_apply` identifies these operators with the
existing `L_map` and Majorana operators, including the three initial minus signs
and the final diagonal minus sign. The conjugation calculation gives `conj(qᵢ)=-qᵢ`.
Thus the readback retains the actual multiplication and its cross-product terms.

Composition in `Module.End` acts as `(f*g)(v)=f(g(v))`. With that convention, the
eightfold product acts as

```text
(s,t) ↦ ((A₁ A₂ A₃ A₄ A₅ A₆ A₇)s,
         -(A₁ A₂ A₃ A₄ A₅ A₆ A₇)t).
```

The imported theorem `leftMajorana_source_ordered_volume` has precisely this
seven-operator order and these signs, and its conclusion is `A₁…A₇=-I`. Therefore
the represented eightfold product is `(s,t) ↦ (-s,t)`, exactly **minus** the
previously chosen chirality `(s,t) ↦ (s,-t)`.

The proof only composes linear operators and reuses the existing source theorem.
It does not reassociate nonassociative octonion products. The auxiliary negation
readback is compatible definitionally with the coordinate-rearrangement
equivalence and the transported additive structure.

## Accepted theorem scope

The proposed public declarations give the seven vector norm signs, an explicitly
defined ordered element of the native Clifford algebra, and these identities:

- Its represented endomorphism is `-diracChirality.toLinearMap`.
- The square of that represented endomorphism is identity.
- Its eigenvalue on the first Zorn summand is `-1`; on the second it is `+1`.
- Negating the ordered Clifford element gives represented chirality.

The operator-square proof correctly uses the existing chirality involution
theorem after rewriting the represented operator. It does not pull that equality
back through an unproved injective representation.

The final declaration is literally an identity for the negative Clifford
element. Its orientation terminology must not be read as a theorem about
reversing the entire eight-entry list: that reversal has even permutation parity.
No oriented-frame transport construction is supplied here.

## Boundaries and remaining validation

This candidate does not assert or establish, as separate native theorems:

- the square of the abstract Clifford element equals one;
- injectivity or surjectivity of the full Clifford representation;
- an exterior-degree-eight readback or a graded pseudoscalar construction;
- a Hodge-star identity;
- a new basis, projective geometry, or differential gauge connection.

The first three candidates' previous source-review disposition remains unchanged.
The new owner may be integrated byte-identically with the exact source-ordered
operator scope above; native elaboration and axiom auditing remain necessary.

## Review activity

The complete candidate was read, together with bounded source definitions for
the coordinate bridge, additive structure, gamma representation, Majorana
operators, and the exact existing seven-operator volume theorem. Pinned Mathlib's
`Module.End.mul_apply` was checked for composition order.

The source scan

```text
rg -n '\b(sorry|admit|axiom|native_decide|unsafe)\b' <volume candidate>
```

returned exit status 1 with no matches. SHA-256 was checked again after reading
the dependency statements. No compiler, Lake command, test, axiom audit, cache
operation, or repository mutation was performed by this reviewer. This token
scan and mathematical source review are not substitutes for native validation.
