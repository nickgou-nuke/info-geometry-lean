# Chiral native diagnostic repair candidate

## Scope and provenance

This candidate changes only `ZornChiralOperatorReconstruction.lean`. It is
based on the preserved owner whose SHA256 is
`94806af215c43ece8f5f79e6c99af71cefb993462ab850844b6363271a02399a`, exactly
matching that owner's source hash in the diagnostic receipt for CI run
`45416776463`, diagnostic run `c73ae23678dd44f398d46c2a8ef7184f`.

The parent checkout at `/tmp/info-geometry-zorn-primal-dual-20261124` had become
unavailable when this task started. The parent explicitly authorized use of
the hash-matching preserved owner while restoring the checkout. No tracked
repository files were changed by this worker.

The candidate SHA256 is
`48de76a90c85a09cd1b2b6515760ff1412d90a874408d7dd3fa06262e8a91500`.

## Observed native diagnostics

The supplied diagnostic log contains one warning and four error messages:

1. `leftMajorana_source_ordered_volume`: unused `Fin.sum_univ_three` in its
   `simp` list at original line 117.
2. `leftMajoranaPlus_associator_witness`: an attempted instance
   `HSMul ℝ (ZornVectorMatrix ℤ) (ZornVectorMatrix ℤ)` at original line 128.
3. The same witness: an unresolved operator-expression type in function
   position at original line 122.
4. Its downstream nonmultiplicativity proof: unknown witness identifier,
   followed by an unsolved `False` goal. These are downstream consequences
   of the rejected witness declaration, rather than evidence that its
   mathematical identity is false.

The diagnostic run used `warningAsError=false` solely to collect errors.
It was explicitly nonaccepting. This report does not promote that run to
strict validation.

## Minimal proposed changes

- Remove only the CI-reported unused `Fin.sum_univ_three` argument from the
  volume theorem's `simp` list.
- Explicitly ascribe the witness's operator difference to
  `Module.End ℝ (ZornVectorMatrix ℝ)` before applying it. This supplies the
  concrete function coercion expected at the observed failing application.
- Add `(R := ℝ)` to the witness's right-hand `diagonal` constructor. The
  scalar `(2 : ℝ)` does not by itself force the independently inferred
  carrier of a heterogeneous scalar action; the explicit carrier prevents
  its numeric coordinates from defaulting to `ℤ`.

No proof body, theorem name, import, multiplication, sign convention,
foundational assumption, or acceptance option is changed. The dependent
nonmultiplicativity proof is left intact. The witness's `norm_num` argument
list is preserved because its proof was not reached in this diagnostic run;
there is no native unused-argument evidence justifying a speculative cleanup.

## Mathematical preservation

Let `Aᵢ = offDiagonal (basis i) (basis i)` in the actual real Zorn carrier.
The repaired statement remains the full carrier identity

`(L_A₀ * L_A₁ - L_(A₀ ⋆ A₁)) A₂ = 2 • diagonal 1 (-1)`.

Under the repository's actual product, the upper cross-product term carries
a minus sign and the lower term a plus sign. Consequently
`A₀ ⋆ (A₁ ⋆ A₂) = diagonal 1 (-1)` whereas
`(A₀ ⋆ A₁) ⋆ A₂ = diagonal (-1) 1`; their difference is precisely the
displayed nonzero result. This is the same genuine operator-composition
defect as before, equivalently `-2 qCut7` in the source convention. The
operator witness is not replaced by a scalar or commuting surrogate.

The final coordinate projection still serves only to derive a contradiction
from a hypothetical operator equality after the full carrier witness.
The ordered source volume remains `-I`.

## Validation boundary

Performed: read the exact diagnostic log and receipt, verify the preserved
owner's hash against the receipt, inspect the actual multiplication and
Majorana definitions, review the candidate's complete source diff, and
record the candidate hash.

Not performed: Lean elaboration, native tests, build, compiler invocation,
syntax parser, axiom audit, or GitHub mutation. Native acceptance of the
newly reachable witness proof and dependent theorem remains for the parent's
unchanged strict CI suite. This candidate addresses every diagnostic emitted
for this owner; it does not assert that no further diagnostic can appear.
