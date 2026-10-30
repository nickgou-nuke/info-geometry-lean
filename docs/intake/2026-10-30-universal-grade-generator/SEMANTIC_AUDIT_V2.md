# Independent semantic acceptance V2: universal grade generator

**Verdict: PASS — accepted within the stated algebraic scope.**

Reviewer: `grade_claim_review`, independent of the three source authors and
the runtime acceptance reviewer. Review date: 2026-10-30. This record is a
semantic assessment of the actual Lean statements, definitions, proof bodies,
and documentation. The reviewer did not author Lean source, edit live owners,
or execute a compiler or build. Runtime and kernel acceptance are separate
gates and must bind to the same source hashes.

## Provenance and exact reviewed surface

The intake is `AGENTS-Universal-Grade-Generator.md` at commit
`f54b83da3756c3ded0decbf92fd887f8083949ed`, Git blob
`1817347ef5f50f799912ba3bd7d03dc40c842bdc`. Its SHA-256 is
`43d60af6f63ef7d9602a7d045668486dada37f4bdc2784a4bcddef05cadc9361`;
the frozen text has 654 lines. The entire intake was reviewed, including the
A55/A56/A57 snippets. Embedded assertions of verification and historical or
physical interpretations were not treated as evidence.

All eight live Lean files were read and their bytes were independently
compared with the frozen source hashes. Every hash matched. The reviewed
surface contains 93 explicit theorem declarations and 5 explicit definitions,
plus the matrix carrier abbreviation. `SEMANTIC_AUDIT_V2.json` enumerates every
reviewed theorem and definition by its exact qualified name, source path, and
source hash.

Paths in the following table are beneath `lean/InfoGeometry/`.

| Source file | SHA-256 |
|---|---|
| `Core/IdempotencyDefect.lean` | `2d7b8fa580abe148fc70a39f8e1831b5505fb7f6a3920f3a79a0ba35bfee5590` |
| `Core/PeirceDefect.lean` | `d26471b128136c2d0b54661a19490c0c132ba366aa91476b4e41c956fe84e9a2` |
| `Core/PeirceDefectAdjoint.lean` | `fb42fa276d547283ebacd4557c43665e05481c6140dd0a3181816db0f6400315` |
| `Core/DefectIteration.lean` | `87608961261812f07eb3041eaf7827bc3a1793482a687a01ac0fdb527c4f0b4d` |
| `Core/TripotentDefect.lean` | `cd07bc3c2d975da1683860685b9bdce86c0a192702e6731fef054cf31f513c85` |
| `Core/TripotentAdjoint.lean` | `c835f1b5f7e3a834b05beffc2951470e732981ea0ec5298ca2d1ce165f1ff1c0` |
| `Core/TripotentEigenspaces.lean` | `35cd9b4579d0cd9e21dfee7021b495fa57f357732b641c81c4cde753d4289353` |
| `Canonical/TripotentMatrixExample.lean` | `f188c713d38c2c7ad48e32fc0448ddb0ca431395606c1c13bd9feead9aadf195` |

The mathematical claims and dependency graph in `README.md`, the generation
contract in `CONTRACT.md`, and the intake metadata in `PROVENANCE.json` were
also reviewed. Their reviewed hashes are recorded in the companion JSON.

## V2 proof addition and gate preservation

This V2 record supersedes the earlier semantic receipts for the revised matrix
source. The earlier receipts remain unchanged. Exactly one Lean theorem and
its doc comment were added; all imports, definitions, other theorem bodies,
and the seven other Lean sources retain their V1 bytes. The README adds only
two sentences documenting this new fact. Removing those exact additions
reproduces both V1 hashes.

The added declaration is
`InfoGeometry.Canonical.TripotentMatrixExample.reflection_tripotent_noncommute`:

```lean
reflection * tripotent ≠ tripotent * reflection
```

Both operands are the existing actual matrices in
`Matrix (Fin 4) (Fin 4) ℝ`. Their density and self-adjointness were already
proved. The proof assumes equality of the full matrix products, evaluates
the `(0,1)` entry, and derives a contradiction by exact rational matrix
multiplication. This supplies an additional geometric noncommutativity
witness; it does not change the carrier or assume the desired conclusion.

The existing T16 simple-operand lexical recognizer prompted this addition.
The reviewer inspected the recognizer and confirmed that
`tools/infra/opengauss_screener.py`,
`tools/quality/proof_proxy_staged_gate.py`, and `.githooks/pre-commit` have no
diff against `HEAD`. The response to the gate is a substantive closed proof,
not a gate modification, suppression, exception, or weakened requirement.
The reviewer did not execute the gate.

All eight V2 source hashes match the new freeze. Only the matrix source hash
and README hash changed among the previously reviewed sources and documents.
The added README claim is exactly supported by the new theorem and the
previous density/self-adjointness proofs. The initial findings remain closed.
Independent QA must bind runtime acceptance of the changed matrix leaf to its
V2 hash.

## Findings by mathematical layer

1. **Defect calculus and tangent geometry.** The new defect is exactly
   `x*x-x` in an arbitrary associative ring. `polarization` preserves both
   ordered mixed products. The sign identities, product identity, and
   `cubic_sub_eq_mul_defect` / `cubic_sub_eq_mul_defect_neg` use no ambient
   commutativity or division. `defect_add_idempotent_eq_square_iff`,
   `tangent_iff_diagonal_corners_zero`, and `tangent_iff_mixed_corners`
   express equivalent algebraic tangent conditions. `commute_square_of_tangent`
   derives the centralizer property from existing Peirce multiplication laws.
   The terminology now says algebraic linearization, without implying an
   analytic derivative theorem.

2. **Opposite corners and inner actions.** The input operators stay in the
   original ring. The new `negative_ad_squares_sum_eq_defect` and
   `ad_squares_sub_eq_defect` are equations for native `LieAlgebra.ad`
   endomorphisms. They retain the operator factor `K*K-K`, with
   `K=u*v+v*u`. They have the correct signs and do not normalize this factor
   to a scalar. The actual double-bracket owner statements were traced.
   `real_ad_cube_eq_ad` transfers the existing integer-linear cubic, while
   `projZero_ad_apply`, `projPos_ad_apply`, and `projNeg_ad_apply` identify
   the existing normalized projectors with actual Peirce components.

3. **Finite iteration and order.** `iterate_mul_iterate_eq_zero` allows
   independent iteration counts. The addition theorem requires both ordered
   products to vanish. `commute_iterate_add_idempotent` correctly begins after
   the first tangent step. `iterate_mem_adjoin` and `adjoin_iterate_antitone`
   are statements in native subalgebra inclusion. They do not assert a strict
   chain, distinct iterates, new adjoint weights, or infinite independence.

4. **Tripotent defects and normalization.** The six off-shell identities are
   exact identities for the existing real projectors. In particular,
   `defect_projZero` has the corrected positive sign
   `defect (projZero t) = t*(t*t*t-t)`. The three recovery theorems require
   two idempotents and both ordered orthogonality conditions. They recover
   the existing normalized projectors, without introducing a second projector
   carrier or treating the scaled expressions `t*t±t` as idempotents.

5. **Native spectral statements.** `adLinear_eq_ad` and
   `adGrade_eq_eigenspace` identify the existing operators with native
   Mathlib structures. `ad_quintic` is an endomorphism equality on all of the
   real associative algebra, proved using the existing five-range
   reconstruction. `fiveGradeRange_eq_eigenspace` proves both directions;
   its converse uses actual projector commutation and distinct real weights.
   Product and Lie-bracket closure follow from the inner derivation law.
   Out-of-range vanishing concerns real eigenspaces outside the five labels.
   No conclusion that every grade is nonzero is assumed in the generic API.

6. **Full matrix non-vacuity and geometry.** The concrete carrier is
   `Matrix (Fin 4) (Fin 4) ℝ`. `frameUnit_mul` retains the full matrix-unit
   multiplication law. `tripotent_entry_ne_zero` proves the generator is
   dense, and `tripotent_noncommute` supplies a noncommuting operator.
   `all_five_weights_occur` uses explicit nonzero matrix witnesses for all
   five native eigenspaces; `fiveGradeRange_ne_bot` transfers through the
   proved eigenspace equality. `zero_weight_forward`, `zero_weight_reverse`,
   and `zero_weight_noncommute` exhibit two noncommuting neutral operators.
   The self-Penrose consequence uses the existing matrix owner and an explicit
   self-adjointness proof. There is no replacement of the ambient algebra by
   a scalar, diagonal, or commuting carrier.

## Existing owners traced

The review followed the actual definitions and relevant proof bodies in
`Core/PeirceDecomposition`, `Core/PeirceGrading`,
`Core/PeirceCoupledCorners`, `Core/PeirceQuadraticFrame`,
`Core/PeirceAdjointCycle`, and `Core/IdempotentCartan`. It also traced
`Physics/Algebra/TripotentPeirceProjectors`,
`Physics/Algebra/TripotentLeftRightPeirceProjectors`,
`Physics/Algebra/TripotentFiveGradingDecomposition`,
`Physics/TripotentAdjointDerivation`, and `NCG/TripotentMatrixGeometry`.

The existing nine-corner reconstruction and five-range linear equivalence
are proved constructions, not assumed theorem fields. Their reuse is
mathematically appropriate. This review makes no repository-wide novelty
claim.

## Review requests and corrections closed

All of the following are closed in the reviewed sources or documentation:

- The intake's zero-projector defect sign was corrected to positive.
- The tangent comment now refers to the algebraic linearization kernel.
- The mixed-corner reconstruction is exposed as an explicit equivalence.
- Both cubic factorizations through the new defect API are present.
- Undefined source macro names are replaced by precisely stated native
  adjoint-square equations, without claiming unsupported identification.
- The matrix example supplies all five nonzero weights, projector recovery,
  and explicit noncommuting grade-zero operators.
- The README dependency edge into double-adjoint corrections now originates
  from defect calculus, not the unused new tangent-cancellation theorem.
- The contract's intake line count agrees with the frozen 654-line text.
- V2 adds the closed `reflection_tripotent_noncommute` proof while preserving
  the T16 recognizer and gate sources unchanged.

## Accepted boundaries

The generic statements permit noncommutative ambient rings and algebras;
particular polynomial expressions in one generator naturally commute.
Real scalar hypotheses are explicit where normalization and weight
separation use them. Algebraic orthogonality is not substituted for
self-adjointness; the concrete geometric consequence has its star hypothesis.

The work does not assert a universal minimal polynomial, occurrence of all
five weights in every algebra, grade-zero commutativity, recovery of the
oriented commutator from the square map, infinitely many independent defect
iterates, analytic differentiation, a manifold, a completion or colimit,
SU(3)/TKK classification, positivity or a mass gap, or a physical model.
The causal diagram records mathematical prerequisites and is not presented
as an independently constructed formal declaration-graph object.

**Unresolved semantic nonconformances: none.** Any change to a reviewed Lean
source hash requires renewed semantic review. Compiler success, exact closure
axiom inspection, strict warnings, and native Lake acceptance remain the
responsibility of the separate runtime gate.
