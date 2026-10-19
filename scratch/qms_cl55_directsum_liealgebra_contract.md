# QMS evidence record: Lie algebra structure on the Cl(5,5) five-grade sum

## Claim and scope

On the existing external carrier

```lean
TkkFiveGradeSum := ⨁ i : Fin 5, tkkFiveGradeSubmodule i
```

transport the actual real Lie algebra structure on `EndV` across the existing
linear equivalence `tkkFiveGradeDirectSumEquiv`. Use the named
`tkkFiveGradeDirectSumLieRing` as the transported additive Lie structure, keep
all structures named/non-global, and prove the exact bracket-compatibility
equation for the reconstruction equivalence.

This is a representation-level packaging result. It does not add a full
indexed grading interface, prove a Lie-color structure, or claim a new
physical interpretation.

## Source-grounded facts

- `Cl55TKKGradeDirectSumInternal.lean` proves the internal direct-sum
  equivalence `tkkFiveGradeDirectSumEquiv : TkkFiveGradeSum ≃ₗ[ℝ] EndV`.
- `Cl55TKKDirectSumBracket.lean` defines
  `tkkFiveGradeDirectSumBracket` by transporting `tkkBracket`, proves its
  Jacobi identity, and defines the named non-global
  `tkkFiveGradeDirectSumLieRing`.
- `tkkFiveGradeDirectSumLieRing_bracket` proves that its bracket notation
  agrees with `tkkFiveGradeDirectSumBracket`.
- `tkkFiveGradeDirectSumLieAlgebra` equips the carrier with a named,
  non-global real Lie-algebra structure using that Lie ring and the existing
  real module structure.
- `tkkFiveGradeDirectSumEquiv_map_bracket` proves the reconstruction
  equivalence preserves the bracket under the named Lie-ring structure.
- `EndV` is an associative real endomorphism algebra; its commutator Lie ring
  is available locally through Mathlib's `LieRing.ofAssociativeRing`.

## Result established in the owner

The owner now provides a named, non-global real Lie-algebra structure and the
exact bracket-compatibility equation:

```lean
noncomputable def tkkFiveGradeDirectSumLieAlgebra :
  letI := tkkFiveGradeDirectSumLieRing
  LieAlgebra ℝ TkkFiveGradeSum

theorem tkkFiveGradeDirectSumEquiv_map_bracket
  (x y : TkkFiveGradeSum) :
  tkkFiveGradeDirectSumEquiv ⁅x, y⁆ =
    ⁅tkkFiveGradeDirectSumEquiv x, tkkFiveGradeDirectSumEquiv y⁆
```

The target EndV Lie-ring instance is local and comes from the associative
endomorphism algebra. The compatibility result is stated directly; the
external direct sum's pre-existing module instance is unchanged and no
`LieEquiv` is bundled.

## Exclusions

- No claim that the five selected bracket laws constitute a complete indexed
  `ℤ`-grading or a `ℤ₂ × ℤ₂` Lie-color algebra.
- No global instance installation that can create ambiguity with other
  transported structures.
- No bundled `LieEquiv` when its transport would require changing the
  direct-sum carrier's existing module/additive instances.
- The ambient commutator Jacobi and ambient grade-closure facts are reused
  from the existing owners. This owner proves their transported direct-sum
  consequences (`tkkFiveGradeDirectSumBracket_jacobi` and the
  `...lof_grade...` theorems).
- No extension to a colimit or physical carrier identification.

## Acceptance

Focused locked Lean build of the audit target completed successfully
(9045/9045 jobs). Its `#print axioms` output lists only `propext`,
`Classical.choice`, and `Quot.sound` for the audited declarations. The strict
OpenGauss screen reports zero violations. Independent QA-A source review
passed after the documentation corrections.

The Gate 4 CLI review was started on 2026-10-19 and emitted only its initial
“Running static preflight” message. After polling with no further output, the
invocation was interrupted (exit 130); Gate 4 remains incomplete, and this
record does not claim Gate 4 kernel certification.
