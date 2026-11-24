# Independent review of the NullIncidence repair

Reviewed candidate SHA256:
`6696706bfb2db944fd8f8899fc729c17bd417f983b99d6bb7e0884018bf26a37`.

Reviewed baseline: recovered checkout commit
`c97caca572514f128e846212ca30f050414dabac`, owner SHA256
`b6818a42c5c3f6057878438891042eb36fd479d69d3eb3ec433f7eb97e9b24a2`.
The reviewer independently read the complete candidate, its source diff,
and the native diagnostic log from run `45416776463`, diagnostic execution
`c73ae23678dd44f398d46c2a8ef7184f`.

## Findings

No source-level blocker was identified in the proposed repair.

### Rank arithmetic uses the same two dimensions

The original `omega` diagnostic displayed two separate internal atoms for
the printed kernel finrank. The candidate binds `kernelDim` and `rangeDim`
once, changes the target to `kernelDim = 4`, and gives both bounds and
rank-nullity explicit expected types using those same local values.

The pinned theorem `LinearMap.finrank_range_add_finrank_ker` states
range finrank plus kernel finrank equals source finrank. Composing it with
`zorn_finrank` gives exactly `rangeDim + kernelDim = 8`. The resulting
natural-number facts `kernelDim ≤ 4`, `rangeDim ≤ 4`, and their sum equal to
eight imply the desired equality. No additional rank assumption is supplied.
The explicit type of each fact ensures elaboration must first reconcile its
underlying dimension expression with the same named dimensions.

### Explicit zeros match the rewritten APIs

The recovered carrier's `AddCommGroup` instance sets `zero := zero`.
Thus native zero and `ZornVectorMatrix.zero` are definitionally the same
element, while the named multiplication and conjugation lemmas explicitly
use the latter syntax.

Changing kernel membership to `mul x y = ZornVectorMatrix.zero` makes the
substitution into `kirmse_right y x` produce the exact left side of
`ZornVectorMatrix.zero_mul`. The contraction remains
`(x ⋆ y) ⋆ conj y = norm y • x`; nonzero `x` then forces `norm y = 0`.

In the conjugate-nonzero proof, changing the zero presentations in the
hypothesis and target lets the existing `conj_conj` and `conj_zero` lemmas
rewrite directly. The contradiction still uses the original nonzero
hypothesis; neither exactness nor nonzero conjugation is assumed.

### Local finite-dimensional evidence is unchanged

The four `letI` to `let` changes follow the four precise style warnings in
the log. Each keeps the same class-valued local evidence obtained from
`FiniteDimensional.of_finrank_eq_succ zorn_finrank`; it introduces no new
assumption. Pinned Mathlib uses ordinary local `have`/`let` declarations of
this proposition-valued class in proof contexts as well.

## Preserved mathematical contract

All theorem statements and hypotheses are unchanged. The actual null
kernel and range have dimension four only for a nonzero null Zorn element.
Conjugate range inclusion for any null element and equality for a nonzero
null element retain their original scope. The equality proof still combines
contraction, nonzero conjugation, and equal four-dimensional subspaces via
`Submodule.eq_of_le_of_finrank_eq`.

There are no import, linter-option, pin, gate, axiom, or operator changes.

## Validation boundary

This is independent source review only. No compiler, build, test, syntax
parser, axiom audit, tracked-file edit, or GitHub mutation was performed by
the reviewer. The parent must obtain native acceptance from the unchanged
strict suite. Diagnostic execution is not strict acceptance.
