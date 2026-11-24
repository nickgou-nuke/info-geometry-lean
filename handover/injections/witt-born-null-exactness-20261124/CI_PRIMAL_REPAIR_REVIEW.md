# Primal/dual CI repair candidate

This candidate addresses only diagnostics emitted by scoped GitHub Actions run
45413662613, job 138513918858, against branch head
`0db6e19eadcfffbfc468138a25d88ff7bef326fb`.

## Candidate files

- `ZornPrimalDual.lean`: complete replacement candidate for the existing owner.
- `primal-repair.patch`: the four focused source edits as a unified diff.
- `metadata.json`: original/candidate SHA-256 hashes and validation status.

Original owner SHA-256:
`9ef2e4467d67cc3ced74b3c641d7f3fbb6fb53586a7266829594fadebf3ab3b9`.

Candidate owner SHA-256:
`e2705577751f0759455f8caecb1ba9481a109b39c409ca0a52ebd93615eab128`.

## Exact repairs

1. Add `RingHom.id_apply` to `encode.map_smul'`'s existing `simp only` list.
   The emitted residual goal differs only by `(RingHom.id ℝ) c` versus `c`.
   Pinned Mathlib's `Mathlib/Algebra/Ring/Hom/Defs.lean` declares the required
   theorem at line 529, proved by `rfl`.
2. Remove `Fin.sum_univ_three` from `primal_square` and `dual_square` only.
   The current compiler explicitly reported each argument unused; the other
   simplification arguments and the closing `ring` remain unchanged.
3. Rewrite the exact native carrier subtraction in the local helper for
   `mixed_operator_anticommutator` using `_root_.sub_eq_add_neg` before `ext`.
   Explicit arguments target that outer Zorn subtraction and leave the scalar
   hyperplane formula untouched by this rewrite.
4. Remove `ZornVectorMatrix.sub` and `ZornVectorMatrix.neg` from that helper's
   simp list. The existing registered coordinate simplifications already cover
   native negation after the subtraction rewrite.

## Why the subtraction distinction matters

In `Algebra/ZornVectorMatrix.lean`, the explicit functions are:

```lean
def sub (X Y : ZornVectorMatrix R) := add X (neg Y)

theorem sub_eq_add_neg (X Y : ZornVectorMatrix R) :
    sub X Y = add X (neg Y) := rfl
```

That namespaced lemma concerns the explicit function. The `AddCommGroup`
instance at lines 488–500 supplies native `add := add` and `neg := neg`, but
does not set `sub := ZornVectorMatrix.sub`. Thus the original simp argument
does not expose the native `A - B` seen in the CI residual coordinate goals.
The root group theorem is the correct interface for native subtraction.

The same owner supplies these registered native coordinate lemmas at
lines 511–514:

```lean
@[simp] theorem neg_a' (X : ZornVectorMatrix R) : (-X).a = -X.a := rfl
@[simp] theorem neg_v' (X : ZornVectorMatrix R) (i : Fin 3) :
    (-X).v i = -X.v i := rfl
@[simp] theorem neg_w' (X : ZornVectorMatrix R) (i : Fin 3) :
    (-X).w i = -X.w i := rfl
@[simp] theorem neg_b' (X : ZornVectorMatrix R) : (-X).b = -X.b := rfl
```

These suffice after the native subtraction is rewritten and coordinate
extensionality exposes the projections. Explicit `ZornVectorMatrix.neg`
unfolding is unnecessary.

## Scope and validation status

No theorem statements, carriers, mathematical conventions, imports, build
gates, pins, or audit rules change. The diagnostic on `norm_encode` saying its
declaration uses `sorry` is downstream of the failed `encode` definition;
no placeholder was added to the source.

This is a source-reviewed candidate only. No Lean compiler, build, cache
download, or test was run. No tracked repository file or GitHub state was
modified by this worker. Root integration and native validation remain pending.
