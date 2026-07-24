# Open Problem: Matrix-to-Cuntz Itakura--Saito Invariance Under Commuting Conjugation

## Precise Statement

Given:
- `n : ℕ`
- `S : CuntzTraceSocket n` with explicit hypotheses:
  - `S.trace : CuntzAlg n → ℝ`
  - `S.inv_of_image : Matrix (Fin n) (Fin n) ℂ → CuntzAlg n`
- `M N : Matrix (Fin n) (Fin n) ℂ`
- `k : CuntzAlg n` with `k * matrixToCuntz n M = matrixToCuntz n M * k` and
  `k * matrixToCuntz n N = matrixToCuntz n N * k`
- `h_trace_conj : S.trace (k * matrixToCuntz n M * k⁻¹) = S.trace (matrixToCuntz n M)`
- `h_inv_left : S.inv_of_image (k * matrixToCuntz n M * k⁻¹) = k * S.inv_of_image M * k⁻¹`

Prove:
```
cuntzItakuraSaitoDivergence n S (k * matrixToCuntz n M * k⁻¹)
                           (k * matrixToCuntz n N * k⁻¹) =
cuntzItakuraSaitoDivergence n S (matrixToCuntz n M) (matrixToCuntz n N)
```

Where:
```
cuntzItakuraSaitoDivergence n S X Y :=
  Real.log (S.trace X) - Real.log (S.trace Y) -
    S.trace (S.inv_of_image Y * (X - Y))
```

---

## Lemma Chain Plan

### Lemma 1: Conjugation preserves scalar trace of matrix image
**Statement**: Under `h_trace_conj`, `S.trace (k * matrixToCuntz n M * k⁻¹) = S.trace (matrixToCuntz n M)`.
**Dependencies**: `h_trace_conj` is already an explicit hypothesis.
**Proof sketch**: `rwa [h_trace_conj]` after unfolding `matrixToCuntz` is not needed; this is literally the hypothesis stated for `X = matrixToCuntz n M`.

### Lemma 2: Conjugation preserves the log-potential
**Statement**: Under `h_trace_conj`, `Real.log (S.trace (k * matrixToCuntz n M * k⁻¹)) = Real.log (S.trace (matrixToCuntz n M))`.
**Dependencies**: Lemma 1.
**Proof sketch**: `simp [Lemma1]` or `rw [Lemma1]`; `Real.log` is a function, so equality of arguments gives equality of values.

### Lemma 3: Conjugation preserves the inv-pairing term for Y
**Statement**: Under `S.trace (k * (S.inv_of_image Y) * k⁻¹) = S.trace (S.inv_of_image Y)` and
`S.inv_of_image (k * Y * k⁻¹) = k * S.inv_of_image Y * k⁻¹`, we have
`S.trace (S.inv_of_image (k * Y * k⁻¹) * (k * X * k⁻¹ - k * Y * k⁻¹)) = S.trace (S.inv_of_image Y * (X - Y))`.
**Dependencies**: Native mathlib: `Matrix.mul_assoc`, `mul_sub`, `sub_mul`, ring distributivity.
**Proof sketch**:
1. Expand `k * X * k⁻¹ - k * Y * k⁻¹` as `k * (X - Y) * k⁻¹` using `mul_sub` and `sub_mul`.
2. Substitute `S.inv_of_image (k * Y * k⁻¹) = k * S.inv_of_image Y * k⁻¹`.
3. The left side becomes `S.trace ((k * S.inv_of_image Y * k⁻¹) * (k * (X - Y) * k⁻¹))`.
4. By `mul_assoc`, this is `S.trace (k * S.inv_of_image Y * (k⁻¹ * k) * (X - Y) * k⁻¹)`.
5. Simplify `k⁻¹ * k = 1` using `inv_mul_cancel`.
6. The left side becomes `S.trace (k * S.inv_of_image Y * (X - Y) * k⁻¹)`.
7. By `h_trace_conj` with `X := S.inv_of_image Y * (X - Y)`, we get `S.trace (k * S.inv_of_image Y * (X - Y) * k⁻¹) = S.trace (S.inv_of_image Y * (X - Y))`.

### Lemma 4: Full divergence invariance under commuting conjugation
**Statement**: Under all the above hypotheses,
`cuntzItakuraSaitoDivergence n S (k * matrixToCuntz n M * k⁻¹) (k * matrixToCuntz n N * k⁻¹) =
 cuntzItakuraSaitoDivergence n S (matrixToCuntz n M) (matrixToCuntz n N)`.
**Dependencies**: Lemma 2, Lemma 3.
**Proof sketch**:
1. Unfold `cuntzItakuraSaitoDivergence`.
2. Apply `Lemma 2` to the log-potential difference.
3. Apply `Lemma 3` to the pairing term.
4. `simp` or `ring` to assemble the equality.

---

## What This Gives Us

Once these lemmas are proved, the operator-bridge claim becomes a genuine native-mathlib chain:
- `matrixToCuntz` is a concrete finite-sum definition
- Conjugation invariance reduces to algebraic manipulation of `mul_assoc`, `inv_mul_cancel`, and the explicit trace-conjugation hypothesis
- No `sorry`, no `by trivial`, no witness defaults

This is the minimal honest kernel-checked path for the open operator Itakura--Saito bridge.
