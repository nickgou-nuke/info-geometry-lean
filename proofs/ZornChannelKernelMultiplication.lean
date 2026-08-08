import proofs.ZornThreeChannelCAR

/-!
# Multiplication of the color-resolved CAR kernel

This module calculates `C r s * C t u` on both chiral Zorn blocks.  The
result decides, rather than assumes, whether the nine kernel entries are
matrix units.
-/

noncomputable section

namespace ZornChannelKernelMultiplication

open SplitOctonionBraidSU3
open CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation
open ZornChiralLightcone ZornThreeChannelCAR
open ZornLightconeCAR ZornLightconeChannelOperator

private theorem copy_val_zero (q : TrialitySector) :
    (0 : ZornCopy q).val = zornZero := by
  apply zorn_ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

/-- Calculated positive block of `C_rs C_tu`. -/
def mixedPlusProductZorn (r s t u : Fin 3) (X : Zorn) : Zorn where
  a := colorDelta r s * colorDelta t u * X.a
  u := fun i => colorDelta i r * colorDelta s t * X.u u
  v := fun i =>
    colorDelta i s * colorDelta r u * X.v t -
      colorDelta i s * colorDelta t u * X.v r -
      colorDelta r s * colorDelta i u * X.v t +
      colorDelta r s * colorDelta t u * X.v i
  b := 0

/-- Calculated negative block of `C_rs C_tu`. -/
def mixedMinusProductZorn (r s t u : Fin 3) (X : Zorn) : Zorn where
  a := 0
  u := fun i =>
    colorDelta i r * colorDelta s t * X.u u -
      colorDelta i r * colorDelta t u * X.u s -
      colorDelta r s * colorDelta i t * X.u u +
      colorDelta r s * colorDelta t u * X.u i
  v := fun i => colorDelta i s * colorDelta r u * X.v t
  b := colorDelta r s * colorDelta t u * X.b

/-- Coordinate multiplication law on the positive chiral block. -/
theorem mixedPlusZorn_comp (r s t u : Fin 3) (X : Zorn) :
    mixedPlusZorn r s (mixedPlusZorn t u X) =
      mixedPlusProductZorn r s t u X := by
  apply zorn_ext
  · simp [mixedPlusZorn, mixedPlusProductZorn, colorDelta]
    split_ifs <;> ring
  · funext i
    simp [mixedPlusZorn, mixedPlusProductZorn, colorDelta]
    split_ifs <;> ring
  · funext i
    simp [mixedPlusZorn, mixedPlusProductZorn, colorDelta]
    split_ifs <;> ring
  · rfl

/-- Coordinate multiplication law on the negative chiral block. -/
theorem mixedMinusZorn_comp (r s t u : Fin 3) (X : Zorn) :
    mixedMinusZorn r s (mixedMinusZorn t u X) =
      mixedMinusProductZorn r s t u X := by
  apply zorn_ext
  · rfl
  · funext i
    simp [mixedMinusZorn, mixedMinusProductZorn, colorDelta]
    split_ifs <;> ring
  · funext i
    simp [mixedMinusZorn, mixedMinusProductZorn, colorDelta]
    split_ifs <;> ring
  · simp [mixedMinusZorn, mixedMinusProductZorn, colorDelta]
    split_ifs <;> ring

/-- Exact positive chiral action of a product of two kernel entries. -/
theorem threeChannelMixed_mul_fst_exact (r s t u : Fin 3)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    ((threeChannelMixed r s * threeChannelMixed t u) (S, C)).1.val =
      mixedPlusProductZorn r s t u S.val := by
  rw [Module.End.mul_apply, threeChannelMixed_fst_exact,
    threeChannelMixed_fst_exact, mixedPlusZorn_comp]

/-- Exact negative chiral action of a product of two kernel entries. -/
theorem threeChannelMixed_mul_snd_exact (r s t u : Fin 3)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    ((threeChannelMixed r s * threeChannelMixed t u) (S, C)).2.val =
      mixedMinusProductZorn r s t u C.val := by
  rw [Module.End.mul_apply, threeChannelMixed_snd_exact,
    threeChannelMixed_snd_exact, mixedMinusZorn_comp]

private theorem mixedPlusProductZorn_offdiag_sq
    {r s : Fin 3} (h : r ≠ s) (X : Zorn) :
    mixedPlusProductZorn r s r s X = zornZero := by
  fin_cases r <;> fin_cases s
  all_goals try contradiction
  all_goals
    apply zorn_ext <;>
      simp [mixedPlusProductZorn, colorDelta, zornZero]

private theorem mixedMinusProductZorn_offdiag_sq
    {r s : Fin 3} (h : r ≠ s) (X : Zorn) :
    mixedMinusProductZorn r s r s X = zornZero := by
  fin_cases r <;> fin_cases s
  all_goals try contradiction
  all_goals
    apply zorn_ext <;>
      simp [mixedMinusProductZorn, colorDelta, zornZero]

/-- All six off-diagonal mixed kernel entries are square-zero. -/
theorem channelKernel_offdiag_sq {r s : Fin 3} (h : r ≠ s) :
    threeChannelMixed r s * threeChannelMixed r s = 0 := by
  apply LinearMap.ext
  rintro ⟨S, C⟩
  rw [LinearMap.zero_apply]
  apply Prod.ext
  · apply ZornCopy.ext
    have hf := threeChannelMixed_mul_fst_exact r s r s S C
    rw [mixedPlusProductZorn_offdiag_sq h] at hf
    rw [Prod.fst_zero]
    rw [copy_val_zero]
    exact hf
  · apply ZornCopy.ext
    have hs := threeChannelMixed_mul_snd_exact r s r s S C
    rw [mixedMinusProductZorn_offdiag_sq h] at hs
    rw [Prod.snd_zero]
    rw [copy_val_zero]
    exact hs

/-- Each diagonal kernel entry is anti-idempotent, not idempotent. -/
theorem channelKernel_diag_sq (r : Fin 3) :
    threeChannelMixed r r * threeChannelMixed r r =
      -threeChannelMixed r r := by
  rw [threeChannelMixed_diag, lightconeChannelProjector_sq]

/-- Consequently the unnormalized kernel entries cannot be matrix units. -/
theorem channelKernel_diag_not_idempotent (r : Fin 3) :
    threeChannelMixed r r * threeChannelMixed r r ≠
      threeChannelMixed r r := by
  intro h
  rw [channelKernel_diag_sq] at h
  have hadd : threeChannelMixed r r + threeChannelMixed r r = 0 :=
    neg_eq_iff_add_eq_zero.mp h
  have htwo : (2 : ℂ) • threeChannelMixed r r = 0 := by
    simpa [two_smul ℂ] using hadd
  have hz : threeChannelMixed r r = 0 := by
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  exact threeChannelMixed_ne_zero r r hz

/-- The textbook matrix-unit multiplication law is false for the kernel `C`. -/
theorem not_channelKernel_matrixUnitLaw :
    ¬ (∀ r s t u : Fin 3,
      threeChannelMixed r s * threeChannelMixed t u =
        if s = t then threeChannelMixed r u else 0) := by
  intro h
  have hdiag := h 0 0 0 0
  exact channelKernel_diag_not_idempotent 0 hdiag

/--
Capstone: both chiral multiplication laws are explicitly calculated and the
ordinary matrix-unit law is ruled out.
-/
theorem channelKernel_multiplication_classification :
    (∀ (r s t u : Fin 3) (X : Zorn),
      mixedPlusZorn r s (mixedPlusZorn t u X) =
        mixedPlusProductZorn r s t u X) ∧
    (∀ (r s t u : Fin 3) (X : Zorn),
      mixedMinusZorn r s (mixedMinusZorn t u X) =
        mixedMinusProductZorn r s t u X) ∧
    (∀ r : Fin 3,
      threeChannelMixed r r * threeChannelMixed r r =
        -threeChannelMixed r r) ∧
    ¬ (∀ r s t u : Fin 3,
      threeChannelMixed r s * threeChannelMixed t u =
        if s = t then threeChannelMixed r u else 0) := by
  exact ⟨mixedPlusZorn_comp, mixedMinusZorn_comp,
    channelKernel_diag_sq, not_channelKernel_matrixUnitLaw⟩

end ZornChannelKernelMultiplication

end noncomputable section
