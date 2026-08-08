import proofs.ZornChannelKernelMultiplication

/-!
# Chirality-twisted color Lie action

The raw mixed CAR kernel has opposite signs on its two chiral blocks.  Twisting
by `(-χ)` aligns those blocks.  This file calculates and proves the resulting
`gl₃` commutator law.
-/

noncomputable section

namespace ZornColorLieAction

open SplitOctonionBraidSU3
open CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation
open ZornCliffordParityAPI ZornChiralLightcone
open ZornThreeChannelCAR ZornChannelKernelMultiplication

/-- Sign of chirality: `(-S,C)` on the two semispinor blocks. -/
def chiralitySign : Module.End ℂ DiracSpinor16 := -chiralityOperator

@[simp] theorem chiralitySign_apply (S : SpinorPlus8) (C : SpinorMinus8) :
    chiralitySign (S, C) = (-S, C) := by
  simp [chiralitySign]

/-- Chirality-twisted mixed CAR entry. -/
def colorEvenOp (r s : Fin 3) : Module.End ℂ DiracSpinor16 :=
  chiralitySign * threeChannelMixed r s

/-- Positive Zorn block of the twisted color action. -/
def colorPlusZorn (r s : Fin 3) (X : Zorn) : Zorn :=
  zornSmul (-1) (mixedPlusZorn r s X)

/-- Negative Zorn block of the twisted color action. -/
def colorMinusZorn (r s : Fin 3) (X : Zorn) : Zorn :=
  mixedMinusZorn r s X

private theorem copy_neg_val {q : TrialitySector} (X : ZornCopy q) :
    (-X).val = zornSmul (-1) X.val := by
  rw [← neg_one_smul ℂ X, copy_smul_val]

private theorem copy_sub_val {q : TrialitySector} (X Y : ZornCopy q) :
    (X - Y).val = zornSub X.val Y.val := by
  rw [sub_eq_add_neg, copy_add_val, copy_neg_val]
  apply zorn_ext
  · simp [zornAdd, zornSub, zornSmul, sub_eq_add_neg]
  · funext i
    simp [zornAdd, zornSub, zornSmul, sub_eq_add_neg]
  · funext i
    simp [zornAdd, zornSub, zornSmul, sub_eq_add_neg]
  · simp [zornAdd, zornSub, zornSmul, sub_eq_add_neg]

theorem colorDelta_symm (r s : Fin 3) : colorDelta r s = colorDelta s r := by
  simp [colorDelta, eq_comm]

/-- `gl₃` commutator on the positive Zorn block. -/
theorem colorPlusZorn_commutator (r s t u : Fin 3) (X : Zorn) :
    zornSub
        (colorPlusZorn r s (colorPlusZorn t u X))
        (colorPlusZorn t u (colorPlusZorn r s X)) =
      zornSub
        (zornSmul (colorDelta s t) (colorPlusZorn r u X))
        (zornSmul (colorDelta u r) (colorPlusZorn t s X)) := by
  apply zorn_ext
  · simp [colorPlusZorn, mixedPlusZorn, zornSmul, zornSub]
    rw [colorDelta_symm t s, colorDelta_symm u r]
    ring
  · funext i
    simp [colorPlusZorn, mixedPlusZorn, zornSmul, zornSub]
    ring
  · funext i
    simp [colorPlusZorn, mixedPlusZorn, zornSmul, zornSub]
    rw [colorDelta_symm t s, colorDelta_symm u r]
    ring
  · simp [colorPlusZorn, mixedPlusZorn, zornSmul, zornSub]

/-- Exact positive chiral block of the twisted operator. -/
theorem colorEvenOp_fst_exact (r s : Fin 3)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    (colorEvenOp r s (S, C)).1.val = colorPlusZorn r s S.val := by
  rw [colorEvenOp, Module.End.mul_apply]
  generalize hY : threeChannelMixed r s (S, C) = Y
  rcases Y with ⟨S', C'⟩
  rw [chiralitySign_apply, copy_neg_val, colorPlusZorn]
  have hf := threeChannelMixed_fst_exact r s S C
  rw [hY] at hf
  rw [hf]

/-- Exact negative chiral block of the twisted operator. -/
theorem colorEvenOp_snd_exact (r s : Fin 3)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    (colorEvenOp r s (S, C)).2.val = colorMinusZorn r s C.val := by
  rw [colorEvenOp, Module.End.mul_apply]
  generalize hY : threeChannelMixed r s (S, C) = Y
  rcases Y with ⟨S', C'⟩
  rw [chiralitySign_apply, colorMinusZorn]
  have hs := threeChannelMixed_snd_exact r s S C
  rw [hY] at hs
  exact hs

theorem colorEvenOp_mul_fst_exact (r s t u : Fin 3)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    ((colorEvenOp r s * colorEvenOp t u) (S, C)).1.val =
      colorPlusZorn r s (colorPlusZorn t u S.val) := by
  rw [Module.End.mul_apply, colorEvenOp_fst_exact, colorEvenOp_fst_exact]

theorem colorEvenOp_mul_snd_exact (r s t u : Fin 3)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    ((colorEvenOp r s * colorEvenOp t u) (S, C)).2.val =
      colorMinusZorn r s (colorMinusZorn t u C.val) := by
  rw [Module.End.mul_apply, colorEvenOp_snd_exact, colorEvenOp_snd_exact]

/-- `gl₃` commutator on the negative Zorn block. -/
theorem colorMinusZorn_commutator (r s t u : Fin 3) (X : Zorn) :
    zornSub
        (colorMinusZorn r s (colorMinusZorn t u X))
        (colorMinusZorn t u (colorMinusZorn r s X)) =
      zornSub
        (zornSmul (colorDelta s t) (colorMinusZorn r u X))
        (zornSmul (colorDelta u r) (colorMinusZorn t s X)) := by
  apply zorn_ext
  · simp [colorMinusZorn, mixedMinusZorn, zornSmul, zornSub]
  · funext i
    simp [colorMinusZorn, mixedMinusZorn, zornSmul, zornSub]
    rw [colorDelta_symm t s, colorDelta_symm u r]
    ring
  · funext i
    simp [colorMinusZorn, mixedMinusZorn, zornSmul, zornSub]
    rw [colorDelta_symm t s, colorDelta_symm u r]
    ring
  · simp [colorMinusZorn, mixedMinusZorn, zornSmul, zornSub]
    rw [colorDelta_symm t s, colorDelta_symm u r]
    ring

/-- The chirality-twisted mixed kernel is a concrete `gl₃` Lie action. -/
theorem colorEvenOp_commutator (r s t u : Fin 3) :
    colorEvenOp r s * colorEvenOp t u -
        colorEvenOp t u * colorEvenOp r s =
      colorDelta s t • colorEvenOp r u -
        colorDelta u r • colorEvenOp t s := by
  apply LinearMap.ext
  rintro ⟨S, C⟩
  apply Prod.ext
  · apply ZornCopy.ext
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Prod.fst_sub,
      Prod.smul_fst]
    rw [copy_sub_val, copy_sub_val, copy_smul_val, copy_smul_val,
      colorEvenOp_mul_fst_exact, colorEvenOp_mul_fst_exact,
      colorEvenOp_fst_exact, colorEvenOp_fst_exact]
    exact colorPlusZorn_commutator r s t u S.val
  · apply ZornCopy.ext
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Prod.snd_sub,
      Prod.smul_snd]
    rw [copy_sub_val, copy_sub_val, copy_smul_val, copy_smul_val,
      colorEvenOp_mul_snd_exact, colorEvenOp_mul_snd_exact,
      colorEvenOp_snd_exact, colorEvenOp_snd_exact]
    exact colorMinusZorn_commutator r s t u C.val

/-- Capstone bundle for the color Lie-action layer. -/
theorem colorLieAction_classification :
    (∀ r s t u : Fin 3,
      colorEvenOp r s * colorEvenOp t u -
          colorEvenOp t u * colorEvenOp r s =
        colorDelta s t • colorEvenOp r u -
          colorDelta u r • colorEvenOp t s) ∧
    (∀ ⦃r s : Fin 3⦄, r ≠ s →
      threeChannelMixed r s * threeChannelMixed r s = 0) := by
  refine ⟨colorEvenOp_commutator, ?_⟩
  intro r s h
  exact channelKernel_offdiag_sq h

end ZornColorLieAction

end noncomputable section
