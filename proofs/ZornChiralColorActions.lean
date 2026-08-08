import proofs.ZornColorLieRepresentation

/-!
# Chirally separated color Lie actions

The raw mixed kernel and its chirality twist are combined to isolate their
positive and negative blocks.  Each block separately satisfies the `gl₃`
matrix-unit commutator, and the two supported families commute.
-/

noncomputable section

namespace ZornChiralColorActions

open CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation
open SplitOctonionBraidSU3
open ZornThreeChannelCAR ZornColorLieAction

private theorem copy_neg_val {q : TrialitySector} (X : ZornCopy q) :
    (-X).val = zornSmul (-1) X.val := by
  rw [← neg_one_smul ℂ X, copy_smul_val]

private theorem copy_sub_val {q : TrialitySector} (X Y : ZornCopy q) :
    (X - Y).val = zornSub X.val Y.val := by
  rw [sub_eq_add_neg, copy_add_val, copy_neg_val]
  apply zorn_ext
  · simp [zornAdd, zornSub, zornSmul, sub_eq_add_neg]
  · funext i; simp [zornAdd, zornSub, zornSmul, sub_eq_add_neg]
  · funext i; simp [zornAdd, zornSub, zornSmul, sub_eq_add_neg]
  · simp [zornAdd, zornSub, zornSmul, sub_eq_add_neg]

/-- Positive-block color action, with the sign normalized to the standard
matrix-unit commutator convention. -/
def positiveColorOp (r s : Fin 3) : Module.End ℂ DiracSpinor16 :=
  (2 : ℂ)⁻¹ • (colorEvenOp r s - threeChannelMixed r s)

/-- Negative-block color action. -/
def negativeColorOp (r s : Fin 3) : Module.End ℂ DiracSpinor16 :=
  (2 : ℂ)⁻¹ • (colorEvenOp r s + threeChannelMixed r s)

/-- The positive family is exactly the positive `gl₃` block and vanishes on
the negative semispinor. -/
theorem positiveColorOp_apply (r s : Fin 3)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    positiveColorOp r s (S, C) = (⟨colorPlusZorn r s S.val⟩, 0) := by
  apply Prod.ext
  · apply ZornCopy.ext
    rw [positiveColorOp, LinearMap.smul_apply, LinearMap.sub_apply,
      Prod.smul_fst, Prod.fst_sub, copy_smul_val, copy_sub_val,
      colorEvenOp_fst_exact, threeChannelMixed_fst_exact]
    apply zorn_ext
    · simp [colorPlusZorn, zornSmul, zornSub]; ring
    · funext i; simp [colorPlusZorn, zornSmul, zornSub]; ring
    · funext i; simp [colorPlusZorn, zornSmul, zornSub]; ring
    · simp [colorPlusZorn, zornSmul, zornSub]; ring
  · apply ZornCopy.ext
    rw [positiveColorOp, LinearMap.smul_apply, LinearMap.sub_apply,
      Prod.smul_snd, Prod.snd_sub, copy_smul_val, copy_sub_val,
      colorEvenOp_snd_exact, threeChannelMixed_snd_exact]
    apply zorn_ext
    · simp [colorMinusZorn, zornSmul, zornSub]
    · funext i; simp [colorMinusZorn, zornSmul, zornSub]
    · funext i; simp [colorMinusZorn, zornSmul, zornSub]
    · simp [colorMinusZorn, zornSmul, zornSub]

/-- The negative family vanishes on the positive semispinor and is exactly
the negative `gl₃` block. -/
theorem negativeColorOp_apply (r s : Fin 3)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    negativeColorOp r s (S, C) = (0, ⟨colorMinusZorn r s C.val⟩) := by
  apply Prod.ext
  · apply ZornCopy.ext
    rw [negativeColorOp, LinearMap.smul_apply, LinearMap.add_apply,
      Prod.smul_fst, Prod.fst_add, copy_smul_val, copy_add_val,
      colorEvenOp_fst_exact, threeChannelMixed_fst_exact]
    apply zorn_ext
    · simp [colorPlusZorn, zornSmul, zornAdd]
    · funext i; simp [colorPlusZorn, zornSmul, zornAdd]
    · funext i; simp [colorPlusZorn, zornSmul, zornAdd]
    · simp [colorPlusZorn, zornSmul, zornAdd]
  · apply ZornCopy.ext
    rw [negativeColorOp, LinearMap.smul_apply, LinearMap.add_apply,
      Prod.smul_snd, Prod.snd_add, copy_smul_val, copy_add_val,
      colorEvenOp_snd_exact, threeChannelMixed_snd_exact]
    apply zorn_ext
    · simp [colorMinusZorn, zornSmul, zornAdd]; ring
    · funext i; simp [colorMinusZorn, zornSmul, zornAdd]; ring
    · funext i; simp [colorMinusZorn, zornSmul, zornAdd]; ring
    · simp [colorMinusZorn, zornSmul, zornAdd]; ring

theorem positiveColorOp_mul_apply (r s t u : Fin 3)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    (positiveColorOp r s * positiveColorOp t u) (S, C) =
      (⟨colorPlusZorn r s (colorPlusZorn t u S.val)⟩, 0) := by
  rw [Module.End.mul_apply, positiveColorOp_apply, positiveColorOp_apply]

theorem negativeColorOp_mul_apply (r s t u : Fin 3)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    (negativeColorOp r s * negativeColorOp t u) (S, C) =
      (0, ⟨colorMinusZorn r s (colorMinusZorn t u C.val)⟩) := by
  rw [Module.End.mul_apply, negativeColorOp_apply, negativeColorOp_apply]

/-- The positive supported family is a `gl₃` action. -/
theorem positiveColorOp_commutator (r s t u : Fin 3) :
    positiveColorOp r s * positiveColorOp t u -
        positiveColorOp t u * positiveColorOp r s =
      colorDelta s t • positiveColorOp r u -
        colorDelta u r • positiveColorOp t s := by
  apply LinearMap.ext
  rintro ⟨S, C⟩
  apply Prod.ext
  · apply ZornCopy.ext
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Prod.fst_sub,
      Prod.smul_fst]
    rw [positiveColorOp_mul_apply, positiveColorOp_mul_apply,
      positiveColorOp_apply, positiveColorOp_apply, copy_sub_val,
      copy_sub_val, copy_smul_val, copy_smul_val]
    exact colorPlusZorn_commutator r s t u S.val
  · apply ZornCopy.ext
    simp [positiveColorOp_apply]

/-- The negative supported family is a `gl₃` action. -/
theorem negativeColorOp_commutator (r s t u : Fin 3) :
    negativeColorOp r s * negativeColorOp t u -
        negativeColorOp t u * negativeColorOp r s =
      colorDelta s t • negativeColorOp r u -
        colorDelta u r • negativeColorOp t s := by
  apply LinearMap.ext
  rintro ⟨S, C⟩
  apply Prod.ext
  · apply ZornCopy.ext
    simp [negativeColorOp_apply]
  · apply ZornCopy.ext
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Prod.snd_sub,
      Prod.smul_snd]
    rw [negativeColorOp_mul_apply, negativeColorOp_mul_apply,
      negativeColorOp_apply, negativeColorOp_apply, copy_sub_val,
      copy_sub_val, copy_smul_val, copy_smul_val]
    exact colorMinusZorn_commutator r s t u C.val

/-- Opposite chiral supports annihilate each other in both orders. -/
theorem positive_negative_mul_eq_zero (r s t u : Fin 3) :
    positiveColorOp r s * negativeColorOp t u = 0 := by
  apply LinearMap.ext
  rintro ⟨S, C⟩
  rw [Module.End.mul_apply, negativeColorOp_apply, positiveColorOp_apply]
  apply Prod.ext <;> apply ZornCopy.ext <;> apply zorn_ext
  · simp [colorPlusZorn, mixedPlusZorn, zornSmul]
  · funext i; simp [colorPlusZorn, mixedPlusZorn, zornSmul]
  · funext i; simp [colorPlusZorn, mixedPlusZorn, zornSmul]
  · simp [colorPlusZorn, mixedPlusZorn, zornSmul]
  · simp
  · funext i; simp
  · funext i; simp
  · simp

theorem negative_positive_mul_eq_zero (r s t u : Fin 3) :
    negativeColorOp r s * positiveColorOp t u = 0 := by
  apply LinearMap.ext
  rintro ⟨S, C⟩
  rw [Module.End.mul_apply, positiveColorOp_apply, negativeColorOp_apply]
  apply Prod.ext <;> apply ZornCopy.ext <;> apply zorn_ext
  · simp
  · funext i; simp
  · funext i; simp
  · simp
  · simp [colorMinusZorn, mixedMinusZorn]
  · funext i; simp [colorMinusZorn, mixedMinusZorn]
  · funext i; simp [colorMinusZorn, mixedMinusZorn]
  · simp [colorMinusZorn, mixedMinusZorn]

/-- The two chiral color actions commute because they have disjoint support. -/
theorem positive_negative_commute (r s t u : Fin 3) :
    positiveColorOp r s * negativeColorOp t u =
      negativeColorOp t u * positiveColorOp r s := by
  rw [positive_negative_mul_eq_zero, negative_positive_mul_eq_zero]

end ZornChiralColorActions

end noncomputable section
