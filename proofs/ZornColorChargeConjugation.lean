import proofs.ZornChiralColorActions

/-!
# Conjugate-linear exchange of the chiral color sectors

This file keeps the complex-linear chirality involution separate from the
conjugate-linear block exchange.  The latter is a finite algebraic analogue
of charge conjugation; no analytic Tomita--Takesaki statement is asserted.
-/

noncomputable section

namespace ZornColorChargeConjugation

open CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation
open SplitOctonionBraidSU3
open ZornThreeChannelCAR ZornColorLieAction ZornChiralColorActions

abbrev complexConjHom : ℂ →+* ℂ :=
  Complex.conjAe.toRingEquiv.toRingHom

/-- Coefficient conjugation together with the particle/antiparticle exchange
of the two scalar and two color coordinates. -/
def particleConjZorn (X : Zorn) : Zorn where
  a := complexConjHom X.b
  u := fun i => complexConjHom (X.v i)
  v := fun i => complexConjHom (X.u i)
  b := complexConjHom X.a

theorem particleConjZorn_add (X Y : Zorn) :
    particleConjZorn (zornAdd X Y) =
      zornAdd (particleConjZorn X) (particleConjZorn Y) := by
  apply zorn_ext
  · simp [particleConjZorn, zornAdd]
  · funext i; simp [particleConjZorn, zornAdd]
  · funext i; simp [particleConjZorn, zornAdd]
  · simp [particleConjZorn, zornAdd]

theorem particleConjZorn_smul (c : ℂ) (X : Zorn) :
    particleConjZorn (zornSmul c X) =
      zornSmul (complexConjHom c) (particleConjZorn X) := by
  apply zorn_ext
  · simp [particleConjZorn, zornSmul]
  · funext i; simp [particleConjZorn, zornSmul]
  · funext i; simp [particleConjZorn, zornSmul]
  · simp [particleConjZorn, zornSmul]

@[simp] theorem particleConjZorn_sq (X : Zorn) :
    particleConjZorn (particleConjZorn X) = X := by
  apply zorn_ext
  · simp [particleConjZorn, complexConjHom]
  · funext i; simp [particleConjZorn, complexConjHom]
  · funext i; simp [particleConjZorn, complexConjHom]
  · simp [particleConjZorn, complexConjHom]

def plusToMinus (S : SpinorPlus8) : SpinorMinus8 :=
  ⟨particleConjZorn S.val⟩

def minusToPlus (C : SpinorMinus8) : SpinorPlus8 :=
  ⟨particleConjZorn C.val⟩

theorem plusToMinus_add (S T : SpinorPlus8) :
    plusToMinus (S + T) = plusToMinus S + plusToMinus T := by
  apply ZornCopy.ext
  simp only [plusToMinus]
  rw [copy_add_val, copy_add_val]
  exact particleConjZorn_add S.val T.val

theorem minusToPlus_add (C D : SpinorMinus8) :
    minusToPlus (C + D) = minusToPlus C + minusToPlus D := by
  apply ZornCopy.ext
  simp only [minusToPlus]
  rw [copy_add_val, copy_add_val]
  exact particleConjZorn_add C.val D.val

theorem plusToMinus_smul (c : ℂ) (S : SpinorPlus8) :
    plusToMinus (c • S) = complexConjHom c • plusToMinus S := by
  apply ZornCopy.ext
  simp only [plusToMinus]
  rw [copy_smul_val, copy_smul_val]
  exact particleConjZorn_smul c S.val

theorem minusToPlus_smul (c : ℂ) (C : SpinorMinus8) :
    minusToPlus (c • C) = complexConjHom c • minusToPlus C := by
  apply ZornCopy.ext
  simp only [minusToPlus]
  rw [copy_smul_val, copy_smul_val]
  exact particleConjZorn_smul c C.val

/-- Conjugate-linear exchange of the two semispinors. -/
def chargeConjugation :
    DiracSpinor16 →ₛₗ[complexConjHom] DiracSpinor16 where
  toFun X := (minusToPlus X.2, plusToMinus X.1)
  map_add' X Y := by
    apply Prod.ext
    · exact minusToPlus_add X.2 Y.2
    · exact plusToMinus_add X.1 Y.1
  map_smul' c X := by
    apply Prod.ext
    · exact minusToPlus_smul c X.2
    · exact plusToMinus_smul c X.1

@[simp] theorem chargeConjugation_apply
    (S : SpinorPlus8) (C : SpinorMinus8) :
    chargeConjugation (S, C) = (minusToPlus C, plusToMinus S) := rfl

/-- The finite conjugate-linear exchange is involutive. -/
theorem chargeConjugation_sq (X : DiracSpinor16) :
    chargeConjugation (chargeConjugation X) = X := by
  rcases X with ⟨S, C⟩
  apply Prod.ext <;> apply ZornCopy.ext <;> exact particleConjZorn_sq _

/-- Conjugation exchanges the positive color action with the transpose-indexed
negative action.  The minus sign is forced by the established normalization
of the two `gl₃` blocks. -/
theorem particleConjZorn_colorPlus (r s : Fin 3) (X : Zorn) :
    particleConjZorn (colorPlusZorn r s X) =
      zornSmul (-1) (colorMinusZorn s r (particleConjZorn X)) := by
  apply zorn_ext
  · by_cases hrs : r = s <;>
      simp [particleConjZorn, colorPlusZorn, colorMinusZorn, mixedPlusZorn,
        mixedMinusZorn, zornSmul, complexConjHom, colorDelta, hrs, eq_comm]
  · funext i
    by_cases hrs : r = s <;> by_cases hir : r = i <;> by_cases his : s = i <;>
      simp [particleConjZorn, colorPlusZorn, colorMinusZorn, mixedPlusZorn,
        mixedMinusZorn, zornSmul, complexConjHom, colorDelta, hrs, hir, his,
        eq_comm]
  · funext i
    by_cases hrs : r = s <;> by_cases hir : r = i <;> by_cases his : s = i <;>
      simp [particleConjZorn, colorPlusZorn, colorMinusZorn, mixedPlusZorn,
        mixedMinusZorn, zornSmul, complexConjHom, colorDelta, hrs, hir, his,
        eq_comm]
  · by_cases hrs : r = s <;>
      simp [particleConjZorn, colorPlusZorn, colorMinusZorn, mixedPlusZorn,
        mixedMinusZorn, zornSmul, complexConjHom, colorDelta, hrs, eq_comm]

theorem particleConjZorn_colorMinus (r s : Fin 3) (X : Zorn) :
    particleConjZorn (colorMinusZorn r s X) =
      zornSmul (-1) (colorPlusZorn s r (particleConjZorn X)) := by
  apply zorn_ext
  · by_cases hrs : r = s <;>
      simp [particleConjZorn, colorPlusZorn, colorMinusZorn, mixedPlusZorn,
        mixedMinusZorn, zornSmul, complexConjHom, colorDelta, hrs, eq_comm]
  · funext i
    by_cases hrs : r = s <;> by_cases hir : r = i <;> by_cases his : s = i <;>
      simp [particleConjZorn, colorPlusZorn, colorMinusZorn, mixedPlusZorn,
        mixedMinusZorn, zornSmul, complexConjHom, colorDelta, hrs, hir, his,
        eq_comm]
  · funext i
    by_cases hrs : r = s <;> by_cases hir : r = i <;> by_cases his : s = i <;>
      simp [particleConjZorn, colorPlusZorn, colorMinusZorn, mixedPlusZorn,
        mixedMinusZorn, zornSmul, complexConjHom, colorDelta, hrs, hir, his,
        eq_comm]
  · by_cases hrs : r = s <;>
      simp [particleConjZorn, colorPlusZorn, colorMinusZorn, mixedPlusZorn,
        mixedMinusZorn, zornSmul, complexConjHom, colorDelta, hrs, eq_comm]

/-- Operator-level particle/antiparticle exchange for the positive action. -/
theorem chargeConjugation_positiveColorOp (r s : Fin 3)
    (X : DiracSpinor16) :
    chargeConjugation (positiveColorOp r s X) =
      (-1 : ℂ) • negativeColorOp s r (chargeConjugation X) := by
  rcases X with ⟨S, C⟩
  rw [positiveColorOp_apply, chargeConjugation_apply,
    chargeConjugation_apply, negativeColorOp_apply]
  apply Prod.ext
  · apply ZornCopy.ext
    rw [Prod.smul_fst, copy_smul_val]
    apply zorn_ext
    · simp [minusToPlus, particleConjZorn, zornSmul]
    · funext i; simp [minusToPlus, particleConjZorn, zornSmul]
    · funext i; simp [minusToPlus, particleConjZorn, zornSmul]
    · simp [minusToPlus, particleConjZorn, zornSmul]
  · apply ZornCopy.ext
    rw [Prod.smul_snd, copy_smul_val]
    exact particleConjZorn_colorPlus r s S.val

/-- Operator-level particle/antiparticle exchange for the negative action. -/
theorem chargeConjugation_negativeColorOp (r s : Fin 3)
    (X : DiracSpinor16) :
    chargeConjugation (negativeColorOp r s X) =
      (-1 : ℂ) • positiveColorOp s r (chargeConjugation X) := by
  rcases X with ⟨S, C⟩
  rw [negativeColorOp_apply, chargeConjugation_apply,
    chargeConjugation_apply, positiveColorOp_apply]
  apply Prod.ext
  · apply ZornCopy.ext
    rw [Prod.smul_fst, copy_smul_val]
    exact particleConjZorn_colorMinus r s C.val
  · apply ZornCopy.ext
    rw [Prod.smul_snd, copy_smul_val]
    apply zorn_ext
    · simp [plusToMinus, particleConjZorn, zornSmul]
    · funext i; simp [plusToMinus, particleConjZorn, zornSmul]
    · funext i; simp [plusToMinus, particleConjZorn, zornSmul]
    · simp [plusToMinus, particleConjZorn, zornSmul]
end ZornColorChargeConjugation

end noncomputable section
